use super::{Call, Result, Tree, Work};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
enum Expr {
    Atom(String),
    List(Vec<Expr>),
}

impl Expr {
    fn atom(&self) -> Result<&str> {
        match self {
            Self::Atom(s) => Ok(s),
            _ => Err("expected HDDL symbol".into()),
        }
    }
    fn list(&self) -> Result<&[Self]> {
        match self {
            Self::List(v) => Ok(v),
            _ => Err("expected HDDL list".into()),
        }
    }
    fn head(&self) -> &str {
        self.list()
            .ok()
            .and_then(|v| v.first())
            .and_then(|s| s.atom().ok())
            .unwrap_or("")
    }
    fn field(&self, key: &str) -> Result<Option<&Self>> {
        let list = self.list()?;
        let mut found = None;
        for (i, value) in list.iter().enumerate() {
            if value.atom().ok() == Some(key) {
                if found.is_some() {
                    return Err(format!("duplicate {key}"));
                }
                found = Some(
                    list.get(i + 1)
                        .ok_or_else(|| format!("missing {key} value"))?,
                );
            }
        }
        Ok(found)
    }
    fn sections(&self, key: &str) -> Result<Vec<&Self>> {
        Ok(self.list()?.iter().filter(|e| e.head() == key).collect())
    }
    fn named(&self, key: &str) -> Result<String> {
        let blocks = self.sections(key)?;
        if blocks.len() != 1 {
            return Err(format!("expected one {key} block"));
        }
        let parts = blocks[0].list()?;
        if parts.len() != 2 {
            return Err(format!("invalid {key} name"));
        }
        let value = parts[1].atom()?;
        name(value)?;
        Ok(value.into())
    }
}

fn name(text: &str) -> Result<()> {
    if !text.starts_with(|c: char| c.is_ascii_alphabetic())
        || !text
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'-')
    {
        return Err(format!("invalid source HDDL name: {text}"));
    }
    Ok(())
}

fn parse(text: &str, work: &mut Work) -> Result<Expr> {
    let mut stack: Vec<Vec<Expr>> = vec![vec![]];
    let text = text
        .lines()
        .map(|l| l.split(';').next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n");
    let text = text
        .replace('(', " ( ")
        .replace(')', " ) ")
        .to_ascii_lowercase();
    for token in text.split_whitespace() {
        work.tick();
        match token {
            "(" => {
                if stack.len() > 256 {
                    return Err("HDDL nesting limit exceeded".into());
                }
                stack.push(vec![]);
            }
            ")" => {
                if stack.len() == 1 {
                    return Err("unbalanced HDDL parentheses".into());
                }
                let node = Expr::List(stack.pop().unwrap());
                stack.last_mut().unwrap().push(node);
            }
            value => stack.last_mut().unwrap().push(Expr::Atom(value.into())),
        }
    }
    if stack.len() != 1 || stack[0].len() != 1 || stack[0][0].head() != "define" {
        return Err("expected one HDDL define form".into());
    }
    Ok(stack.pop().unwrap().pop().unwrap())
}

fn typed(list: &[Expr]) -> Result<Vec<(String, String)>> {
    let mut result = vec![];
    let mut pending = vec![];
    let mut index = 0;
    while index < list.len() {
        let value = list[index].atom()?;
        if value == "-" {
            if pending.is_empty() {
                return Err("invalid typed parameter list".into());
            }
            index += 1;
            let kind = list.get(index).ok_or("missing parameter type")?.atom()?;
            result.extend(pending.drain(..).map(|s| (s, kind.into())));
        } else {
            pending.push(value.into());
        }
        index += 1;
    }
    result.extend(pending.into_iter().map(|s| (s, "object".into())));
    Ok(result)
}

type Env = BTreeMap<String, String>;
type State = BTreeSet<Vec<String>>;

fn resolve(term: &str, env: &Env) -> Result<String> {
    if term.starts_with('?') {
        env.get(term)
            .cloned()
            .ok_or_else(|| format!("unbound source variable {term}"))
    } else {
        Ok(term.into())
    }
}

fn ground(expr: &Expr, env: &Env) -> Result<Vec<String>> {
    expr.list()?
        .iter()
        .map(|e| resolve(e.atom()?, env))
        .collect()
}

fn unify(expr: &Expr, call: &Call, env: &mut Env) -> Result<()> {
    let words = expr.list()?;
    if words.len() != call.args.len() + 1 || expr.head() != call.name {
        return Err("source task mismatch".into());
    }
    for (word, arg) in words[1..].iter().zip(&call.args) {
        let term = word.atom()?;
        if term.starts_with('?') {
            if env
                .insert(term.into(), arg.clone())
                .is_some_and(|old| old != *arg)
            {
                return Err(format!("inconsistent source binding for {term}"));
            }
        } else if term != arg {
            return Err("source task constant mismatch".into());
        }
    }
    Ok(())
}

fn subtasks(schema: &Expr) -> Result<Vec<&Expr>> {
    let mut tasks = None;
    for key in [":subtasks", ":ordered-subtasks", ":tasks", ":ordered-tasks"] {
        if let Some(value) = schema.field(key)? {
            if tasks.is_some() {
                return Err("multiple source subtask lists".into());
            }
            tasks = Some(value);
        }
    }
    let Some(tasks) = tasks else {
        return Ok(vec![]);
    };
    let list = tasks.list()?;
    let list: Vec<_> = if tasks.head() == "and" {
        list[1..].iter().collect()
    } else if list.is_empty() {
        vec![]
    } else {
        vec![tasks]
    };
    list.into_iter()
        .map(|task| {
            let parts = task.list()?;
            Ok(if parts.len() == 2 && matches!(parts[1], Expr::List(_)) {
                &parts[1]
            } else {
                task
            })
        })
        .collect()
}

pub(super) struct Source {
    domain: Expr,
    problem: Expr,
    domain_name: String,
    problem_name: String,
    objects: BTreeMap<String, BTreeSet<String>>,
}

impl Source {
    pub(super) fn parse(domain: &str, problem: &str, work: &mut Work) -> Result<Self> {
        let domain = parse(domain, work)?;
        let problem = parse(problem, work)?;
        let domain_name = domain.named("domain")?;
        let problem_name = problem.named("problem")?;
        if problem.named(":domain")? != domain_name {
            return Err("source domain name mismatch".into());
        }
        let mut parents: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for block in domain.sections(":types")? {
            for (kind, parent) in typed(&block.list()?[1..])? {
                parents.entry(kind).or_default().insert(parent);
            }
        }
        let mut objects: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for block in domain
            .sections(":constants")?
            .into_iter()
            .chain(problem.sections(":objects")?)
        {
            for (object, kind) in typed(&block.list()?[1..])? {
                name(&object)?;
                let mut pending = vec![kind, "object".into()];
                let mut seen = BTreeSet::new();
                while let Some(kind) = pending.pop() {
                    work.tick();
                    if seen.insert(kind.clone()) {
                        pending.extend(parents.get(&kind).into_iter().flatten().cloned());
                        objects.entry(kind).or_default().insert(object.clone());
                    }
                }
            }
        }
        Ok(Self {
            domain,
            problem,
            domain_name,
            problem_name,
            objects,
        })
    }

    pub(super) fn header(&self) -> String {
        format!(
            "(define (plan {}-solution)\n  (:domain {})\n  (:problem {})\n",
            self.problem_name, self.domain_name, self.problem_name
        )
    }

    fn assignments(
        &self,
        params: &[(String, String)],
        fixed: &Env,
        work: &mut Work,
        mut accept: impl FnMut(&Env, &mut Work) -> Result<bool>,
    ) -> Result<Option<Env>> {
        let mut choices = vec![];
        for (variable, kind) in params {
            let values = self.objects.get(kind);
            let items: Vec<_> = if let Some(value) = fixed.get(variable) {
                if !values.is_some_and(|v| v.contains(value)) {
                    return Err("source parameter type mismatch".into());
                }
                vec![value.clone()]
            } else {
                values.into_iter().flatten().cloned().collect()
            };
            if items.is_empty() {
                return Ok(None);
            }
            choices.push(items);
        }
        let mut indices = vec![0; params.len()];
        loop {
            work.tick();
            let mut env = fixed.clone();
            for ((variable, _), (items, &index)) in params.iter().zip(choices.iter().zip(&indices))
            {
                env.insert(variable.clone(), items[index].clone());
            }
            if accept(&env, work)? {
                return Ok(Some(env));
            }
            let mut position = indices.len();
            loop {
                if position == 0 {
                    return Ok(None);
                }
                position -= 1;
                indices[position] += 1;
                if indices[position] < choices[position].len() {
                    break;
                }
                indices[position] = 0;
            }
        }
    }

    fn condition(
        &self,
        expr: Option<&Expr>,
        env: &Env,
        state: &State,
        work: &mut Work,
    ) -> Result<bool> {
        work.tick();
        let Some(expr) = expr else {
            return Ok(true);
        };
        let parts = expr.list()?;
        if parts.is_empty() {
            return Ok(true);
        }
        match expr.head() {
            "and" | "or" => {
                let all = expr.head() == "and";
                for part in &parts[1..] {
                    if self.condition(Some(part), env, state, work)? != all {
                        return Ok(!all);
                    }
                }
                Ok(all)
            }
            "not" if parts.len() == 2 => Ok(!self.condition(Some(&parts[1]), env, state, work)?),
            "imply" if parts.len() == 3 => {
                Ok(!self.condition(Some(&parts[1]), env, state, work)?
                    || self.condition(Some(&parts[2]), env, state, work)?)
            }
            "=" if parts.len() == 3 => {
                Ok(resolve(parts[1].atom()?, env)? == resolve(parts[2].atom()?, env)?)
            }
            "forall" | "exists" if parts.len() == 3 => {
                let universal = expr.head() == "forall";
                let params = typed(parts[1].list()?)?;
                let mut outer = env.clone();
                for (v, _) in &params {
                    outer.remove(v);
                }
                let witness = self.assignments(&params, &outer, work, |binding, work| {
                    Ok(self.condition(Some(&parts[2]), binding, state, work)? != universal)
                })?;
                Ok(witness.is_none() == universal)
            }
            "not" | "imply" | "=" | "forall" | "exists" => Err("malformed source condition".into()),
            _ => Ok(state.contains(&ground(expr, env)?)),
        }
    }

    fn effects(
        &self,
        expr: &Expr,
        env: &Env,
        state: &State,
        add: &mut State,
        delete: &mut State,
        work: &mut Work,
    ) -> Result<()> {
        work.tick();
        let parts = expr.list()?;
        if parts.is_empty() {
            return Ok(());
        }
        match expr.head() {
            "and" => {
                for part in &parts[1..] {
                    self.effects(part, env, state, add, delete, work)?;
                }
            }
            "not" if parts.len() == 2 => {
                delete.insert(ground(&parts[1], env)?);
            }
            "when" if parts.len() == 3 => {
                if self.condition(Some(&parts[1]), env, state, work)? {
                    self.effects(&parts[2], env, state, add, delete, work)?;
                }
            }
            "forall" if parts.len() == 3 => {
                let params = typed(parts[1].list()?)?;
                let mut outer = env.clone();
                for (v, _) in &params {
                    outer.remove(v);
                }
                self.assignments(&params, &outer, work, |binding, work| {
                    self.effects(&parts[2], binding, state, add, delete, work)?;
                    Ok(false)
                })?;
            }
            "increase" if parts.len() == 3 && parts[1].head() == "total-cost" => {}
            "increase" | "assign" | "decrease" | "scale-up" | "scale-down" | "not" | "when"
            | "forall" => return Err("unsupported source effect".into()),
            _ => {
                add.insert(ground(expr, env)?);
            }
        }
        Ok(())
    }

    fn bindings(
        &self,
        schema: &Expr,
        head: Option<&Call>,
        children: &[u64],
        tree: &Tree,
        state: &State,
        work: &mut Work,
    ) -> Result<Vec<String>> {
        let params = schema
            .field(":parameters")?
            .map(|e| typed(e.list()?))
            .transpose()?
            .unwrap_or_default();
        let mut env = Env::new();
        if let Some(head) = head {
            unify(
                schema.field(":task")?.ok_or("missing source method head")?,
                head,
                &mut env,
            )?;
        }
        let tasks = subtasks(schema)?;
        if tasks.len() != children.len() {
            return Err("source subtask count mismatch".into());
        }
        for (task, child) in tasks.into_iter().zip(children) {
            unify(task, &tree.nodes[child].call, &mut env)?;
        }
        if env.keys().any(|v| !params.iter().any(|(p, _)| p == v)) {
            return Err("undeclared source method parameter".into());
        }
        let env = self
            .assignments(&params, &env, work, |env, work| {
                Ok(
                    self.condition(schema.field(":constraints")?, env, state, work)?
                        && self.condition(schema.field(":precondition")?, env, state, work)?,
                )
            })?
            .ok_or(
                "no source parameter binding satisfies the method guard at its execution point",
            )?;
        Ok(params.iter().map(|(v, _)| env[v].clone()).collect())
    }

    pub(super) fn bind(
        &self,
        tree: &Tree,
        work: &mut Work,
    ) -> Result<(Vec<String>, BTreeMap<u64, Call>)> {
        let mut state = State::new();
        for init in self.problem.sections(":init")? {
            for fact in &init.list()?[1..] {
                if fact.head() != "=" && fact.head() != "not" {
                    state.insert(ground(fact, &Env::new())?);
                }
            }
        }
        let roots = self.problem.sections(":htn")?;
        if roots.len() != 1 {
            return Err("HDDL output requires one source initial task network".into());
        }
        let root_args = self.bindings(roots[0], None, &tree.roots, tree, &state, work)?;
        let mut schemas = BTreeMap::new();
        for method in self.domain.sections(":method")? {
            let method_name = method.list()?.get(1).ok_or("missing method name")?.atom()?;
            if schemas.insert(method_name, method).is_some() {
                return Err("duplicate source method".into());
            }
        }
        let actions: BTreeMap<_, _> = self
            .domain
            .sections(":action")?
            .into_iter()
            .map(|a| Ok((a.list()?.get(1).ok_or("missing action name")?.atom()?, a)))
            .collect::<Result<_>>()?;
        let mut pending: Vec<_> = tree
            .nodes
            .iter()
            .filter(|(_, n)| n.method.is_some())
            .map(|(&id, n)| (n.position, id))
            .collect();
        pending.sort_unstable();
        let mut pending = pending.into_iter().peekable();
        let mut methods = BTreeMap::new();
        for action in tree
            .actions
            .iter()
            .copied()
            .map(Some)
            .chain(std::iter::once(None))
        {
            let position = action.map_or(usize::MAX, |id| tree.nodes[&id].position);
            while pending.peek().is_some_and(|&(p, _)| p <= position) {
                work.tick();
                let (_, id) = pending.next().unwrap();
                let node = &tree.nodes[&id];
                let method = node.method.as_deref().unwrap();
                let schema = schemas
                    .get(method)
                    .ok_or_else(|| format!("unknown source method {method}"))?;
                let args =
                    self.bindings(schema, Some(&node.call), &node.children, tree, &state, work)?;
                methods.insert(
                    id,
                    Call {
                        name: method.into(),
                        args,
                    },
                );
            }
            let Some(id) = action else {
                break;
            };
            let call = &tree.nodes[&id].call;
            let schema = actions
                .get(call.name.as_str())
                .ok_or_else(|| format!("unknown source action {}", call.name))?;
            let params = schema
                .field(":parameters")?
                .map(|e| typed(e.list()?))
                .transpose()?
                .unwrap_or_default();
            if params.len() != call.args.len() {
                return Err("source action arity mismatch".into());
            }
            let env: Env = params
                .iter()
                .zip(&call.args)
                .map(|((v, _), a)| (v.clone(), a.clone()))
                .collect();
            for ((_, kind), arg) in params.iter().zip(&call.args) {
                if !self
                    .objects
                    .get(kind)
                    .is_some_and(|values| values.contains(arg))
                {
                    return Err("source action type mismatch".into());
                }
            }
            if !self.condition(schema.field(":precondition")?, &env, &state, work)? {
                return Err("source action is not executable".into());
            }
            let mut add = State::new();
            let mut delete = State::new();
            if let Some(effect) = schema.field(":effect")? {
                self.effects(effect, &env, &state, &mut add, &mut delete, work)?;
            }
            for fact in delete {
                state.remove(&fact);
            }
            state.extend(add);
        }
        if !self.condition(
            self.problem
                .sections(":goal")?
                .first()
                .and_then(|g| g.list().ok()?.get(1)),
            &Env::new(),
            &state,
            work,
        )? {
            return Err("source goal is not satisfied".into());
        }
        Ok((root_args, methods))
    }
}
