use crate::{
    order::Order,
    plan::Call,
    report::{Diagnostic, Location, Result, Status},
    work::Work,
};
use hddl_analyzer::*;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) type Bindings = BTreeMap<String, usize>;
type Scope = BTreeMap<String, String>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Atom {
    pub predicate: usize,
    pub arguments: Vec<usize>,
}
#[derive(Clone, Debug)]
pub(crate) struct Literal {
    pub atom: Atom,
    pub positive: bool,
}
#[derive(Clone, Debug, Default)]
pub(crate) enum Condition {
    #[default]
    True,
    False,
    Literal(Literal),
    And(Vec<Condition>),
    Or(Vec<Condition>),
}
impl Condition {
    fn constant(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }

    // Keep a formula tree in negation normal form; distributing into DNF can
    // multiply its size exponentially before execution checking even starts.
    fn junction(all: bool, parts: Vec<Self>) -> Self {
        let mut terms = vec![];
        for part in parts {
            match part {
                Self::False if all => return Self::False,
                Self::True if !all => return Self::True,
                Self::True | Self::False => (),
                Self::And(children) if all => terms.extend(children),
                Self::Or(children) if !all => terms.extend(children),
                other => terms.push(other),
            }
        }
        match terms.len() {
            0 => Self::constant(all),
            1 => terms.pop().unwrap(),
            _ if all => Self::And(terms),
            _ => Self::Or(terms),
        }
    }

    pub fn holds(&self, state: &BTreeSet<Atom>, work: &mut Work) -> Result<bool> {
        work.tick();
        match self {
            Self::True => Ok(true),
            Self::False => Ok(false),
            Self::Literal(l) => Ok(state.contains(&l.atom) == l.positive),
            Self::And(parts) | Self::Or(parts) => {
                let all = matches!(self, Self::And(_));
                for part in parts {
                    if part.holds(state, work)? != all {
                        return Ok(!all);
                    }
                }
                Ok(all)
            }
        }
    }

    pub fn conjunction<'a>(&'a self, work: &mut Work) -> Result<Option<Vec<&'a Literal>>> {
        work.tick();
        match self {
            Self::True | Self::False => Ok(Some(vec![])),
            Self::Literal(l) => Ok(Some(vec![l])),
            Self::Or(_) => Ok(None),
            Self::And(parts) => {
                let mut literals = vec![];
                for part in parts {
                    let Some(inner) = part.conjunction(work)? else {
                        return Ok(None);
                    };
                    literals.extend(inner);
                }
                Ok(Some(literals))
            }
        }
    }

    // None means that execution may change this formula's truth. A false
    // static disjunct alone cannot make the whole condition false.
    pub fn static_value(
        &self,
        state: &BTreeSet<Atom>,
        changed: &BTreeSet<Atom>,
        work: &mut Work,
    ) -> Result<Option<bool>> {
        work.tick();
        match self {
            Self::True => Ok(Some(true)),
            Self::False => Ok(Some(false)),
            Self::Literal(l) => {
                Ok((!changed.contains(&l.atom)).then(|| state.contains(&l.atom) == l.positive))
            }
            Self::And(parts) | Self::Or(parts) => {
                let all = matches!(self, Self::And(_));
                let mut dynamic = false;
                for part in parts {
                    match part.static_value(state, changed, work)? {
                        Some(value) if value != all => return Ok(Some(!all)),
                        None => dynamic = true,
                        _ => (),
                    }
                }
                Ok((!dynamic).then_some(all))
            }
        }
    }
}
#[derive(Clone, Debug)]
pub(crate) struct ConditionalEffect {
    pub condition: Condition,
    pub add: BTreeSet<Atom>,
    pub delete: BTreeSet<Atom>,
}
#[derive(Clone, Debug)]
pub(crate) struct GroundAction {
    pub condition: Condition,
    pub add: BTreeSet<Atom>,
    pub delete: BTreeSet<Atom>,
    pub conditional: Vec<ConditionalEffect>,
    pub cost: u128,
}
impl GroundAction {
    pub fn apply(&self, state: &mut BTreeSet<Atom>, work: &mut Work) -> Result<()> {
        work.charge((self.add.len() + self.delete.len() + state.len()) as u64);
        if self.conditional.is_empty() {
            state.retain(|a| !self.delete.contains(a));
            state.extend(self.add.iter().cloned());
            return Ok(());
        }
        let mut add = self.add.clone();
        let mut delete = self.delete.clone();
        // Every guard reads the same pre-action state, including guards whose
        // atoms are changed by unconditional or other conditional effects.
        for effect in &self.conditional {
            if effect.condition.holds(state, work)? {
                work.charge((effect.add.len() + effect.delete.len()) as u64);
                add.extend(effect.add.iter().cloned());
                delete.extend(effect.delete.iter().cloned());
            }
        }
        state.retain(|a| !delete.contains(a));
        state.extend(add);
        Ok(())
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Objective {
    Length,
    Cost,
    Makespan,
}

pub(crate) struct Model<'a> {
    pub domain: &'a DomainAST<'a>,
    pub problem: &'a ProblemAST<'a>,
    pub actions: BTreeMap<&'a str, usize>,
    pub methods: BTreeMap<&'a str, usize>,
    pub tasks: BTreeMap<&'a str, &'a [Symbol<'a>]>,
    predicates: BTreeMap<&'a str, usize>,
    functions: BTreeMap<&'a str, usize>,
    parents: BTreeMap<String, String>,
    objects: BTreeMap<String, usize>,
    object_names: Vec<String>,
    object_types: Vec<String>,
    constants: BTreeSet<String>,
    values: BTreeMap<(String, Vec<usize>), u128>,
    pub initial: BTreeSet<Atom>,
    pub objective: Objective,
}

fn number(n: &NumberType) -> Result<u128> {
    match n {
        NumberType::Integer(n) if *n >= 0 => Ok(*n as u128),
        _ => Err(Diagnostic::input(
            "integer_required",
            "costs must be non-negative integers",
        )),
    }
}

impl<'a> Model<'a> {
    pub fn new(
        domain: &'a DomainAST<'a>,
        problem: &'a ProblemAST<'a>,
        negative_init: &BTreeSet<(u32, u32)>,
        work: &mut Work,
    ) -> Result<Self> {
        if domain.name != problem.domain_name {
            return Err(Diagnostic::input(
                "domain_mismatch",
                "problem refers to a different domain",
            ));
        }
        let mut m = Self {
            domain,
            problem,
            actions: BTreeMap::new(),
            methods: BTreeMap::new(),
            tasks: BTreeMap::new(),
            predicates: BTreeMap::new(),
            functions: BTreeMap::new(),
            parents: BTreeMap::new(),
            objects: BTreeMap::new(),
            object_names: vec![],
            object_types: vec![],
            constants: BTreeSet::new(),
            values: BTreeMap::new(),
            initial: BTreeSet::new(),
            objective: Objective::Length,
        };
        for t in domain.types.iter().flatten() {
            work.tick();
            if t.name == "object"
                || m.parents
                    .insert(t.name.into(), t.symbol_type.unwrap_or("object").into())
                    .is_some()
            {
                return Err(m.error(
                    "duplicate_type",
                    format!("duplicate or reserved type {}", t.name),
                    "domain",
                    t.name_pos,
                ));
            }
        }
        for parent in m.parents.values() {
            m.known_type(parent)?;
        }
        for t in m.parents.keys() {
            let mut seen = BTreeSet::new();
            let mut current = t.as_str();
            while current != "object" {
                work.tick();
                if !seen.insert(current) {
                    return Err(Diagnostic::input(
                        "type_cycle",
                        format!("cyclic type hierarchy at {t}"),
                    ));
                }
                current = &m.parents[current];
            }
        }
        for (file, symbols) in [
            ("domain", domain.constants.as_deref().unwrap_or_default()),
            ("problem", problem.objects.as_slice()),
        ] {
            for object in symbols {
                work.tick();
                m.known_type(object.symbol_type.unwrap_or("object"))?;
                if object.name.starts_with('?') || m.objects.contains_key(object.name) {
                    return Err(m.error(
                        "object_declaration",
                        format!("duplicate or invalid object {}", object.name),
                        file,
                        object.name_pos,
                    ));
                }
                let id = m.object_names.len();
                m.objects.insert(object.name.into(), id);
                m.object_names.push(object.name.into());
                m.object_types
                    .push(object.symbol_type.unwrap_or("object").into());
                if file == "domain" {
                    m.constants.insert(object.name.into());
                }
            }
        }
        for (i, p) in domain.predicates.iter().enumerate() {
            if m.predicates.insert(p.name, i).is_some() {
                return Err(m.error(
                    "duplicate_predicate",
                    format!("duplicate predicate {}", p.name),
                    "domain",
                    p.name_pos,
                ));
            }
            m.scope(&p.variables, "domain")?;
        }
        for (i, f) in domain.functions.iter().enumerate() {
            if f.name == "makespan" || m.functions.insert(f.name, i).is_some() {
                return Err(m.error(
                    "function_declaration",
                    format!("duplicate or reserved function {}", f.name),
                    "domain",
                    f.name_pos,
                ));
            }
            m.scope(&f.variables, "domain")?;
        }
        for t in &domain.compound_tasks {
            if m.tasks.insert(t.name, &t.parameters).is_some() {
                return Err(m.error(
                    "duplicate_task",
                    format!("duplicate task {}", t.name),
                    "domain",
                    t.name_pos,
                ));
            }
            m.scope(&t.parameters, "domain")?;
        }
        for (i, a) in domain.actions.iter().enumerate() {
            if m.tasks.insert(a.name, &a.parameters).is_some() {
                return Err(m.error(
                    "duplicate_task",
                    format!("duplicate task/action {}", a.name),
                    "domain",
                    a.name_pos,
                ));
            }
            m.actions.insert(a.name, i);
        }
        for (i, method) in domain.methods.iter().enumerate() {
            if m.methods.insert(method.name.name, i).is_some() {
                return Err(m.error(
                    "duplicate_method",
                    format!("duplicate method {}", method.name.name),
                    "domain",
                    method.name.name_pos,
                ));
            }
        }
        let requirements: BTreeSet<_> = domain
            .requirements
            .iter()
            .chain(&problem.requirements)
            .map(ToString::to_string)
            .collect();
        for r in &requirements {
            if matches!(
                r.as_str(),
                ":fluents"
                    | ":numeric-fluents"
                    | ":probabilistic-effects"
                    | ":domain-axioms"
                    | ":durative-actions"
                    | ":duration-inequalities"
                    | ":continuous-effects"
            ) {
                return Err(Diagnostic::unsupported(format!(
                    "requirement {r} is outside bell's supported fragment"
                )));
            }
        }
        if requirements.contains(":action-costs") && requirements.contains(":makespan") {
            return Err(Diagnostic::input(
                "metric_requirements",
                ":action-costs and :makespan are mutually exclusive",
            ));
        }
        m.objective = match &problem.metric {
            None => Objective::Length,
            Some(Metric::Makespan) if requirements.contains(":makespan") => Objective::Makespan,
            Some(Metric::Minimize(NumericExpr::Fluent(f)))
                if f.name == "total-cost"
                    && f.variables.is_empty()
                    && requirements.contains(":action-costs") =>
            {
                Objective::Cost
            }
            _ => {
                return Err(Diagnostic::input(
                    "metric",
                    "expected a declared total-cost or makespan objective",
                ));
            }
        };
        if requirements.contains(":action-costs") && m.objective != Objective::Cost {
            return Err(Diagnostic::input(
                "cost_metric",
                ":action-costs requires the total-cost metric",
            ));
        }
        if m.objective != Objective::Cost
            && (!domain.functions.is_empty()
                || problem.init_values.as_ref().is_some_and(|v| !v.is_empty()))
        {
            return Err(Diagnostic::input(
                "cost_metric",
                "numeric functions require the total-cost metric",
            ));
        }
        let mut numeric_actions = 0;
        for a in &domain.actions {
            work.tick();
            let scope = m.scope(&a.parameters, "domain")?;
            let check = (|| {
                if let Some(c) = &a.preconditions {
                    m.check_condition(c, &scope, "domain", work)?;
                }
                let count = if let Some(e) = &a.effects {
                    m.check_effect(e, &scope, true, work)?
                } else {
                    0
                };
                if count > 1 {
                    return Err(Diagnostic::input(
                        "cost_effect",
                        "an action can have only one top-level cost increase",
                    ));
                }
                Ok(count)
            })();
            numeric_actions += check.map_err(|mut e| {
                if e.location.is_none() {
                    e.location = Some(Box::new(Location::new("domain", a.name_pos)));
                }
                e
            })?;
        }
        if (m.objective == Objective::Cost) != (numeric_actions > 0) {
            return Err(Diagnostic::input(
                "cost_metric",
                "total-cost metric must occur exactly when the domain has cost effects",
            ));
        }
        if numeric_actions > 0 && !domain.requirements.contains(&RequirementType::ActionCosts) {
            return Err(Diagnostic::input(
                "cost_requirement",
                "domain numeric effects require :action-costs",
            ));
        }
        for method in &domain.methods {
            work.tick();
            let scope = m.scope(&method.params, "domain")?;
            let parameters = m.tasks.get(method.task.name).ok_or_else(|| {
                m.error(
                    "unknown_task",
                    format!("unknown task {}", method.task.name),
                    "domain",
                    method.task.name_pos,
                )
            })?;
            if m.actions.contains_key(method.task.name) {
                return Err(m.error(
                    "method_head",
                    "a method must decompose a compound task",
                    "domain",
                    method.task.name_pos,
                ));
            }
            m.check_terms(parameters, &method.task_terms, &scope, "domain")?;
            if let Some(c) = &method.precondition {
                m.check_condition(c, &scope, "domain", work)?;
            }
            m.check_network(&method.tn, &scope, "domain", work)?;
        }
        if let Some(root) = &problem.init_tn {
            let scope = m.scope(root.parameters.as_deref().unwrap_or_default(), "problem")?;
            m.check_network(&root.tn, &scope, "problem", work)?;
        }
        if let Some(goal) = &problem.goal {
            m.check_condition(goal, &Scope::new(), "problem", work)?;
        }
        let mut negative = BTreeSet::new();
        for p in &problem.init_state {
            m.check_predicate(p, &Scope::new(), "problem")?;
            let atom = m.atom(p, &Bindings::new())?;
            if negative_init.contains(&(p.name_pos.line, p.name_pos.column)) {
                negative.insert(atom);
            } else {
                m.initial.insert(atom);
            }
        }
        if !m.initial.is_disjoint(&negative) {
            return Err(Diagnostic::input(
                "contradictory_init",
                "initial state contains both a fact and its negation",
            ));
        }
        for v in problem.init_values.iter().flatten() {
            m.check_function(&v.fluent, &Scope::new(), "problem")?;
            let key = (
                v.fluent.name.to_string(),
                m.arguments(&v.fluent.variables, &Bindings::new())?,
            );
            if m.values.insert(key, number(&v.value)?).is_some() {
                return Err(m.error(
                    "duplicate_value",
                    "duplicate numeric initialization",
                    "problem",
                    v.fluent.name_pos,
                ));
            }
        }
        if m.objective == Objective::Cost
            && (!m.functions.contains_key("total-cost")
                || !domain.functions[m.functions["total-cost"]]
                    .variables
                    .is_empty()
                || m.values.get(&("total-cost".into(), vec![])) != Some(&0))
        {
            return Err(Diagnostic::input(
                "total_cost",
                "total-cost must be declared without parameters and initialized to 0",
            ));
        }
        Ok(m)
    }

    fn error(
        &self,
        code: &str,
        message: impl Into<String>,
        file: &str,
        pos: TokenPosition,
    ) -> Diagnostic {
        Diagnostic::input(code, message).at(Location::new(file, pos))
    }
    fn known_type(&self, t: &str) -> Result<()> {
        if t == "object" || self.parents.contains_key(t) {
            Ok(())
        } else {
            Err(Diagnostic::input(
                "unknown_type",
                format!("unknown type {t}"),
            ))
        }
    }
    fn subtype<'b>(&'b self, mut actual: &'b str, expected: &str) -> bool {
        loop {
            if actual == expected {
                return true;
            }
            if actual == "object" {
                return false;
            }
            actual = &self.parents[actual];
        }
    }
    fn scope(&self, parameters: &[Symbol<'_>], file: &str) -> Result<Scope> {
        let mut scope = Scope::new();
        for p in parameters {
            let kind = p.symbol_type.unwrap_or("object");
            self.known_type(kind)?;
            if !p.name.starts_with('?') || scope.insert(p.name.into(), kind.into()).is_some() {
                return Err(self.error(
                    "parameter",
                    format!("duplicate or invalid parameter {}", p.name),
                    file,
                    p.name_pos,
                ));
            }
        }
        Ok(scope)
    }
    fn term_type<'b>(&'b self, term: &str, scope: &'b Scope, file: &str) -> Result<&'b str> {
        if term.starts_with('?') {
            return scope.get(term).map(String::as_str).ok_or_else(|| {
                Diagnostic::input("unbound_variable", format!("undeclared variable {term}"))
            });
        }
        if file == "domain" && !self.constants.contains(term) {
            return Err(Diagnostic::input(
                "unknown_constant",
                format!("{term} is not a domain constant"),
            ));
        }
        self.objects
            .get(term)
            .map(|&id| self.object_types[id].as_str())
            .ok_or_else(|| Diagnostic::input("unknown_object", format!("unknown object {term}")))
    }
    fn check_terms(
        &self,
        parameters: &[Symbol<'_>],
        terms: &[Symbol<'_>],
        scope: &Scope,
        file: &str,
    ) -> Result<()> {
        if parameters.len() != terms.len() {
            return Err(Diagnostic::input(
                "arity",
                format!(
                    "expected {} arguments, found {}",
                    parameters.len(),
                    terms.len()
                ),
            ));
        }
        for (p, t) in parameters.iter().zip(terms) {
            let actual = self
                .term_type(t.name, scope, file)
                .map_err(|e| e.at(Location::new(file, t.name_pos)))?;
            if !self.subtype(actual, p.symbol_type.unwrap_or("object")) {
                return Err(self.error(
                    "type_mismatch",
                    format!(
                        "{} has type {actual}; expected {}",
                        t.name,
                        p.symbol_type.unwrap_or("object")
                    ),
                    file,
                    t.name_pos,
                ));
            }
        }
        Ok(())
    }
    fn check_predicate(&self, p: &Predicate<'_>, scope: &Scope, file: &str) -> Result<()> {
        let &i = self.predicates.get(p.name).ok_or_else(|| {
            self.error(
                "unknown_predicate",
                format!("unknown predicate {}", p.name),
                file,
                p.name_pos,
            )
        })?;
        self.check_terms(
            &self.domain.predicates[i].variables,
            &p.variables,
            scope,
            file,
        )
    }
    fn check_function(&self, f: &Function<'_>, scope: &Scope, file: &str) -> Result<()> {
        let &i = self.functions.get(f.name).ok_or_else(|| {
            self.error(
                "unknown_function",
                format!("unknown function {}", f.name),
                file,
                f.name_pos,
            )
        })?;
        self.check_terms(
            &self.domain.functions[i].variables,
            &f.variables,
            scope,
            file,
        )
    }
    fn check_condition(
        &self,
        c: &Precondition<'_>,
        scope: &Scope,
        file: &str,
        work: &mut Work,
    ) -> Result<()> {
        work.tick();
        match c {
            Precondition::Empty => Ok(()),
            Precondition::Atom(p) => self.check_predicate(p, scope, file),
            Precondition::And(cs) | Precondition::Or(cs) => {
                for c in cs {
                    self.check_condition(c, scope, file, work)?;
                }
                Ok(())
            }
            Precondition::Not(c) => self.check_condition(c, scope, file, work),
            Precondition::Imply(a, b) => {
                self.check_condition(a, scope, file, work)?;
                self.check_condition(b, scope, file, work)
            }
            Precondition::Equals(a, b) => {
                self.term_type(a, scope, file)?;
                self.term_type(b, scope, file)?;
                Ok(())
            }
            Precondition::ForAll(vars, c) | Precondition::Exists(vars, c) => {
                let mut inner = scope.clone();
                inner.extend(self.scope(vars, file)?);
                self.check_condition(c, &inner, file, work)
            }
            _ => Err(Diagnostic::unsupported("non-HDDL condition connective")),
        }
    }
    fn check_effect(
        &self,
        effect: &Effect<'_>,
        scope: &Scope,
        top: bool,
        work: &mut Work,
    ) -> Result<usize> {
        work.tick();
        match effect {
            Effect::Empty => Ok(0),
            Effect::Atom(p) => {
                self.check_predicate(p, scope, "domain")?;
                Ok(0)
            }
            Effect::Not(e) if matches!(**e, Effect::Atom(_)) => {
                self.check_effect(e, scope, false, work)
            }
            Effect::And(es) => {
                let mut count = 0;
                for e in es {
                    // Only a numeric effect directly in the outer conjunction is top-level.
                    count += self.check_effect(
                        e,
                        scope,
                        top && matches!(**e, Effect::Numeric(_, _, _)),
                        work,
                    )?;
                }
                Ok(count)
            }
            Effect::ForAll(vars, e) => {
                let mut inner = scope.clone();
                inner.extend(self.scope(vars, "domain")?);
                self.check_effect(e, &inner, false, work)
            }
            Effect::Imply(guard, body) => {
                self.check_condition(guard, scope, "domain", work)?;
                self.check_conditional_body(body, scope, work)?;
                Ok(0)
            }
            Effect::Numeric(AssignmentOperator::Increase, f, n)
                if top && f.name == "total-cost" && f.variables.is_empty() =>
            {
                self.check_function(f, scope, "domain")?;
                match n {
                    NumericExpr::Number(n) => {
                        number(n)?;
                    }
                    NumericExpr::Fluent(f) if f.name != "total-cost" => {
                        self.check_function(f, scope, "domain")?
                    }
                    _ => {
                        return Err(Diagnostic::input(
                            "cost_expression",
                            "cost must be a non-negative integer or a static function term",
                        ));
                    }
                }
                Ok(1)
            }
            Effect::Numeric(_, _, _) => Err(Diagnostic::input(
                "cost_effect",
                "only one top-level increase of total-cost is permitted",
            )),
            _ => Err(Diagnostic::unsupported(
                "only deterministic add/delete, conditional, and universal effects are supported",
            )),
        }
    }

    fn check_conditional_body(
        &self,
        effect: &Effect<'_>,
        scope: &Scope,
        work: &mut Work,
    ) -> Result<()> {
        work.tick();
        let literal = |effect: &Effect<'_>, work: &mut Work| match effect {
            Effect::Atom(_) => self.check_effect(effect, scope, false, work).map(|_| ()),
            Effect::Not(inner) if matches!(**inner, Effect::Atom(_)) => {
                self.check_effect(effect, scope, false, work).map(|_| ())
            }
            Effect::Numeric(_, _, _) => Err(Diagnostic::input(
                "cost_effect",
                "cost effects cannot occur inside when",
            )),
            _ => Err(Diagnostic::input(
                "conditional_effect_body",
                "a when body must be a literal or a conjunction of literals",
            )),
        };
        match effect {
            Effect::And(parts) => {
                for part in parts {
                    literal(part, work)?;
                }
                Ok(())
            }
            _ => literal(effect, work),
        }
    }

    fn check_network(
        &self,
        tn: &HTN<'_>,
        scope: &Scope,
        file: &str,
        work: &mut Work,
    ) -> Result<()> {
        for task in &tn.subtasks {
            work.tick();
            let parameters = self.tasks.get(task.task.name).ok_or_else(|| {
                self.error(
                    "unknown_task",
                    format!("unknown task {}", task.task.name),
                    file,
                    task.task.name_pos,
                )
            })?;
            self.check_terms(parameters, &task.terms, scope, file)?;
        }
        for c in tn.constraints.iter().flatten() {
            let (a, b) = match c {
                Constraint::Equal(a, b) | Constraint::NotEqual(a, b) => (a, b),
            };
            self.term_type(a, scope, file)?;
            self.term_type(b, scope, file)?;
        }
        self.network_order(tn, work).map_err(|mut e| {
            if e.status == Status::InvalidPlan {
                e.status = Status::InputError;
            }
            e
        })?;
        Ok(())
    }
    pub fn network_order(&self, tn: &HTN<'_>, work: &mut Work) -> Result<Order> {
        let mut ids = BTreeMap::new();
        for (i, s) in tn.subtasks.iter().enumerate() {
            if let Some(id) = &s.id
                && ids.insert(id.name, i).is_some()
            {
                return Err(Diagnostic::input(
                    "duplicate_subtask_id",
                    format!("duplicate source subtask ID {}", id.name),
                ));
            }
        }
        let edges = match &tn.orderings {
            TaskOrdering::Total => (1..tn.subtasks.len())
                .map(|i| (i - 1, i))
                .collect::<Vec<_>>(),
            TaskOrdering::Partial(edges) => edges
                .iter()
                .map(|(a, b)| {
                    let lookup = |id: &str| {
                        ids.get(id).copied().ok_or_else(|| {
                            Diagnostic::input(
                                "ordering_reference",
                                format!("unknown source subtask ID {id}"),
                            )
                        })
                    };
                    Ok((lookup(a)?, lookup(b)?))
                })
                .collect::<Result<Vec<_>>>()?,
        };
        Order::new(tn.subtasks.len(), edges, work)
    }
    pub fn bind(&self, parameters: &[Symbol<'_>], args: &[String]) -> Result<Bindings> {
        if parameters.len() != args.len() {
            return Err(Diagnostic::invalid(
                "binding_arity",
                format!(
                    "expected {} arguments, found {}",
                    parameters.len(),
                    args.len()
                ),
            ));
        }
        let mut env = Bindings::new();
        for (p, arg) in parameters.iter().zip(args) {
            let &id = self.objects.get(arg).ok_or_else(|| {
                Diagnostic::invalid("unknown_object", format!("unknown object {arg}"))
            })?;
            if !self.subtype(&self.object_types[id], p.symbol_type.unwrap_or("object")) {
                return Err(Diagnostic::invalid(
                    "binding_type",
                    format!(
                        "object {arg} is not of type {}",
                        p.symbol_type.unwrap_or("object")
                    ),
                ));
            }
            env.insert(p.name.into(), id);
        }
        Ok(env)
    }
    fn resolve(&self, term: &str, env: &Bindings) -> Result<usize> {
        if term.starts_with('?') {
            env.get(term)
        } else {
            self.objects.get(term)
        }
        .copied()
        .ok_or_else(|| Diagnostic::input("unbound_term", format!("unbound term {term}")))
    }
    fn arguments(&self, terms: &[Symbol<'_>], env: &Bindings) -> Result<Vec<usize>> {
        terms.iter().map(|t| self.resolve(t.name, env)).collect()
    }
    pub fn call(&self, name: &str, terms: &[Symbol<'_>], env: &Bindings) -> Result<Call> {
        Ok(Call {
            name: name.into(),
            args: self
                .arguments(terms, env)?
                .iter()
                .map(|&i| self.object_names[i].clone())
                .collect(),
        })
    }
    fn atom(&self, p: &Predicate<'_>, env: &Bindings) -> Result<Atom> {
        Ok(Atom {
            predicate: self.predicates[p.name],
            arguments: self.arguments(&p.variables, env)?,
        })
    }
    pub fn atom_label(&self, atom: &Atom) -> String {
        let mut words = vec![self.domain.predicates[atom.predicate].name.to_string()];
        words.extend(atom.arguments.iter().map(|&i| self.object_names[i].clone()));
        format!("({})", words.join(" "))
    }
    pub fn constraints(&self, tn: &HTN<'_>, env: &Bindings) -> Result<()> {
        for c in tn.constraints.iter().flatten() {
            let (a, b, equal) = match c {
                Constraint::Equal(a, b) => (a, b, true),
                Constraint::NotEqual(a, b) => (a, b, false),
            };
            if (self.resolve(a, env)? == self.resolve(b, env)?) != equal {
                return Err(Diagnostic::invalid(
                    "binding_constraint",
                    format!("task-network constraint on {a} and {b} fails"),
                ));
            }
        }
        Ok(())
    }
    fn assignments(
        &self,
        vars: &[Symbol<'_>],
        env: &Bindings,
        work: &mut Work,
    ) -> Result<Vec<Bindings>> {
        let mut all = vec![env.clone()];
        for v in vars {
            let mut next = vec![];
            for binding in &all {
                for (id, kind) in self.object_types.iter().enumerate() {
                    work.tick();
                    if self.subtype(kind, v.symbol_type.unwrap_or("object")) {
                        let mut binding = binding.clone();
                        binding.insert(v.name.into(), id);
                        next.push(binding);
                    }
                }
            }
            all = next;
        }
        Ok(all)
    }
    pub fn condition(
        &self,
        c: Option<&Precondition<'_>>,
        env: &Bindings,
        work: &mut Work,
    ) -> Result<Condition> {
        match c {
            Some(c) => self.formula(c, env, false, work),
            None => Ok(Condition::True),
        }
    }
    fn formula(
        &self,
        c: &Precondition<'_>,
        env: &Bindings,
        negative: bool,
        work: &mut Work,
    ) -> Result<Condition> {
        work.tick();
        match c {
            Precondition::Empty => Ok(Condition::constant(!negative)),
            Precondition::Atom(p) => Ok(Condition::Literal(Literal {
                atom: self.atom(p, env)?,
                positive: !negative,
            })),
            Precondition::Equals(a, b) => Ok(Condition::constant(
                (self.resolve(a, env)? == self.resolve(b, env)?) != negative,
            )),
            Precondition::Not(c) => self.formula(c, env, !negative, work),
            Precondition::And(cs) | Precondition::Or(cs) => {
                let all = matches!(c, Precondition::And(_)) != negative;
                let mut parts = vec![];
                for c in cs {
                    parts.push(self.formula(c, env, negative, work)?);
                }
                Ok(Condition::junction(all, parts))
            }
            Precondition::Imply(a, b) => Ok(Condition::junction(
                negative,
                vec![
                    self.formula(a, env, !negative, work)?,
                    self.formula(b, env, negative, work)?,
                ],
            )),
            Precondition::ForAll(vars, body) | Precondition::Exists(vars, body) => {
                let all = matches!(c, Precondition::ForAll(_, _)) != negative;
                let mut parts = vec![];
                for env in self.assignments(vars, env, work)? {
                    parts.push(self.formula(body, &env, negative, work)?);
                }
                Ok(Condition::junction(all, parts))
            }
            _ => Err(Diagnostic::unsupported("non-HDDL condition connective")),
        }
    }
    pub fn ground_action(&self, call: &Call, work: &mut Work) -> Result<GroundAction> {
        let &i = self.actions.get(call.name.as_str()).ok_or_else(|| {
            Diagnostic::invalid("unknown_action", format!("{} is not an action", call.name))
        })?;
        let schema = &self.domain.actions[i];
        let env = self.bind(&schema.parameters, &call.args)?;
        let mut action = GroundAction {
            condition: self.condition(schema.preconditions.as_ref(), &env, work)?,
            add: BTreeSet::new(),
            delete: BTreeSet::new(),
            conditional: vec![],
            cost: if self.objective == Objective::Cost {
                0
            } else {
                1
            },
        };
        if let Some(e) = &schema.effects {
            self.effects(e, &env, &mut action, work)?;
        }
        // Simultaneous STRIPS effects: add wins over delete.
        action.delete.retain(|a| !action.add.contains(a));
        Ok(action)
    }
    fn effects(
        &self,
        e: &Effect<'_>,
        env: &Bindings,
        out: &mut GroundAction,
        work: &mut Work,
    ) -> Result<()> {
        work.tick();
        match e {
            Effect::Empty => (),
            Effect::Atom(p) => {
                out.add.insert(self.atom(p, env)?);
            }
            Effect::Not(e) => {
                if let Effect::Atom(p) = &**e {
                    out.delete.insert(self.atom(p, env)?);
                }
            }
            Effect::And(es) => {
                for e in es {
                    self.effects(e, env, out, work)?;
                }
            }
            Effect::ForAll(vars, e) => {
                for env in self.assignments(vars, env, work)? {
                    self.effects(e, &env, out, work)?;
                }
            }
            Effect::Imply(guard, body) => {
                let mut effect = ConditionalEffect {
                    condition: self.condition(Some(guard), env, work)?,
                    add: BTreeSet::new(),
                    delete: BTreeSet::new(),
                };
                self.effect_literals(body, env, &mut effect, work)?;
                match effect.condition {
                    Condition::False => (),
                    Condition::True => {
                        out.add.extend(effect.add);
                        out.delete.extend(effect.delete);
                    }
                    _ => out.conditional.push(effect),
                }
            }
            Effect::Numeric(_, _, n) => {
                out.cost = match n {
                    NumericExpr::Number(n) => number(n)?,
                    NumericExpr::Fluent(f) => *self
                        .values
                        .get(&(f.name.into(), self.arguments(&f.variables, env)?))
                        .ok_or_else(|| {
                            Diagnostic::invalid(
                                "undefined_cost",
                                format!(
                                    "action {} uses undefined cost function {}",
                                    self.domain.name, f.name
                                ),
                            )
                        })?,
                    _ => {
                        return Err(Diagnostic::input(
                            "cost_expression",
                            "invalid cost expression",
                        ));
                    }
                }
            }
            _ => {
                return Err(Diagnostic::unsupported(
                    "non-deterministic or non-HDDL effect",
                ));
            }
        }
        Ok(())
    }

    fn effect_literals(
        &self,
        effect: &Effect<'_>,
        env: &Bindings,
        out: &mut ConditionalEffect,
        work: &mut Work,
    ) -> Result<()> {
        work.tick();
        match effect {
            Effect::Atom(p) => {
                out.add.insert(self.atom(p, env)?);
            }
            Effect::Not(inner) => {
                if let Effect::Atom(p) = &**inner {
                    out.delete.insert(self.atom(p, env)?);
                }
            }
            Effect::And(parts) => {
                for part in parts {
                    self.effect_literals(part, env, out, work)?;
                }
            }
            _ => {
                return Err(Diagnostic::input(
                    "conditional_effect_body",
                    "invalid when body",
                ));
            }
        }
        Ok(())
    }
}
