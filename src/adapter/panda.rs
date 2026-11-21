use super::{Call, Node, Result, Tree, Work};
use std::collections::BTreeMap;

fn compressed_method(tree: &mut Tree, id: u64) -> Result<()> {
    let node = tree.nodes[&id].clone();
    let method = node.method.as_deref().unwrap();
    let body = method
        .strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .ok_or("malformed compressed method")?;
    let mut depth = 0usize;
    let mut start = 0;
    let mut parts = vec![];
    for (i, c) in body.char_indices() {
        match c {
            '<' => depth += 1,
            '>' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or("malformed compressed method nesting")?
            }
            ';' if depth == 0 => {
                parts.push(&body[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&body[start..]);
    if parts.len() != 5 || depth != 0 {
        return Err("malformed compressed method fields".into());
    }
    let slot: usize = parts[3]
        .parse()
        .map_err(|_| "invalid compressed method slot")?;
    let translation: Vec<i64> = if parts[4].is_empty() {
        vec![]
    } else {
        parts[4]
            .split(',')
            .map(|s| {
                s.parse()
                    .map_err(|_| "invalid subtask translation".to_string())
            })
            .collect::<Result<_>>()?
    };
    if translation.len() != node.children.len() {
        return Err("compressed method child count mismatch".into());
    }
    let mut outer = BTreeMap::new();
    let mut inner = BTreeMap::new();
    for (position, child) in translation.into_iter().zip(node.children) {
        let (target, slot) = if position < 0 {
            (
                &mut inner,
                usize::try_from(-(position + 1)).map_err(|_| "invalid inner slot")?,
            )
        } else {
            (
                &mut outer,
                usize::try_from(position).map_err(|_| "invalid outer slot")?,
            )
        };
        if target.insert(slot, child).is_some() {
            return Err("duplicate compressed method slot".into());
        }
    }
    let new_id = tree.allocate()?;
    if outer.insert(slot, new_id).is_some() {
        return Err("overlapping compressed method slot".into());
    }
    tree.nodes.insert(
        new_id,
        Node {
            call: Call::grounded(parts[1])?,
            method: Some(parts[2].into()),
            children: inner.into_values().collect(),
            position: 0,
        },
    );
    let parent = tree.nodes.get_mut(&id).unwrap();
    parent.method = Some(parts[0].into());
    parent.children = outer.into_values().collect();
    Ok(())
}

fn compressed_action(tree: &mut Tree, id: u64, work: &mut Work) -> Result<()> {
    let node = tree.nodes[&id].clone();
    if node.method.is_some() {
        return Err("compressed primitive has a method".into());
    }
    let body = node
        .call
        .name
        .strip_prefix('%')
        .and_then(|s| s.strip_suffix('%'))
        .ok_or("malformed compressed action")?;
    let parts: Vec<_> = body.split('#').collect();
    if parts.len() < 3 || parts.len() % 2 != 1 {
        return Err("malformed compressed action fields".into());
    }
    let mut offset: usize = 0;
    let mut replacement = vec![];
    for pair in parts[1..].as_chunks::<2>().0 {
        work.tick();
        let arity: usize = pair[1]
            .parse()
            .map_err(|_| "invalid compressed action arity")?;
        let end = offset
            .checked_add(arity)
            .ok_or("compressed action arity overflow")?;
        let args = node
            .call
            .args
            .get(offset..end)
            .ok_or("missing compressed action arguments")?
            .to_vec();
        offset = end;
        let new_id = tree.allocate()?;
        tree.nodes.insert(
            new_id,
            Node {
                call: Call {
                    name: pair[0].into(),
                    args,
                },
                method: None,
                children: vec![],
                position: 0,
            },
        );
        replacement.push(new_id);
    }
    if offset != node.call.args.len() {
        return Err("extra compressed action arguments".into());
    }
    tree.splice(id, &replacement, work)
}

pub(super) fn restore(tree: &mut Tree, work: &mut Work) -> Result<()> {
    // Undo PANDA's encodings in compiler order before erasing auxiliary occurrences.
    loop {
        work.tick();
        work.charge(tree.nodes.len() as u64);
        let artificial = tree.nodes.iter().find(|(_, n)| {
            n.method.as_deref().is_some_and(|m| m.starts_with("_!"))
                || n.call.name.starts_with("_!")
        });
        if let Some((&id, node)) = artificial {
            let children = node.children.clone();
            tree.splice(id, &children, work)?;
            continue;
        }
        if let Some((&id, _)) = tree
            .nodes
            .iter()
            .find(|(_, n)| n.call.name.starts_with('%'))
        {
            compressed_action(tree, id, work)?;
            continue;
        }
        if let Some((&id, _)) = tree
            .nodes
            .iter()
            .find(|(_, n)| n.method.as_deref().is_some_and(|m| m.starts_with('<')))
        {
            compressed_method(tree, id)?;
            continue;
        }
        break;
    }
    tree.positions(work)?;
    let order = tree.traversal(work)?;
    let mut replacements: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut retained = BTreeMap::new();
    for id in order.into_iter().rev() {
        work.tick();
        let node = &tree.nodes[&id];
        let children = node
            .children
            .iter()
            .flat_map(|id| replacements[id].iter().copied())
            .collect();
        if node.call.name.starts_with('_')
            || node.method.as_deref().is_some_and(|m| m.starts_with('_'))
        {
            replacements.insert(id, children);
        } else {
            let mut node = node.clone();
            node.children = children;
            node.call.name = node.call.name.split('|').next().unwrap().into();
            retained.insert(id, node);
            replacements.insert(id, vec![id]);
        }
    }
    tree.roots = tree
        .roots
        .iter()
        .flat_map(|id| replacements[id].iter().copied())
        .collect();
    tree.actions.retain(|id| retained.contains_key(id));
    tree.nodes = retained;
    Ok(())
}
