pub fn parse(diff: &str) -> (String, String) {
  let mut before = String::new();
  let mut after = String::new();

  for line in diff.lines() {
    if let Some(line) = line.strip_prefix("- ") {
      before.push_str(line);
      before.push('\n');
    } else if let Some(line) = line.strip_prefix("+ ") {
      after.push_str(line);
      after.push('\n');
    } else {
      before.push_str(line);
      before.push('\n');
      after.push_str(line);
      after.push('\n');
    }
  }

  (before, after)
}
pub fn diff(before: String, after: String) -> String {
  let mut diff = String::new();

  let mut b = 0;
  let mut a = 0;

  // NB: Don't indent strings with no changes, so that nc-test works.
  if before == after {
    return before;
  }

  let before_lines = before.lines().collect::<Vec<_>>();
  let after_lines = after.lines().collect::<Vec<_>>();

  while b < before_lines.len() || a < after_lines.len() {
    match (before_lines.get(b), after_lines.get(a)) {
      (Some(b_line), Some(a_line)) => {
        if b_line == a_line {
          diff.push_str("  ");
          diff.push_str(b_line);
          diff.push('\n');
          b += 1;
          a += 1;
        } else {
          let (a_rec, b_rec) = reconcile(&before_lines[b..], &after_lines[a..]);

          for i in 0..b_rec {
            diff.push_str("- ");
            diff.push_str(before_lines[b + i]);
            diff.push('\n');
          }
          for i in 0..a_rec {
            diff.push_str("+ ");
            diff.push_str(after_lines[a + i]);
            diff.push('\n');
          }

          a += a_rec;
          b += b_rec;
        }
      }

      (Some(b_line), None) => {
        diff.push_str("- ");
        diff.push_str(b_line);
        diff.push('\n');
        b += 1;
      }

      (None, Some(a_line)) => {
        diff.push_str("+ ");
        diff.push_str(a_line);
        diff.push('\n');
        a += 1;
      }

      (None, None) => unreachable!(),
    }
  }

  diff
}

fn reconcile(before: &[&str], after: &[&str]) -> (usize, usize) {
  for i in 0..(before.len().max(after.len())) {
    for j in 0..i {
      let b = before.get(i);
      let a = after.get(j);
      if b.is_some() && a.is_some() && b == a {
        return (j, i);
      }
    }
  }

  (before.len(), after.len())
}
