
Hammer invocations in both files, and the amount of time they take to execute (roughly)

Name                  | Lean                       | Isabelle
                      |                            |
nb. 1                 | l.10  t:_       fail       | l.115 `by blast`                       t:_
nb. 2                 | l.15  t:_       succ       | l.125 `by blast`                       t:_
nb. 3                 | l.20  t:_       succ       | l.127 `by blast`                       t:_
nb. 4                 | l.24  t:_       fail       | l.134 `by auto`                        t:_
nb. 5                 | l.41  t:_       fail       | l.152 `by auto`                        t:_
nb. 6                 | l.61  t:_       succ       | l.186 `by blast`                       t:_
nb. 7                 | l.63  t:_       succ       | l.189 `by blast`                       t:_
nb. 8                 | l.71  t:_       fail       | l.199 `by blast`                       t:_
nb. 9                 | l.72  t:_       succ       | l.200 `by blast`                       t:_
nb. 10                | l.76  t:_       fail       | l.219 `by blast`                       t:_
nb. 11                | l.80  t:_       fail       | l.223 `by blast`                       t:_
nb. 12                | l.86  t:_       fail       | l.229 `by blast`                       t:_
nb. 13                | l.103 t:_       succ       | l.234 `by blast`                       t:_
nb. 14                | l.107 t:_       succ       | l.235 `by blast`                       t:_
nb. 15                | l.107 t:_       succ       | l.239 `by (metis sim_while_cong_aux)`  t:_
nb. 16                | l.107 t:_       succ       | l.245 `by blast`                       t:_
nb. 17                | l.107 t:_       succ       | l.246 `by blast`                       t:_
nb. 18                | l.107 t:_       succ       | l.247 `by blast`                       t:_
nb. 19                | l.124 t:_       fail       | l.254 `blast +`                        t:_

Note: l.124 has an invocation of hammer for each branch of the induction, all calls fail

We need to find out why the following invocations fail:

nb. 1:


nb. 4:


nb. 5:


nb. 8:


nb.10:


nb.11:


nb.12:


nb.19:


