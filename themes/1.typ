#import "../conf.typ": *

= О наилучшем приближении

#definition(title: "Наилучшее приближение")[
  Пусть $B$ -- нормированное пространство, фиксируем некоторое непустое подмножество $M$. Пусть $norm(x)$ обозначает норму элемента $x$ в нормированном пространстве $B$.

  Число
  #eq[
    $epsilon(x, M) = inf_(y in M) norm(x - y)$
  ]
  называется *наилучшим приближением* элемента $x in B$ на множестве $M$.

  Элемент $y_* in M$ называется *наименее уклоняющимся* от $x$, или *элементом наилучшего приближения* на множестве $M$, если
  #eq[
    $norm(x - y_*) = epsilon(x, M)$
  ]
]

#proposition(title: "Свойства наименьшего уклонения")[
  + Для любого $M subset B$ функция $epsilon(x, M)$ равномерно непрерывна по $x$.
  + Если $M subset B$ -- подпространство, то
    - $epsilon(alpha x, M) = abs(alpha) epsilon (x, M)$ для любых $x in B$ и $alpha in RR$
    - $epsilon(x_1 + x_2, M) <= epsilon(x_1, M) + epsilon(x_2, M)$ для любых $x_1, x_2 in B$
    - $epsilon(x, M) <= norm(x)$ для любого $x in B$
  + Пусть $M subset B$ -- конечномерное линейное многообразие. Тогда отображение $pi: P_M -> M$ непрерывно
]

#proof[
  Пункт 2 очевидно следует из свойств нормы.

  Для пункта 1 докажем неравенство
  #eq[
    $abs(epsilon(x_1, M) - epsilon(x_2, M)) <= norm(x_1 - x_2)$
  ]
  Для произвольного $y in M$ имеем
  #eq[
    $epsilon(x_1, M) <= norm(x_1 - y) <= norm(x_1 - x_2) + norm(x_2 - y) => epsilon(x_1, M) - norm(x_1 - x_2) <= norm(x_2 - y)$
  ]
  Ввиду произвольности $y in M$ получим
  #eq[
    $epsilon(x_1, M) - norm(x_1 - x_2) <= epsilon(x_2, M)$
  ]
  Поэтому, выполняется неравенство
  #eq[
    $epsilon(x_1, M) - epsilon(x_2, M) <= norm(x_1 - x_2)$
  ]
  Аналогично доказывается неравенство со знаком - и получили, что хотели.

  Для пункта 3 рассмотрим сходящуюся в $P_M$ последовательность $x_n$ и пусть
  #eq[
    $lim_(n -> oo) x_n = x_0$
  ]
  Докажем сначала, что последовательность $pi(x_n)$ ограничена
  #eq[
    $norm(pi(x_n)) = norm(pi(x_n) - x_n + x_n) <= \
    norm(pi(x_n) - x_n) + norm(x_n) = epsilon(x_n, M) + norm(x_n) = epsilon(x_n, M) - epsilon(x_0, M) + epsilon(x_0, M) + norm(x_n) <= \
    abs(epsilon(x_n, M) - epsilon(x_0, M)) + epsilon(x_0, M) + norm(x_n) underset(<=, п.1) \
    abs(x_n - x_0) + epsilon(x_0, M) + norm(x_n)$
  ]
  Поскольку последовательность $x_n$ сходится, все слагаемые последней суммы ограничены, следовательно, последовательность $pi(x_n)$ ограничена.

  Теперь необходимо доказать, что последовательность $pi(x_n)$ сходится к $pi(x_0)$. Пусть это не так. Тогда существуют такие $epsilon > 0$ и подпоследовательность $x_n_k$, для которых выполняется неравенство
  #eq[
    $abs(pi(x_n_k) - pi(x_0)) > epsilon$
  ]
  Без ограничения общности можно считать, что подпоследовательность $x_n_k$ совпадает со всей последовательностью $x_n$. 

  Поскольку последовательность $pi(x_n)$ ограничена, а подпространство $M$ конечномерно, из неё можно выбрать сходящуюся подпоследовательность.

  Опять БОО будем считать, что этой подпоследовательностью является сама последовательность $pi(x_n)$ и $lim_(n -> oo) pi(x_n) = y_0$. Тогда переходя к пределам в неравенстве из отрицания сходимости:
  #eq[
    $norm(pi(x_n) - pi(x_0)) > epsilon => norm(y_0 - pi(x_n)) >= epsilon > 0$
  ]
  Согласно определению проекции $pi$ выполнены равенства
  #eq[
    $norm(pi(x_n) - x_n) = epsilon(x_n, M)$
  ]
  Переходя к пределу в равенстве ввиду непрерывности функции $epsilon$
  #eq[
    $norm(y_0 - x_0) = epsilon(x_0, M)$
  ]
  Следовательно, $y_0$ -- наименее уклоняющийся элемент пространства $M => y_0 = pi(x_0)$.
  
  Противоречие!
]

#pagebreak()
