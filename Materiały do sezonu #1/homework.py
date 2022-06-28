dane =[]
def rae(a,b, dane):
     liczba1=max(a, b)
     liczba2=min(a,b)
     if liczba1 % liczba2 ==0:
          dane.append([liczba1,liczba2, liczba1% liczba2])

          nowe_dane=[]

          for i, d in enumerate(dane[::-1]):
               if i == 0:
                    nowe_dane.append([d[0], d[1], d[2], 0, 1])

               else:
                    p = nowe_dane[i-1][-1]
                    q=nowe_dane[i-1][-2]-(d[0]//d[1])*p
                    nowe_dane.append([d[0], d[1], d[2], p, q])

          print('Podsumowując:')
          print('{} to największy wspólny dzielnik liczb {} i {}.'.format(dane[-2][2], dane[0][0], dane[0][1]))
          print("czyli: {} x {}  + {} x {} = {}".format(d[0], p, d[1], q, dane[-2][2]))


     else:

          dane.append([liczba1,liczba2, liczba1% liczba2])
          rae( liczba2,  liczba1% liczba2, dane)


rae(123, 27, dane)
