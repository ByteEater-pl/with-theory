def nwd(liczba1, liczba2, iteracja =0):
     reszta = liczba1 % liczba2
     print("Iteracja nr: {}. Licza_1: {}, Liczba_2: {}, reszta z dzielenia: {}".format(iteracja, liczba1, liczba2, reszta))
     iteracja +=1
     if reszta ==0:
          print("NWD to: {}".format(liczba2))
     else:
          nwd(liczba2, reszta, iteracja)


nwd(282,78)
