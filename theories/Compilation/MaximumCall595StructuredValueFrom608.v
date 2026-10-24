From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall595StructuredContextFrom608 MaximumCall595StructuredChunk000From608 MaximumCall595StructuredChunk001From608 MaximumCall595StructuredChunk002From608 MaximumCall595StructuredChunk003From608 MaximumCall595StructuredChunk004From608 MaximumCall595StructuredChunk005From608 MaximumCall595StructuredChunk006From608 MaximumCall595StructuredChunk007From608 MaximumCall595StructuredChunk008From608 MaximumCall595StructuredChunk009From608 MaximumCall595StructuredChunk010From608 MaximumCall595StructuredChunk011From608 MaximumCall595StructuredChunk012From608 MaximumCall595StructuredChunk013From608 MaximumCall595StructuredChunk014From608 MaximumCall595StructuredChunk015From608 MaximumCall595StructuredChunk016From608 MaximumCall595StructuredChunk017From608 MaximumCall595StructuredChunk018From608 MaximumCall595StructuredChunk019From608 MaximumCall595StructuredChunk020From608 MaximumCall595StructuredChunk021From608 MaximumCall595StructuredChunk022From608 MaximumCall595StructuredChunk023From608 MaximumCall595StructuredChunk024From608 MaximumCall595StructuredChunk025From608 MaximumCall595StructuredChunk026From608 MaximumCall595StructuredChunk027From608 MaximumCall595StructuredChunk028From608 MaximumCall595StructuredChunk029From608 MaximumCall595StructuredChunk030From608 MaximumCall595StructuredChunk031From608 MaximumCall595StructuredChunk032From608 MaximumCall595StructuredChunk033From608 MaximumCall595StructuredChunk034From608 MaximumCall595StructuredChunk035From608 MaximumCall595StructuredChunk036From608 MaximumCall595StructuredChunk037From608 MaximumCall595StructuredChunk038From608 MaximumCall595StructuredChunk039From608 MaximumCall595StructuredChunk040From608 MaximumCall595StructuredChunk041From608 MaximumCall595StructuredChunk042From608 MaximumCall595StructuredChunk043From608 MaximumCall595StructuredChunk044From608 MaximumCall595StructuredChunk045From608 MaximumCall595StructuredChunk046From608 MaximumCall595StructuredChunk047From608 MaximumCall595StructuredChunk048From608 MaximumCall595StructuredChunk049From608 MaximumCall595StructuredChunk050From608 MaximumCall595StructuredChunk051From608 MaximumCall595StructuredChunk052From608 MaximumCall595StructuredChunk053From608 MaximumCall595StructuredChunk054From608 MaximumCall595StructuredChunk055From608 MaximumCall595StructuredChunk056From608 MaximumCall595StructuredChunk057From608 MaximumCall595StructuredChunk058From608 MaximumCall595StructuredChunk059From608 MaximumCall595StructuredChunk060From608 MaximumCall595StructuredChunk061From608 MaximumCall595StructuredChunk062From608 MaximumCall595StructuredChunk063From608 MaximumCall595StructuredChunk064From608 MaximumCall595StructuredChunk065From608 MaximumCall595StructuredChunk066From608 MaximumCall595StructuredChunk067From608 MaximumCall595StructuredChunk068From608 MaximumCall595StructuredChunk069From608 MaximumCall595StructuredChunk070From608 MaximumCall595StructuredChunk071From608 MaximumCall595StructuredChunk072From608 MaximumCall595StructuredChunk073From608 MaximumCall595StructuredChunk074From608 MaximumCall595StructuredChunk075From608 MaximumCall595StructuredChunk076From608 MaximumCall595StructuredChunk077From608 MaximumCall595StructuredChunk078From608 MaximumCall595StructuredChunk079From608 MaximumCall595StructuredChunk080From608 MaximumCall595StructuredChunk081From608 MaximumCall595StructuredChunk082From608 MaximumCall595StructuredChunk083From608 MaximumCall595StructuredChunk084From608 MaximumCall595StructuredChunk085From608 MaximumCall595StructuredChunk086From608 MaximumCall595StructuredChunk087From608 MaximumCall595StructuredChunk088From608 MaximumCall595StructuredChunk089From608 MaximumCall595StructuredChunk090From608 MaximumCall595StructuredChunk091From608 MaximumCall595StructuredChunk092From608 MaximumCall595StructuredChunk093From608 MaximumCall595StructuredChunk094From608 MaximumCall595StructuredChunk095From608 MaximumCall595StructuredChunk096From608 MaximumCall595StructuredChunk097From608 MaximumCall595StructuredChunk098From608 MaximumCall595StructuredChunk099From608 MaximumCall595StructuredChunk100From608 MaximumCall595StructuredChunk101From608 MaximumCall595StructuredChunk102From608 MaximumCall595StructuredChunk103From608 MaximumCall595StructuredChunk104From608 MaximumCall595StructuredChunk105From608 MaximumCall595StructuredChunk106From608 MaximumCall595StructuredChunk107From608 MaximumCall595StructuredChunk108From608 MaximumCall595StructuredChunk109From608 MaximumCall595StructuredChunk110From608 MaximumCall595StructuredChunk111From608 MaximumCall595StructuredChunk112From608 MaximumCall595StructuredChunk113From608 MaximumCall595StructuredChunk114From608 MaximumCall595StructuredChunk115From608 MaximumCall595StructuredChunk116From608 MaximumCall595StructuredChunk117From608 MaximumCall595StructuredChunk118From608 MaximumCall595StructuredChunk119From608 MaximumCall595StructuredChunk120From608 MaximumCall595StructuredChunk121From608 MaximumCall595StructuredChunk122From608 MaximumCall595StructuredChunk123From608 MaximumCall595StructuredChunk124From608 MaximumCall595StructuredChunk125From608 MaximumCall595StructuredChunk126From608 MaximumCall595StructuredChunk127From608 MaximumCall595StructuredChunk128From608 MaximumCall595StructuredChunk129From608 MaximumCall595StructuredChunk130From608 MaximumCall595StructuredChunk131From608 MaximumCall595StructuredChunk132From608 MaximumCall595StructuredChunk133From608 MaximumCall595StructuredChunk134From608 MaximumCall595StructuredChunk135From608 MaximumCall595StructuredChunk136From608 MaximumCall595StructuredChunk137From608 MaximumCall595StructuredChunk138From608.

Definition values :=
  MaximumCall595StructuredChunk000From608.values ++
  MaximumCall595StructuredChunk001From608.values ++
  MaximumCall595StructuredChunk002From608.values ++
  MaximumCall595StructuredChunk003From608.values ++
  MaximumCall595StructuredChunk004From608.values ++
  MaximumCall595StructuredChunk005From608.values ++
  MaximumCall595StructuredChunk006From608.values ++
  MaximumCall595StructuredChunk007From608.values ++
  MaximumCall595StructuredChunk008From608.values ++
  MaximumCall595StructuredChunk009From608.values ++
  MaximumCall595StructuredChunk010From608.values ++
  MaximumCall595StructuredChunk011From608.values ++
  MaximumCall595StructuredChunk012From608.values ++
  MaximumCall595StructuredChunk013From608.values ++
  MaximumCall595StructuredChunk014From608.values ++
  MaximumCall595StructuredChunk015From608.values ++
  MaximumCall595StructuredChunk016From608.values ++
  MaximumCall595StructuredChunk017From608.values ++
  MaximumCall595StructuredChunk018From608.values ++
  MaximumCall595StructuredChunk019From608.values ++
  MaximumCall595StructuredChunk020From608.values ++
  MaximumCall595StructuredChunk021From608.values ++
  MaximumCall595StructuredChunk022From608.values ++
  MaximumCall595StructuredChunk023From608.values ++
  MaximumCall595StructuredChunk024From608.values ++
  MaximumCall595StructuredChunk025From608.values ++
  MaximumCall595StructuredChunk026From608.values ++
  MaximumCall595StructuredChunk027From608.values ++
  MaximumCall595StructuredChunk028From608.values ++
  MaximumCall595StructuredChunk029From608.values ++
  MaximumCall595StructuredChunk030From608.values ++
  MaximumCall595StructuredChunk031From608.values ++
  MaximumCall595StructuredChunk032From608.values ++
  MaximumCall595StructuredChunk033From608.values ++
  MaximumCall595StructuredChunk034From608.values ++
  MaximumCall595StructuredChunk035From608.values ++
  MaximumCall595StructuredChunk036From608.values ++
  MaximumCall595StructuredChunk037From608.values ++
  MaximumCall595StructuredChunk038From608.values ++
  MaximumCall595StructuredChunk039From608.values ++
  MaximumCall595StructuredChunk040From608.values ++
  MaximumCall595StructuredChunk041From608.values ++
  MaximumCall595StructuredChunk042From608.values ++
  MaximumCall595StructuredChunk043From608.values ++
  MaximumCall595StructuredChunk044From608.values ++
  MaximumCall595StructuredChunk045From608.values ++
  MaximumCall595StructuredChunk046From608.values ++
  MaximumCall595StructuredChunk047From608.values ++
  MaximumCall595StructuredChunk048From608.values ++
  MaximumCall595StructuredChunk049From608.values ++
  MaximumCall595StructuredChunk050From608.values ++
  MaximumCall595StructuredChunk051From608.values ++
  MaximumCall595StructuredChunk052From608.values ++
  MaximumCall595StructuredChunk053From608.values ++
  MaximumCall595StructuredChunk054From608.values ++
  MaximumCall595StructuredChunk055From608.values ++
  MaximumCall595StructuredChunk056From608.values ++
  MaximumCall595StructuredChunk057From608.values ++
  MaximumCall595StructuredChunk058From608.values ++
  MaximumCall595StructuredChunk059From608.values ++
  MaximumCall595StructuredChunk060From608.values ++
  MaximumCall595StructuredChunk061From608.values ++
  MaximumCall595StructuredChunk062From608.values ++
  MaximumCall595StructuredChunk063From608.values ++
  MaximumCall595StructuredChunk064From608.values ++
  MaximumCall595StructuredChunk065From608.values ++
  MaximumCall595StructuredChunk066From608.values ++
  MaximumCall595StructuredChunk067From608.values ++
  MaximumCall595StructuredChunk068From608.values ++
  MaximumCall595StructuredChunk069From608.values ++
  MaximumCall595StructuredChunk070From608.values ++
  MaximumCall595StructuredChunk071From608.values ++
  MaximumCall595StructuredChunk072From608.values ++
  MaximumCall595StructuredChunk073From608.values ++
  MaximumCall595StructuredChunk074From608.values ++
  MaximumCall595StructuredChunk075From608.values ++
  MaximumCall595StructuredChunk076From608.values ++
  MaximumCall595StructuredChunk077From608.values ++
  MaximumCall595StructuredChunk078From608.values ++
  MaximumCall595StructuredChunk079From608.values ++
  MaximumCall595StructuredChunk080From608.values ++
  MaximumCall595StructuredChunk081From608.values ++
  MaximumCall595StructuredChunk082From608.values ++
  MaximumCall595StructuredChunk083From608.values ++
  MaximumCall595StructuredChunk084From608.values ++
  MaximumCall595StructuredChunk085From608.values ++
  MaximumCall595StructuredChunk086From608.values ++
  MaximumCall595StructuredChunk087From608.values ++
  MaximumCall595StructuredChunk088From608.values ++
  MaximumCall595StructuredChunk089From608.values ++
  MaximumCall595StructuredChunk090From608.values ++
  MaximumCall595StructuredChunk091From608.values ++
  MaximumCall595StructuredChunk092From608.values ++
  MaximumCall595StructuredChunk093From608.values ++
  MaximumCall595StructuredChunk094From608.values ++
  MaximumCall595StructuredChunk095From608.values ++
  MaximumCall595StructuredChunk096From608.values ++
  MaximumCall595StructuredChunk097From608.values ++
  MaximumCall595StructuredChunk098From608.values ++
  MaximumCall595StructuredChunk099From608.values ++
  MaximumCall595StructuredChunk100From608.values ++
  MaximumCall595StructuredChunk101From608.values ++
  MaximumCall595StructuredChunk102From608.values ++
  MaximumCall595StructuredChunk103From608.values ++
  MaximumCall595StructuredChunk104From608.values ++
  MaximumCall595StructuredChunk105From608.values ++
  MaximumCall595StructuredChunk106From608.values ++
  MaximumCall595StructuredChunk107From608.values ++
  MaximumCall595StructuredChunk108From608.values ++
  MaximumCall595StructuredChunk109From608.values ++
  MaximumCall595StructuredChunk110From608.values ++
  MaximumCall595StructuredChunk111From608.values ++
  MaximumCall595StructuredChunk112From608.values ++
  MaximumCall595StructuredChunk113From608.values ++
  MaximumCall595StructuredChunk114From608.values ++
  MaximumCall595StructuredChunk115From608.values ++
  MaximumCall595StructuredChunk116From608.values ++
  MaximumCall595StructuredChunk117From608.values ++
  MaximumCall595StructuredChunk118From608.values ++
  MaximumCall595StructuredChunk119From608.values ++
  MaximumCall595StructuredChunk120From608.values ++
  MaximumCall595StructuredChunk121From608.values ++
  MaximumCall595StructuredChunk122From608.values ++
  MaximumCall595StructuredChunk123From608.values ++
  MaximumCall595StructuredChunk124From608.values ++
  MaximumCall595StructuredChunk125From608.values ++
  MaximumCall595StructuredChunk126From608.values ++
  MaximumCall595StructuredChunk127From608.values ++
  MaximumCall595StructuredChunk128From608.values ++
  MaximumCall595StructuredChunk129From608.values ++
  MaximumCall595StructuredChunk130From608.values ++
  MaximumCall595StructuredChunk131From608.values ++
  MaximumCall595StructuredChunk132From608.values ++
  MaximumCall595StructuredChunk133From608.values ++
  MaximumCall595StructuredChunk134From608.values ++
  MaximumCall595StructuredChunk135From608.values ++
  MaximumCall595StructuredChunk136From608.values ++
  MaximumCall595StructuredChunk137From608.values ++
  MaximumCall595StructuredChunk138From608.values.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom608.depth MaximumCall595StructuredContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 139
    MaximumCall595StructuredContextFrom608.depth MaximumCall595StructuredContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall595StructuredChunk000From608.values_eq,
      MaximumCall595StructuredChunk001From608.values_eq,
      MaximumCall595StructuredChunk002From608.values_eq,
      MaximumCall595StructuredChunk003From608.values_eq,
      MaximumCall595StructuredChunk004From608.values_eq,
      MaximumCall595StructuredChunk005From608.values_eq,
      MaximumCall595StructuredChunk006From608.values_eq,
      MaximumCall595StructuredChunk007From608.values_eq,
      MaximumCall595StructuredChunk008From608.values_eq,
      MaximumCall595StructuredChunk009From608.values_eq,
      MaximumCall595StructuredChunk010From608.values_eq,
      MaximumCall595StructuredChunk011From608.values_eq,
      MaximumCall595StructuredChunk012From608.values_eq,
      MaximumCall595StructuredChunk013From608.values_eq,
      MaximumCall595StructuredChunk014From608.values_eq,
      MaximumCall595StructuredChunk015From608.values_eq,
      MaximumCall595StructuredChunk016From608.values_eq,
      MaximumCall595StructuredChunk017From608.values_eq,
      MaximumCall595StructuredChunk018From608.values_eq,
      MaximumCall595StructuredChunk019From608.values_eq,
      MaximumCall595StructuredChunk020From608.values_eq,
      MaximumCall595StructuredChunk021From608.values_eq,
      MaximumCall595StructuredChunk022From608.values_eq,
      MaximumCall595StructuredChunk023From608.values_eq,
      MaximumCall595StructuredChunk024From608.values_eq,
      MaximumCall595StructuredChunk025From608.values_eq,
      MaximumCall595StructuredChunk026From608.values_eq,
      MaximumCall595StructuredChunk027From608.values_eq,
      MaximumCall595StructuredChunk028From608.values_eq,
      MaximumCall595StructuredChunk029From608.values_eq,
      MaximumCall595StructuredChunk030From608.values_eq,
      MaximumCall595StructuredChunk031From608.values_eq,
      MaximumCall595StructuredChunk032From608.values_eq,
      MaximumCall595StructuredChunk033From608.values_eq,
      MaximumCall595StructuredChunk034From608.values_eq,
      MaximumCall595StructuredChunk035From608.values_eq,
      MaximumCall595StructuredChunk036From608.values_eq,
      MaximumCall595StructuredChunk037From608.values_eq,
      MaximumCall595StructuredChunk038From608.values_eq,
      MaximumCall595StructuredChunk039From608.values_eq,
      MaximumCall595StructuredChunk040From608.values_eq,
      MaximumCall595StructuredChunk041From608.values_eq,
      MaximumCall595StructuredChunk042From608.values_eq,
      MaximumCall595StructuredChunk043From608.values_eq,
      MaximumCall595StructuredChunk044From608.values_eq,
      MaximumCall595StructuredChunk045From608.values_eq,
      MaximumCall595StructuredChunk046From608.values_eq,
      MaximumCall595StructuredChunk047From608.values_eq,
      MaximumCall595StructuredChunk048From608.values_eq,
      MaximumCall595StructuredChunk049From608.values_eq,
      MaximumCall595StructuredChunk050From608.values_eq,
      MaximumCall595StructuredChunk051From608.values_eq,
      MaximumCall595StructuredChunk052From608.values_eq,
      MaximumCall595StructuredChunk053From608.values_eq,
      MaximumCall595StructuredChunk054From608.values_eq,
      MaximumCall595StructuredChunk055From608.values_eq,
      MaximumCall595StructuredChunk056From608.values_eq,
      MaximumCall595StructuredChunk057From608.values_eq,
      MaximumCall595StructuredChunk058From608.values_eq,
      MaximumCall595StructuredChunk059From608.values_eq,
      MaximumCall595StructuredChunk060From608.values_eq,
      MaximumCall595StructuredChunk061From608.values_eq,
      MaximumCall595StructuredChunk062From608.values_eq,
      MaximumCall595StructuredChunk063From608.values_eq,
      MaximumCall595StructuredChunk064From608.values_eq,
      MaximumCall595StructuredChunk065From608.values_eq,
      MaximumCall595StructuredChunk066From608.values_eq,
      MaximumCall595StructuredChunk067From608.values_eq,
      MaximumCall595StructuredChunk068From608.values_eq,
      MaximumCall595StructuredChunk069From608.values_eq,
      MaximumCall595StructuredChunk070From608.values_eq,
      MaximumCall595StructuredChunk071From608.values_eq,
      MaximumCall595StructuredChunk072From608.values_eq,
      MaximumCall595StructuredChunk073From608.values_eq,
      MaximumCall595StructuredChunk074From608.values_eq,
      MaximumCall595StructuredChunk075From608.values_eq,
      MaximumCall595StructuredChunk076From608.values_eq,
      MaximumCall595StructuredChunk077From608.values_eq,
      MaximumCall595StructuredChunk078From608.values_eq,
      MaximumCall595StructuredChunk079From608.values_eq,
      MaximumCall595StructuredChunk080From608.values_eq,
      MaximumCall595StructuredChunk081From608.values_eq,
      MaximumCall595StructuredChunk082From608.values_eq,
      MaximumCall595StructuredChunk083From608.values_eq,
      MaximumCall595StructuredChunk084From608.values_eq,
      MaximumCall595StructuredChunk085From608.values_eq,
      MaximumCall595StructuredChunk086From608.values_eq,
      MaximumCall595StructuredChunk087From608.values_eq,
      MaximumCall595StructuredChunk088From608.values_eq,
      MaximumCall595StructuredChunk089From608.values_eq,
      MaximumCall595StructuredChunk090From608.values_eq,
      MaximumCall595StructuredChunk091From608.values_eq,
      MaximumCall595StructuredChunk092From608.values_eq,
      MaximumCall595StructuredChunk093From608.values_eq,
      MaximumCall595StructuredChunk094From608.values_eq,
      MaximumCall595StructuredChunk095From608.values_eq,
      MaximumCall595StructuredChunk096From608.values_eq,
      MaximumCall595StructuredChunk097From608.values_eq,
      MaximumCall595StructuredChunk098From608.values_eq,
      MaximumCall595StructuredChunk099From608.values_eq,
      MaximumCall595StructuredChunk100From608.values_eq,
      MaximumCall595StructuredChunk101From608.values_eq,
      MaximumCall595StructuredChunk102From608.values_eq,
      MaximumCall595StructuredChunk103From608.values_eq,
      MaximumCall595StructuredChunk104From608.values_eq,
      MaximumCall595StructuredChunk105From608.values_eq,
      MaximumCall595StructuredChunk106From608.values_eq,
      MaximumCall595StructuredChunk107From608.values_eq,
      MaximumCall595StructuredChunk108From608.values_eq,
      MaximumCall595StructuredChunk109From608.values_eq,
      MaximumCall595StructuredChunk110From608.values_eq,
      MaximumCall595StructuredChunk111From608.values_eq,
      MaximumCall595StructuredChunk112From608.values_eq,
      MaximumCall595StructuredChunk113From608.values_eq,
      MaximumCall595StructuredChunk114From608.values_eq,
      MaximumCall595StructuredChunk115From608.values_eq,
      MaximumCall595StructuredChunk116From608.values_eq,
      MaximumCall595StructuredChunk117From608.values_eq,
      MaximumCall595StructuredChunk118From608.values_eq,
      MaximumCall595StructuredChunk119From608.values_eq,
      MaximumCall595StructuredChunk120From608.values_eq,
      MaximumCall595StructuredChunk121From608.values_eq,
      MaximumCall595StructuredChunk122From608.values_eq,
      MaximumCall595StructuredChunk123From608.values_eq,
      MaximumCall595StructuredChunk124From608.values_eq,
      MaximumCall595StructuredChunk125From608.values_eq,
      MaximumCall595StructuredChunk126From608.values_eq,
      MaximumCall595StructuredChunk127From608.values_eq,
      MaximumCall595StructuredChunk128From608.values_eq,
      MaximumCall595StructuredChunk129From608.values_eq,
      MaximumCall595StructuredChunk130From608.values_eq,
      MaximumCall595StructuredChunk131From608.values_eq,
      MaximumCall595StructuredChunk132From608.values_eq,
      MaximumCall595StructuredChunk133From608.values_eq,
      MaximumCall595StructuredChunk134From608.values_eq,
      MaximumCall595StructuredChunk135From608.values_eq,
      MaximumCall595StructuredChunk136From608.values_eq,
      MaximumCall595StructuredChunk137From608.values_eq,
      MaximumCall595StructuredChunk138From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
