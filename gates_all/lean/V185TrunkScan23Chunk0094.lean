import V185TrunkScan23Chunk0093

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_557642 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_557642 : Nat := 118140960795 + 557642 * 2 ^ 59
def prefixEnd_557642 : Nat := 4983230072969 + 3 ^ 40 * 557642 * 2
def baseEnd_557642 : Nat := 286338379134612456810457

theorem tailTrace_557642 : CollatzResearch.WordTrace tailWord_557642 prefixEnd_557642 286338379134612456810457 := by
  unfold tailWord_557642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084718661441436629112795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13559249763843831010967453 5084718661441436629112795)
  ·
    refine ⟨7627077992162154943669193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5084718661441436629112795 7627077992162154943669193)
    ·
      refine ⟨5720308494121616207751895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7627077992162154943669193 5720308494121616207751895)
      ·
        refine ⟨8580462741182424311627843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720308494121616207751895 8580462741182424311627843)
        ·
          refine ⟨12870694111773636467441765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580462741182424311627843 12870694111773636467441765)
          ·
            refine ⟨2413255145957556837645331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12870694111773636467441765 2413255145957556837645331)
            ·
              refine ⟨3619882718936335256467997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413255145957556837645331 3619882718936335256467997)
              ·
                refine ⟨1357456019601125721175499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619882718936335256467997 1357456019601125721175499)
                ·
                  refine ⟨2036184029401688581763249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357456019601125721175499 2036184029401688581763249)
                  ·
                    refine ⟨1527138022051266436322437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2036184029401688581763249 1527138022051266436322437)
                    ·
                      refine ⟨286338379134612456810457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1527138022051266436322437 286338379134612456810457)
                      ·
                        rfl

theorem cell23_557642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_557642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557642 prefixEnd_557642 := by exact prefixLift 557642
  have htrace : WordTrace (prefixWord ++ tailWord_557642) baseStart_557642 baseEnd_557642 := by
    simpa [prefixWord, tailWord_557642, baseEnd_557642] using wordTrace_append hprefix tailTrace_557642
  have hstable : (prefixWord ++ tailWord_557642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557642).length < 2 ^ (prefixWord ++ tailWord_557642).sum := by decide
  have hdescent : baseEnd_557642 < baseStart_557642 := by decide
  rcases family_descends (prefixWord ++ tailWord_557642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557675 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_557675 : Nat := 118140960795 + 557675 * 2 ^ 59
def prefixEnd_557675 : Nat := 4983230072969 + 3 ^ 40 * 557675 * 2
def baseEnd_557675 : Nat := 286355323996210827697805

theorem tailTrace_557675 : CollatzResearch.WordTrace tailWord_557675 prefixEnd_557675 286355323996210827697805 := by
  unfold tailWord_557675
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340078254646193152402479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13560052169764128768268319 20340078254646193152402479)
  ·
    refine ⟨30510117381969289728603719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20340078254646193152402479 30510117381969289728603719)
    ·
      refine ⟨45765176072953934592905579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30510117381969289728603719 45765176072953934592905579)
      ·
        refine ⟨68647764109430901889358369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45765176072953934592905579 68647764109430901889358369)
        ·
          refine ⟨51485823082073176417018777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68647764109430901889358369 51485823082073176417018777)
          ·
            refine ⟨38614367311554882312764083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51485823082073176417018777 38614367311554882312764083)
            ·
              refine ⟨57921550967332323469146125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38614367311554882312764083 57921550967332323469146125)
              ·
                refine ⟨21720581612749621300929797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57921550967332323469146125 21720581612749621300929797)
                ·
                  refine ⟨4072609052390553993924337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21720581612749621300929797 4072609052390553993924337)
                  ·
                    refine ⟨3054456789292915495443253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4072609052390553993924337 3054456789292915495443253)
                    ·
                      refine ⟨286355323996210827697805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3054456789292915495443253 286355323996210827697805)
                      ·
                        rfl

theorem cell23_557675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_557675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557675 prefixEnd_557675 := by exact prefixLift 557675
  have htrace : WordTrace (prefixWord ++ tailWord_557675) baseStart_557675 baseEnd_557675 := by
    simpa [prefixWord, tailWord_557675, baseEnd_557675] using wordTrace_append hprefix tailTrace_557675
  have hstable : (prefixWord ++ tailWord_557675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557675).length < 2 ^ (prefixWord ++ tailWord_557675).sum := by decide
  have hdescent : baseEnd_557675 < baseStart_557675 := by decide
  rcases family_descends (prefixWord ++ tailWord_557675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557695 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 8]
def baseStart_557695 : Nat := 118140960795 + 557695 * 2 ^ 59
def prefixEnd_557695 : Nat := 4983230072969 + 3 ^ 40 * 557695 * 2
def baseEnd_557695 : Nat := 95455197869766916482571

theorem tailTrace_557695 : CollatzResearch.WordTrace tailWord_557695 prefixEnd_557695 95455197869766916482571 := by
  unfold tailWord_557695
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340807714573736568130539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13560538476382491045420359 20340807714573736568130539)
  ·
    refine ⟨30511211571860604852195809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20340807714573736568130539 30511211571860604852195809)
    ·
      refine ⟨22883408678895453639146857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30511211571860604852195809 22883408678895453639146857)
      ·
        refine ⟨17162556509171590229360143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22883408678895453639146857 17162556509171590229360143)
        ·
          refine ⟨25743834763757385344040215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17162556509171590229360143 25743834763757385344040215)
          ·
            refine ⟨38615752145636078016060323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25743834763757385344040215 38615752145636078016060323)
            ·
              refine ⟨57923628218454117024090485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38615752145636078016060323 57923628218454117024090485)
              ·
                refine ⟨5430340145480073471008483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57923628218454117024090485 5430340145480073471008483)
                ·
                  refine ⟨8145510218220110206512725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430340145480073471008483 8145510218220110206512725)
                  ·
                    refine ⟨95455197869766916482571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8145510218220110206512725 95455197869766916482571)
                    ·
                      rfl

theorem cell23_557695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_557695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557695 prefixEnd_557695 := by exact prefixLift 557695
  have htrace : WordTrace (prefixWord ++ tailWord_557695) baseStart_557695 baseEnd_557695 := by
    simpa [prefixWord, tailWord_557695, baseEnd_557695] using wordTrace_append hprefix tailTrace_557695
  have hstable : (prefixWord ++ tailWord_557695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557695).length < 2 ^ (prefixWord ++ tailWord_557695).sum := by decide
  have hdescent : baseEnd_557695 < baseStart_557695 := by decide
  rcases family_descends (prefixWord ++ tailWord_557695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557719 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_557719 : Nat := 118140960795 + 557719 * 2 ^ 59
def prefixEnd_557719 : Nat := 4983230072969 + 3 ^ 40 * 557719 * 2
def baseEnd_557719 : Nat := 286377917145008655547603

theorem tailTrace_557719 : CollatzResearch.WordTrace tailWord_557719 prefixEnd_557719 286377917145008655547603 := by
  unfold tailWord_557719
  simp only [CollatzResearch.WordTrace]
  refine ⟨20341683066486788667004211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13561122044324525778002807 20341683066486788667004211)
  ·
    refine ⟨30512524599730183000506317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20341683066486788667004211 30512524599730183000506317)
    ·
      refine ⟨11442196724898818625189869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30512524599730183000506317 11442196724898818625189869)
      ·
        refine ⟨4290823771837056984446201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11442196724898818625189869 4290823771837056984446201)
        ·
          refine ⟨3218117828877792738334651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4290823771837056984446201 3218117828877792738334651)
          ·
            refine ⟨4827176743316689107501977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218117828877792738334651 4827176743316689107501977)
            ·
              refine ⟨3620382557487516830626483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827176743316689107501977 3620382557487516830626483)
              ·
                refine ⟨5430573836231275245939725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620382557487516830626483 5430573836231275245939725)
                ·
                  refine ⟨2036465188586728217227397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5430573836231275245939725 2036465188586728217227397)
                  ·
                    refine ⟨381837222860011540730137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036465188586728217227397 381837222860011540730137)
                    ·
                      refine ⟨286377917145008655547603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381837222860011540730137 286377917145008655547603)
                      ·
                        rfl

theorem cell23_557719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_557719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557719 prefixEnd_557719 := by exact prefixLift 557719
  have htrace : WordTrace (prefixWord ++ tailWord_557719) baseStart_557719 baseEnd_557719 := by
    simpa [prefixWord, tailWord_557719, baseEnd_557719] using wordTrace_append hprefix tailTrace_557719
  have hstable : (prefixWord ++ tailWord_557719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557719).length < 2 ^ (prefixWord ++ tailWord_557719).sum := by decide
  have hdescent : baseEnd_557719 < baseStart_557719 := by decide
  rcases family_descends (prefixWord ++ tailWord_557719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557792 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_557792 : Nat := 118140960795 + 557792 * 2 ^ 59
def prefixEnd_557792 : Nat := 4983230072969 + 3 ^ 40 * 557792 * 2
def baseEnd_557792 : Nat := 286415401232786869934767

theorem tailTrace_557792 : CollatzResearch.WordTrace tailWord_557792 prefixEnd_557792 286415401232786869934767 := by
  unfold tailWord_557792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172172797611161067205815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13562897063481548089607753 10172172797611161067205815)
  ·
    refine ⟨15258259196416741600808723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10172172797611161067205815 15258259196416741600808723)
    ·
      refine ⟨22887388794625112401213085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15258259196416741600808723 22887388794625112401213085)
      ·
        refine ⟨8582770797984417150454907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22887388794625112401213085 8582770797984417150454907)
        ·
          refine ⟨12874156196976625725682361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8582770797984417150454907 12874156196976625725682361)
          ·
            refine ⟨9655617147732469294261771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12874156196976625725682361 9655617147732469294261771)
            ·
              refine ⟨14483425721598703941392657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655617147732469294261771 14483425721598703941392657)
              ·
                refine ⟨10862569291199027956044493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14483425721598703941392657 10862569291199027956044493)
                ·
                  refine ⟨4073463484199635483516685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10862569291199027956044493 4073463484199635483516685)
                  ·
                    refine ⟨1527548806574863306318757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4073463484199635483516685 1527548806574863306318757)
                    ·
                      refine ⟨286415401232786869934767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1527548806574863306318757 286415401232786869934767)
                      ·
                        rfl

theorem cell23_557792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_557792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557792 prefixEnd_557792 := by exact prefixLift 557792
  have htrace : WordTrace (prefixWord ++ tailWord_557792) baseStart_557792 baseEnd_557792 := by
    simpa [prefixWord, tailWord_557792, baseEnd_557792] using wordTrace_append hprefix tailTrace_557792
  have hstable : (prefixWord ++ tailWord_557792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557792).length < 2 ^ (prefixWord ++ tailWord_557792).sum := by decide
  have hdescent : baseEnd_557792 < baseStart_557792 := by decide
  rcases family_descends (prefixWord ++ tailWord_557792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557793 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 5]
def baseStart_557793 : Nat := 118140960795 + 557793 * 2 ^ 59
def prefixEnd_557793 : Nat := 4983230072969 + 3 ^ 40 * 557793 * 2
def baseEnd_557793 : Nat := 31823990523715707335807

theorem tailTrace_557793 : CollatzResearch.WordTrace tailWord_557793 prefixEnd_557793 31823990523715707335807 := by
  unfold tailWord_557793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344382068218699305198033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13562921378812466203465355 20344382068218699305198033)
  ·
    refine ⟨15258286551164024478898525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20344382068218699305198033 15258286551164024478898525)
    ·
      refine ⟨5721857456686509179586947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15258286551164024478898525 5721857456686509179586947)
      ·
        refine ⟨8582786185029763769380421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5721857456686509179586947 8582786185029763769380421)
        ·
          refine ⟨1609272409693080706758829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8582786185029763769380421 1609272409693080706758829)
          ·
            refine ⟨603477153634905265034561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1609272409693080706758829 603477153634905265034561)
            ·
              refine ⟨452607865226178948775921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603477153634905265034561 452607865226178948775921)
              ·
                refine ⟨339455898919634211581941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452607865226178948775921 339455898919634211581941)
                ·
                  refine ⟨31823990523715707335807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339455898919634211581941 31823990523715707335807)
                  ·
                    rfl

theorem cell23_557793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 5].length) (baseStart_557793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557793 prefixEnd_557793 := by exact prefixLift 557793
  have htrace : WordTrace (prefixWord ++ tailWord_557793) baseStart_557793 baseEnd_557793 := by
    simpa [prefixWord, tailWord_557793, baseEnd_557793] using wordTrace_append hprefix tailTrace_557793
  have hstable : (prefixWord ++ tailWord_557793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557793).length < 2 ^ (prefixWord ++ tailWord_557793).sum := by decide
  have hdescent : baseEnd_557793 < baseStart_557793 := by decide
  rcases family_descends (prefixWord ++ tailWord_557793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557802 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_557802 : Nat := 118140960795 + 557802 * 2 ^ 59
def prefixEnd_557802 : Nat := 4983230072969 + 3 ^ 40 * 557802 * 2
def baseEnd_557802 : Nat := 95473512013110610269907

theorem tailTrace_557802 : CollatzResearch.WordTrace tailWord_557802 prefixEnd_557802 95473512013110610269907 := by
  unfold tailWord_557802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086177581296523460568915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13563140216790729228183773 5086177581296523460568915)
  ·
    refine ⟨7629266371944785190853373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5086177581296523460568915 7629266371944785190853373)
    ·
      refine ⟨2860974889479294446570015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7629266371944785190853373 2860974889479294446570015)
      ·
        refine ⟨4291462334218941669855023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2860974889479294446570015 4291462334218941669855023)
        ·
          refine ⟨6437193501328412504782535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291462334218941669855023 6437193501328412504782535)
          ·
            refine ⟨9655790251992618757173803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437193501328412504782535 9655790251992618757173803)
            ·
              refine ⟨14483685377988928135760705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655790251992618757173803 14483685377988928135760705)
              ·
                refine ⟨10862764033491696101820529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14483685377988928135760705 10862764033491696101820529)
                ·
                  refine ⟨8147073025118772076365397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10862764033491696101820529 8147073025118772076365397)
                  ·
                    refine ⟨95473512013110610269907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8147073025118772076365397 95473512013110610269907)
                    ·
                      rfl

theorem cell23_557802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_557802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557802 prefixEnd_557802 := by exact prefixLift 557802
  have htrace : WordTrace (prefixWord ++ tailWord_557802) baseStart_557802 baseEnd_557802 := by
    simpa [prefixWord, tailWord_557802, baseEnd_557802] using wordTrace_append hprefix tailTrace_557802
  have hstable : (prefixWord ++ tailWord_557802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557802).length < 2 ^ (prefixWord ++ tailWord_557802).sum := by decide
  have hdescent : baseEnd_557802 < baseStart_557802 := by decide
  rcases family_descends (prefixWord ++ tailWord_557802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557826 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_557826 : Nat := 118140960795 + 557826 * 2 ^ 59
def prefixEnd_557826 : Nat := 4983230072969 + 3 ^ 40 * 557826 * 2
def baseEnd_557826 : Nat := 286432859575039736909611

theorem tailTrace_557826 : CollatzResearch.WordTrace tailWord_557826 prefixEnd_557826 286432859575039736909611 := by
  unfold tailWord_557826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086396419274786485287333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13563723784732763960766221 5086396419274786485287333)
  ·
    refine ⟨953699328614022465991375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5086396419274786485287333 953699328614022465991375)
    ·
      refine ⟨1430548992921033698987063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953699328614022465991375 1430548992921033698987063)
      ·
        refine ⟨2145823489381550548480595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430548992921033698987063 2145823489381550548480595)
        ·
          refine ⟨3218735234072325822720893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145823489381550548480595 3218735234072325822720893)
          ·
            refine ⟨1207025712777122183520335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3218735234072325822720893 1207025712777122183520335)
            ·
              refine ⟨1810538569165683275280503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207025712777122183520335 1810538569165683275280503)
              ·
                refine ⟨2715807853748524912920755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810538569165683275280503 2715807853748524912920755)
                ·
                  refine ⟨4073711780622787369381133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715807853748524912920755 4073711780622787369381133)
                  ·
                    refine ⟨1527641917733545263517925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4073711780622787369381133 1527641917733545263517925)
                    ·
                      refine ⟨286432859575039736909611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1527641917733545263517925 286432859575039736909611)
                      ·
                        rfl

theorem cell23_557826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_557826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557826 prefixEnd_557826 := by exact prefixLift 557826
  have htrace : WordTrace (prefixWord ++ tailWord_557826) baseStart_557826 baseEnd_557826 := by
    simpa [prefixWord, tailWord_557826, baseEnd_557826] using wordTrace_append hprefix tailTrace_557826
  have hstable : (prefixWord ++ tailWord_557826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557826).length < 2 ^ (prefixWord ++ tailWord_557826).sum := by decide
  have hdescent : baseEnd_557826 < baseStart_557826 := by decide
  rcases family_descends (prefixWord ++ tailWord_557826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557872 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_557872 : Nat := 118140960795 + 557872 * 2 ^ 59
def prefixEnd_557872 : Nat := 4983230072969 + 3 ^ 40 * 557872 * 2
def baseEnd_557872 : Nat := 286456479685146556934399

theorem tailTrace_557872 : CollatzResearch.WordTrace tailWord_557872 prefixEnd_557872 286456479685146556934399 := by
  unfold tailWord_557872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173631717466247898661935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13564842289954997198215913 10173631717466247898661935)
  ·
    refine ⟨15260447576199371847992903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10173631717466247898661935 15260447576199371847992903)
    ·
      refine ⟨22890671364299057771989355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15260447576199371847992903 22890671364299057771989355)
      ·
        refine ⟨34336007046448586657984033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22890671364299057771989355 34336007046448586657984033)
        ·
          refine ⟨25752005284836439993488025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34336007046448586657984033 25752005284836439993488025)
          ·
            refine ⟨19314003963627329995116019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25752005284836439993488025 19314003963627329995116019)
            ·
              refine ⟨28971005945440994992674029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19314003963627329995116019 28971005945440994992674029)
              ·
                refine ⟨10864127229540373122252761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28971005945440994992674029 10864127229540373122252761)
                ·
                  refine ⟨8148095422155279841689571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10864127229540373122252761 8148095422155279841689571)
                  ·
                    refine ⟨12222143133232919762534357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8148095422155279841689571 12222143133232919762534357)
                    ·
                      refine ⟨286456479685146556934399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12222143133232919762534357 286456479685146556934399)
                      ·
                        rfl

theorem cell23_557872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_557872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557872 prefixEnd_557872 := by exact prefixLift 557872
  have htrace : WordTrace (prefixWord ++ tailWord_557872) baseStart_557872 baseEnd_557872 := by
    simpa [prefixWord, tailWord_557872, baseEnd_557872] using wordTrace_append hprefix tailTrace_557872
  have hstable : (prefixWord ++ tailWord_557872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557872).length < 2 ^ (prefixWord ++ tailWord_557872).sum := by decide
  have hdescent : baseEnd_557872 < baseStart_557872 := by decide
  rcases family_descends (prefixWord ++ tailWord_557872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557893 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_557893 : Nat := 118140960795 + 557893 * 2 ^ 59
def prefixEnd_557893 : Nat := 4983230072969 + 3 ^ 40 * 557893 * 2
def baseEnd_557893 : Nat := 286467262778890974771803

theorem tailTrace_557893 : CollatzResearch.WordTrace tailWord_557893 prefixEnd_557893 286467262778890974771803 := by
  unfold tailWord_557893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348029367856416383838333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13565352911904277589225555 20348029367856416383838333)
  ·
    refine ⟨7630511012946156143939375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20348029367856416383838333 7630511012946156143939375)
    ·
      refine ⟨11445766519419234215909063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630511012946156143939375 11445766519419234215909063)
      ·
        refine ⟨17168649779128851323863595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11445766519419234215909063 17168649779128851323863595)
        ·
          refine ⟨25752974668693276985795393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17168649779128851323863595 25752974668693276985795393)
          ·
            refine ⟨19314731001519957739346545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25752974668693276985795393 19314731001519957739346545)
            ·
              refine ⟨14486048251139968304509909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19314731001519957739346545 14486048251139968304509909)
              ·
                refine ⟨339516755886093007136951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14486048251139968304509909 339516755886093007136951)
                ·
                  refine ⟨509275133829139510705427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339516755886093007136951 509275133829139510705427)
                  ·
                    refine ⟨763912700743709266058141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 509275133829139510705427 763912700743709266058141)
                    ·
                      refine ⟨286467262778890974771803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 763912700743709266058141 286467262778890974771803)
                      ·
                        rfl

theorem cell23_557893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_557893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557893 prefixEnd_557893 := by exact prefixLift 557893
  have htrace : WordTrace (prefixWord ++ tailWord_557893) baseStart_557893 baseEnd_557893 := by
    simpa [prefixWord, tailWord_557893, baseEnd_557893] using wordTrace_append hprefix tailTrace_557893
  have hstable : (prefixWord ++ tailWord_557893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557893).length < 2 ^ (prefixWord ++ tailWord_557893).sum := by decide
  have hdescent : baseEnd_557893 < baseStart_557893 := by decide
  rcases family_descends (prefixWord ++ tailWord_557893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557919 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_557919 : Nat := 118140960795 + 557919 * 2 ^ 59
def prefixEnd_557919 : Nat := 4983230072969 + 3 ^ 40 * 557919 * 2
def baseEnd_557919 : Nat := 286480613275907873046683

theorem tailTrace_557919 : CollatzResearch.WordTrace tailWord_557919 prefixEnd_557919 286480613275907873046683 := by
  unfold tailWord_557919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348977665762222824284811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13565985110508148549523207 20348977665762222824284811)
  ·
    refine ⟨30523466498643334236427217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20348977665762222824284811 30523466498643334236427217)
    ·
      refine ⟨22892599873982500677320413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30523466498643334236427217 22892599873982500677320413)
      ·
        refine ⟨8584724952743437753995155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22892599873982500677320413 8584724952743437753995155)
        ·
          refine ⟨12877087429115156630992733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584724952743437753995155 12877087429115156630992733)
          ·
            refine ⟨4828907785918183736622275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12877087429115156630992733 4828907785918183736622275)
            ·
              refine ⟨7243361678877275604933413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828907785918183736622275 7243361678877275604933413)
              ·
                refine ⟨1358130314789489175925015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7243361678877275604933413 1358130314789489175925015)
                ·
                  refine ⟨2037195472184233763887523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358130314789489175925015 2037195472184233763887523)
                  ·
                    refine ⟨3055793208276350645831285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2037195472184233763887523 3055793208276350645831285)
                    ·
                      refine ⟨286480613275907873046683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3055793208276350645831285 286480613275907873046683)
                      ·
                        rfl

theorem cell23_557919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_557919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557919 prefixEnd_557919 := by exact prefixLift 557919
  have htrace : WordTrace (prefixWord ++ tailWord_557919) baseStart_557919 baseEnd_557919 := by
    simpa [prefixWord, tailWord_557919, baseEnd_557919] using wordTrace_append hprefix tailTrace_557919
  have hstable : (prefixWord ++ tailWord_557919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557919).length < 2 ^ (prefixWord ++ tailWord_557919).sum := by decide
  have hdescent : baseEnd_557919 < baseStart_557919 := by decide
  rcases family_descends (prefixWord ++ tailWord_557919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557933 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_557933 : Nat := 118140960795 + 557933 * 2 ^ 59
def prefixEnd_557933 : Nat := 4983230072969 + 3 ^ 40 * 557933 * 2
def baseEnd_557933 : Nat := 286487802005070818271619

theorem tailTrace_557933 : CollatzResearch.WordTrace tailWord_557933 prefixEnd_557933 286487802005070818271619 := by
  unfold tailWord_557933
  simp only [CollatzResearch.WordTrace]
  refine ⟨20349488287711503215294453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13566325525141002143529635 20349488287711503215294453)
  ·
    refine ⟨1907764526972953426433855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20349488287711503215294453 1907764526972953426433855)
    ·
      refine ⟨2861646790459430139650783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907764526972953426433855 2861646790459430139650783)
      ·
        refine ⟨4292470185689145209476175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861646790459430139650783 4292470185689145209476175)
        ·
          refine ⟨6438705278533717814214263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292470185689145209476175 6438705278533717814214263)
          ·
            refine ⟨9658057917800576721321395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438705278533717814214263 9658057917800576721321395)
            ·
              refine ⟨14487086876700865081982093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9658057917800576721321395 14487086876700865081982093)
              ·
                refine ⟨5432657578762824405743285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14487086876700865081982093 5432657578762824405743285)
                ·
                  refine ⟨509311648009014788038433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5432657578762824405743285 509311648009014788038433)
                  ·
                    refine ⟨381983736006761091028825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 509311648009014788038433 381983736006761091028825)
                    ·
                      refine ⟨286487802005070818271619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381983736006761091028825 286487802005070818271619)
                      ·
                        rfl

theorem cell23_557933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_557933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557933 prefixEnd_557933 := by exact prefixLift 557933
  have htrace : WordTrace (prefixWord ++ tailWord_557933) baseStart_557933 baseEnd_557933 := by
    simpa [prefixWord, tailWord_557933, baseEnd_557933] using wordTrace_append hprefix tailTrace_557933
  have hstable : (prefixWord ++ tailWord_557933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557933).length < 2 ^ (prefixWord ++ tailWord_557933).sum := by decide
  have hdescent : baseEnd_557933 < baseStart_557933 := by decide
  rcases family_descends (prefixWord ++ tailWord_557933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557983 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_557983 : Nat := 118140960795 + 557983 * 2 ^ 59
def prefixEnd_557983 : Nat := 4983230072969 + 3 ^ 40 * 557983 * 2
def baseEnd_557983 : Nat := 286513476037795622646389

theorem tailTrace_557983 : CollatzResearch.WordTrace tailWord_557983 prefixEnd_557983 286513476037795622646389 := by
  unfold tailWord_557983
  simp only [CollatzResearch.WordTrace]
  refine ⟨20351311937530361754614603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13567541291686907836409735 20351311937530361754614603)
  ·
    refine ⟨30526967906295542631921905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20351311937530361754614603 30526967906295542631921905)
    ·
      refine ⟨22895225929721656973941429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30526967906295542631921905 22895225929721656973941429)
      ·
        refine ⟨2146427430911405341307009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22895225929721656973941429 2146427430911405341307009)
        ·
          refine ⟨1609820573183554005980257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146427430911405341307009 1609820573183554005980257)
          ·
            refine ⟨1207365429887665504485193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609820573183554005980257 1207365429887665504485193)
            ·
              refine ⟨905524072415749128363895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207365429887665504485193 905524072415749128363895)
              ·
                refine ⟨1358286108623623692545843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905524072415749128363895 1358286108623623692545843)
                ·
                  refine ⟨2037429162935435538818765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358286108623623692545843 2037429162935435538818765)
                  ·
                    refine ⟨764035936100788327057037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037429162935435538818765 764035936100788327057037)
                    ·
                      refine ⟨286513476037795622646389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764035936100788327057037 286513476037795622646389)
                      ·
                        rfl

theorem cell23_557983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_557983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557983 prefixEnd_557983 := by exact prefixLift 557983
  have htrace : WordTrace (prefixWord ++ tailWord_557983) baseStart_557983 baseEnd_557983 := by
    simpa [prefixWord, tailWord_557983, baseEnd_557983] using wordTrace_append hprefix tailTrace_557983
  have hstable : (prefixWord ++ tailWord_557983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557983).length < 2 ^ (prefixWord ++ tailWord_557983).sum := by decide
  have hdescent : baseEnd_557983 < baseStart_557983 := by decide
  rcases family_descends (prefixWord ++ tailWord_557983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557993 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 1, 3, 2]
def baseStart_557993 : Nat := 118140960795 + 557993 * 2 ^ 59
def prefixEnd_557993 : Nat := 4983230072969 + 3 ^ 40 * 557993 * 2
def baseEnd_557993 : Nat := 286518610844340583521343

theorem tailTrace_557993 : CollatzResearch.WordTrace tailWord_557993 prefixEnd_557993 286518610844340583521343 := by
  unfold tailWord_557993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20351676667494133462478633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13567784444996088974985755 20351676667494133462478633)
  ·
    refine ⟨15263757500620600096858975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20351676667494133462478633 15263757500620600096858975)
    ·
      refine ⟨22895636250930900145288463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15263757500620600096858975 22895636250930900145288463)
      ·
        refine ⟨34343454376396350217932695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22895636250930900145288463 34343454376396350217932695)
        ·
          refine ⟨51515181564594525326899043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34343454376396350217932695 51515181564594525326899043)
          ·
            refine ⟨77272772346891787990348565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51515181564594525326899043 77272772346891787990348565)
            ·
              refine ⟨3622161203760552562047589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77272772346891787990348565 3622161203760552562047589)
              ·
                refine ⟨679155225705103605383923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3622161203760552562047589 679155225705103605383923)
                ·
                  refine ⟨1018732838557655408075885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679155225705103605383923 1018732838557655408075885)
                  ·
                    refine ⟨382024814459120778028457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018732838557655408075885 382024814459120778028457)
                    ·
                      refine ⟨286518610844340583521343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382024814459120778028457 286518610844340583521343)
                      ·
                        rfl

theorem cell23_557993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3, 2].length) (baseStart_557993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557993 prefixEnd_557993 := by exact prefixLift 557993
  have htrace : WordTrace (prefixWord ++ tailWord_557993) baseStart_557993 baseEnd_557993 := by
    simpa [prefixWord, tailWord_557993, baseEnd_557993] using wordTrace_append hprefix tailTrace_557993
  have hstable : (prefixWord ++ tailWord_557993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557993).length < 2 ^ (prefixWord ++ tailWord_557993).sum := by decide
  have hdescent : baseEnd_557993 < baseStart_557993 := by decide
  rcases family_descends (prefixWord ++ tailWord_557993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558004 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_558004 : Nat := 118140960795 + 558004 * 2 ^ 59
def prefixEnd_558004 : Nat := 4983230072969 + 3 ^ 40 * 558004 * 2
def baseEnd_558004 : Nat := 286524259131540040483793

theorem tailTrace_558004 : CollatzResearch.WordTrace tailWord_558004 prefixEnd_558004 286524259131540040483793 := by
  unfold tailWord_558004
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176038935227141170564533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13568051913636188227419377 10176038935227141170564533)
  ·
    refine ⟨954003650177544484740425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10176038935227141170564533 954003650177544484740425)
    ·
      refine ⟨715502737633158363555319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 954003650177544484740425 715502737633158363555319)
      ·
        refine ⟨1073254106449737545332979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715502737633158363555319 1073254106449737545332979)
        ·
          refine ⟨1609881159674606317999469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073254106449737545332979 1609881159674606317999469)
          ·
            refine ⟨603705434877977369249801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1609881159674606317999469 603705434877977369249801)
            ·
              refine ⟨452779076158483026937351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603705434877977369249801 452779076158483026937351)
              ·
                refine ⟨679168614237724540406027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452779076158483026937351 679168614237724540406027)
                ·
                  refine ⟨1018752921356586810609041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679168614237724540406027 1018752921356586810609041)
                  ·
                    refine ⟨764064691017440107956781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018752921356586810609041 764064691017440107956781)
                    ·
                      refine ⟨286524259131540040483793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764064691017440107956781 286524259131540040483793)
                      ·
                        rfl

theorem cell23_558004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_558004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558004 prefixEnd_558004 := by exact prefixLift 558004
  have htrace : WordTrace (prefixWord ++ tailWord_558004) baseStart_558004 baseEnd_558004 := by
    simpa [prefixWord, tailWord_558004, baseEnd_558004] using wordTrace_append hprefix tailTrace_558004
  have hstable : (prefixWord ++ tailWord_558004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558004).length < 2 ^ (prefixWord ++ tailWord_558004).sum := by decide
  have hdescent : baseEnd_558004 < baseStart_558004 := by decide
  rcases family_descends (prefixWord ++ tailWord_558004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558019 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_558019 : Nat := 118140960795 + 558019 * 2 ^ 59
def prefixEnd_558019 : Nat := 4983230072969 + 3 ^ 40 * 558019 * 2
def baseEnd_558019 : Nat := 286531961341357481796223

theorem tailTrace_558019 : CollatzResearch.WordTrace tailWord_558019 prefixEnd_558019 286531961341357481796223 := by
  unfold tailWord_558019
  simp only [CollatzResearch.WordTrace]
  refine ⟨20352624965399939902925111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13568416643599959935283407 20352624965399939902925111)
  ·
    refine ⟨30528937448099909854387667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20352624965399939902925111 30528937448099909854387667)
    ·
      refine ⟨45793406172149864781581501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30528937448099909854387667 45793406172149864781581501)
      ·
        refine ⟨17172527314556199293093063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45793406172149864781581501 17172527314556199293093063)
        ·
          refine ⟨25758790971834298939639595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17172527314556199293093063 25758790971834298939639595)
          ·
            refine ⟨38638186457751448409459393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25758790971834298939639595 38638186457751448409459393)
            ·
              refine ⟨28978639843313586307094545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38638186457751448409459393 28978639843313586307094545)
              ·
                refine ⟨21733979882485189730320909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28978639843313586307094545 21733979882485189730320909)
                ·
                  refine ⟨8150242455931946148870341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21733979882485189730320909 8150242455931946148870341)
                  ·
                    refine ⟨1528170460487239902913189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8150242455931946148870341 1528170460487239902913189)
                    ·
                      refine ⟨286531961341357481796223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1528170460487239902913189 286531961341357481796223)
                      ·
                        rfl

theorem cell23_558019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_558019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558019 prefixEnd_558019 := by exact prefixLift 558019
  have htrace : WordTrace (prefixWord ++ tailWord_558019) baseStart_558019 baseEnd_558019 := by
    simpa [prefixWord, tailWord_558019, baseEnd_558019] using wordTrace_append hprefix tailTrace_558019
  have hstable : (prefixWord ++ tailWord_558019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558019).length < 2 ^ (prefixWord ++ tailWord_558019).sum := by decide
  have hdescent : baseEnd_558019 < baseStart_558019 := by decide
  rcases family_descends (prefixWord ++ tailWord_558019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558040 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_558040 : Nat := 118140960795 + 558040 * 2 ^ 59
def prefixEnd_558040 : Nat := 4983230072969 + 3 ^ 40 * 558040 * 2
def baseEnd_558040 : Nat := 286542744435101899633627

theorem tailTrace_558040 : CollatzResearch.WordTrace tailWord_558040 prefixEnd_558040 286542744435101899633627 := by
  unfold tailWord_558040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176695449161930244719787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13568927265549240326293049 10176695449161930244719787)
  ·
    refine ⟨15265043173742895367079681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10176695449161930244719787 15265043173742895367079681)
    ·
      refine ⟨11448782380307171525309761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15265043173742895367079681 11448782380307171525309761)
      ·
        refine ⟨8586586785230378643982321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11448782380307171525309761 8586586785230378643982321)
        ·
          refine ⟨6439940088922783982986741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8586586785230378643982321 6439940088922783982986741)
          ·
            refine ⟨603744383336510998405007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6439940088922783982986741 603744383336510998405007)
            ·
              refine ⟨905616575004766497607511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603744383336510998405007 905616575004766497607511)
              ·
                refine ⟨1358424862507149746411267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905616575004766497607511 1358424862507149746411267)
                ·
                  refine ⟨2037637293760724619616901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358424862507149746411267 2037637293760724619616901)
                  ·
                    refine ⟨382056992580135866178169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2037637293760724619616901 382056992580135866178169)
                    ·
                      refine ⟨286542744435101899633627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382056992580135866178169 286542744435101899633627)
                      ·
                        rfl

theorem cell23_558040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_558040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558040 prefixEnd_558040 := by exact prefixLift 558040
  have htrace : WordTrace (prefixWord ++ tailWord_558040) baseStart_558040 baseEnd_558040 := by
    simpa [prefixWord, tailWord_558040, baseEnd_558040] using wordTrace_append hprefix tailTrace_558040
  have hstable : (prefixWord ++ tailWord_558040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558040).length < 2 ^ (prefixWord ++ tailWord_558040).sum := by decide
  have hdescent : baseEnd_558040 < baseStart_558040 := by decide
  rcases family_descends (prefixWord ++ tailWord_558040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558056 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_558056 : Nat := 118140960795 + 558056 * 2 ^ 59
def prefixEnd_558056 : Nat := 4983230072969 + 3 ^ 40 * 558056 * 2
def baseEnd_558056 : Nat := 286550960125573837033553

theorem tailTrace_558056 : CollatzResearch.WordTrace tailWord_558056 prefixEnd_558056 286550960125573837033553 := by
  unfold tailWord_558056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176987233132947611011011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13569316310843930148014681 10176987233132947611011011)
  ·
    refine ⟨15265480849699421416516517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10176987233132947611011011 15265480849699421416516517)
    ·
      refine ⟨2862277659318641515596847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15265480849699421416516517 2862277659318641515596847)
      ·
        refine ⟨4293416488977962273395271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862277659318641515596847 4293416488977962273395271)
        ·
          refine ⟨6440124733466943410092907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293416488977962273395271 6440124733466943410092907)
          ·
            refine ⟨9660187100200415115139361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440124733466943410092907 9660187100200415115139361)
            ·
              refine ⟨7245140325150311336354521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660187100200415115139361 7245140325150311336354521)
              ·
                refine ⟨5433855243862733502265891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245140325150311336354521 5433855243862733502265891)
                ·
                  refine ⟨8150782865794100253398837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433855243862733502265891 8150782865794100253398837)
                  ·
                    refine ⟨764135893668196898756141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8150782865794100253398837 764135893668196898756141)
                    ·
                      refine ⟨286550960125573837033553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764135893668196898756141 286550960125573837033553)
                      ·
                        rfl

theorem cell23_558056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_558056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558056 prefixEnd_558056 := by exact prefixLift 558056
  have htrace : WordTrace (prefixWord ++ tailWord_558056) baseStart_558056 baseEnd_558056 := by
    simpa [prefixWord, tailWord_558056, baseEnd_558056] using wordTrace_append hprefix tailTrace_558056
  have hstable : (prefixWord ++ tailWord_558056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558056).length < 2 ^ (prefixWord ++ tailWord_558056).sum := by decide
  have hdescent : baseEnd_558056 < baseStart_558056 := by decide
  rcases family_descends (prefixWord ++ tailWord_558056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558063 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 5]
def baseStart_558063 : Nat := 118140960795 + 558063 * 2 ^ 59
def prefixEnd_558063 : Nat := 4983230072969 + 3 ^ 40 * 558063 * 2
def baseEnd_558063 : Nat := 31839394943350589960669

theorem tailTrace_558063 : CollatzResearch.WordTrace tailWord_558063 prefixEnd_558063 31839394943350589960669 := by
  unfold tailWord_558063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20354229777240535417526843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13569486518160356945017895 20354229777240535417526843)
  ·
    refine ⟨30531344665860803126290265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20354229777240535417526843 30531344665860803126290265)
    ·
      refine ⟨22898508499395602344717699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30531344665860803126290265 22898508499395602344717699)
      ·
        refine ⟨34347762749093403517076549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22898508499395602344717699 34347762749093403517076549)
        ·
          refine ⟨6440205515455013159451853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34347762749093403517076549 6440205515455013159451853)
          ·
            refine ⟨2415077068295629934794445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6440205515455013159451853 2415077068295629934794445)
            ·
              refine ⟨905653900610861225547917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2415077068295629934794445 905653900610861225547917)
              ·
                refine ⟨339620212729072959580469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905653900610861225547917 339620212729072959580469)
                ·
                  refine ⟨31839394943350589960669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339620212729072959580469 31839394943350589960669)
                  ·
                    rfl

theorem cell23_558063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 5].length) (baseStart_558063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558063 prefixEnd_558063 := by exact prefixLift 558063
  have htrace : WordTrace (prefixWord ++ tailWord_558063) baseStart_558063 baseEnd_558063 := by
    simpa [prefixWord, tailWord_558063, baseEnd_558063] using wordTrace_append hprefix tailTrace_558063
  have hstable : (prefixWord ++ tailWord_558063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558063).length < 2 ^ (prefixWord ++ tailWord_558063).sum := by decide
  have hdescent : baseEnd_558063 < baseStart_558063 := by decide
  rcases family_descends (prefixWord ++ tailWord_558063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558076 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_558076 : Nat := 118140960795 + 558076 * 2 ^ 59
def prefixEnd_558076 : Nat := 4983230072969 + 3 ^ 40 * 558076 * 2
def baseEnd_558076 : Nat := 95520409912887919594487

theorem tailTrace_558076 : CollatzResearch.WordTrace tailWord_558076 prefixEnd_558076 95520409912887919594487 := by
  unfold tailWord_558076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177351963096719318875041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13569802617462292425166721 10177351963096719318875041)
  ·
    refine ⟨7633013972322539489156281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10177351963096719318875041 7633013972322539489156281)
    ·
      refine ⟨5724760479241904616867211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7633013972322539489156281 5724760479241904616867211)
      ·
        refine ⟨8587140718862856925300817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5724760479241904616867211 8587140718862856925300817)
        ·
          refine ⟨6440355539147142693975613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8587140718862856925300817 6440355539147142693975613)
          ·
            refine ⟨2415133327180178510240855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6440355539147142693975613 2415133327180178510240855)
            ·
              refine ⟨3622699990770267765361283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415133327180178510240855 3622699990770267765361283)
              ·
                refine ⟨5434049986155401648041925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622699990770267765361283 5434049986155401648041925)
                ·
                  refine ⟨1018884372404137809007861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5434049986155401648041925 1018884372404137809007861)
                  ·
                    refine ⟨95520409912887919594487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1018884372404137809007861 95520409912887919594487)
                    ·
                      rfl

theorem cell23_558076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_558076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558076 prefixEnd_558076 := by exact prefixLift 558076
  have htrace : WordTrace (prefixWord ++ tailWord_558076) baseStart_558076 baseEnd_558076 := by
    simpa [prefixWord, tailWord_558076, baseEnd_558076] using wordTrace_append hprefix tailTrace_558076
  have hstable : (prefixWord ++ tailWord_558076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558076).length < 2 ^ (prefixWord ++ tailWord_558076).sum := by decide
  have hdescent : baseEnd_558076 < baseStart_558076 := by decide
  rcases family_descends (prefixWord ++ tailWord_558076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_558079 : Nat := 118140960795 + 558079 * 2 ^ 59
def prefixEnd_558079 : Nat := 4983230072969 + 3 ^ 40 * 558079 * 2
def baseEnd_558079 : Nat := 286562770180627247045947

theorem tailTrace_558079 : CollatzResearch.WordTrace tailWord_558079 prefixEnd_558079 286562770180627247045947 := by
  unfold tailWord_558079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20354813345182570150109291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13569875563455046766739527 20354813345182570150109291)
  ·
    refine ⟨30532220017773855225163937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20354813345182570150109291 30532220017773855225163937)
    ·
      refine ⟨22899165013330391418872953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30532220017773855225163937 22899165013330391418872953)
      ·
        refine ⟨17174373759997793564154715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22899165013330391418872953 17174373759997793564154715)
        ·
          refine ⟨25761560639996690346232073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17174373759997793564154715 25761560639996690346232073)
          ·
            refine ⟨19321170479997517759674055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25761560639996690346232073 19321170479997517759674055)
            ·
              refine ⟨28981755719996276639511083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19321170479997517759674055 28981755719996276639511083)
              ·
                refine ⟨43472633579994414959266625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28981755719996276639511083 43472633579994414959266625)
                ·
                  refine ⟨32604475184995811219449969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43472633579994414959266625 32604475184995811219449969)
                  ·
                    refine ⟨24453356388746858414587477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32604475184995811219449969 24453356388746858414587477)
                    ·
                      refine ⟨286562770180627247045947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24453356388746858414587477 286562770180627247045947)
                      ·
                        rfl

theorem cell23_558079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_558079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558079 prefixEnd_558079 := by exact prefixLift 558079
  have htrace : WordTrace (prefixWord ++ tailWord_558079) baseStart_558079 baseEnd_558079 := by
    simpa [prefixWord, tailWord_558079, baseEnd_558079] using wordTrace_append hprefix tailTrace_558079
  have hstable : (prefixWord ++ tailWord_558079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558079).length < 2 ^ (prefixWord ++ tailWord_558079).sum := by decide
  have hdescent : baseEnd_558079 < baseStart_558079 := by decide
  rcases family_descends (prefixWord ++ tailWord_558079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558113 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_558113 : Nat := 118140960795 + 558113 * 2 ^ 59
def prefixEnd_558113 : Nat := 4983230072969 + 3 ^ 40 * 558113 * 2
def baseEnd_558113 : Nat := 286580228522880114020791

theorem tailTrace_558113 : CollatzResearch.WordTrace tailWord_558113 prefixEnd_558113 286580228522880114020791 := by
  unfold tailWord_558113
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356053427059393956846993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13570702284706262637897995 20356053427059393956846993)
  ·
    refine ⟨15267040070294545467635245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20356053427059393956846993 15267040070294545467635245)
    ·
      refine ⟨5725140026360454550363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15267040070294545467635245 5725140026360454550363217)
      ·
        refine ⟨4293855019770340912772413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5725140026360454550363217 4293855019770340912772413)
        ·
          refine ⟨1610195632413877842289655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4293855019770340912772413 1610195632413877842289655)
          ·
            refine ⟨2415293448620816763434483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610195632413877842289655 2415293448620816763434483)
            ·
              refine ⟨3622940172931225145151725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415293448620816763434483 3622940172931225145151725)
              ·
                refine ⟨1358602564849209429431897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3622940172931225145151725 1358602564849209429431897)
                ·
                  refine ⟨1018951923636907072073923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1358602564849209429431897 1018951923636907072073923)
                  ·
                    refine ⟨1528427885455360608110885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018951923636907072073923 1528427885455360608110885)
                    ·
                      refine ⟨286580228522880114020791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1528427885455360608110885 286580228522880114020791)
                      ·
                        rfl

theorem cell23_558113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_558113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558113 prefixEnd_558113 := by exact prefixLift 558113
  have htrace : WordTrace (prefixWord ++ tailWord_558113) baseStart_558113 baseEnd_558113 := by
    simpa [prefixWord, tailWord_558113, baseEnd_558113] using wordTrace_append hprefix tailTrace_558113
  have hstable : (prefixWord ++ tailWord_558113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558113).length < 2 ^ (prefixWord ++ tailWord_558113).sum := by decide
  have hdescent : baseEnd_558113 < baseStart_558113 := by decide
  rcases family_descends (prefixWord ++ tailWord_558113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558163 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 3]
def baseStart_558163 : Nat := 118140960795 + 558163 * 2 ^ 59
def prefixEnd_558163 : Nat := 4983230072969 + 3 ^ 40 * 558163 * 2
def baseEnd_558163 : Nat := 286605902555604918395561

theorem tailTrace_558163 : CollatzResearch.WordTrace tailWord_558163 prefixEnd_558163 286605902555604918395561 := by
  unfold tailWord_558163
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357877076878252496167143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13571918051252168330778095 20357877076878252496167143)
  ·
    refine ⟨30536815615317378744250715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20357877076878252496167143 30536815615317378744250715)
    ·
      refine ⟨45805223422976068116376073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30536815615317378744250715 45805223422976068116376073)
      ·
        refine ⟨34353917567232051087282055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45805223422976068116376073 34353917567232051087282055)
        ·
          refine ⟨51530876350848076630923083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34353917567232051087282055 51530876350848076630923083)
          ·
            refine ⟨77296314526272114946384625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51530876350848076630923083 77296314526272114946384625)
            ·
              refine ⟨57972235894704086209788469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77296314526272114946384625 57972235894704086209788469)
              ·
                refine ⟨5434897115128508082167669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57972235894704086209788469 5434897115128508082167669)
                ·
                  refine ⟨509521604543297632703219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5434897115128508082167669 509521604543297632703219)
                  ·
                    refine ⟨764282406814946449054829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 509521604543297632703219 764282406814946449054829)
                    ·
                      refine ⟨286605902555604918395561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764282406814946449054829 286605902555604918395561)
                      ·
                        rfl

theorem cell23_558163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_558163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558163 prefixEnd_558163 := by exact prefixLift 558163
  have htrace : WordTrace (prefixWord ++ tailWord_558163) baseStart_558163 baseEnd_558163 := by
    simpa [prefixWord, tailWord_558163, baseEnd_558163] using wordTrace_append hprefix tailTrace_558163
  have hstable : (prefixWord ++ tailWord_558163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558163).length < 2 ^ (prefixWord ++ tailWord_558163).sum := by decide
  have hdescent : baseEnd_558163 < baseStart_558163 := by decide
  rcases family_descends (prefixWord ++ tailWord_558163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558240 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_558240 : Nat := 118140960795 + 558240 * 2 ^ 59
def prefixEnd_558240 : Nat := 4983230072969 + 3 ^ 40 * 558240 * 2
def baseEnd_558240 : Nat := 286645440566001117132707

theorem tailTrace_558240 : CollatzResearch.WordTrace tailWord_558240 prefixEnd_558240 286645440566001117132707 := by
  unfold tailWord_558240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180342748799647323360087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13573790331732863097813449 10180342748799647323360087)
  ·
    refine ⟨15270514123199470985040131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180342748799647323360087 15270514123199470985040131)
    ·
      refine ⟨22905771184799206477560197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270514123199470985040131 22905771184799206477560197)
      ·
        refine ⟨4294832097149851214542537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22905771184799206477560197 4294832097149851214542537)
        ·
          refine ⟨3221124072862388410906903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4294832097149851214542537 3221124072862388410906903)
          ·
            refine ⟨4831686109293582616360355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221124072862388410906903 4831686109293582616360355)
            ·
              refine ⟨7247529163940373924540533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831686109293582616360355 7247529163940373924540533)
              ·
                refine ⟨679455859119410055425675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7247529163940373924540533 679455859119410055425675)
                ·
                  refine ⟨1019183788679115083138513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679455859119410055425675 1019183788679115083138513)
                  ·
                    refine ⟨764387841509336312353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1019183788679115083138513 764387841509336312353885)
                    ·
                      refine ⟨286645440566001117132707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764387841509336312353885 286645440566001117132707)
                      ·
                        rfl

theorem cell23_558240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_558240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558240 prefixEnd_558240 := by exact prefixLift 558240
  have htrace : WordTrace (prefixWord ++ tailWord_558240) baseStart_558240 baseEnd_558240 := by
    simpa [prefixWord, tailWord_558240, baseEnd_558240] using wordTrace_append hprefix tailTrace_558240
  have hstable : (prefixWord ++ tailWord_558240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558240).length < 2 ^ (prefixWord ++ tailWord_558240).sum := by decide
  have hdescent : baseEnd_558240 < baseStart_558240 := by decide
  rcases family_descends (prefixWord ++ tailWord_558240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558250 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_558250 : Nat := 118140960795 + 558250 * 2 ^ 59
def prefixEnd_558250 : Nat := 4983230072969 + 3 ^ 40 * 558250 * 2
def baseEnd_558250 : Nat := 286650575372546078007661

theorem tailTrace_558250 : CollatzResearch.WordTrace tailWord_558250 prefixEnd_558250 286650575372546078007661 := by
  unfold tailWord_558250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090262556890766588646051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13574033485042044236389469 5090262556890766588646051)
  ·
    refine ⟨7635393835336149882969077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090262556890766588646051 7635393835336149882969077)
    ·
      refine ⟨715818172062764051528351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7635393835336149882969077 715818172062764051528351)
      ·
        refine ⟨1073727258094146077292527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715818172062764051528351 1073727258094146077292527)
        ·
          refine ⟨1610590887141219115938791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073727258094146077292527 1610590887141219115938791)
          ·
            refine ⟨2415886330711828673908187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610590887141219115938791 2415886330711828673908187)
            ·
              refine ⟨3623829496067743010862281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415886330711828673908187 3623829496067743010862281)
              ·
                refine ⟨2717872122050807258146711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623829496067743010862281 2717872122050807258146711)
                ·
                  refine ⟨4076808183076210887220067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717872122050807258146711 4076808183076210887220067)
                  ·
                    refine ⟨6115212274614316330830101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4076808183076210887220067 6115212274614316330830101)
                    ·
                      refine ⟨286650575372546078007661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6115212274614316330830101 286650575372546078007661)
                      ·
                        rfl

theorem cell23_558250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_558250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558250 prefixEnd_558250 := by exact prefixLift 558250
  have htrace : WordTrace (prefixWord ++ tailWord_558250) baseStart_558250 baseEnd_558250 := by
    simpa [prefixWord, tailWord_558250, baseEnd_558250] using wordTrace_append hprefix tailTrace_558250
  have hstable : (prefixWord ++ tailWord_558250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558250).length < 2 ^ (prefixWord ++ tailWord_558250).sum := by decide
  have hdescent : baseEnd_558250 < baseStart_558250 := by decide
  rcases family_descends (prefixWord ++ tailWord_558250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558256 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_558256 : Nat := 118140960795 + 558256 * 2 ^ 59
def prefixEnd_558256 : Nat := 4983230072969 + 3 ^ 40 * 558256 * 2
def baseEnd_558256 : Nat := 95551218752157684844211

theorem tailTrace_558256 : CollatzResearch.WordTrace tailWord_558256 prefixEnd_558256 95551218752157684844211 := by
  unfold tailWord_558256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180634532770664689651311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13574179377027552919535081 10180634532770664689651311)
  ·
    refine ⟨15270951799155997034476967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180634532770664689651311 15270951799155997034476967)
    ·
      refine ⟨22906427698733995551715451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270951799155997034476967 22906427698733995551715451)
      ·
        refine ⟨34359641548100993327573177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22906427698733995551715451 34359641548100993327573177)
        ·
          refine ⟨25769731161075744995679883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34359641548100993327573177 25769731161075744995679883)
          ·
            refine ⟨38654596741613617493519825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25769731161075744995679883 38654596741613617493519825)
            ·
              refine ⟨28990947556210213120139869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38654596741613617493519825 28990947556210213120139869)
              ·
                refine ⟨10871605333578829920052451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28990947556210213120139869 10871605333578829920052451)
                ·
                  refine ⟨16307408000368244880078677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10871605333578829920052451 16307408000368244880078677)
                  ·
                    refine ⟨95551218752157684844211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16307408000368244880078677 95551218752157684844211)
                    ·
                      rfl

theorem cell23_558256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_558256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558256 prefixEnd_558256 := by exact prefixLift 558256
  have htrace : WordTrace (prefixWord ++ tailWord_558256) baseStart_558256 baseEnd_558256 := by
    simpa [prefixWord, tailWord_558256, baseEnd_558256] using wordTrace_append hprefix tailTrace_558256
  have hstable : (prefixWord ++ tailWord_558256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558256).length < 2 ^ (prefixWord ++ tailWord_558256).sum := by decide
  have hdescent : baseEnd_558256 < baseStart_558256 := by decide
  rcases family_descends (prefixWord ++ tailWord_558256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558323 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_558323 : Nat := 118140960795 + 558323 * 2 ^ 59
def prefixEnd_558323 : Nat := 4983230072969 + 3 ^ 40 * 558323 * 2
def baseEnd_558323 : Nat := 286688059460324292394825

theorem tailTrace_558323 : CollatzResearch.WordTrace tailWord_558323 prefixEnd_558323 286688059460324292394825 := by
  unfold tailWord_558323
  simp only [CollatzResearch.WordTrace]
  refine ⟨20363712756298599821991623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13575808504199066547994415 20363712756298599821991623)
  ·
    refine ⟨30545569134447899732987435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20363712756298599821991623 30545569134447899732987435)
    ·
      refine ⟨45818353701671849599481153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30545569134447899732987435 45818353701671849599481153)
      ·
        refine ⟨34363765276253887199610865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45818353701671849599481153 34363765276253887199610865)
        ·
          refine ⟨25772823957190415399708149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34363765276253887199610865 25772823957190415399708149)
          ·
            refine ⟨2416202245986601443722639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25772823957190415399708149 2416202245986601443722639)
            ·
              refine ⟨3624303368979902165583959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416202245986601443722639 3624303368979902165583959)
              ·
                refine ⟨5436455053469853248375939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624303368979902165583959 5436455053469853248375939)
                ·
                  refine ⟨8154682580204779872563909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436455053469853248375939 8154682580204779872563909)
                  ·
                    refine ⟨1529002983788396226105733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8154682580204779872563909 1529002983788396226105733)
                    ·
                      refine ⟨286688059460324292394825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1529002983788396226105733 286688059460324292394825)
                      ·
                        rfl

theorem cell23_558323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_558323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558323 prefixEnd_558323 := by exact prefixLift 558323
  have htrace : WordTrace (prefixWord ++ tailWord_558323) baseStart_558323 baseEnd_558323 := by
    simpa [prefixWord, tailWord_558323, baseEnd_558323] using wordTrace_append hprefix tailTrace_558323
  have hstable : (prefixWord ++ tailWord_558323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558323).length < 2 ^ (prefixWord ++ tailWord_558323).sum := by decide
  have hdescent : baseEnd_558323 < baseStart_558323 := by decide
  rcases family_descends (prefixWord ++ tailWord_558323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558360 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_558360 : Nat := 118140960795 + 558360 * 2 ^ 59
def prefixEnd_558360 : Nat := 4983230072969 + 3 ^ 40 * 558360 * 2
def baseEnd_558360 : Nat := 286707058244540647632155

theorem tailTrace_558360 : CollatzResearch.WordTrace tailWord_558360 prefixEnd_558360 286707058244540647632155 := by
  unfold tailWord_558360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182531128582277570544267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13576708171443036760725689 10182531128582277570544267)
  ·
    refine ⟨15273796692873416355816401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10182531128582277570544267 15273796692873416355816401)
    ·
      refine ⟨11455347519655062266862301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15273796692873416355816401 11455347519655062266862301)
      ·
        refine ⟨4295755319870648350073363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11455347519655062266862301 4295755319870648350073363)
        ·
          refine ⟨6443632979805972525110045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295755319870648350073363 6443632979805972525110045)
          ·
            refine ⟨2416362367427239696916267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6443632979805972525110045 2416362367427239696916267)
            ·
              refine ⟨3624543551140859545374401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416362367427239696916267 3624543551140859545374401)
              ·
                refine ⟨2718407663355644659030801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624543551140859545374401 2718407663355644659030801)
                ·
                  refine ⟨2038805747516733494273101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2718407663355644659030801 2038805747516733494273101)
                  ·
                    refine ⟨764552155318775060352413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038805747516733494273101 764552155318775060352413)
                    ·
                      refine ⟨286707058244540647632155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764552155318775060352413 286707058244540647632155)
                      ·
                        rfl

theorem cell23_558360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_558360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558360 prefixEnd_558360 := by exact prefixLift 558360
  have htrace : WordTrace (prefixWord ++ tailWord_558360) baseStart_558360 baseEnd_558360 := by
    simpa [prefixWord, tailWord_558360, baseEnd_558360] using wordTrace_append hprefix tailTrace_558360
  have hstable : (prefixWord ++ tailWord_558360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558360).length < 2 ^ (prefixWord ++ tailWord_558360).sum := by decide
  have hdescent : baseEnd_558360 < baseStart_558360 := by decide
  rcases family_descends (prefixWord ++ tailWord_558360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558363 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 4, 5]
def baseStart_558363 : Nat := 118140960795 + 558363 * 2 ^ 59
def prefixEnd_558363 : Nat := 4983230072969 + 3 ^ 40 * 558363 * 2
def baseEnd_558363 : Nat := 95569532895501378631547

theorem tailTrace_558363 : CollatzResearch.WordTrace tailWord_558363 prefixEnd_558363 95569532895501378631547 := by
  unfold tailWord_558363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365171676153686653447743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13576781117435791102298495 20365171676153686653447743)
  ·
    refine ⟨30547757514230529980171615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365171676153686653447743 30547757514230529980171615)
    ·
      refine ⟨45821636271345794970257423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30547757514230529980171615 45821636271345794970257423)
      ·
        refine ⟨68732454407018692455386135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45821636271345794970257423 68732454407018692455386135)
        ·
          refine ⟨103098681610528038683079203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68732454407018692455386135 103098681610528038683079203)
          ·
            refine ⟨154648022415792058024618805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103098681610528038683079203 154648022415792058024618805)
            ·
              refine ⟨14498252101480505439808013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154648022415792058024618805 14498252101480505439808013)
              ·
                refine ⟨5436844538055189539928005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14498252101480505439808013 5436844538055189539928005)
                ·
                  refine ⟨1019408350885348038736501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5436844538055189539928005 1019408350885348038736501)
                  ·
                    refine ⟨95569532895501378631547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1019408350885348038736501 95569532895501378631547)
                    ·
                      rfl

theorem cell23_558363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].length) (baseStart_558363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558363 prefixEnd_558363 := by exact prefixLift 558363
  have htrace : WordTrace (prefixWord ++ tailWord_558363) baseStart_558363 baseEnd_558363 := by
    simpa [prefixWord, tailWord_558363, baseEnd_558363] using wordTrace_append hprefix tailTrace_558363
  have hstable : (prefixWord ++ tailWord_558363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558363).length < 2 ^ (prefixWord ++ tailWord_558363).sum := by decide
  have hdescent : baseEnd_558363 < baseStart_558363 := by decide
  rcases family_descends (prefixWord ++ tailWord_558363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558378 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_558378 : Nat := 118140960795 + 558378 * 2 ^ 59
def prefixEnd_558378 : Nat := 4983230072969 + 3 ^ 40 * 558378 * 2
def baseEnd_558378 : Nat := 286716300896321577207073

theorem tailTrace_558378 : CollatzResearch.WordTrace tailWord_558378 prefixEnd_558378 286716300896321577207073 := by
  unfold tailWord_558378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091429692774836053810947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13577145847399562810162525 5091429692774836053810947)
  ·
    refine ⟨7637144539162254080716421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091429692774836053810947 7637144539162254080716421)
    ·
      refine ⟨1431964601092922640134329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7637144539162254080716421 1431964601092922640134329)
      ·
        refine ⟨1073973450819691980100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431964601092922640134329 1073973450819691980100747)
        ·
          refine ⟨1610960176229537970151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073973450819691980100747 1610960176229537970151121)
          ·
            refine ⟨1208220132172153477613341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610960176229537970151121 1208220132172153477613341)
            ·
              refine ⟨453082549564557554105003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1208220132172153477613341 453082549564557554105003)
              ·
                refine ⟨679623824346836331157505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453082549564557554105003 679623824346836331157505)
                ·
                  refine ⟨509717868260127248368129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679623824346836331157505 509717868260127248368129)
                  ·
                    refine ⟨382288401195095436276097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 509717868260127248368129 382288401195095436276097)
                    ·
                      refine ⟨286716300896321577207073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382288401195095436276097 286716300896321577207073)
                      ·
                        rfl

theorem cell23_558378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_558378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558378 prefixEnd_558378 := by exact prefixLift 558378
  have htrace : WordTrace (prefixWord ++ tailWord_558378) baseStart_558378 baseEnd_558378 := by
    simpa [prefixWord, tailWord_558378, baseEnd_558378] using wordTrace_append hprefix tailTrace_558378
  have hstable : (prefixWord ++ tailWord_558378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558378).length < 2 ^ (prefixWord ++ tailWord_558378).sum := by decide
  have hdescent : baseEnd_558378 < baseStart_558378 := by decide
  rcases family_descends (prefixWord ++ tailWord_558378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558400 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_558400 : Nat := 118140960795 + 558400 * 2 ^ 59
def prefixEnd_558400 : Nat := 4983230072969 + 3 ^ 40 * 558400 * 2
def baseEnd_558400 : Nat := 286727597470720491131971

theorem tailTrace_558400 : CollatzResearch.WordTrace tailWord_558400 prefixEnd_558400 286727597470720491131971 := by
  unfold tailWord_558400
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183260588509820986272327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13577680784679761315029769 10183260588509820986272327)
  ·
    refine ⟨15274890882764731479408491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10183260588509820986272327 15274890882764731479408491)
    ·
      refine ⟨22912336324147097219112737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274890882764731479408491 22912336324147097219112737)
      ·
        refine ⟨17184252243110322914334553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22912336324147097219112737 17184252243110322914334553)
        ·
          refine ⟨12888189182332742185750915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17184252243110322914334553 12888189182332742185750915)
          ·
            refine ⟨19332283773499113278626373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888189182332742185750915 19332283773499113278626373)
            ·
              refine ⟨3624803207531083739742445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19332283773499113278626373 3624803207531083739742445)
              ·
                refine ⟨1359301202824156402403417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624803207531083739742445 1359301202824156402403417)
                ·
                  refine ⟨1019475902118117301802563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359301202824156402403417 1019475902118117301802563)
                  ·
                    refine ⟨1529213853177175952703845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1019475902118117301802563 1529213853177175952703845)
                    ·
                      refine ⟨286727597470720491131971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1529213853177175952703845 286727597470720491131971)
                      ·
                        rfl

theorem cell23_558400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_558400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558400 prefixEnd_558400 := by exact prefixLift 558400
  have htrace : WordTrace (prefixWord ++ tailWord_558400) baseStart_558400 baseEnd_558400 := by
    simpa [prefixWord, tailWord_558400, baseEnd_558400] using wordTrace_append hprefix tailTrace_558400
  have hstable : (prefixWord ++ tailWord_558400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558400).length < 2 ^ (prefixWord ++ tailWord_558400).sum := by decide
  have hdescent : baseEnd_558400 < baseStart_558400 := by decide
  rcases family_descends (prefixWord ++ tailWord_558400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558403 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_558403 : Nat := 118140960795 + 558403 * 2 ^ 59
def prefixEnd_558403 : Nat := 4983230072969 + 3 ^ 40 * 558403 * 2
def baseEnd_558403 : Nat := 286729137912683979394457

theorem tailTrace_558403 : CollatzResearch.WordTrace tailWord_558403 prefixEnd_558403 286729137912683979394457 := by
  unfold tailWord_558403
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366630596008773484903863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13577753730672515656602575 20366630596008773484903863)
  ·
    refine ⟨30549945894013160227355795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20366630596008773484903863 30549945894013160227355795)
    ·
      refine ⟨45824918841019740341033693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30549945894013160227355795 45824918841019740341033693)
      ·
        refine ⟨17184344565382402627887635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45824918841019740341033693 17184344565382402627887635)
        ·
          refine ⟨25776516848073603941831453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17184344565382402627887635 25776516848073603941831453)
          ·
            refine ⟨9666193818027601478186795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25776516848073603941831453 9666193818027601478186795)
            ·
              refine ⟨14499290727041402217280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666193818027601478186795 14499290727041402217280193)
              ·
                refine ⟨10874468045281051662960145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14499290727041402217280193 10874468045281051662960145)
                ·
                  refine ⟨8155851033960788747220109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10874468045281051662960145 8155851033960788747220109)
                  ·
                    refine ⟨3058444137735295780207541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8155851033960788747220109 3058444137735295780207541)
                    ·
                      refine ⟨286729137912683979394457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3058444137735295780207541 286729137912683979394457)
                      ·
                        rfl

theorem cell23_558403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_558403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558403 prefixEnd_558403 := by exact prefixLift 558403
  have htrace : WordTrace (prefixWord ++ tailWord_558403) baseStart_558403 baseEnd_558403 := by
    simpa [prefixWord, tailWord_558403, baseEnd_558403] using wordTrace_append hprefix tailTrace_558403
  have hstable : (prefixWord ++ tailWord_558403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558403).length < 2 ^ (prefixWord ++ tailWord_558403).sum := by decide
  have hdescent : baseEnd_558403 < baseStart_558403 := by decide
  rcases family_descends (prefixWord ++ tailWord_558403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558410 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_558410 : Nat := 118140960795 + 558410 * 2 ^ 59
def prefixEnd_558410 : Nat := 4983230072969 + 3 ^ 40 * 558410 * 2
def baseEnd_558410 : Nat := 95577577425755150668975

theorem tailTrace_558410 : CollatzResearch.WordTrace tailWord_558410 prefixEnd_558410 95577577425755150668975 := by
  unfold tailWord_558410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091721476745853420102171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13577923937988942453605789 5091721476745853420102171)
  ·
    refine ⟨7637582215118780130153257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091721476745853420102171 7637582215118780130153257)
    ·
      refine ⟨5728186661339085097614943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7637582215118780130153257 5728186661339085097614943)
      ·
        refine ⟨8592279992008627646422415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728186661339085097614943 8592279992008627646422415)
        ·
          refine ⟨12888419988012941469633623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592279992008627646422415 12888419988012941469633623)
          ·
            refine ⟨19332629982019412204450435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888419988012941469633623 19332629982019412204450435)
            ·
              refine ⟨28998944973029118306675653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19332629982019412204450435 28998944973029118306675653)
              ·
                refine ⟨5437302182442959682501685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28998944973029118306675653 5437302182442959682501685)
                ·
                  refine ⟨509747079604027470234533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5437302182442959682501685 509747079604027470234533)
                  ·
                    refine ⟨95577577425755150668975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 509747079604027470234533 95577577425755150668975)
                    ·
                      rfl

theorem cell23_558410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_558410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558410 prefixEnd_558410 := by exact prefixLift 558410
  have htrace : WordTrace (prefixWord ++ tailWord_558410) baseStart_558410 baseEnd_558410 := by
    simpa [prefixWord, tailWord_558410, baseEnd_558410] using wordTrace_append hprefix tailTrace_558410
  have hstable : (prefixWord ++ tailWord_558410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558410).length < 2 ^ (prefixWord ++ tailWord_558410).sum := by decide
  have hdescent : baseEnd_558410 < baseStart_558410 := by decide
  rcases family_descends (prefixWord ++ tailWord_558410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558429 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_558429 : Nat := 118140960795 + 558429 * 2 ^ 59
def prefixEnd_558429 : Nat := 4983230072969 + 3 ^ 40 * 558429 * 2
def baseEnd_558429 : Nat := 286742488409700877669339

theorem tailTrace_558429 : CollatzResearch.WordTrace tailWord_558429 prefixEnd_558429 286742488409700877669339 := by
  unfold tailWord_558429
  simp only [CollatzResearch.WordTrace]
  refine ⟨20367578893914579925350341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13578385929276386616900227 20367578893914579925350341)
  ·
    refine ⟨3818921042608983736003189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20367578893914579925350341 3818921042608983736003189)
    ·
      refine ⟨358023847744592225250299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3818921042608983736003189 358023847744592225250299)
      ·
        refine ⟨537035771616888337875449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358023847744592225250299 537035771616888337875449)
        ·
          refine ⟨402776828712666253406587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537035771616888337875449 402776828712666253406587)
          ·
            refine ⟨604165243068999380109881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402776828712666253406587 604165243068999380109881)
            ·
              refine ⟨453123932301749535082411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604165243068999380109881 453123932301749535082411)
              ·
                refine ⟨679685898452624302623617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453123932301749535082411 679685898452624302623617)
                ·
                  refine ⟨509764423839468226967713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679685898452624302623617 509764423839468226967713)
                  ·
                    refine ⟨382323317879601170225785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 509764423839468226967713 382323317879601170225785)
                    ·
                      refine ⟨286742488409700877669339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382323317879601170225785 286742488409700877669339)
                      ·
                        rfl

theorem cell23_558429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_558429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558429 prefixEnd_558429 := by exact prefixLift 558429
  have htrace : WordTrace (prefixWord ++ tailWord_558429) baseStart_558429 baseEnd_558429 := by
    simpa [prefixWord, tailWord_558429, baseEnd_558429] using wordTrace_append hprefix tailTrace_558429
  have hstable : (prefixWord ++ tailWord_558429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558429).length < 2 ^ (prefixWord ++ tailWord_558429).sum := by decide
  have hdescent : baseEnd_558429 < baseStart_558429 := by decide
  rcases family_descends (prefixWord ++ tailWord_558429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558517 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_558517 : Nat := 118140960795 + 558517 * 2 ^ 59
def prefixEnd_558517 : Nat := 4983230072969 + 3 ^ 40 * 558517 * 2
def baseEnd_558517 : Nat := 95595891569098844456311

theorem tailTrace_558517 : CollatzResearch.WordTrace tailWord_558517 prefixEnd_558517 95595891569098844456311 := by
  unfold tailWord_558517
  simp only [CollatzResearch.WordTrace]
  refine ⟨20370788517595770954553805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13580525678397180636369203 20370788517595770954553805)
  ·
    refine ⟨7639045694098414107957677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20370788517595770954553805 7639045694098414107957677)
    ·
      refine ⟨2864642135286905290484129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7639045694098414107957677 2864642135286905290484129)
      ·
        refine ⟨2148481601465178967863097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2864642135286905290484129 2148481601465178967863097)
        ·
          refine ⟨1611361201098884225897323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2148481601465178967863097 1611361201098884225897323)
          ·
            refine ⟨2417041801648326338845985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611361201098884225897323 2417041801648326338845985)
            ·
              refine ⟨1812781351236244754134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417041801648326338845985 1812781351236244754134489)
              ·
                refine ⟨1359586013427183565600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812781351236244754134489 1359586013427183565600867)
                ·
                  refine ⟨2039379020140775348401301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359586013427183565600867 2039379020140775348401301)
                  ·
                    refine ⟨95595891569098844456311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2039379020140775348401301 95595891569098844456311)
                    ·
                      rfl

theorem cell23_558517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_558517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558517 prefixEnd_558517 := by exact prefixLift 558517
  have htrace : WordTrace (prefixWord ++ tailWord_558517) baseStart_558517 baseEnd_558517 := by
    simpa [prefixWord, tailWord_558517, baseEnd_558517] using wordTrace_append hprefix tailTrace_558517
  have hstable : (prefixWord ++ tailWord_558517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558517).length < 2 ^ (prefixWord ++ tailWord_558517).sum := by decide
  have hdescent : baseEnd_558517 < baseStart_558517 := by decide
  rcases family_descends (prefixWord ++ tailWord_558517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558521 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_558521 : Nat := 118140960795 + 558521 * 2 ^ 59
def prefixEnd_558521 : Nat := 4983230072969 + 3 ^ 40 * 558521 * 2
def baseEnd_558521 : Nat := 95596576209971505906305

theorem tailTrace_558521 : CollatzResearch.WordTrace tailWord_558521 prefixEnd_558521 95596576209971505906305 := by
  unfold tailWord_558521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20370934409581279637699417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13580622939720853091799611 20370934409581279637699417)
  ·
    refine ⟨15278200807185959728274563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20370934409581279637699417 15278200807185959728274563)
    ·
      refine ⟨22917301210778939592411845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15278200807185959728274563 22917301210778939592411845)
      ·
        refine ⟨4296993977021051173577221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22917301210778939592411845 4296993977021051173577221)
        ·
          refine ⟨805686370691447095045729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4296993977021051173577221 805686370691447095045729)
          ·
            refine ⟨604264778018585321284297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805686370691447095045729 604264778018585321284297)
            ·
              refine ⟨453198583513938990963223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604264778018585321284297 453198583513938990963223)
              ·
                refine ⟨679797875270908486444835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453198583513938990963223 679797875270908486444835)
                ·
                  refine ⟨1019696812906362729667253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679797875270908486444835 1019696812906362729667253)
                  ·
                    refine ⟨95596576209971505906305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1019696812906362729667253 95596576209971505906305)
                    ·
                      rfl

theorem cell23_558521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_558521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558521 prefixEnd_558521 := by exact prefixLift 558521
  have htrace : WordTrace (prefixWord ++ tailWord_558521) baseStart_558521 baseEnd_558521 := by
    simpa [prefixWord, tailWord_558521, baseEnd_558521] using wordTrace_append hprefix tailTrace_558521
  have hstable : (prefixWord ++ tailWord_558521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558521).length < 2 ^ (prefixWord ++ tailWord_558521).sum := by decide
  have hdescent : baseEnd_558521 < baseStart_558521 := by decide
  rcases family_descends (prefixWord ++ tailWord_558521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558554 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_558554 : Nat := 118140960795 + 558554 * 2 ^ 59
def prefixEnd_558554 : Nat := 4983230072969 + 3 ^ 40 * 558554 * 2
def baseEnd_558554 : Nat := 286806673491512888606263

theorem tailTrace_558554 : CollatzResearch.WordTrace tailWord_558554 prefixEnd_558554 286806673491512888606263 := by
  unfold tailWord_558554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093034504615431568412679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13581425345641150849100477 5093034504615431568412679)
  ·
    refine ⟨7639551756923147352619019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5093034504615431568412679 7639551756923147352619019)
    ·
      refine ⟨11459327635384721028928529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639551756923147352619019 11459327635384721028928529)
      ·
        refine ⟨8594495726538540771696397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11459327635384721028928529 8594495726538540771696397)
        ·
          refine ⟨3222935897451952789386149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8594495726538540771696397 3222935897451952789386149)
          ·
            refine ⟨604300480772241148009903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3222935897451952789386149 604300480772241148009903)
            ·
              refine ⟨906450721158361722014855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604300480772241148009903 906450721158361722014855)
              ·
                refine ⟨1359676081737542583022283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906450721158361722014855 1359676081737542583022283)
                ·
                  refine ⟨2039514122606313874533425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359676081737542583022283 2039514122606313874533425)
                  ·
                    refine ⟨1529635591954735405900069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2039514122606313874533425 1529635591954735405900069)
                    ·
                      refine ⟨286806673491512888606263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1529635591954735405900069 286806673491512888606263)
                      ·
                        rfl

theorem cell23_558554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_558554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558554 prefixEnd_558554 := by exact prefixLift 558554
  have htrace : WordTrace (prefixWord ++ tailWord_558554) baseStart_558554 baseEnd_558554 := by
    simpa [prefixWord, tailWord_558554, baseEnd_558554] using wordTrace_append hprefix tailTrace_558554
  have hstable : (prefixWord ++ tailWord_558554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558554).length < 2 ^ (prefixWord ++ tailWord_558554).sum := by decide
  have hdescent : baseEnd_558554 < baseStart_558554 := by decide
  rcases family_descends (prefixWord ++ tailWord_558554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558574 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_558574 : Nat := 118140960795 + 558574 * 2 ^ 59
def prefixEnd_558574 : Nat := 4983230072969 + 3 ^ 40 * 558574 * 2
def baseEnd_558574 : Nat := 286816943104602810356171

theorem tailTrace_558574 : CollatzResearch.WordTrace tailWord_558574 prefixEnd_558574 286816943104602810356171 := by
  unfold tailWord_558574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546608434798658711172347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13581911652259513126252517 2546608434798658711172347)
  ·
    refine ⟨3819912652197988066758521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546608434798658711172347 3819912652197988066758521)
    ·
      refine ⟨2864934489148491050068891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3819912652197988066758521 2864934489148491050068891)
      ·
        refine ⟨4297401733722736575103337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864934489148491050068891 4297401733722736575103337)
        ·
          refine ⟨3223051300292052431327503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297401733722736575103337 3223051300292052431327503)
          ·
            refine ⟨4834576950438078646991255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223051300292052431327503 4834576950438078646991255)
            ·
              refine ⟨7251865425657117970486883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834576950438078646991255 7251865425657117970486883)
              ·
                refine ⟨10877798138485676955730325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7251865425657117970486883 10877798138485676955730325)
                ·
                  refine ⟨509896787741516107299859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10877798138485676955730325 509896787741516107299859)
                  ·
                    refine ⟨764845181612274160949789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 509896787741516107299859 764845181612274160949789)
                    ·
                      refine ⟨286816943104602810356171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 764845181612274160949789 286816943104602810356171)
                      ·
                        rfl

theorem cell23_558574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_558574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558574 prefixEnd_558574 := by exact prefixLift 558574
  have htrace : WordTrace (prefixWord ++ tailWord_558574) baseStart_558574 baseEnd_558574 := by
    simpa [prefixWord, tailWord_558574, baseEnd_558574] using wordTrace_append hprefix tailTrace_558574
  have hstable : (prefixWord ++ tailWord_558574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558574).length < 2 ^ (prefixWord ++ tailWord_558574).sum := by decide
  have hdescent : baseEnd_558574 < baseStart_558574 := by decide
  rcases family_descends (prefixWord ++ tailWord_558574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558598 : List Nat := [6, 2, 1, 1, 2, 1, 2, 8]
def baseStart_558598 : Nat := 118140960795 + 558598 * 2 ^ 59
def prefixEnd_558598 : Nat := 4983230072969 + 3 ^ 40 * 558598 * 2
def baseEnd_558598 : Nat := 10623306171863359868743

theorem tailTrace_558598 : CollatzResearch.WordTrace tailWord_558598 prefixEnd_558598 10623306171863359868743 := by
  unfold tailWord_558598
  simp only [CollatzResearch.WordTrace]
  refine ⟨636679463446947555882889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13582495220201547858834965 636679463446947555882889)
  ·
    refine ⟨477509597585210666912167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 636679463446947555882889 477509597585210666912167)
    ·
      refine ⟨716264396377816000368251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477509597585210666912167 716264396377816000368251)
      ·
        refine ⟨1074396594566724000552377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716264396377816000368251 1074396594566724000552377)
        ·
          refine ⟨805797445925043000414283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074396594566724000552377 805797445925043000414283)
          ·
            refine ⟨1208696168887564500621425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805797445925043000414283 1208696168887564500621425)
            ·
              refine ⟨906522126665673375466069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208696168887564500621425 906522126665673375466069)
              ·
                refine ⟨10623306171863359868743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 906522126665673375466069 10623306171863359868743)
                ·
                  rfl

theorem cell23_558598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_558598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558598 prefixEnd_558598 := by exact prefixLift 558598
  have htrace : WordTrace (prefixWord ++ tailWord_558598) baseStart_558598 baseEnd_558598 := by
    simpa [prefixWord, tailWord_558598, baseEnd_558598] using wordTrace_append hprefix tailTrace_558598
  have hstable : (prefixWord ++ tailWord_558598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558598).length < 2 ^ (prefixWord ++ tailWord_558598).sum := by decide
  have hdescent : baseEnd_558598 < baseStart_558598 := by decide
  rcases family_descends (prefixWord ++ tailWord_558598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558648 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_558648 : Nat := 118140960795 + 558648 * 2 ^ 59
def prefixEnd_558648 : Nat := 4983230072969 + 3 ^ 40 * 558648 * 2
def baseEnd_558648 : Nat := 286854940673035520830831

theorem tailTrace_558648 : CollatzResearch.WordTrace tailWord_558648 prefixEnd_558648 286854940673035520830831 := by
  unfold tailWord_558648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187783240060590163786299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13583710986747453551715065 10187783240060590163786299)
  ·
    refine ⟨15281674860090885245679449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10187783240060590163786299 15281674860090885245679449)
    ·
      refine ⟨11461256145068163934259587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15281674860090885245679449 11461256145068163934259587)
      ·
        refine ⟨17191884217602245901389381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11461256145068163934259587 17191884217602245901389381)
        ·
          refine ⟨3223478290800421106510509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17191884217602245901389381 3223478290800421106510509)
          ·
            refine ⟨1208804359050157914941441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3223478290800421106510509 1208804359050157914941441)
            ·
              refine ⟨906603269287618436206081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208804359050157914941441 906603269287618436206081)
              ·
                refine ⟨679952451965713827154561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906603269287618436206081 679952451965713827154561)
                ·
                  refine ⟨509964338974285370365921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679952451965713827154561 509964338974285370365921)
                  ·
                    refine ⟨382473254230714027774441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 509964338974285370365921 382473254230714027774441)
                    ·
                      refine ⟨286854940673035520830831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382473254230714027774441 286854940673035520830831)
                      ·
                        rfl

theorem cell23_558648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_558648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558648 prefixEnd_558648 := by exact prefixLift 558648
  have htrace : WordTrace (prefixWord ++ tailWord_558648) baseStart_558648 baseEnd_558648 := by
    simpa [prefixWord, tailWord_558648, baseEnd_558648] using wordTrace_append hprefix tailTrace_558648
  have hstable : (prefixWord ++ tailWord_558648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558648).length < 2 ^ (prefixWord ++ tailWord_558648).sum := by decide
  have hdescent : baseEnd_558648 < baseStart_558648 := by decide
  rcases family_descends (prefixWord ++ tailWord_558648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558684 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_558684 : Nat := 118140960795 + 558684 * 2 ^ 59
def prefixEnd_558684 : Nat := 4983230072969 + 3 ^ 40 * 558684 * 2
def baseEnd_558684 : Nat := 95624475325532459993555

theorem tailTrace_558684 : CollatzResearch.WordTrace tailWord_558684 prefixEnd_558684 95624475325532459993555 := by
  unfold tailWord_558684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188439753995379237941553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13584586338660505650588737 10188439753995379237941553)
  ·
    refine ⟨7641329815496534428456165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10188439753995379237941553 7641329815496534428456165)
    ·
      refine ⟨1432749340405600205335531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7641329815496534428456165 1432749340405600205335531)
      ·
        refine ⟨2149124010608400308003297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432749340405600205335531 2149124010608400308003297)
        ·
          refine ⟨1611843007956300231002473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2149124010608400308003297 1611843007956300231002473)
          ·
            refine ⟨1208882255967225173251855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611843007956300231002473 1208882255967225173251855)
            ·
              refine ⟨1813323383950837759877783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208882255967225173251855 1813323383950837759877783)
              ·
                refine ⟨2719985075926256639816675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813323383950837759877783 2719985075926256639816675)
                ·
                  refine ⟨4079977613889384959725013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719985075926256639816675 4079977613889384959725013)
                  ·
                    refine ⟨95624475325532459993555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4079977613889384959725013 95624475325532459993555)
                    ·
                      rfl

theorem cell23_558684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_558684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558684 prefixEnd_558684 := by exact prefixLift 558684
  have htrace : WordTrace (prefixWord ++ tailWord_558684) baseStart_558684 baseEnd_558684 := by
    simpa [prefixWord, tailWord_558684, baseEnd_558684] using wordTrace_append hprefix tailTrace_558684
  have hstable : (prefixWord ++ tailWord_558684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558684).length < 2 ^ (prefixWord ++ tailWord_558684).sum := by decide
  have hdescent : baseEnd_558684 < baseStart_558684 := by decide
  rcases family_descends (prefixWord ++ tailWord_558684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558721 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_558721 : Nat := 118140960795 + 558721 * 2 ^ 59
def prefixEnd_558721 : Nat := 4983230072969 + 3 ^ 40 * 558721 * 2
def baseEnd_558721 : Nat := 286892424760813735217995

theorem tailTrace_558721 : CollatzResearch.WordTrace tailWord_558721 prefixEnd_558721 286892424760813735217995 := by
  unfold tailWord_558721
  simp only [CollatzResearch.WordTrace]
  refine ⟨20378229008856713794980017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13585486005904475863320011 20378229008856713794980017)
  ·
    refine ⟨15283671756642535346235013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20378229008856713794980017 15283671756642535346235013)
    ·
      refine ⟨2865688454370475377419065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15283671756642535346235013 2865688454370475377419065)
      ·
        refine ⟨2149266340777856533064299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2865688454370475377419065 2149266340777856533064299)
        ·
          refine ⟨3223899511166784799596449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149266340777856533064299 3223899511166784799596449)
          ·
            refine ⟨2417924633375088599697337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223899511166784799596449 2417924633375088599697337)
            ·
              refine ⟨1813443475031316449773003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417924633375088599697337 1813443475031316449773003)
              ·
                refine ⟨2720165212546974674659505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813443475031316449773003 2720165212546974674659505)
                ·
                  refine ⟨2040123909410231005994629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720165212546974674659505 2040123909410231005994629)
                  ·
                    refine ⟨382523233014418313623993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040123909410231005994629 382523233014418313623993)
                    ·
                      refine ⟨286892424760813735217995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382523233014418313623993 286892424760813735217995)
                      ·
                        rfl

theorem cell23_558721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_558721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558721 prefixEnd_558721 := by exact prefixLift 558721
  have htrace : WordTrace (prefixWord ++ tailWord_558721) baseStart_558721 baseEnd_558721 := by
    simpa [prefixWord, tailWord_558721, baseEnd_558721] using wordTrace_append hprefix tailTrace_558721
  have hstable : (prefixWord ++ tailWord_558721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558721).length < 2 ^ (prefixWord ++ tailWord_558721).sum := by decide
  have hdescent : baseEnd_558721 < baseStart_558721 := by decide
  rcases family_descends (prefixWord ++ tailWord_558721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_558764 : Nat := 118140960795 + 558764 * 2 ^ 59
def prefixEnd_558764 : Nat := 4983230072969 + 3 ^ 40 * 558764 * 2
def baseEnd_558764 : Nat := 286914504428957066980297

theorem tailTrace_558764 : CollatzResearch.WordTrace tailWord_558764 prefixEnd_558764 286914504428957066980297 := by
  unfold tailWord_558764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10189898673850466069397673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13586531565133954759196897 10189898673850466069397673)
  ·
    refine ⟨7642424005387849552048255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10189898673850466069397673 7642424005387849552048255)
    ·
      refine ⟨11463636008081774328072383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7642424005387849552048255 11463636008081774328072383)
      ·
        refine ⟨17195454012122661492108575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11463636008081774328072383 17195454012122661492108575)
        ·
          refine ⟨25793181018183992238162863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17195454012122661492108575 25793181018183992238162863)
          ·
            refine ⟨38689771527275988357244295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25793181018183992238162863 38689771527275988357244295)
            ·
              refine ⟨58034657290913982535866443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38689771527275988357244295 58034657290913982535866443)
              ·
                refine ⟨87051985936370973803799665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58034657290913982535866443 87051985936370973803799665)
                ·
                  refine ⟨65288989452278230352849749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87051985936370973803799665 65288989452278230352849749)
                  ·
                    refine ⟨382552672571942755973729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 65288989452278230352849749 382552672571942755973729)
                    ·
                      refine ⟨286914504428957066980297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382552672571942755973729 286914504428957066980297)
                      ·
                        rfl

theorem cell23_558764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_558764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558764 prefixEnd_558764 := by exact prefixLift 558764
  have htrace : WordTrace (prefixWord ++ tailWord_558764) baseStart_558764 baseEnd_558764 := by
    simpa [prefixWord, tailWord_558764, baseEnd_558764] using wordTrace_append hprefix tailTrace_558764
  have hstable : (prefixWord ++ tailWord_558764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558764).length < 2 ^ (prefixWord ++ tailWord_558764).sum := by decide
  have hdescent : baseEnd_558764 < baseStart_558764 := by decide
  rcases family_descends (prefixWord ++ tailWord_558764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558765 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_558765 : Nat := 118140960795 + 558765 * 2 ^ 59
def prefixEnd_558765 : Nat := 4983230072969 + 3 ^ 40 * 558765 * 2
def baseEnd_558765 : Nat := 95638339303203854355931

theorem tailTrace_558765 : CollatzResearch.WordTrace tailWord_558765 prefixEnd_558765 95638339303203854355931 := by
  unfold tailWord_558765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20379833820697309309581749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13586555880464872873054499 20379833820697309309581749)
  ·
    refine ⟨1910609420690372747773289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20379833820697309309581749 1910609420690372747773289)
    ·
      refine ⟨1432957065517779560829967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1910609420690372747773289 1432957065517779560829967)
      ·
        refine ⟨2149435598276669341244951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432957065517779560829967 2149435598276669341244951)
        ·
          refine ⟨3224153397415004011867427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149435598276669341244951 3224153397415004011867427)
          ·
            refine ⟨4836230096122506017801141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224153397415004011867427 4836230096122506017801141)
            ·
              refine ⟨453396571511484939168857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4836230096122506017801141 453396571511484939168857)
              ·
                refine ⟨340047428633613704376643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453396571511484939168857 340047428633613704376643)
                ·
                  refine ⟨510071142950420556564965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340047428633613704376643 510071142950420556564965)
                  ·
                    refine ⟨95638339303203854355931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 510071142950420556564965 95638339303203854355931)
                    ·
                      rfl

theorem cell23_558765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_558765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558765 prefixEnd_558765 := by exact prefixLift 558765
  have htrace : WordTrace (prefixWord ++ tailWord_558765) baseStart_558765 baseEnd_558765 := by
    simpa [prefixWord, tailWord_558765, baseEnd_558765] using wordTrace_append hprefix tailTrace_558765
  have hstable : (prefixWord ++ tailWord_558765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558765).length < 2 ^ (prefixWord ++ tailWord_558765).sum := by decide
  have hdescent : baseEnd_558765 < baseStart_558765 := by decide
  rcases family_descends (prefixWord ++ tailWord_558765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558781 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_558781 : Nat := 118140960795 + 558781 * 2 ^ 59
def prefixEnd_558781 : Nat := 4983230072969 + 3 ^ 40 * 558781 * 2
def baseEnd_558781 : Nat := 286923233600083500467719

theorem tailTrace_558781 : CollatzResearch.WordTrace tailWord_558781 prefixEnd_558781 286923233600083500467719 := by
  unfold tailWord_558781
  simp only [CollatzResearch.WordTrace]
  refine ⟨20380417388639344042164197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13586944925759562694776131 20380417388639344042164197)
  ·
    refine ⟨3821328260369877007905787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20380417388639344042164197 3821328260369877007905787)
    ·
      refine ⟨5731992390554815511858681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821328260369877007905787 5731992390554815511858681)
      ·
        refine ⟨4298994292916111633894011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5731992390554815511858681 4298994292916111633894011)
        ·
          refine ⟨6448491439374167450841017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298994292916111633894011 6448491439374167450841017)
          ·
            refine ⟨4836368579530625588130763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6448491439374167450841017 4836368579530625588130763)
            ·
              refine ⟨7254552869295938382196145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836368579530625588130763 7254552869295938382196145)
              ·
                refine ⟨5440914651971953786647109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7254552869295938382196145 5440914651971953786647109)
                ·
                  refine ⟨1020171497244741334996333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5440914651971953786647109 1020171497244741334996333)
                  ·
                    refine ⟨382564311466778000623625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020171497244741334996333 382564311466778000623625)
                    ·
                      refine ⟨286923233600083500467719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382564311466778000623625 286923233600083500467719)
                      ·
                        rfl

theorem cell23_558781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_558781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558781 prefixEnd_558781 := by exact prefixLift 558781
  have htrace : WordTrace (prefixWord ++ tailWord_558781) baseStart_558781 baseEnd_558781 := by
    simpa [prefixWord, tailWord_558781, baseEnd_558781] using wordTrace_append hprefix tailTrace_558781
  have hstable : (prefixWord ++ tailWord_558781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558781).length < 2 ^ (prefixWord ++ tailWord_558781).sum := by decide
  have hdescent : baseEnd_558781 < baseStart_558781 := by decide
  rcases family_descends (prefixWord ++ tailWord_558781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558787 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 6]
def baseStart_558787 : Nat := 118140960795 + 558787 * 2 ^ 59
def prefixEnd_558787 : Nat := 4983230072969 + 3 ^ 40 * 558787 * 2
def baseEnd_558787 : Nat := 95642104828003492330897

theorem tailTrace_558787 : CollatzResearch.WordTrace tailWord_558787 prefixEnd_558787 95642104828003492330897 := by
  unfold tailWord_558787
  simp only [CollatzResearch.WordTrace]
  refine ⟨20380636226617607066882615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587090817745071377921743 20380636226617607066882615)
  ·
    refine ⟨30570954339926410600323923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20380636226617607066882615 30570954339926410600323923)
    ·
      refine ⟨45856431509889615900485885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30570954339926410600323923 45856431509889615900485885)
      ·
        refine ⟨17196161816208605962682207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45856431509889615900485885 17196161816208605962682207)
        ·
          refine ⟨25794242724312908944023311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17196161816208605962682207 25794242724312908944023311)
          ·
            refine ⟨38691364086469363416034967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25794242724312908944023311 38691364086469363416034967)
            ·
              refine ⟨58037046129704045124052451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38691364086469363416034967 58037046129704045124052451)
              ·
                refine ⟨87055569194556067686078677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58037046129704045124052451 87055569194556067686078677)
                ·
                  refine ⟨2040364902997407836392469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87055569194556067686078677 2040364902997407836392469)
                  ·
                    refine ⟨95642104828003492330897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2040364902997407836392469 95642104828003492330897)
                    ·
                      rfl

theorem cell23_558787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_558787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558787 prefixEnd_558787 := by exact prefixLift 558787
  have htrace : WordTrace (prefixWord ++ tailWord_558787) baseStart_558787 baseEnd_558787 := by
    simpa [prefixWord, tailWord_558787, baseEnd_558787] using wordTrace_append hprefix tailTrace_558787
  have hstable : (prefixWord ++ tailWord_558787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558787).length < 2 ^ (prefixWord ++ tailWord_558787).sum := by decide
  have hdescent : baseEnd_558787 < baseStart_558787 := by decide
  rcases family_descends (prefixWord ++ tailWord_558787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558798 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_558798 : Nat := 118140960795 + 558798 * 2 ^ 59
def prefixEnd_558798 : Nat := 4983230072969 + 3 ^ 40 * 558798 * 2
def baseEnd_558798 : Nat := 286931962771209933955141

theorem tailTrace_558798 : CollatzResearch.WordTrace tailWord_558798 prefixEnd_558798 286931962771209933955141 := by
  unfold tailWord_558798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547629678697219493191631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13587358286385170630355365 2547629678697219493191631)
  ·
    refine ⟨3821444518045829239787447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547629678697219493191631 3821444518045829239787447)
    ·
      refine ⟨5732166777068743859681171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821444518045829239787447 5732166777068743859681171)
      ·
        refine ⟨8598250165603115789521757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732166777068743859681171 8598250165603115789521757)
        ·
          refine ⟨3224343812101168421070659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8598250165603115789521757 3224343812101168421070659)
          ·
            refine ⟨4836515718151752631605989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224343812101168421070659 4836515718151752631605989)
            ·
              refine ⟨906846697153453618426123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4836515718151752631605989 906846697153453618426123)
              ·
                refine ⟨1360270045730180427639185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906846697153453618426123 1360270045730180427639185)
                ·
                  refine ⟨1020202534297635320729389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360270045730180427639185 1020202534297635320729389)
                  ·
                    refine ⟨382575950361613245273521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020202534297635320729389 382575950361613245273521)
                    ·
                      refine ⟨286931962771209933955141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382575950361613245273521 286931962771209933955141)
                      ·
                        rfl

theorem cell23_558798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_558798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558798 prefixEnd_558798 := by exact prefixLift 558798
  have htrace : WordTrace (prefixWord ++ tailWord_558798) baseStart_558798 baseEnd_558798 := by
    simpa [prefixWord, tailWord_558798, baseEnd_558798] using wordTrace_append hprefix tailTrace_558798
  have hstable : (prefixWord ++ tailWord_558798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558798).length < 2 ^ (prefixWord ++ tailWord_558798).sum := by decide
  have hdescent : baseEnd_558798 < baseStart_558798 := by decide
  rcases family_descends (prefixWord ++ tailWord_558798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558817 : List Nat := [1, 2, 3, 1, 16]
def baseStart_558817 : Nat := 118140960795 + 558817 * 2 ^ 59
def prefixEnd_558817 : Nat := 4983230072969 + 3 ^ 40 * 558817 * 2
def baseEnd_558817 : Nat := 393610039648347544057

theorem tailTrace_558817 : CollatzResearch.WordTrace tailWord_558817 prefixEnd_558817 393610039648347544057 := by
  unfold tailWord_558817
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381730416508922190474705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587820277672614793649803 20381730416508922190474705)
  ·
    refine ⟨15286297812381691642856029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20381730416508922190474705 15286297812381691642856029)
    ·
      refine ⟨5732361679643134366071011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15286297812381691642856029 5732361679643134366071011)
      ·
        refine ⟨8598542519464701549106517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732361679643134366071011 8598542519464701549106517)
        ·
          refine ⟨393610039648347544057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 8598542519464701549106517 393610039648347544057)
          ·
            rfl

theorem cell23_558817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 16].length) (baseStart_558817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558817 prefixEnd_558817 := by exact prefixLift 558817
  have htrace : WordTrace (prefixWord ++ tailWord_558817) baseStart_558817 baseEnd_558817 := by
    simpa [prefixWord, tailWord_558817, baseEnd_558817] using wordTrace_append hprefix tailTrace_558817
  have hstable : (prefixWord ++ tailWord_558817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558817).length < 2 ^ (prefixWord ++ tailWord_558817).sum := by decide
  have hdescent : baseEnd_558817 < baseStart_558817 := by decide
  rcases family_descends (prefixWord ++ tailWord_558817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558838 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_558838 : Nat := 118140960795 + 558838 * 2 ^ 59
def prefixEnd_558838 : Nat := 4983230072969 + 3 ^ 40 * 558838 * 2
def baseEnd_558838 : Nat := 95650833999129925818319

theorem tailTrace_558838 : CollatzResearch.WordTrace tailWord_558838 prefixEnd_558838 95650833999129925818319 := by
  unfold tailWord_558838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273906021839552673561823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13588330899621895184659445 1273906021839552673561823)
  ·
    refine ⟨1910859032759329010342735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273906021839552673561823 1910859032759329010342735)
    ·
      refine ⟨2866288549138993515514103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910859032759329010342735 2866288549138993515514103)
      ·
        refine ⟨4299432823708490273271155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866288549138993515514103 4299432823708490273271155)
        ·
          refine ⟨6449149235562735409906733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299432823708490273271155 6449149235562735409906733)
          ·
            refine ⟨2418430963336025778715025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6449149235562735409906733 2418430963336025778715025)
            ·
              refine ⟨1813823222502019334036269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418430963336025778715025 1813823222502019334036269)
              ·
                refine ⟨680183708438257250263601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813823222502019334036269 680183708438257250263601)
                ·
                  refine ⟨510137781328692937697701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680183708438257250263601 510137781328692937697701)
                  ·
                    refine ⟨95650833999129925818319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 510137781328692937697701 95650833999129925818319)
                    ·
                      rfl

theorem cell23_558838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_558838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558838 prefixEnd_558838 := by exact prefixLift 558838
  have htrace : WordTrace (prefixWord ++ tailWord_558838) baseStart_558838 baseEnd_558838 := by
    simpa [prefixWord, tailWord_558838, baseEnd_558838] using wordTrace_append hprefix tailTrace_558838
  have hstable : (prefixWord ++ tailWord_558838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558838).length < 2 ^ (prefixWord ++ tailWord_558838).sum := by decide
  have hdescent : baseEnd_558838 < baseStart_558838 := by decide
  rcases family_descends (prefixWord ++ tailWord_558838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558951 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_558951 : Nat := 118140960795 + 558951 * 2 ^ 59
def prefixEnd_558951 : Nat := 4983230072969 + 3 ^ 40 * 558951 * 2
def baseEnd_558951 : Nat := 287010525311347835341937

theorem tailTrace_558951 : CollatzResearch.WordTrace tailWord_558951 prefixEnd_558951 287010525311347835341937 := by
  unfold tailWord_558951
  simp only [CollatzResearch.WordTrace]
  refine ⟨20386617798023463075852707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13591078532015642050568471 20386617798023463075852707)
  ·
    refine ⟨30579926697035194613779061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20386617798023463075852707 30579926697035194613779061)
    ·
      refine ⟨2866868127847049495041787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30579926697035194613779061 2866868127847049495041787)
      ·
        refine ⟨4300302191770574242562681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866868127847049495041787 4300302191770574242562681)
        ·
          refine ⟨3225226643827930681922011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300302191770574242562681 3225226643827930681922011)
          ·
            refine ⟨4837839965741896022883017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225226643827930681922011 4837839965741896022883017)
            ·
              refine ⟨3628379974306422017162263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837839965741896022883017 3628379974306422017162263)
              ·
                refine ⟨5442569961459633025743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628379974306422017162263 5442569961459633025743395)
                ·
                  refine ⟨8163854942189449538615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442569961459633025743395 8163854942189449538615093)
                  ·
                    refine ⟨765361400830260894245165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8163854942189449538615093 765361400830260894245165)
                    ·
                      refine ⟨287010525311347835341937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765361400830260894245165 287010525311347835341937)
                      ·
                        rfl

theorem cell23_558951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_558951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_558951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_558951 prefixEnd_558951 := by exact prefixLift 558951
  have htrace : WordTrace (prefixWord ++ tailWord_558951) baseStart_558951 baseEnd_558951 := by
    simpa [prefixWord, tailWord_558951, baseEnd_558951] using wordTrace_append hprefix tailTrace_558951
  have hstable : (prefixWord ++ tailWord_558951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558951).length < 2 ^ (prefixWord ++ tailWord_558951).sum := by decide
  have hdescent : baseEnd_558951 < baseStart_558951 := by decide
  rcases family_descends (prefixWord ++ tailWord_558951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559011 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3]
def baseStart_559011 : Nat := 118140960795 + 559011 * 2 ^ 59
def prefixEnd_559011 : Nat := 4983230072969 + 3 ^ 40 * 559011 * 2
def baseEnd_559011 : Nat := 287041334150617600591661

theorem tailTrace_559011 : CollatzResearch.WordTrace tailWord_559011 prefixEnd_559011 287041334150617600591661 := by
  unfold tailWord_559011
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388806177806093323036887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13592537451870728882024591 20388806177806093323036887)
  ·
    refine ⟨30583209266709139984555331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388806177806093323036887 30583209266709139984555331)
    ·
      refine ⟨45874813900063709976832997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30583209266709139984555331 45874813900063709976832997)
      ·
        refine ⟨8601527606261945620656187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45874813900063709976832997 8601527606261945620656187)
        ·
          refine ⟨12902291409392918430984281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601527606261945620656187 12902291409392918430984281)
          ·
            refine ⟨9676718557044688823238211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12902291409392918430984281 9676718557044688823238211)
            ·
              refine ⟨14515077835567033234857317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9676718557044688823238211 14515077835567033234857317)
              ·
                refine ⟨2721577094168818731535747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14515077835567033234857317 2721577094168818731535747)
                ·
                  refine ⟨4082365641253228097303621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721577094168818731535747 4082365641253228097303621)
                  ·
                    refine ⟨765443557734980268244429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082365641253228097303621 765443557734980268244429)
                    ·
                      refine ⟨287041334150617600591661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765443557734980268244429 287041334150617600591661)
                      ·
                        rfl

theorem cell23_559011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_559011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559011 prefixEnd_559011 := by exact prefixLift 559011
  have htrace : WordTrace (prefixWord ++ tailWord_559011) baseStart_559011 baseEnd_559011 := by
    simpa [prefixWord, tailWord_559011, baseEnd_559011] using wordTrace_append hprefix tailTrace_559011
  have hstable : (prefixWord ++ tailWord_559011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559011).length < 2 ^ (prefixWord ++ tailWord_559011).sum := by decide
  have hdescent : baseEnd_559011 < baseStart_559011 := by decide
  rcases family_descends (prefixWord ++ tailWord_559011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559022 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_559022 : Nat := 118140960795 + 559022 * 2 ^ 59
def prefixEnd_559022 : Nat := 4983230072969 + 3 ^ 40 * 559022 * 2
def baseEnd_559022 : Nat := 95682327479272352518037

theorem tailTrace_559022 : CollatzResearch.WordTrace tailWord_559022 prefixEnd_559022 95682327479272352518037 := by
  unfold tailWord_559022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548650922595780275210915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13592804920510828134458213 2548650922595780275210915)
  ·
    refine ⟨3822976383893670412816373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548650922595780275210915 3822976383893670412816373)
    ·
      refine ⟨358404035990031601201535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3822976383893670412816373 358404035990031601201535)
      ·
        refine ⟨537606053985047401802303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358404035990031601201535 537606053985047401802303)
        ·
          refine ⟨806409080977571102703455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537606053985047401802303 806409080977571102703455)
          ·
            refine ⟨1209613621466356654055183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806409080977571102703455 1209613621466356654055183)
            ·
              refine ⟨1814420432199534981082775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209613621466356654055183 1814420432199534981082775)
              ·
                refine ⟨2721630648299302471624163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814420432199534981082775 2721630648299302471624163)
                ·
                  refine ⟨4082445972448953707436245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721630648299302471624163 4082445972448953707436245)
                  ·
                    refine ⟨95682327479272352518037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4082445972448953707436245 95682327479272352518037)
                    ·
                      rfl

theorem cell23_559022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_559022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559022 prefixEnd_559022 := by exact prefixLift 559022
  have htrace : WordTrace (prefixWord ++ tailWord_559022) baseStart_559022 baseEnd_559022 := by
    simpa [prefixWord, tailWord_559022, baseEnd_559022] using wordTrace_append hprefix tailTrace_559022
  have hstable : (prefixWord ++ tailWord_559022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559022).length < 2 ^ (prefixWord ++ tailWord_559022).sum := by decide
  have hdescent : baseEnd_559022 < baseStart_559022 := by decide
  rcases family_descends (prefixWord ++ tailWord_559022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559025 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_559025 : Nat := 118140960795 + 559025 * 2 ^ 59
def prefixEnd_559025 : Nat := 4983230072969 + 3 ^ 40 * 559025 * 2
def baseEnd_559025 : Nat := 287048522879780545816597

theorem tailTrace_559025 : CollatzResearch.WordTrace tailWord_559025 prefixEnd_559025 287048522879780545816597 := by
  unfold tailWord_559025
  simp only [CollatzResearch.WordTrace]
  refine ⟨20389316799755373714046529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13592877866503582476031019 20389316799755373714046529)
  ·
    refine ⟨15291987599816530285534897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20389316799755373714046529 15291987599816530285534897)
    ·
      refine ⟨11468990699862397714151173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15291987599816530285534897 11468990699862397714151173)
      ·
        refine ⟨2150435756224199571403345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11468990699862397714151173 2150435756224199571403345)
        ·
          refine ⟨1612826817168149678552509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150435756224199571403345 1612826817168149678552509)
          ·
            refine ⟨604810056438056129457191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1612826817168149678552509 604810056438056129457191)
            ·
              refine ⟨907215084657084194185787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604810056438056129457191 907215084657084194185787)
              ·
                refine ⟨1360822626985626291278681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907215084657084194185787 1360822626985626291278681)
                ·
                  refine ⟨1020616970239219718459011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360822626985626291278681 1020616970239219718459011)
                  ·
                    refine ⟨1530925455358829577688517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1020616970239219718459011 1530925455358829577688517)
                    ·
                      refine ⟨287048522879780545816597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1530925455358829577688517 287048522879780545816597)
                      ·
                        rfl

theorem cell23_559025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_559025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559025 prefixEnd_559025 := by exact prefixLift 559025
  have htrace : WordTrace (prefixWord ++ tailWord_559025) baseStart_559025 baseEnd_559025 := by
    simpa [prefixWord, tailWord_559025, baseEnd_559025] using wordTrace_append hprefix tailTrace_559025
  have hstable : (prefixWord ++ tailWord_559025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559025).length < 2 ^ (prefixWord ++ tailWord_559025).sum := by decide
  have hdescent : baseEnd_559025 < baseStart_559025 := by decide
  rcases family_descends (prefixWord ++ tailWord_559025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559048 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 6]
def baseStart_559048 : Nat := 118140960795 + 559048 * 2 ^ 59
def prefixEnd_559048 : Nat := 4983230072969 + 3 ^ 40 * 559048 * 2
def baseEnd_559048 : Nat := 31895592548314883980999

theorem tailTrace_559048 : CollatzResearch.WordTrace tailWord_559048 prefixEnd_559048 31895592548314883980999 := by
  unfold tailWord_559048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195077839336024321066899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13593437119114699094755865 10195077839336024321066899)
  ·
    refine ⟨15292616759004036481600349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10195077839336024321066899 15292616759004036481600349)
    ·
      refine ⟨5734731284626513680600131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15292616759004036481600349 5734731284626513680600131)
      ·
        refine ⟨8602096926939770520900197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734731284626513680600131 8602096926939770520900197)
        ·
          refine ⟨1612893173801206972668787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8602096926939770520900197 1612893173801206972668787)
          ·
            refine ⟨2419339760701810459003181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612893173801206972668787 2419339760701810459003181)
            ·
              refine ⟨907252410263178922126193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2419339760701810459003181 907252410263178922126193)
              ·
                refine ⟨680439307697384191594645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907252410263178922126193 680439307697384191594645)
                ·
                  refine ⟨31895592548314883980999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 680439307697384191594645 31895592548314883980999)
                  ·
                    rfl

theorem cell23_559048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_559048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559048 prefixEnd_559048 := by exact prefixLift 559048
  have htrace : WordTrace (prefixWord ++ tailWord_559048) baseStart_559048 baseEnd_559048 := by
    simpa [prefixWord, tailWord_559048, baseEnd_559048] using wordTrace_append hprefix tailTrace_559048
  have hstable : (prefixWord ++ tailWord_559048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559048).length < 2 ^ (prefixWord ++ tailWord_559048).sum := by decide
  have hdescent : baseEnd_559048 < baseStart_559048 := by decide
  rcases family_descends (prefixWord ++ tailWord_559048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559065 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 6]
def baseStart_559065 : Nat := 118140960795 + 559065 * 2 ^ 59
def prefixEnd_559065 : Nat := 4983230072969 + 3 ^ 40 * 559065 * 2
def baseEnd_559065 : Nat := 31896562456217821035157

theorem tailTrace_559065 : CollatzResearch.WordTrace tailWord_559065 prefixEnd_559065 31896562456217821035157 := by
  unfold tailWord_559065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20390775719610460545502649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13593850479740307030335099 20390775719610460545502649)
  ·
    refine ⟨15293081789707845409126987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20390775719610460545502649 15293081789707845409126987)
    ·
      refine ⟨22939622684561768113690481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15293081789707845409126987 22939622684561768113690481)
      ·
        refine ⟨17204717013421326085267861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22939622684561768113690481 17204717013421326085267861)
        ·
          refine ⟨806471110004124660246931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17204717013421326085267861 806471110004124660246931)
          ·
            refine ⟨1209706665006186990370397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806471110004124660246931 1209706665006186990370397)
            ·
              refine ⟨453639999377320121388899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209706665006186990370397 453639999377320121388899)
              ·
                refine ⟨680459999065980182083349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453639999377320121388899 680459999065980182083349)
                ·
                  refine ⟨31896562456217821035157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 680459999065980182083349 31896562456217821035157)
                  ·
                    rfl

theorem cell23_559065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_559065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559065 prefixEnd_559065 := by exact prefixLift 559065
  have htrace : WordTrace (prefixWord ++ tailWord_559065) baseStart_559065 baseEnd_559065 := by
    simpa [prefixWord, tailWord_559065, baseEnd_559065] using wordTrace_append hprefix tailTrace_559065
  have hstable : (prefixWord ++ tailWord_559065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559065).length < 2 ^ (prefixWord ++ tailWord_559065).sum := by decide
  have hdescent : baseEnd_559065 < baseStart_559065 := by decide
  rcases family_descends (prefixWord ++ tailWord_559065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559075 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 3]
def baseStart_559075 : Nat := 118140960795 + 559075 * 2 ^ 59
def prefixEnd_559075 : Nat := 4983230072969 + 3 ^ 40 * 559075 * 2
def baseEnd_559075 : Nat := 287074196912505350191367

theorem tailTrace_559075 : CollatzResearch.WordTrace tailWord_559075 prefixEnd_559075 287074196912505350191367 := by
  unfold tailWord_559075
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391140449574232253366679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594093633049488168911119 20391140449574232253366679)
  ·
    refine ⟨30586710674361348380050019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20391140449574232253366679 30586710674361348380050019)
    ·
      refine ⟨45880066011542022570075029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30586710674361348380050019 45880066011542022570075029)
      ·
        refine ⟨2150628094291032307972267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45880066011542022570075029 2150628094291032307972267)
        ·
          refine ⟨3225942141436548461958401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150628094291032307972267 3225942141436548461958401)
          ·
            refine ⟨2419456606077411346468801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225942141436548461958401 2419456606077411346468801)
            ·
              refine ⟨1814592454558058509851601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419456606077411346468801 1814592454558058509851601)
              ·
                refine ⟨1360944340918543882388701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814592454558058509851601 1360944340918543882388701)
                ·
                  refine ⟨510354127844453955895763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1360944340918543882388701 510354127844453955895763)
                  ·
                    refine ⟨765531191766680933843645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510354127844453955895763 765531191766680933843645)
                    ·
                      refine ⟨287074196912505350191367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765531191766680933843645 287074196912505350191367)
                      ·
                        rfl

theorem cell23_559075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_559075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559075 prefixEnd_559075 := by exact prefixLift 559075
  have htrace : WordTrace (prefixWord ++ tailWord_559075) baseStart_559075 baseEnd_559075 := by
    simpa [prefixWord, tailWord_559075, baseEnd_559075] using wordTrace_append hprefix tailTrace_559075
  have hstable : (prefixWord ++ tailWord_559075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559075).length < 2 ^ (prefixWord ++ tailWord_559075).sum := by decide
  have hdescent : baseEnd_559075 < baseStart_559075 := by decide
  rcases family_descends (prefixWord ++ tailWord_559075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559091 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 6]
def baseStart_559091 : Nat := 118140960795 + 559091 * 2 ^ 59
def prefixEnd_559091 : Nat := 4983230072969 + 3 ^ 40 * 559091 * 2
def baseEnd_559091 : Nat := 95694137534325762530431

theorem tailTrace_559091 : CollatzResearch.WordTrace tailWord_559091 prefixEnd_559091 95694137534325762530431 := by
  unfold tailWord_559091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391724017516266985949127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594482678344177990632751 20391724017516266985949127)
  ·
    refine ⟨30587586026274400478923691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20391724017516266985949127 30587586026274400478923691)
    ·
      refine ⟨45881379039411600718385537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30587586026274400478923691 45881379039411600718385537)
      ·
        refine ⟨34411034279558700538789153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45881379039411600718385537 34411034279558700538789153)
        ·
          refine ⟨25808275709669025404091865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34411034279558700538789153 25808275709669025404091865)
          ·
            refine ⟨19356206782251769053068899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25808275709669025404091865 19356206782251769053068899)
            ·
              refine ⟨29034310173377653579603349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19356206782251769053068899 29034310173377653579603349)
              ·
                refine ⟨1360983289377077511543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29034310173377653579603349 1360983289377077511543907)
                ·
                  refine ⟨2041474934065616267315861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360983289377077511543907 2041474934065616267315861)
                  ·
                    refine ⟨95694137534325762530431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2041474934065616267315861 95694137534325762530431)
                    ·
                      rfl

theorem cell23_559091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_559091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559091 prefixEnd_559091 := by exact prefixLift 559091
  have htrace : WordTrace (prefixWord ++ tailWord_559091) baseStart_559091 baseEnd_559091 := by
    simpa [prefixWord, tailWord_559091, baseEnd_559091] using wordTrace_append hprefix tailTrace_559091
  have hstable : (prefixWord ++ tailWord_559091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559091).length < 2 ^ (prefixWord ++ tailWord_559091).sum := by decide
  have hdescent : baseEnd_559091 < baseStart_559091 := by decide
  rcases family_descends (prefixWord ++ tailWord_559091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559102 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_559102 : Nat := 118140960795 + 559102 * 2 ^ 59
def prefixEnd_559102 : Nat := 4983230072969 + 3 ^ 40 * 559102 * 2
def baseEnd_559102 : Nat := 287088060890176744553743

theorem tailTrace_559102 : CollatzResearch.WordTrace tailWord_559102 prefixEnd_559102 287088060890176744553743 := by
  unfold tailWord_559102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549015652559551983074945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13594750146984277243066373 2549015652559551983074945)
  ·
    refine ⟨1911761739419663987306209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2549015652559551983074945 1911761739419663987306209)
    ·
      refine ⟨1433821304564747990479657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911761739419663987306209 1433821304564747990479657)
      ·
        refine ⟨1075365978423560992859743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433821304564747990479657 1075365978423560992859743)
        ·
          refine ⟨1613048967635341489289615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075365978423560992859743 1613048967635341489289615)
          ·
            refine ⟨2419573451453012233934423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613048967635341489289615 2419573451453012233934423)
            ·
              refine ⟨3629360177179518350901635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419573451453012233934423 3629360177179518350901635)
              ·
                refine ⟨5444040265769277526352453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629360177179518350901635 5444040265769277526352453)
                ·
                  refine ⟨1020757549831739536191085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5444040265769277526352453 1020757549831739536191085)
                  ·
                    refine ⟨382784081186902326071657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020757549831739536191085 382784081186902326071657)
                    ·
                      refine ⟨287088060890176744553743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382784081186902326071657 287088060890176744553743)
                      ·
                        rfl

theorem cell23_559102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_559102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559102 prefixEnd_559102 := by exact prefixLift 559102
  have htrace : WordTrace (prefixWord ++ tailWord_559102) baseStart_559102 baseEnd_559102 := by
    simpa [prefixWord, tailWord_559102, baseEnd_559102] using wordTrace_append hprefix tailTrace_559102
  have hstable : (prefixWord ++ tailWord_559102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559102).length < 2 ^ (prefixWord ++ tailWord_559102).sum := by decide
  have hdescent : baseEnd_559102 < baseStart_559102 := by decide
  rcases family_descends (prefixWord ++ tailWord_559102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559109 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_559109 : Nat := 118140960795 + 559109 * 2 ^ 59
def prefixEnd_559109 : Nat := 4983230072969 + 3 ^ 40 * 559109 * 2
def baseEnd_559109 : Nat := 287091655254758217166211

theorem tailTrace_559109 : CollatzResearch.WordTrace tailWord_559109 prefixEnd_559109 287091655254758217166211 := by
  unfold tailWord_559109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392380531451056060104381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594920354300704040069587 20392380531451056060104381)
  ·
    refine ⟨7647142699294146022539143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20392380531451056060104381 7647142699294146022539143)
    ·
      refine ⟨11470714048941219033808715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647142699294146022539143 11470714048941219033808715)
      ·
        refine ⟨17206071073411828550713073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11470714048941219033808715 17206071073411828550713073)
        ·
          refine ⟨12904553305058871413034805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17206071073411828550713073 12904553305058871413034805)
          ·
            refine ⟨1209801872349269194972013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12904553305058871413034805 1209801872349269194972013)
            ·
              refine ⟨453675702130975948114505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209801872349269194972013 453675702130975948114505)
              ·
                refine ⟨340256776598231961085879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453675702130975948114505 340256776598231961085879)
                ·
                  refine ⟨510385164897347941628819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340256776598231961085879 510385164897347941628819)
                  ·
                    refine ⟨765577747346021912443229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510385164897347941628819 765577747346021912443229)
                    ·
                      refine ⟨287091655254758217166211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765577747346021912443229 287091655254758217166211)
                      ·
                        rfl

theorem cell23_559109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_559109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559109 prefixEnd_559109 := by exact prefixLift 559109
  have htrace : WordTrace (prefixWord ++ tailWord_559109) baseStart_559109 baseEnd_559109 := by
    simpa [prefixWord, tailWord_559109, baseEnd_559109] using wordTrace_append hprefix tailTrace_559109
  have hstable : (prefixWord ++ tailWord_559109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559109).length < 2 ^ (prefixWord ++ tailWord_559109).sum := by decide
  have hdescent : baseEnd_559109 < baseStart_559109 := by decide
  rcases family_descends (prefixWord ++ tailWord_559109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559118 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_559118 : Nat := 118140960795 + 559118 * 2 ^ 59
def prefixEnd_559118 : Nat := 4983230072969 + 3 ^ 40 * 559118 * 2
def baseEnd_559118 : Nat := 287096276580648681953669

theorem tailTrace_559118 : CollatzResearch.WordTrace tailWord_559118 prefixEnd_559118 287096276580648681953669 := by
  unfold tailWord_559118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549088598552306324647751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13595139192278967064788005 2549088598552306324647751)
  ·
    refine ⟨3823632897828459486971627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549088598552306324647751 3823632897828459486971627)
    ·
      refine ⟨5735449346742689230457441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823632897828459486971627 5735449346742689230457441)
      ·
        refine ⟨4301587010057016922843081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5735449346742689230457441 4301587010057016922843081)
        ·
          refine ⟨3226190257542762692132311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301587010057016922843081 3226190257542762692132311)
          ·
            refine ⟨4839285386314144038198467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226190257542762692132311 4839285386314144038198467)
            ·
              refine ⟨7258928079471216057297701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839285386314144038198467 7258928079471216057297701)
              ·
                refine ⟨1361049014900853010743319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7258928079471216057297701 1361049014900853010743319)
                ·
                  refine ⟨2041573522351279516114979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361049014900853010743319 2041573522351279516114979)
                  ·
                    refine ⟨3062360283526919274172469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041573522351279516114979 3062360283526919274172469)
                    ·
                      refine ⟨287096276580648681953669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3062360283526919274172469 287096276580648681953669)
                      ·
                        rfl

theorem cell23_559118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_559118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559118 prefixEnd_559118 := by exact prefixLift 559118
  have htrace : WordTrace (prefixWord ++ tailWord_559118) baseStart_559118 baseEnd_559118 := by
    simpa [prefixWord, tailWord_559118, baseEnd_559118] using wordTrace_append hprefix tailTrace_559118
  have hstable : (prefixWord ++ tailWord_559118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559118).length < 2 ^ (prefixWord ++ tailWord_559118).sum := by decide
  have hdescent : baseEnd_559118 < baseStart_559118 := by decide
  rcases family_descends (prefixWord ++ tailWord_559118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559128 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_559128 : Nat := 118140960795 + 559128 * 2 ^ 59
def prefixEnd_559128 : Nat := 4983230072969 + 3 ^ 40 * 559128 * 2
def baseEnd_559128 : Nat := 287101411387193642828623

theorem tailTrace_559128 : CollatzResearch.WordTrace tailWord_559128 prefixEnd_559128 287101411387193642828623 := by
  unfold tailWord_559128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196536759191111152523019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13595382345588148203364025 10196536759191111152523019)
  ·
    refine ⟨15294805138786666728784529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10196536759191111152523019 15294805138786666728784529)
    ·
      refine ⟨11471103854090000046588397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15294805138786666728784529 11471103854090000046588397)
      ·
        refine ⟨4301663945283750017470649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11471103854090000046588397 4301663945283750017470649)
        ·
          refine ⟨3226247958962812513102987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301663945283750017470649 3226247958962812513102987)
          ·
            refine ⟨4839371938444218769654481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226247958962812513102987 4839371938444218769654481)
            ·
              refine ⟨3629528953833164077240861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839371938444218769654481 3629528953833164077240861)
              ·
                refine ⟨1361073357687436528965323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3629528953833164077240861 1361073357687436528965323)
                ·
                  refine ⟨2041610036531154793447985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361073357687436528965323 2041610036531154793447985)
                  ·
                    refine ⟨1531207527398366095085989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041610036531154793447985 1531207527398366095085989)
                    ·
                      refine ⟨287101411387193642828623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1531207527398366095085989 287101411387193642828623)
                      ·
                        rfl

theorem cell23_559128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_559128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559128 prefixEnd_559128 := by exact prefixLift 559128
  have htrace : WordTrace (prefixWord ++ tailWord_559128) baseStart_559128 baseEnd_559128 := by
    simpa [prefixWord, tailWord_559128, baseEnd_559128] using wordTrace_append hprefix tailTrace_559128
  have hstable : (prefixWord ++ tailWord_559128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559128).length < 2 ^ (prefixWord ++ tailWord_559128).sum := by decide
  have hdescent : baseEnd_559128 < baseStart_559128 := by decide
  rcases family_descends (prefixWord ++ tailWord_559128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559132 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_559132 : Nat := 118140960795 + 559132 * 2 ^ 59
def prefixEnd_559132 : Nat := 4983230072969 + 3 ^ 40 * 559132 * 2
def baseEnd_559132 : Nat := 287103465309811627178605

theorem tailTrace_559132 : CollatzResearch.WordTrace tailWord_559132 prefixEnd_559132 287103465309811627178605 := by
  unfold tailWord_559132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196609705183865494095825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13595479606911820658794433 10196609705183865494095825)
  ·
    refine ⟨7647457278887899120571869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10196609705183865494095825 7647457278887899120571869)
    ·
      refine ⟨2867796479582962170214451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7647457278887899120571869 2867796479582962170214451)
      ·
        refine ⟨4301694719374443255321677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867796479582962170214451 4301694719374443255321677)
        ·
          refine ⟨1613135519765416220745629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4301694719374443255321677 1613135519765416220745629)
          ·
            refine ⟨604925819912031082779611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1613135519765416220745629 604925819912031082779611)
            ·
              refine ⟨907388729868046624169417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604925819912031082779611 907388729868046624169417)
              ·
                refine ⟨680541547401034968127063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907388729868046624169417 680541547401034968127063)
                ·
                  refine ⟨1020812321101552452190595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680541547401034968127063 1020812321101552452190595)
                  ·
                    refine ⟨1531218481652328678285893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1020812321101552452190595 1531218481652328678285893)
                    ·
                      refine ⟨287103465309811627178605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1531218481652328678285893 287103465309811627178605)
                      ·
                        rfl

theorem cell23_559132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_559132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559132 prefixEnd_559132 := by exact prefixLift 559132
  have htrace : WordTrace (prefixWord ++ tailWord_559132) baseStart_559132 baseEnd_559132 := by
    simpa [prefixWord, tailWord_559132, baseEnd_559132] using wordTrace_append hprefix tailTrace_559132
  have hstable : (prefixWord ++ tailWord_559132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559132).length < 2 ^ (prefixWord ++ tailWord_559132).sum := by decide
  have hdescent : baseEnd_559132 < baseStart_559132 := by decide
  rcases family_descends (prefixWord ++ tailWord_559132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559152 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3]
def baseStart_559152 : Nat := 118140960795 + 559152 * 2 ^ 59
def prefixEnd_559152 : Nat := 4983230072969 + 3 ^ 40 * 559152 * 2
def baseEnd_559152 : Nat := 287113734922901548928513

theorem tailTrace_559152 : CollatzResearch.WordTrace tailWord_559152 prefixEnd_559152 287113734922901548928513 := by
  unfold tailWord_559152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196974435147637201959855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13595965913530182935946473 10196974435147637201959855)
  ·
    refine ⟨15295461652721455802939783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10196974435147637201959855 15295461652721455802939783)
    ·
      refine ⟨22943192479082183704409675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15295461652721455802939783 22943192479082183704409675)
      ·
        refine ⟨34414788718623275556614513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22943192479082183704409675 34414788718623275556614513)
        ·
          refine ⟨25811091538967456667460885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34414788718623275556614513 25811091538967456667460885)
          ·
            refine ⟨1209894915889099531287229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25811091538967456667460885 1209894915889099531287229)
            ·
              refine ⟨453710593458412324232711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209894915889099531287229 453710593458412324232711)
              ·
                refine ⟨680565890187618486349067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453710593458412324232711 680565890187618486349067)
                ·
                  refine ⟨1020848835281427729523601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680565890187618486349067 1020848835281427729523601)
                  ·
                    refine ⟨765636626461070797142701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1020848835281427729523601 765636626461070797142701)
                    ·
                      refine ⟨287113734922901548928513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765636626461070797142701 287113734922901548928513)
                      ·
                        rfl

theorem cell23_559152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3].length) (baseStart_559152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559152 prefixEnd_559152 := by exact prefixLift 559152
  have htrace : WordTrace (prefixWord ++ tailWord_559152) baseStart_559152 baseEnd_559152 := by
    simpa [prefixWord, tailWord_559152, baseEnd_559152] using wordTrace_append hprefix tailTrace_559152
  have hstable : (prefixWord ++ tailWord_559152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559152).length < 2 ^ (prefixWord ++ tailWord_559152).sum := by decide
  have hdescent : baseEnd_559152 < baseStart_559152 := by decide
  rcases family_descends (prefixWord ++ tailWord_559152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559175 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_559175 : Nat := 118140960795 + 559175 * 2 ^ 59
def prefixEnd_559175 : Nat := 4983230072969 + 3 ^ 40 * 559175 * 2
def baseEnd_559175 : Nat := 287125544977954958940907

theorem tailTrace_559175 : CollatzResearch.WordTrace tailWord_559175 prefixEnd_559175 287125544977954958940907 := by
  unfold tailWord_559175
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394787749211949332006979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13596525166141299554671319 20394787749211949332006979)
  ·
    refine ⟨30592181623817923998010469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20394787749211949332006979 30592181623817923998010469)
    ·
      refine ⟨5736034054465860749626963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30592181623817923998010469 5736034054465860749626963)
      ·
        refine ⟨8604051081698791124440445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736034054465860749626963 8604051081698791124440445)
        ·
          refine ⟨3226519155637046671665167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8604051081698791124440445 3226519155637046671665167)
          ·
            refine ⟨4839778733455570007497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226519155637046671665167 4839778733455570007497751)
            ·
              refine ⟨7259668100183355011246627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839778733455570007497751 7259668100183355011246627)
              ·
                refine ⟨10889502150275032516869941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259668100183355011246627 10889502150275032516869941)
                ·
                  refine ⟨1020890826588284298456557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10889502150275032516869941 1020890826588284298456557)
                  ·
                    refine ⟨382834059970606611921209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020890826588284298456557 382834059970606611921209)
                    ·
                      refine ⟨287125544977954958940907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382834059970606611921209 287125544977954958940907)
                      ·
                        rfl

theorem cell23_559175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_559175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559175 prefixEnd_559175 := by exact prefixLift 559175
  have htrace : WordTrace (prefixWord ++ tailWord_559175) baseStart_559175 baseEnd_559175 := by
    simpa [prefixWord, tailWord_559175, baseEnd_559175] using wordTrace_append hprefix tailTrace_559175
  have hstable : (prefixWord ++ tailWord_559175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559175).length < 2 ^ (prefixWord ++ tailWord_559175).sum := by decide
  have hdescent : baseEnd_559175 < baseStart_559175 := by decide
  rcases family_descends (prefixWord ++ tailWord_559175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559182 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_559182 : Nat := 118140960795 + 559182 * 2 ^ 59
def prefixEnd_559182 : Nat := 4983230072969 + 3 ^ 40 * 559182 * 2
def baseEnd_559182 : Nat := 287129139342536431553375

theorem tailTrace_559182 : CollatzResearch.WordTrace tailWord_559182 prefixEnd_559182 287129139342536431553375 := by
  unfold tailWord_559182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549380382523323690938975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13596695373457726351674533 2549380382523323690938975)
  ·
    refine ⟨3824070573784985536408463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549380382523323690938975 3824070573784985536408463)
    ·
      refine ⟨5736105860677478304612695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824070573784985536408463 5736105860677478304612695)
      ·
        refine ⟨8604158791016217456919043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736105860677478304612695 8604158791016217456919043)
        ·
          refine ⟨12906238186524326185378565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604158791016217456919043 12906238186524326185378565)
          ·
            refine ⟨2419919659973311159758481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12906238186524326185378565 2419919659973311159758481)
            ·
              refine ⟨1814939744979983369818861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419919659973311159758481 1814939744979983369818861)
              ·
                refine ⟨680602404367493763682073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814939744979983369818861 680602404367493763682073)
                ·
                  refine ⟨510451803275620322761555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680602404367493763682073 510451803275620322761555)
                  ·
                    refine ⟨765677704913430484142333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510451803275620322761555 765677704913430484142333)
                    ·
                      refine ⟨287129139342536431553375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765677704913430484142333 287129139342536431553375)
                      ·
                        rfl

theorem cell23_559182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_559182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559182 prefixEnd_559182 := by exact prefixLift 559182
  have htrace : WordTrace (prefixWord ++ tailWord_559182) baseStart_559182 baseEnd_559182 := by
    simpa [prefixWord, tailWord_559182, baseEnd_559182] using wordTrace_append hprefix tailTrace_559182
  have hstable : (prefixWord ++ tailWord_559182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559182).length < 2 ^ (prefixWord ++ tailWord_559182).sum := by decide
  have hdescent : baseEnd_559182 < baseStart_559182 := by decide
  rcases family_descends (prefixWord ++ tailWord_559182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559188 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_559188 : Nat := 118140960795 + 559188 * 2 ^ 59
def prefixEnd_559188 : Nat := 4983230072969 + 3 ^ 40 * 559188 * 2
def baseEnd_559188 : Nat := 287132220226463408078347

theorem tailTrace_559188 : CollatzResearch.WordTrace tailWord_559188 prefixEnd_559188 287132220226463408078347 := by
  unfold tailWord_559188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197630949082426276115109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13596841265443235034820145 10197630949082426276115109)
  ·
    refine ⟨1912055802952954926771583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10197630949082426276115109 1912055802952954926771583)
    ·
      refine ⟨2868083704429432390157375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912055802952954926771583 2868083704429432390157375)
      ·
        refine ⟨4302125556644148585236063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868083704429432390157375 4302125556644148585236063)
        ·
          refine ⟨6453188334966222877854095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302125556644148585236063 6453188334966222877854095)
          ·
            refine ⟨9679782502449334316781143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453188334966222877854095 9679782502449334316781143)
            ·
              refine ⟨14519673753674001475171715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679782502449334316781143 14519673753674001475171715)
              ·
                refine ⟨21779510630511002212757573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14519673753674001475171715 21779510630511002212757573)
                ·
                  refine ⟨4083658243220812914892045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21779510630511002212757573 4083658243220812914892045)
                  ·
                    refine ⟨1531371841207804843084517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4083658243220812914892045 1531371841207804843084517)
                    ·
                      refine ⟨287132220226463408078347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1531371841207804843084517 287132220226463408078347)
                      ·
                        rfl

theorem cell23_559188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_559188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559188 prefixEnd_559188 := by exact prefixLift 559188
  have htrace : WordTrace (prefixWord ++ tailWord_559188) baseStart_559188 baseEnd_559188 := by
    simpa [prefixWord, tailWord_559188, baseEnd_559188] using wordTrace_append hprefix tailTrace_559188
  have hstable : (prefixWord ++ tailWord_559188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559188).length < 2 ^ (prefixWord ++ tailWord_559188).sum := by decide
  have hdescent : baseEnd_559188 < baseStart_559188 := by decide
  rcases family_descends (prefixWord ++ tailWord_559188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559228 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 7]
def baseStart_559228 : Nat := 118140960795 + 559228 * 2 ^ 59
def prefixEnd_559228 : Nat := 4983230072969 + 3 ^ 40 * 559228 * 2
def baseEnd_559228 : Nat := 31905862161404805730907

theorem tailTrace_559228 : CollatzResearch.WordTrace tailWord_559228 prefixEnd_559228 31905862161404805730907 := by
  unfold tailWord_559228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198360409009969691843169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13597813878679959589124225 10198360409009969691843169)
  ·
    refine ⟨7648770306757477268882377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10198360409009969691843169 7648770306757477268882377)
    ·
      refine ⟨5736577730068107951661783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7648770306757477268882377 5736577730068107951661783)
      ·
        refine ⟨8604866595102161927492675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736577730068107951661783 8604866595102161927492675)
        ·
          refine ⟨12907299892653242891239013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604866595102161927492675 12907299892653242891239013)
          ·
            refine ⟨2420118729872483042107315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12907299892653242891239013 2420118729872483042107315)
            ·
              refine ⟨3630178094808724563160973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420118729872483042107315 3630178094808724563160973)
              ·
                refine ⟨1361316785553271711185365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630178094808724563160973 1361316785553271711185365)
                ·
                  refine ⟨31905862161404805730907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1361316785553271711185365 31905862161404805730907)
                  ·
                    rfl

theorem cell23_559228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_559228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559228 prefixEnd_559228 := by exact prefixLift 559228
  have htrace : WordTrace (prefixWord ++ tailWord_559228) baseStart_559228 baseEnd_559228 := by
    simpa [prefixWord, tailWord_559228, baseEnd_559228] using wordTrace_append hprefix tailTrace_559228
  have hstable : (prefixWord ++ tailWord_559228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559228).length < 2 ^ (prefixWord ++ tailWord_559228).sum := by decide
  have hdescent : baseEnd_559228 < baseStart_559228 := by decide
  rcases family_descends (prefixWord ++ tailWord_559228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559295 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 6, 2]
def baseStart_559295 : Nat := 118140960795 + 559295 * 2 ^ 59
def prefixEnd_559295 : Nat := 4983230072969 + 3 ^ 40 * 559295 * 2
def baseEnd_559295 : Nat := 287187162656494489440355

theorem tailTrace_559295 : CollatzResearch.WordTrace tailWord_559295 prefixEnd_559295 287187162656494489440355 := by
  unfold tailWord_559295
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399164508777209826375339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13599443005851473217583559 20399164508777209826375339)
  ·
    refine ⟨30598746763165814739563009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20399164508777209826375339 30598746763165814739563009)
    ·
      refine ⟨22949060072374361054672257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30598746763165814739563009 22949060072374361054672257)
      ·
        refine ⟨17211795054280770791004193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22949060072374361054672257 17211795054280770791004193)
        ·
          refine ⟨12908846290710578093253145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17211795054280770791004193 12908846290710578093253145)
          ·
            refine ⟨9681634718032933569939859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12908846290710578093253145 9681634718032933569939859)
            ·
              refine ⟨14522452077049400354909789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9681634718032933569939859 14522452077049400354909789)
              ·
                refine ⟨5445919528893525133091171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14522452077049400354909789 5445919528893525133091171)
                ·
                  refine ⟨8168879293340287699636757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445919528893525133091171 8168879293340287699636757)
                  ·
                    refine ⟨382916216875325985920473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8168879293340287699636757 382916216875325985920473)
                    ·
                      refine ⟨287187162656494489440355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382916216875325985920473 287187162656494489440355)
                      ·
                        rfl

theorem cell23_559295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_559295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559295 prefixEnd_559295 := by exact prefixLift 559295
  have htrace : WordTrace (prefixWord ++ tailWord_559295) baseStart_559295 baseEnd_559295 := by
    simpa [prefixWord, tailWord_559295, baseEnd_559295] using wordTrace_append hprefix tailTrace_559295
  have hstable : (prefixWord ++ tailWord_559295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559295).length < 2 ^ (prefixWord ++ tailWord_559295).sum := by decide
  have hdescent : baseEnd_559295 < baseStart_559295 := by decide
  rcases family_descends (prefixWord ++ tailWord_559295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559330 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_559330 : Nat := 118140960795 + 559330 * 2 ^ 59
def prefixEnd_559330 : Nat := 4983230072969 + 3 ^ 40 * 559330 * 2
def baseEnd_559330 : Nat := 31911681608822428055855

theorem tailTrace_559330 : CollatzResearch.WordTrace tailWord_559330 prefixEnd_559330 31911681608822428055855 := by
  unfold tailWord_559330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100110265912602700974861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13600294042433607202599629 5100110265912602700974861)
  ·
    refine ⟨1912541349717226012865573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5100110265912602700974861 1912541349717226012865573)
    ·
      refine ⟨358601503071979877412295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1912541349717226012865573 358601503071979877412295)
      ·
        refine ⟨537902254607969816118443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358601503071979877412295 537902254607969816118443)
        ·
          refine ⟨806853381911954724177665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537902254607969816118443 806853381911954724177665)
          ·
            refine ⟨605140036433966043133249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806853381911954724177665 605140036433966043133249)
            ·
              refine ⟨453855027325474532349937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605140036433966043133249 453855027325474532349937)
              ·
                refine ⟨340391270494105899262453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453855027325474532349937 340391270494105899262453)
                ·
                  refine ⟨31911681608822428055855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340391270494105899262453 31911681608822428055855)
                  ·
                    rfl

theorem cell23_559330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_559330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559330 prefixEnd_559330 := by exact prefixLift 559330
  have htrace : WordTrace (prefixWord ++ tailWord_559330) baseStart_559330 baseEnd_559330 := by
    simpa [prefixWord, tailWord_559330, baseEnd_559330] using wordTrace_append hprefix tailTrace_559330
  have hstable : (prefixWord ++ tailWord_559330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559330).length < 2 ^ (prefixWord ++ tailWord_559330).sum := by decide
  have hdescent : baseEnd_559330 < baseStart_559330 := by decide
  rcases family_descends (prefixWord ++ tailWord_559330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559372 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_559372 : Nat := 118140960795 + 559372 * 2 ^ 59
def prefixEnd_559372 : Nat := 4983230072969 + 3 ^ 40 * 559372 * 2
def baseEnd_559372 : Nat := 287226700666890688177501

theorem tailTrace_559372 : CollatzResearch.WordTrace tailWord_559372 prefixEnd_559372 287226700666890688177501 := by
  unfold tailWord_559372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200986464749125988464185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13601315286332167984618913 10200986464749125988464185)
  ·
    refine ⟨7650739848561844491348139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10200986464749125988464185 7650739848561844491348139)
    ·
      refine ⟨11476109772842766737022209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650739848561844491348139 11476109772842766737022209)
      ·
        refine ⟨8607082329632075052766657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11476109772842766737022209 8607082329632075052766657)
        ·
          refine ⟨6455311747224056289574993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8607082329632075052766657 6455311747224056289574993)
          ·
            refine ⟨4841483810418042217181245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6455311747224056289574993 4841483810418042217181245)
            ·
              refine ⟨1815556428906765831442967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4841483810418042217181245 1815556428906765831442967)
              ·
                refine ⟨2723334643360148747164451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815556428906765831442967 2723334643360148747164451)
                ·
                  refine ⟨4085001965040223120746677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723334643360148747164451 4085001965040223120746677)
                  ·
                    refine ⟨382968934222520917570001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4085001965040223120746677 382968934222520917570001)
                    ·
                      refine ⟨287226700666890688177501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 382968934222520917570001 287226700666890688177501)
                      ·
                        rfl

theorem cell23_559372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_559372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559372 prefixEnd_559372 := by exact prefixLift 559372
  have htrace : WordTrace (prefixWord ++ tailWord_559372) baseStart_559372 baseEnd_559372 := by
    simpa [prefixWord, tailWord_559372, baseEnd_559372] using wordTrace_append hprefix tailTrace_559372
  have hstable : (prefixWord ++ tailWord_559372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559372).length < 2 ^ (prefixWord ++ tailWord_559372).sum := by decide
  have hdescent : baseEnd_559372 < baseStart_559372 := by decide
  rcases family_descends (prefixWord ++ tailWord_559372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559396 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_559396 : Nat := 118140960795 + 559396 * 2 ^ 59
def prefixEnd_559396 : Nat := 4983230072969 + 3 ^ 40 * 559396 * 2
def baseEnd_559396 : Nat := 287239024202598594277391

theorem tailTrace_559396 : CollatzResearch.WordTrace tailWord_559396 prefixEnd_559396 287239024202598594277391 := by
  unfold tailWord_559396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201424140705652037901021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13601898854274202717201361 10201424140705652037901021)
  ·
    refine ⟨3825534052764619514212883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10201424140705652037901021 3825534052764619514212883)
    ·
      refine ⟨5738301079146929271319325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3825534052764619514212883 5738301079146929271319325)
      ·
        refine ⟨2151862904680098476744747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5738301079146929271319325 2151862904680098476744747)
        ·
          refine ⟨3227794357020147715117121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151862904680098476744747 3227794357020147715117121)
          ·
            refine ⟨2420845767765110786337841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3227794357020147715117121 2420845767765110786337841)
            ·
              refine ⟨1815634325823833089753381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420845767765110786337841 1815634325823833089753381)
              ·
                refine ⟨340431436091968704328759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1815634325823833089753381 340431436091968704328759)
                ·
                  refine ⟨510647154137953056493139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340431436091968704328759 510647154137953056493139)
                  ·
                    refine ⟨765970731206929584739709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510647154137953056493139 765970731206929584739709)
                    ·
                      refine ⟨287239024202598594277391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 765970731206929584739709 287239024202598594277391)
                      ·
                        rfl

theorem cell23_559396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_559396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559396 prefixEnd_559396 := by exact prefixLift 559396
  have htrace : WordTrace (prefixWord ++ tailWord_559396) baseStart_559396 baseEnd_559396 := by
    simpa [prefixWord, tailWord_559396, baseEnd_559396] using wordTrace_append hprefix tailTrace_559396
  have hstable : (prefixWord ++ tailWord_559396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559396).length < 2 ^ (prefixWord ++ tailWord_559396).sum := by decide
  have hdescent : baseEnd_559396 < baseStart_559396 := by decide
  rcases family_descends (prefixWord ++ tailWord_559396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559475 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_559475 : Nat := 118140960795 + 559475 * 2 ^ 59
def prefixEnd_559475 : Nat := 4983230072969 + 3 ^ 40 * 559475 * 2
def baseEnd_559475 : Nat := 287279589174303785189527

theorem tailTrace_559475 : CollatzResearch.WordTrace tailWord_559475 prefixEnd_559475 287279589174303785189527 := by
  unfold tailWord_559475
  simp only [CollatzResearch.WordTrace]
  refine ⟨20405729648125100567927879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13603819765416733711951919 20405729648125100567927879)
  ·
    refine ⟨30608594472187650851891819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20405729648125100567927879 30608594472187650851891819)
    ·
      refine ⟨45912891708281476277837729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30608594472187650851891819 45912891708281476277837729)
      ·
        refine ⟨34434668781211107208378297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45912891708281476277837729 34434668781211107208378297)
        ·
          refine ⟨25826001585908330406283723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34434668781211107208378297 25826001585908330406283723)
          ·
            refine ⟨38739002378862495609425585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25826001585908330406283723 38739002378862495609425585)
            ·
              refine ⟨29054251784146871707069189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38739002378862495609425585 29054251784146871707069189)
              ·
                refine ⟨5447672209527538445075473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29054251784146871707069189 5447672209527538445075473)
                ·
                  refine ⟨4085754157145653833806605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5447672209527538445075473 4085754157145653833806605)
                  ·
                    refine ⟨1532157808929620187677477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4085754157145653833806605 1532157808929620187677477)
                    ·
                      refine ⟨287279589174303785189527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1532157808929620187677477 287279589174303785189527)
                      ·
                        rfl

theorem cell23_559475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_559475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559475 prefixEnd_559475 := by exact prefixLift 559475
  have htrace : WordTrace (prefixWord ++ tailWord_559475) baseStart_559475 baseEnd_559475 := by
    simpa [prefixWord, tailWord_559475, baseEnd_559475] using wordTrace_append hprefix tailTrace_559475
  have hstable : (prefixWord ++ tailWord_559475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559475).length < 2 ^ (prefixWord ++ tailWord_559475).sum := by decide
  have hdescent : baseEnd_559475 < baseStart_559475 := by decide
  rcases family_descends (prefixWord ++ tailWord_559475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559479 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_559479 : Nat := 118140960795 + 559479 * 2 ^ 59
def prefixEnd_559479 : Nat := 4983230072969 + 3 ^ 40 * 559479 * 2
def baseEnd_559479 : Nat := 287281643096921769539509

theorem tailTrace_559479 : CollatzResearch.WordTrace tailWord_559479 prefixEnd_559479 287281643096921769539509 := by
  unfold tailWord_559479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20405875540110609251073491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13603917026740406167382327 20405875540110609251073491)
  ·
    refine ⟨30608813310165913876610237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20405875540110609251073491 30608813310165913876610237)
    ·
      refine ⟨11478304991312217703728839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30608813310165913876610237 11478304991312217703728839)
      ·
        refine ⟨17217457486968326555593259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11478304991312217703728839 17217457486968326555593259)
        ·
          refine ⟨25826186230452489833389889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17217457486968326555593259 25826186230452489833389889)
          ·
            refine ⟨19369639672839367375042417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25826186230452489833389889 19369639672839367375042417)
            ·
              refine ⟨14527229754629525531281813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19369639672839367375042417 14527229754629525531281813)
              ·
                refine ⟨680963894748259009278835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14527229754629525531281813 680963894748259009278835)
                ·
                  refine ⟨1021445842122388513918253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680963894748259009278835 1021445842122388513918253)
                  ·
                    refine ⟨383042190795895692719345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1021445842122388513918253 383042190795895692719345)
                    ·
                      refine ⟨287281643096921769539509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383042190795895692719345 287281643096921769539509)
                      ·
                        rfl

theorem cell23_559479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_559479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559479 prefixEnd_559479 := by exact prefixLift 559479
  have htrace : WordTrace (prefixWord ++ tailWord_559479) baseStart_559479 baseEnd_559479 := by
    simpa [prefixWord, tailWord_559479, baseEnd_559479] using wordTrace_append hprefix tailTrace_559479
  have hstable : (prefixWord ++ tailWord_559479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559479).length < 2 ^ (prefixWord ++ tailWord_559479).sum := by decide
  have hdescent : baseEnd_559479 < baseStart_559479 := by decide
  rcases family_descends (prefixWord ++ tailWord_559479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559490 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_559490 : Nat := 118140960795 + 559490 * 2 ^ 59
def prefixEnd_559490 : Nat := 4983230072969 + 3 ^ 40 * 559490 * 2
def baseEnd_559490 : Nat := 287287291384121226501959

theorem tailTrace_559490 : CollatzResearch.WordTrace tailWord_559490 prefixEnd_559490 287287291384121226501959 := by
  unfold tailWord_559490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101569185767689532430981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13604184495380505419815949 5101569185767689532430981)
  ·
    refine ⟨956544222331441787330809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5101569185767689532430981 956544222331441787330809)
    ·
      refine ⟨717408166748581340498107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 956544222331441787330809 717408166748581340498107)
      ·
        refine ⟨1076112250122872010747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717408166748581340498107 1076112250122872010747161)
        ·
          refine ⟨807084187592154008060371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076112250122872010747161 807084187592154008060371)
          ·
            refine ⟨1210626281388231012090557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807084187592154008060371 1210626281388231012090557)
            ·
              refine ⟨453984855520586629533959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210626281388231012090557 453984855520586629533959)
              ·
                refine ⟨680977283280879944300939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453984855520586629533959 680977283280879944300939)
                ·
                  refine ⟨1021465924921319916451409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680977283280879944300939 1021465924921319916451409)
                  ·
                    refine ⟨766099443690989937338557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021465924921319916451409 766099443690989937338557)
                    ·
                      refine ⟨287287291384121226501959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 766099443690989937338557 287287291384121226501959)
                      ·
                        rfl

theorem cell23_559490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_559490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559490 prefixEnd_559490 := by exact prefixLift 559490
  have htrace : WordTrace (prefixWord ++ tailWord_559490) baseStart_559490 baseEnd_559490 := by
    simpa [prefixWord, tailWord_559490, baseEnd_559490] using wordTrace_append hprefix tailTrace_559490
  have hstable : (prefixWord ++ tailWord_559490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559490).length < 2 ^ (prefixWord ++ tailWord_559490).sum := by decide
  have hdescent : baseEnd_559490 < baseStart_559490 := by decide
  rcases family_descends (prefixWord ++ tailWord_559490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559510 : List Nat := [5, 3, 1, 2, 2, 1, 1, 8]
def baseStart_559510 : Nat := 118140960795 + 559510 * 2 ^ 59
def prefixEnd_559510 : Nat := 4983230072969 + 3 ^ 40 * 559510 * 2
def baseEnd_559510 : Nat := 10640650407304116601921

theorem tailTrace_559510 : CollatzResearch.WordTrace tailWord_559510 prefixEnd_559510 10640650407304116601921 := by
  unfold tailWord_559510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275437887687393846590749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13604670801998867696967989 1275437887687393846590749)
  ·
    refine ⟨478289207882772692471531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1275437887687393846590749 478289207882772692471531)
    ·
      refine ⟨717433811824159038707297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478289207882772692471531 717433811824159038707297)
      ·
        refine ⟨538075358868119279030473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717433811824159038707297 538075358868119279030473)
        ·
          refine ⟨403556519151089459272855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538075358868119279030473 403556519151089459272855)
          ·
            refine ⟨605334778726634188909283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403556519151089459272855 605334778726634188909283)
            ·
              refine ⟨908002168089951283363925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605334778726634188909283 908002168089951283363925)
              ·
                refine ⟨10640650407304116601921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 908002168089951283363925 10640650407304116601921)
                ·
                  rfl

theorem cell23_559510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_559510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559510 prefixEnd_559510 := by exact prefixLift 559510
  have htrace : WordTrace (prefixWord ++ tailWord_559510) baseStart_559510 baseEnd_559510 := by
    simpa [prefixWord, tailWord_559510, baseEnd_559510] using wordTrace_append hprefix tailTrace_559510
  have hstable : (prefixWord ++ tailWord_559510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559510).length < 2 ^ (prefixWord ++ tailWord_559510).sum := by decide
  have hdescent : baseEnd_559510 < baseStart_559510 := by decide
  rcases family_descends (prefixWord ++ tailWord_559510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559549 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 5]
def baseStart_559549 : Nat := 118140960795 + 559549 * 2 ^ 59
def prefixEnd_559549 : Nat := 4983230072969 + 3 ^ 40 * 559549 * 2
def baseEnd_559549 : Nat := 31924176304748499518243

theorem tailTrace_559549 : CollatzResearch.WordTrace tailWord_559549 prefixEnd_559549 31924176304748499518243 := by
  unfold tailWord_559549
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408428649857011206121701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13605619099904674137414467 20408428649857011206121701)
  ·
    refine ⟨3826580371848189601147819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20408428649857011206121701 3826580371848189601147819)
    ·
      refine ⟨5739870557772284401721729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3826580371848189601147819 5739870557772284401721729)
      ·
        refine ⟨4304902918329213301291297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5739870557772284401721729 4304902918329213301291297)
        ·
          refine ⟨3228677188746909975968473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304902918329213301291297 3228677188746909975968473)
          ·
            refine ⟨2421507891560182481976355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228677188746909975968473 2421507891560182481976355)
            ·
              refine ⟨3632261837340273722964533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421507891560182481976355 3632261837340273722964533)
              ·
                refine ⟨340524547250650661527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3632261837340273722964533 340524547250650661527925)
                ·
                  refine ⟨31924176304748499518243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340524547250650661527925 31924176304748499518243)
                  ·
                    rfl

theorem cell23_559549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_559549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559549 prefixEnd_559549 := by exact prefixLift 559549
  have htrace : WordTrace (prefixWord ++ tailWord_559549) baseStart_559549 baseEnd_559549 := by
    simpa [prefixWord, tailWord_559549, baseEnd_559549] using wordTrace_append hprefix tailTrace_559549
  have hstable : (prefixWord ++ tailWord_559549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559549).length < 2 ^ (prefixWord ++ tailWord_559549).sum := by decide
  have hdescent : baseEnd_559549 < baseStart_559549 := by decide
  rcases family_descends (prefixWord ++ tailWord_559549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559562 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_559562 : Nat := 118140960795 + 559562 * 2 ^ 59
def prefixEnd_559562 : Nat := 4983230072969 + 3 ^ 40 * 559562 * 2
def baseEnd_559562 : Nat := 95774753997081648267209

theorem tailTrace_559562 : CollatzResearch.WordTrace tailWord_559562 prefixEnd_559562 95774753997081648267209 := by
  unfold tailWord_559562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102225699702478606586235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13605935199206609617563293 5102225699702478606586235)
  ·
    refine ⟨7653338549553717909879353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5102225699702478606586235 7653338549553717909879353)
    ·
      refine ⟨5740003912165288432409515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7653338549553717909879353 5740003912165288432409515)
      ·
        refine ⟨8610005868247932648614273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5740003912165288432409515 8610005868247932648614273)
        ·
          refine ⟨6457504401185949486460705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8610005868247932648614273 6457504401185949486460705)
          ·
            refine ⟨4843128300889462114845529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6457504401185949486460705 4843128300889462114845529)
            ·
              refine ⟨3632346225667096586134147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4843128300889462114845529 3632346225667096586134147)
              ·
                refine ⟨5448519338500644879201221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632346225667096586134147 5448519338500644879201221)
                ·
                  refine ⟨1021597375968870914850229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5448519338500644879201221 1021597375968870914850229)
                  ·
                    refine ⟨95774753997081648267209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1021597375968870914850229 95774753997081648267209)
                    ·
                      rfl

theorem cell23_559562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_559562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559562 prefixEnd_559562 := by exact prefixLift 559562
  have htrace : WordTrace (prefixWord ++ tailWord_559562) baseStart_559562 baseEnd_559562 := by
    simpa [prefixWord, tailWord_559562, baseEnd_559562] using wordTrace_append hprefix tailTrace_559562
  have hstable : (prefixWord ++ tailWord_559562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559562).length < 2 ^ (prefixWord ++ tailWord_559562).sum := by decide
  have hdescent : baseEnd_559562 < baseStart_559562 := by decide
  rcases family_descends (prefixWord ++ tailWord_559562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559619 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3]
def baseStart_559619 : Nat := 118140960795 + 559619 * 2 ^ 59
def prefixEnd_559619 : Nat := 4983230072969 + 3 ^ 40 * 559619 * 2
def baseEnd_559619 : Nat := 287353530388551221788865

theorem tailTrace_559619 : CollatzResearch.WordTrace tailWord_559619 prefixEnd_559619 287353530388551221788865 := by
  unfold tailWord_559619
  simp only [CollatzResearch.WordTrace]
  refine ⟨20410981759603413161169911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13607321173068942107446607 20410981759603413161169911)
  ·
    refine ⟨30616472639405119741754867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20410981759603413161169911 30616472639405119741754867)
    ·
      refine ⟨45924708959107679612632301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30616472639405119741754867 45924708959107679612632301)
      ·
        refine ⟨17221765859665379854737113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45924708959107679612632301 17221765859665379854737113)
        ·
          refine ⟨12916324394749034891052835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17221765859665379854737113 12916324394749034891052835)
          ·
            refine ⟨19374486592123552336579253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12916324394749034891052835 19374486592123552336579253)
            ·
              refine ⟨1816358118011583031554305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19374486592123552336579253 1816358118011583031554305)
              ·
                refine ⟨1362268588508687273665729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816358118011583031554305 1362268588508687273665729)
                ·
                  refine ⟨1021701441381515455249297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362268588508687273665729 1021701441381515455249297)
                  ·
                    refine ⟨766276081036136591436973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021701441381515455249297 766276081036136591436973)
                    ·
                      refine ⟨287353530388551221788865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 766276081036136591436973 287353530388551221788865)
                      ·
                        rfl

theorem cell23_559619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_559619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559619 prefixEnd_559619 := by exact prefixLift 559619
  have htrace : WordTrace (prefixWord ++ tailWord_559619) baseStart_559619 baseEnd_559619 := by
    simpa [prefixWord, tailWord_559619, baseEnd_559619] using wordTrace_append hprefix tailTrace_559619
  have hstable : (prefixWord ++ tailWord_559619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559619).length < 2 ^ (prefixWord ++ tailWord_559619).sum := by decide
  have hdescent : baseEnd_559619 < baseStart_559619 := by decide
  rcases family_descends (prefixWord ++ tailWord_559619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559632 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_559632 : Nat := 118140960795 + 559632 * 2 ^ 59
def prefixEnd_559632 : Nat := 4983230072969 + 3 ^ 40 * 559632 * 2
def baseEnd_559632 : Nat := 287360205637059670926305

theorem tailTrace_559632 : CollatzResearch.WordTrace tailWord_559632 prefixEnd_559632 287360205637059670926305 := by
  unfold tailWord_559632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205727954278158190696575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13607637272370877587595433 10205727954278158190696575)
  ·
    refine ⟨15308591931417237286044863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10205727954278158190696575 15308591931417237286044863)
    ·
      refine ⟨22962887897125855929067295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15308591931417237286044863 22962887897125855929067295)
      ·
        refine ⟨34444331845688783893600943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22962887897125855929067295 34444331845688783893600943)
        ·
          refine ⟨51666497768533175840401415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34444331845688783893600943 51666497768533175840401415)
          ·
            refine ⟨77499746652799763760602123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51666497768533175840401415 77499746652799763760602123)
            ·
              refine ⟨116249619979199645640903185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77499746652799763760602123 116249619979199645640903185)
              ·
                refine ⟨87187214984399734230677389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116249619979199645640903185 87187214984399734230677389)
                ·
                  refine ⟨32695205619149900336504021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87187214984399734230677389 32695205619149900336504021)
                  ·
                    refine ⟨766293881698825789136813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32695205619149900336504021 766293881698825789136813)
                    ·
                      refine ⟨287360205637059670926305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 766293881698825789136813 287360205637059670926305)
                      ·
                        rfl

theorem cell23_559632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_559632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559632 prefixEnd_559632 := by exact prefixLift 559632
  have htrace : WordTrace (prefixWord ++ tailWord_559632) baseStart_559632 baseEnd_559632 := by
    simpa [prefixWord, tailWord_559632, baseEnd_559632] using wordTrace_append hprefix tailTrace_559632
  have hstable : (prefixWord ++ tailWord_559632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559632).length < 2 ^ (prefixWord ++ tailWord_559632).sum := by decide
  have hdescent : baseEnd_559632 < baseStart_559632 := by decide
  rcases family_descends (prefixWord ++ tailWord_559632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559642 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_559642 : Nat := 118140960795 + 559642 * 2 ^ 59
def prefixEnd_559642 : Nat := 4983230072969 + 3 ^ 40 * 559642 * 2
def baseEnd_559642 : Nat := 287365340443604631801259

theorem tailTrace_559642 : CollatzResearch.WordTrace tailWord_559642 prefixEnd_559642 287365340443604631801259 := by
  unfold tailWord_559642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102955159630022022314295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13607880425680058726171453 5102955159630022022314295)
  ·
    refine ⟨7654432739445033033471443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5102955159630022022314295 7654432739445033033471443)
    ·
      refine ⟨11481649109167549550207165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7654432739445033033471443 11481649109167549550207165)
      ·
        refine ⟨4305618415937831081327687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11481649109167549550207165 4305618415937831081327687)
        ·
          refine ⟨6458427623906746621991531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305618415937831081327687 6458427623906746621991531)
          ·
            refine ⟨9687641435860119932987297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6458427623906746621991531 9687641435860119932987297)
            ·
              refine ⟨7265731076895089949740473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9687641435860119932987297 7265731076895089949740473)
              ·
                refine ⟨5449298307671317462305355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265731076895089949740473 5449298307671317462305355)
                ·
                  refine ⟨8173947461506976193458033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449298307671317462305355 8173947461506976193458033)
                  ·
                    refine ⟨6130460596130232145093525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8173947461506976193458033 6130460596130232145093525)
                    ·
                      refine ⟨287365340443604631801259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6130460596130232145093525 287365340443604631801259)
                      ·
                        rfl

theorem cell23_559642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_559642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559642 prefixEnd_559642 := by exact prefixLift 559642
  have htrace : WordTrace (prefixWord ++ tailWord_559642) baseStart_559642 baseEnd_559642 := by
    simpa [prefixWord, tailWord_559642, baseEnd_559642] using wordTrace_append hprefix tailTrace_559642
  have hstable : (prefixWord ++ tailWord_559642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559642).length < 2 ^ (prefixWord ++ tailWord_559642).sum := by decide
  have hdescent : baseEnd_559642 < baseStart_559642 := by decide
  rcases family_descends (prefixWord ++ tailWord_559642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559659 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 5, 2]
def baseStart_559659 : Nat := 118140960795 + 559659 * 2 ^ 59
def prefixEnd_559659 : Nat := 4983230072969 + 3 ^ 40 * 559659 * 2
def baseEnd_559659 : Nat := 287374069614731065288681

theorem tailTrace_559659 : CollatzResearch.WordTrace tailWord_559659 prefixEnd_559659 287374069614731065288681 := by
  unfold tailWord_559659
  simp only [CollatzResearch.WordTrace]
  refine ⟨20412440679458499992626031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13608293786305666661750687 20412440679458499992626031)
  ·
    refine ⟨30618661019187749988939047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20412440679458499992626031 30618661019187749988939047)
    ·
      refine ⟨45927991528781624983408571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30618661019187749988939047 45927991528781624983408571)
      ·
        refine ⟨68891987293172437475112857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45927991528781624983408571 68891987293172437475112857)
        ·
          refine ⟨51668990469879328106334643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68891987293172437475112857 51668990469879328106334643)
          ·
            refine ⟨77503485704818992159501965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51668990469879328106334643 77503485704818992159501965)
            ·
              refine ⟨29063807139307122059813237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77503485704818992159501965 29063807139307122059813237)
              ·
                refine ⟨2724731919310042693107491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29063807139307122059813237 2724731919310042693107491)
                ·
                  refine ⟨4087097878965064039661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724731919310042693107491 4087097878965064039661237)
                  ·
                    refine ⟨383165426152974753718241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4087097878965064039661237 383165426152974753718241)
                    ·
                      refine ⟨287374069614731065288681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383165426152974753718241 287374069614731065288681)
                      ·
                        rfl

theorem cell23_559659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5, 2].length) (baseStart_559659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559659 prefixEnd_559659 := by exact prefixLift 559659
  have htrace : WordTrace (prefixWord ++ tailWord_559659) baseStart_559659 baseEnd_559659 := by
    simpa [prefixWord, tailWord_559659, baseEnd_559659] using wordTrace_append hprefix tailTrace_559659
  have hstable : (prefixWord ++ tailWord_559659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559659).length < 2 ^ (prefixWord ++ tailWord_559659).sum := by decide
  have hdescent : baseEnd_559659 < baseStart_559659 := by decide
  rcases family_descends (prefixWord ++ tailWord_559659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559689 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 6, 2]
def baseStart_559689 : Nat := 118140960795 + 559689 * 2 ^ 59
def prefixEnd_559689 : Nat := 4983230072969 + 3 ^ 40 * 559689 * 2
def baseEnd_559689 : Nat := 287389474034365947913543

theorem tailTrace_559689 : CollatzResearch.WordTrace tailWord_559689 prefixEnd_559689 287389474034365947913543 := by
  unfold tailWord_559689
  simp only [CollatzResearch.WordTrace]
  refine ⟨20413534869349815116218121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13609023246233210077478747 20413534869349815116218121)
  ·
    refine ⟨15310151152012361337163591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20413534869349815116218121 15310151152012361337163591)
    ·
      refine ⟨22965226728018542005745387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15310151152012361337163591 22965226728018542005745387)
      ·
        refine ⟨34447840092027813008618081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22965226728018542005745387 34447840092027813008618081)
        ·
          refine ⟨25835880069020859756463561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34447840092027813008618081 25835880069020859756463561)
          ·
            refine ⟨19376910051765644817347671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25835880069020859756463561 19376910051765644817347671)
            ·
              refine ⟨29065365077648467226021507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19376910051765644817347671 29065365077648467226021507)
              ·
                refine ⟨43598047616472700839032261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29065365077648467226021507 43598047616472700839032261)
                ·
                  refine ⟨8174633928088631407318549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43598047616472700839032261 8174633928088631407318549)
                  ·
                    refine ⟨383185965379154597218057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8174633928088631407318549 383185965379154597218057)
                    ·
                      refine ⟨287389474034365947913543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383185965379154597218057 287389474034365947913543)
                      ·
                        rfl

theorem cell23_559689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6, 2].length) (baseStart_559689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559689 prefixEnd_559689 := by exact prefixLift 559689
  have htrace : WordTrace (prefixWord ++ tailWord_559689) baseStart_559689 baseEnd_559689 := by
    simpa [prefixWord, tailWord_559689, baseEnd_559689] using wordTrace_append hprefix tailTrace_559689
  have hstable : (prefixWord ++ tailWord_559689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559689).length < 2 ^ (prefixWord ++ tailWord_559689).sum := by decide
  have hdescent : baseEnd_559689 < baseStart_559689 := by decide
  rcases family_descends (prefixWord ++ tailWord_559689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559712 : List Nat := [2, 1, 1, 3, 2, 1, 2, 11]
def baseStart_559712 : Nat := 118140960795 + 559712 * 2 ^ 59
def prefixEnd_559712 : Nat := 4983230072969 + 3 ^ 40 * 559712 * 2
def baseEnd_559712 : Nat := 10644492003311828071331

theorem tailTrace_559712 : CollatzResearch.WordTrace tailWord_559712 prefixEnd_559712 10644492003311828071331 := by
  unfold tailWord_559712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207186874133245022152695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13609582498844326696203593 10207186874133245022152695)
  ·
    refine ⟨15310780311199867533229043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10207186874133245022152695 15310780311199867533229043)
    ·
      refine ⟨22966170466799801299843565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15310780311199867533229043 22966170466799801299843565)
      ·
        refine ⟨8612313925049925487441337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22966170466799801299843565 8612313925049925487441337)
        ·
          refine ⟨6459235443787444115581003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8612313925049925487441337 6459235443787444115581003)
          ·
            refine ⟨9688853165681166173371505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6459235443787444115581003 9688853165681166173371505)
            ·
              refine ⟨7266639874260874630028629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9688853165681166173371505 7266639874260874630028629)
              ·
                refine ⟨10644492003311828071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7266639874260874630028629 10644492003311828071331)
                ·
                  rfl

theorem cell23_559712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_559712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559712 prefixEnd_559712 := by exact prefixLift 559712
  have htrace : WordTrace (prefixWord ++ tailWord_559712) baseStart_559712 baseEnd_559712 := by
    simpa [prefixWord, tailWord_559712, baseEnd_559712] using wordTrace_append hprefix tailTrace_559712
  have hstable : (prefixWord ++ tailWord_559712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559712).length < 2 ^ (prefixWord ++ tailWord_559712).sum := by decide
  have hdescent : baseEnd_559712 < baseStart_559712 := by decide
  rcases family_descends (prefixWord ++ tailWord_559712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559720 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_559720 : Nat := 118140960795 + 559720 * 2 ^ 59
def prefixEnd_559720 : Nat := 4983230072969 + 3 ^ 40 * 559720 * 2
def baseEnd_559720 : Nat := 95801797311551775541967

theorem tailTrace_559720 : CollatzResearch.WordTrace tailWord_559720 prefixEnd_559720 95801797311551775541967 := by
  unfold tailWord_559720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207332766118753705298307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13609777021491671607064409 10207332766118753705298307)
  ·
    refine ⟨15310999149178130557947461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10207332766118753705298307 15310999149178130557947461)
    ·
      refine ⟨2870812340470899479615149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15310999149178130557947461 2870812340470899479615149)
      ·
        refine ⟨1076554627676587304855681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2870812340470899479615149 1076554627676587304855681)
        ·
          refine ⟨807415970757440478641761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076554627676587304855681 807415970757440478641761)
          ·
            refine ⟨605561978068080358981321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807415970757440478641761 605561978068080358981321)
            ·
              refine ⟨454171483551060269235991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605561978068080358981321 454171483551060269235991)
              ·
                refine ⟨681257225326590403853987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454171483551060269235991 681257225326590403853987)
                ·
                  refine ⟨1021885837989885605780981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681257225326590403853987 1021885837989885605780981)
                  ·
                    refine ⟨95801797311551775541967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1021885837989885605780981 95801797311551775541967)
                    ·
                      rfl

theorem cell23_559720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_559720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559720 prefixEnd_559720 := by exact prefixLift 559720
  have htrace : WordTrace (prefixWord ++ tailWord_559720) baseStart_559720 baseEnd_559720 := by
    simpa [prefixWord, tailWord_559720, baseEnd_559720] using wordTrace_append hprefix tailTrace_559720
  have hstable : (prefixWord ++ tailWord_559720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559720).length < 2 ^ (prefixWord ++ tailWord_559720).sum := by decide
  have hdescent : baseEnd_559720 < baseStart_559720 := by decide
  rcases family_descends (prefixWord ++ tailWord_559720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559733 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_559733 : Nat := 118140960795 + 559733 * 2 ^ 59
def prefixEnd_559733 : Nat := 4983230072969 + 3 ^ 40 * 559733 * 2
def baseEnd_559733 : Nat := 95804022394387925254447

theorem tailTrace_559733 : CollatzResearch.WordTrace tailWord_559733 prefixEnd_559733 95804022394387925254447 := by
  unfold tailWord_559733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20415139681190410630819853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13610093120793607087213235 20415139681190410630819853)
  ·
    refine ⟨7655677380446403986557445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20415139681190410630819853 7655677380446403986557445)
    ·
      refine ⟨1435439508833700747479521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7655677380446403986557445 1435439508833700747479521)
      ·
        refine ⟨1076579631625275560609641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1435439508833700747479521 1076579631625275560609641)
        ·
          refine ⟨807434723718956670457231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076579631625275560609641 807434723718956670457231)
          ·
            refine ⟨1211152085578435005685847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807434723718956670457231 1211152085578435005685847)
            ·
              refine ⟨1816728128367652508528771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211152085578435005685847 1816728128367652508528771)
              ·
                refine ⟨2725092192551478762793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816728128367652508528771 2725092192551478762793157)
                ·
                  refine ⟨510954786103402268023717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2725092192551478762793157 510954786103402268023717)
                  ·
                    refine ⟨95804022394387925254447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 510954786103402268023717 95804022394387925254447)
                    ·
                      rfl

theorem cell23_559733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_559733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559733 prefixEnd_559733 := by exact prefixLift 559733
  have htrace : WordTrace (prefixWord ++ tailWord_559733) baseStart_559733 baseEnd_559733 := by
    simpa [prefixWord, tailWord_559733, baseEnd_559733] using wordTrace_append hprefix tailTrace_559733
  have hstable : (prefixWord ++ tailWord_559733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559733).length < 2 ^ (prefixWord ++ tailWord_559733).sum := by decide
  have hdescent : baseEnd_559733 < baseStart_559733 := by decide
  rcases family_descends (prefixWord ++ tailWord_559733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559740 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_559740 : Nat := 118140960795 + 559740 * 2 ^ 59
def prefixEnd_559740 : Nat := 4983230072969 + 3 ^ 40 * 559740 * 2
def baseEnd_559740 : Nat := 287415661547745248375809

theorem tailTrace_559740 : CollatzResearch.WordTrace tailWord_559740 prefixEnd_559740 287415661547745248375809 := by
  unfold tailWord_559740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207697496082525413162337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13610263328110033884216449 10207697496082525413162337)
  ·
    refine ⟨7655773122061894059871753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10207697496082525413162337 7655773122061894059871753)
    ·
      refine ⟨5741829841546420544903815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7655773122061894059871753 5741829841546420544903815)
      ·
        refine ⟨8612744762319630817355723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5741829841546420544903815 8612744762319630817355723)
        ·
          refine ⟨12919117143479446226033585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8612744762319630817355723 12919117143479446226033585)
          ·
            refine ⟨9689337857609584669525189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12919117143479446226033585 9689337857609584669525189)
            ·
              refine ⟨1816750848301797125535973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9689337857609584669525189 1816750848301797125535973)
              ·
                refine ⟨340640784056586961037995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1816750848301797125535973 340640784056586961037995)
                ·
                  refine ⟨510961176084880441556993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340640784056586961037995 510961176084880441556993)
                  ·
                    refine ⟨383220882063660331167745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 510961176084880441556993 383220882063660331167745)
                    ·
                      refine ⟨287415661547745248375809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383220882063660331167745 287415661547745248375809)
                      ·
                        rfl

theorem cell23_559740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_559740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559740 prefixEnd_559740 := by exact prefixLift 559740
  have htrace : WordTrace (prefixWord ++ tailWord_559740) baseStart_559740 baseEnd_559740 := by
    simpa [prefixWord, tailWord_559740, baseEnd_559740] using wordTrace_append hprefix tailTrace_559740
  have hstable : (prefixWord ++ tailWord_559740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559740).length < 2 ^ (prefixWord ++ tailWord_559740).sum := by decide
  have hdescent : baseEnd_559740 < baseStart_559740 := by decide
  rcases family_descends (prefixWord ++ tailWord_559740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559790 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_559790 : Nat := 118140960795 + 559790 * 2 ^ 59
def prefixEnd_559790 : Nat := 4983230072969 + 3 ^ 40 * 559790 * 2
def baseEnd_559790 : Nat := 287441335580470052750579

theorem tailTrace_559790 : CollatzResearch.WordTrace tailWord_559790 prefixEnd_559790 287441335580470052750579 := by
  unfold tailWord_559790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552152330247988670705603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13611479094655939577096549 2552152330247988670705603)
  ·
    refine ⟨3828228495371983006058405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552152330247988670705603 3828228495371983006058405)
    ·
      refine ⟨717792842882246813635951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3828228495371983006058405 717792842882246813635951)
      ·
        refine ⟨1076689264323370220453927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717792842882246813635951 1076689264323370220453927)
        ·
          refine ⟨1615033896485055330680891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076689264323370220453927 1615033896485055330680891)
          ·
            refine ⟨2422550844727582996021337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615033896485055330680891 2422550844727582996021337)
            ·
              refine ⟨1816913133545687247016003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422550844727582996021337 1816913133545687247016003)
              ·
                refine ⟨2725369700318530870524005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816913133545687247016003 2725369700318530870524005)
                ·
                  refine ⟨511006818809724538223251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2725369700318530870524005 511006818809724538223251)
                  ·
                    refine ⟨766510228214586807334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511006818809724538223251 766510228214586807334877)
                    ·
                      refine ⟨287441335580470052750579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 766510228214586807334877 287441335580470052750579)
                      ·
                        rfl

theorem cell23_559790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_559790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559790 prefixEnd_559790 := by exact prefixLift 559790
  have htrace : WordTrace (prefixWord ++ tailWord_559790) baseStart_559790 baseEnd_559790 := by
    simpa [prefixWord, tailWord_559790, baseEnd_559790] using wordTrace_append hprefix tailTrace_559790
  have hstable : (prefixWord ++ tailWord_559790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559790).length < 2 ^ (prefixWord ++ tailWord_559790).sum := by decide
  have hdescent : baseEnd_559790 < baseStart_559790 := by decide
  rcases family_descends (prefixWord ++ tailWord_559790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559853 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 5]
def baseStart_559853 : Nat := 118140960795 + 559853 * 2 ^ 59
def prefixEnd_559853 : Nat := 4983230072969 + 3 ^ 40 * 559853 * 2
def baseEnd_559853 : Nat := 31941520540189256251421

theorem tailTrace_559853 : CollatzResearch.WordTrace tailWord_559853 prefixEnd_559853 31941520540189256251421 := by
  unfold tailWord_559853
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419516440755671125188213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13613010960503780750125475 20419516440755671125188213)
  ·
    refine ⟨1914329666320844167986395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20419516440755671125188213 1914329666320844167986395)
    ·
      refine ⟨2871494499481266251979593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914329666320844167986395 2871494499481266251979593)
      ·
        refine ⟨2153620874610949688984695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871494499481266251979593 2153620874610949688984695)
        ·
          refine ⟨3230431311916424533477043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153620874610949688984695 3230431311916424533477043)
          ·
            refine ⟨4845646967874636800215565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230431311916424533477043 4845646967874636800215565)
            ·
              refine ⟨1817117612952988800080837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4845646967874636800215565 1817117612952988800080837)
              ·
                refine ⟨340709552428685400015157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1817117612952988800080837 340709552428685400015157)
                ·
                  refine ⟨31941520540189256251421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340709552428685400015157 31941520540189256251421)
                  ·
                    rfl

theorem cell23_559853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_559853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559853 prefixEnd_559853 := by exact prefixLift 559853
  have htrace : WordTrace (prefixWord ++ tailWord_559853) baseStart_559853 baseEnd_559853 := by
    simpa [prefixWord, tailWord_559853, baseEnd_559853] using wordTrace_append hprefix tailTrace_559853
  have hstable : (prefixWord ++ tailWord_559853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559853).length < 2 ^ (prefixWord ++ tailWord_559853).sum := by decide
  have hdescent : baseEnd_559853 < baseStart_559853 := by decide
  rcases family_descends (prefixWord ++ tailWord_559853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559856 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2]
def baseStart_559856 : Nat := 118140960795 + 559856 * 2 ^ 59
def prefixEnd_559856 : Nat := 4983230072969 + 3 ^ 40 * 559856 * 2
def baseEnd_559856 : Nat := 287475225303666794525275

theorem tailTrace_559856 : CollatzResearch.WordTrace tailWord_559856 prefixEnd_559856 287475225303666794525275 := by
  unfold tailWord_559856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209812929872401318773711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13613083906496535091698281 10209812929872401318773711)
  ·
    refine ⟨15314719394808601978160567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10209812929872401318773711 15314719394808601978160567)
    ·
      refine ⟨22972079092212902967240851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15314719394808601978160567 22972079092212902967240851)
      ·
        refine ⟨34458118638319354450861277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22972079092212902967240851 34458118638319354450861277)
        ·
          refine ⟨12921794489369757919072979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34458118638319354450861277 12921794489369757919072979)
          ·
            refine ⟨19382691734054636878609469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12921794489369757919072979 19382691734054636878609469)
            ·
              refine ⟨7268509400270488829478551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19382691734054636878609469 7268509400270488829478551)
              ·
                refine ⟨10902764100405733244217827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7268509400270488829478551 10902764100405733244217827)
                ·
                  refine ⟨16354146150608599866326741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10902764100405733244217827 16354146150608599866326741)
                  ·
                    refine ⟨383300300404889059367033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16354146150608599866326741 383300300404889059367033)
                    ·
                      refine ⟨287475225303666794525275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383300300404889059367033 287475225303666794525275)
                      ·
                        rfl

theorem cell23_559856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2].length) (baseStart_559856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559856 prefixEnd_559856 := by exact prefixLift 559856
  have htrace : WordTrace (prefixWord ++ tailWord_559856) baseStart_559856 baseEnd_559856 := by
    simpa [prefixWord, tailWord_559856, baseEnd_559856] using wordTrace_append hprefix tailTrace_559856
  have hstable : (prefixWord ++ tailWord_559856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559856).length < 2 ^ (prefixWord ++ tailWord_559856).sum := by decide
  have hdescent : baseEnd_559856 < baseStart_559856 := by decide
  rcases family_descends (prefixWord ++ tailWord_559856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559896 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_559896 : Nat := 118140960795 + 559896 * 2 ^ 59
def prefixEnd_559896 : Nat := 4983230072969 + 3 ^ 40 * 559896 * 2
def baseEnd_559896 : Nat := 95831921509948879341697

theorem tailTrace_559896 : CollatzResearch.WordTrace tailWord_559896 prefixEnd_559896 95831921509948879341697 := by
  unfold tailWord_559896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210542389799944734501771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13614056519733259646002361 10210542389799944734501771)
  ·
    refine ⟨15315813584699917101752657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210542389799944734501771 15315813584699917101752657)
    ·
      refine ⟨11486860188524937826314493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15315813584699917101752657 11486860188524937826314493)
      ·
        refine ⟨4307572570696851684867935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11486860188524937826314493 4307572570696851684867935)
        ·
          refine ⟨6461358856045277527301903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307572570696851684867935 6461358856045277527301903)
          ·
            refine ⟨9692038284067916290952855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461358856045277527301903 9692038284067916290952855)
            ·
              refine ⟨14538057426101874436429283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9692038284067916290952855 14538057426101874436429283)
              ·
                refine ⟨21807086139152811654643925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14538057426101874436429283 21807086139152811654643925)
                ·
                  refine ⟨511103581386394023155717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21807086139152811654643925 511103581386394023155717)
                  ·
                    refine ⟨95831921509948879341697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511103581386394023155717 95831921509948879341697)
                    ·
                      rfl

theorem cell23_559896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_559896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559896 prefixEnd_559896 := by exact prefixLift 559896
  have htrace : WordTrace (prefixWord ++ tailWord_559896) baseStart_559896 baseEnd_559896 := by
    simpa [prefixWord, tailWord_559896, baseEnd_559896] using wordTrace_append hprefix tailTrace_559896
  have hstable : (prefixWord ++ tailWord_559896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559896).length < 2 ^ (prefixWord ++ tailWord_559896).sum := by decide
  have hdescent : baseEnd_559896 < baseStart_559896 := by decide
  rcases family_descends (prefixWord ++ tailWord_559896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559903 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 4, 2]
def baseStart_559903 : Nat := 118140960795 + 559903 * 2 ^ 59
def prefixEnd_559903 : Nat := 4983230072969 + 3 ^ 40 * 559903 * 2
def baseEnd_559903 : Nat := 287499358894428110637559

theorem tailTrace_559903 : CollatzResearch.WordTrace tailWord_559903 prefixEnd_559903 287499358894428110637559 := by
  unfold tailWord_559903
  simp only [CollatzResearch.WordTrace]
  refine ⟨20421340090574529664508363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13614226727049686443005575 20421340090574529664508363)
  ·
    refine ⟨30632010135861794496762545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20421340090574529664508363 30632010135861794496762545)
    ·
      refine ⟨22974007601896345872571909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30632010135861794496762545 22974007601896345872571909)
      ·
        refine ⟨4307626425355564851107233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22974007601896345872571909 4307626425355564851107233)
        ·
          refine ⟨3230719819016673638330425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4307626425355564851107233 3230719819016673638330425)
          ·
            refine ⟨2423039864262505228747819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3230719819016673638330425 2423039864262505228747819)
            ·
              refine ⟨3634559796393757843121729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423039864262505228747819 3634559796393757843121729)
              ·
                refine ⟨2725919847295318382341297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634559796393757843121729 2725919847295318382341297)
                ·
                  refine ⟨2044439885471488786755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725919847295318382341297 2044439885471488786755973)
                  ·
                    refine ⟨383332478525904147516745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2044439885471488786755973 383332478525904147516745)
                    ·
                      refine ⟨287499358894428110637559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383332478525904147516745 287499358894428110637559)
                      ·
                        rfl

theorem cell23_559903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_559903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559903 prefixEnd_559903 := by exact prefixLift 559903
  have htrace : WordTrace (prefixWord ++ tailWord_559903) baseStart_559903 baseEnd_559903 := by
    simpa [prefixWord, tailWord_559903, baseEnd_559903] using wordTrace_append hprefix tailTrace_559903
  have hstable : (prefixWord ++ tailWord_559903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559903).length < 2 ^ (prefixWord ++ tailWord_559903).sum := by decide
  have hdescent : baseEnd_559903 < baseStart_559903 := by decide
  rcases family_descends (prefixWord ++ tailWord_559903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559964 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_559964 : Nat := 118140960795 + 559964 * 2 ^ 59
def prefixEnd_559964 : Nat := 4983230072969 + 3 ^ 40 * 559964 * 2
def baseEnd_559964 : Nat := 95843560404784123991593

theorem tailTrace_559964 : CollatzResearch.WordTrace tailWord_559964 prefixEnd_559964 95843560404784123991593 := by
  unfold tailWord_559964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211782471676768541239473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13615709962235691388319297 10211782471676768541239473)
  ·
    refine ⟨7658836853757576405929605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10211782471676768541239473 7658836853757576405929605)
    ·
      refine ⟨1436031910079545576111801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7658836853757576405929605 1436031910079545576111801)
      ·
        refine ⟨1077023932559659182083851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1436031910079545576111801 1077023932559659182083851)
        ·
          refine ⟨1615535898839488773125777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077023932559659182083851 1615535898839488773125777)
          ·
            refine ⟨1211651924129616579844333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615535898839488773125777 1211651924129616579844333)
            ·
              refine ⟨454369471548606217441625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1211651924129616579844333 454369471548606217441625)
              ·
                refine ⟨340777103661454663081219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454369471548606217441625 340777103661454663081219)
                ·
                  refine ⟨511165655492181994621829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340777103661454663081219 511165655492181994621829)
                  ·
                    refine ⟨95843560404784123991593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511165655492181994621829 95843560404784123991593)
                    ·
                      rfl

theorem cell23_559964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_559964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559964 prefixEnd_559964 := by exact prefixLift 559964
  have htrace : WordTrace (prefixWord ++ tailWord_559964) baseStart_559964 baseEnd_559964 := by
    simpa [prefixWord, tailWord_559964, baseEnd_559964] using wordTrace_append hprefix tailTrace_559964
  have hstable : (prefixWord ++ tailWord_559964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559964).length < 2 ^ (prefixWord ++ tailWord_559964).sum := by decide
  have hdescent : baseEnd_559964 < baseStart_559964 := by decide
  rcases family_descends (prefixWord ++ tailWord_559964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559990 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_559990 : Nat := 118140960795 + 559990 * 2 ^ 59
def prefixEnd_559990 : Nat := 4983230072969 + 3 ^ 40 * 559990 * 2
def baseEnd_559990 : Nat := 95848010570456423416553

theorem tailTrace_559990 : CollatzResearch.WordTrace tailWord_559990 prefixEnd_559990 95848010570456423416553 := by
  unfold tailWord_559990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276532077578708970182839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13616342160839562348616949 1276532077578708970182839)
  ·
    refine ⟨1914798116368063455274259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276532077578708970182839 1914798116368063455274259)
    ·
      refine ⟨2872197174552095182911389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914798116368063455274259 2872197174552095182911389)
      ·
        refine ⟨1077073940457035693591771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2872197174552095182911389 1077073940457035693591771)
        ·
          refine ⟨1615610910685553540387657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077073940457035693591771 1615610910685553540387657)
          ·
            refine ⟨1211708183014165155290743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615610910685553540387657 1211708183014165155290743)
            ·
              refine ⟨1817562274521247732936115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211708183014165155290743 1817562274521247732936115)
              ·
                refine ⟨2726343411781871599404173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817562274521247732936115 2726343411781871599404173)
                ·
                  refine ⟨1022378779418201849776565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2726343411781871599404173 1022378779418201849776565)
                  ·
                    refine ⟨95848010570456423416553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1022378779418201849776565 95848010570456423416553)
                    ·
                      rfl

theorem cell23_559990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_559990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559990 prefixEnd_559990 := by exact prefixLift 559990
  have htrace : WordTrace (prefixWord ++ tailWord_559990) baseStart_559990 baseEnd_559990 := by
    simpa [prefixWord, tailWord_559990, baseEnd_559990] using wordTrace_append hprefix tailTrace_559990
  have hstable : (prefixWord ++ tailWord_559990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559990).length < 2 ^ (prefixWord ++ tailWord_559990).sum := by decide
  have hdescent : baseEnd_559990 < baseStart_559990 := by decide
  rcases family_descends (prefixWord ++ tailWord_559990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559993 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_559993 : Nat := 118140960795 + 559993 * 2 ^ 59
def prefixEnd_559993 : Nat := 4983230072969 + 3 ^ 40 * 559993 * 2
def baseEnd_559993 : Nat := 287545572153332758512145

theorem tailTrace_559993 : CollatzResearch.WordTrace tailWord_559993 prefixEnd_559993 287545572153332758512145 := by
  unfold tailWord_559993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424622660248475035284633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13616415106832316690189755 20424622660248475035284633)
  ·
    refine ⟨15318466995186356276463475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20424622660248475035284633 15318466995186356276463475)
    ·
      refine ⟨22977700492779534414695213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318466995186356276463475 22977700492779534414695213)
      ·
        refine ⟨8616637684792325405510705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22977700492779534414695213 8616637684792325405510705)
        ·
          refine ⟨6462478263594244054133029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8616637684792325405510705 6462478263594244054133029)
          ·
            refine ⟨1211714674423920760149943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6462478263594244054133029 1211714674423920760149943)
            ·
              refine ⟨1817572011635881140224915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211714674423920760149943 1817572011635881140224915)
              ·
                refine ⟨2726358017453821710337373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817572011635881140224915 2726358017453821710337373)
                ·
                  refine ⟨1022384256545183141376515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2726358017453821710337373 1022384256545183141376515)
                  ·
                    refine ⟨1533576384817774712064773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1022384256545183141376515 1533576384817774712064773)
                    ·
                      refine ⟨287545572153332758512145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1533576384817774712064773 287545572153332758512145)
                      ·
                        rfl

theorem cell23_559993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_559993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559993 prefixEnd_559993 := by exact prefixLift 559993
  have htrace : WordTrace (prefixWord ++ tailWord_559993) baseStart_559993 baseEnd_559993 := by
    simpa [prefixWord, tailWord_559993, baseEnd_559993] using wordTrace_append hprefix tailTrace_559993
  have hstable : (prefixWord ++ tailWord_559993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559993).length < 2 ^ (prefixWord ++ tailWord_559993).sum := by decide
  have hdescent : baseEnd_559993 < baseStart_559993 := by decide
  rcases family_descends (prefixWord ++ tailWord_559993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_559996 : Nat := 118140960795 + 559996 * 2 ^ 59
def prefixEnd_559996 : Nat := 4983230072969 + 3 ^ 40 * 559996 * 2
def baseEnd_559996 : Nat := 287547112595296246774631

theorem tailTrace_559996 : CollatzResearch.WordTrace tailWord_559996 prefixEnd_559996 287547112595296246774631 := by
  unfold tailWord_559996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212366039618803273821921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13616488052825071031762561 10212366039618803273821921)
  ·
    refine ⟨7659274529714102455366441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10212366039618803273821921 7659274529714102455366441)
    ·
      refine ⟨5744455897285576841524831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7659274529714102455366441 5744455897285576841524831)
      ·
        refine ⟨8616683845928365262287247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744455897285576841524831 8616683845928365262287247)
        ·
          refine ⟨12925025768892547893430871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8616683845928365262287247 12925025768892547893430871)
          ·
            refine ⟨19387538653338821840146307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925025768892547893430871 19387538653338821840146307)
            ·
              refine ⟨29081307980008232760219461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19387538653338821840146307 29081307980008232760219461)
              ·
                refine ⟨5452745246251543642541149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29081307980008232760219461 5452745246251543642541149)
                ·
                  refine ⟨2044779467344328865952931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5452745246251543642541149 2044779467344328865952931)
                  ·
                    refine ⟨3067169201016493298929397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044779467344328865952931 3067169201016493298929397)
                    ·
                      refine ⟨287547112595296246774631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3067169201016493298929397 287547112595296246774631)
                      ·
                        rfl

theorem cell23_559996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_559996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_559996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_559996 prefixEnd_559996 := by exact prefixLift 559996
  have htrace : WordTrace (prefixWord ++ tailWord_559996) baseStart_559996 baseEnd_559996 := by
    simpa [prefixWord, tailWord_559996, baseEnd_559996] using wordTrace_append hprefix tailTrace_559996
  have hstable : (prefixWord ++ tailWord_559996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559996).length < 2 ^ (prefixWord ++ tailWord_559996).sum := by decide
  have hdescent : baseEnd_559996 < baseStart_559996 := by decide
  rcases family_descends (prefixWord ++ tailWord_559996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560033 : List Nat := [1, 2, 3, 4, 1, 1, 3, 8]
def baseStart_560033 : Nat := 118140960795 + 560033 * 2 ^ 59
def prefixEnd_560033 : Nat := 4983230072969 + 3 ^ 40 * 560033 * 2
def baseEnd_560033 : Nat := 10650596717759726000443

theorem tailTrace_560033 : CollatzResearch.WordTrace tailWord_560033 prefixEnd_560033 10650596717759726000443 := by
  unfold tailWord_560033
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426081580103561866740753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13617387720069041244493835 20426081580103561866740753)
  ·
    refine ⟨15319561185077671400055565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20426081580103561866740753 15319561185077671400055565)
    ·
      refine ⟨5744835444404126775020837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15319561185077671400055565 5744835444404126775020837)
      ·
        refine ⟨1077156645825773770316407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5744835444404126775020837 1077156645825773770316407)
        ·
          refine ⟨1615734968738660655474611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077156645825773770316407 1615734968738660655474611)
          ·
            refine ⟨2423602453107990983211917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615734968738660655474611 2423602453107990983211917)
            ·
              refine ⟨908850919915496618704469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2423602453107990983211917 908850919915496618704469)
              ·
                refine ⟨10650596717759726000443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 908850919915496618704469 10650596717759726000443)
                ·
                  rfl

theorem cell23_560033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 8].length) (baseStart_560033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560033 prefixEnd_560033 := by exact prefixLift 560033
  have htrace : WordTrace (prefixWord ++ tailWord_560033) baseStart_560033 baseEnd_560033 := by
    simpa [prefixWord, tailWord_560033, baseEnd_560033] using wordTrace_append hprefix tailTrace_560033
  have hstable : (prefixWord ++ tailWord_560033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560033).length < 2 ^ (prefixWord ++ tailWord_560033).sum := by decide
  have hdescent : baseEnd_560033 < baseStart_560033 := by decide
  rcases family_descends (prefixWord ++ tailWord_560033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560061 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_560061 : Nat := 118140960795 + 560061 * 2 ^ 59
def prefixEnd_560061 : Nat := 4983230072969 + 3 ^ 40 * 560061 * 2
def baseEnd_560061 : Nat := 287580488837838492461833

theorem tailTrace_560061 : CollatzResearch.WordTrace tailWord_560061 prefixEnd_560061 287580488837838492461833 := by
  unfold tailWord_560061
  simp only [CollatzResearch.WordTrace]
  refine ⟨20427102824002122648760037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13618068549334748432506691 20427102824002122648760037)
  ·
    refine ⟨3830081779500397996642507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20427102824002122648760037 3830081779500397996642507)
    ·
      refine ⟨5745122669250596994963761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830081779500397996642507 5745122669250596994963761)
      ·
        refine ⟨4308842001937947746222821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5745122669250596994963761 4308842001937947746222821)
        ·
          refine ⟨807907875363365202416779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4308842001937947746222821 807907875363365202416779)
          ·
            refine ⟨1211861813045047803625169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807907875363365202416779 1211861813045047803625169)
            ·
              refine ⟨908896359783785852718877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211861813045047803625169 908896359783785852718877)
              ·
                refine ⟨340836134918919694769579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908896359783785852718877 340836134918919694769579)
                ·
                  refine ⟨511254202378379542154369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340836134918919694769579 511254202378379542154369)
                  ·
                    refine ⟨383440651783784656615777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511254202378379542154369 383440651783784656615777)
                    ·
                      refine ⟨287580488837838492461833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383440651783784656615777 287580488837838492461833)
                      ·
                        rfl

theorem cell23_560061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_560061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560061 prefixEnd_560061 := by exact prefixLift 560061
  have htrace : WordTrace (prefixWord ++ tailWord_560061) baseStart_560061 baseEnd_560061 := by
    simpa [prefixWord, tailWord_560061, baseEnd_560061] using wordTrace_append hprefix tailTrace_560061
  have hstable : (prefixWord ++ tailWord_560061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560061).length < 2 ^ (prefixWord ++ tailWord_560061).sum := by decide
  have hdescent : baseEnd_560061 < baseStart_560061 := by decide
  rcases family_descends (prefixWord ++ tailWord_560061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560100 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_560100 : Nat := 118140960795 + 560100 * 2 ^ 59
def prefixEnd_560100 : Nat := 4983230072969 + 3 ^ 40 * 560100 * 2
def baseEnd_560100 : Nat := 287600514583363839874153

theorem tailTrace_560100 : CollatzResearch.WordTrace tailWord_560100 prefixEnd_560100 287600514583363839874153 := by
  unfold tailWord_560100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214262635430416154714877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13619016847240554872953169 10214262635430416154714877)
  ·
    refine ⟨3830348488286406058018079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10214262635430416154714877 3830348488286406058018079)
    ·
      refine ⟨5745522732429609087027119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830348488286406058018079 5745522732429609087027119)
      ·
        refine ⟨8618284098644413630540679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745522732429609087027119 8618284098644413630540679)
        ·
          refine ⟨12927426147966620445811019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8618284098644413630540679 12927426147966620445811019)
          ·
            refine ⟨19391139221949930668716529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927426147966620445811019 19391139221949930668716529)
            ·
              refine ⟨14543354416462448001537397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19391139221949930668716529 14543354416462448001537397)
              ·
                refine ⟨1363439476543354500144131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14543354416462448001537397 1363439476543354500144131)
                ·
                  refine ⟨2045159214815031750216197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363439476543354500144131 2045159214815031750216197)
                  ·
                    refine ⟨383467352777818453165537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2045159214815031750216197 383467352777818453165537)
                    ·
                      refine ⟨287600514583363839874153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383467352777818453165537 287600514583363839874153)
                      ·
                        rfl

theorem cell23_560100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_560100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560100 prefixEnd_560100 := by exact prefixLift 560100
  have htrace : WordTrace (prefixWord ++ tailWord_560100) baseStart_560100 baseEnd_560100 := by
    simpa [prefixWord, tailWord_560100, baseEnd_560100] using wordTrace_append hprefix tailTrace_560100
  have hstable : (prefixWord ++ tailWord_560100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560100).length < 2 ^ (prefixWord ++ tailWord_560100).sum := by decide
  have hdescent : baseEnd_560100 < baseStart_560100 := by decide
  rcases family_descends (prefixWord ++ tailWord_560100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560140 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 7]
def baseStart_560140 : Nat := 118140960795 + 560140 * 2 ^ 59
def prefixEnd_560140 : Nat := 4983230072969 + 3 ^ 40 * 560140 * 2
def baseEnd_560140 : Nat := 31957894867727075930441

theorem tailTrace_560140 : CollatzResearch.WordTrace tailWord_560140 prefixEnd_560140 31957894867727075930441 := by
  unfold tailWord_560140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214992095357959570442937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13619989460477279427257249 10214992095357959570442937)
  ·
    refine ⟨7661244071518469677832203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10214992095357959570442937 7661244071518469677832203)
    ·
      refine ⟨11491866107277704516748305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7661244071518469677832203 11491866107277704516748305)
      ·
        refine ⟨8618899580458278387561229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11491866107277704516748305 8618899580458278387561229)
        ·
          refine ⟨3232087342671854395335461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8618899580458278387561229 3232087342671854395335461)
          ·
            refine ⟨606016376750972699125399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3232087342671854395335461 606016376750972699125399)
            ·
              refine ⟨909024565126459048688099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606016376750972699125399 909024565126459048688099)
              ·
                refine ⟨1363536847689688573032149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909024565126459048688099 1363536847689688573032149)
                ·
                  refine ⟨31957894867727075930441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1363536847689688573032149 31957894867727075930441)
                  ·
                    rfl

theorem cell23_560140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_560140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560140 prefixEnd_560140 := by exact prefixLift 560140
  have htrace : WordTrace (prefixWord ++ tailWord_560140) baseStart_560140 baseEnd_560140 := by
    simpa [prefixWord, tailWord_560140, baseEnd_560140] using wordTrace_append hprefix tailTrace_560140
  have hstable : (prefixWord ++ tailWord_560140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560140).length < 2 ^ (prefixWord ++ tailWord_560140).sum := by decide
  have hdescent : baseEnd_560140 < baseStart_560140 := by decide
  rcases family_descends (prefixWord ++ tailWord_560140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560151 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_560151 : Nat := 118140960795 + 560151 * 2 ^ 59
def prefixEnd_560151 : Nat := 4983230072969 + 3 ^ 40 * 560151 * 2
def baseEnd_560151 : Nat := 287626702096743140336419

theorem tailTrace_560151 : CollatzResearch.WordTrace tailWord_560151 prefixEnd_560151 287626702096743140336419 := by
  unfold tailWord_560151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20430385393676068019536307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13620256929117378679690871 20430385393676068019536307)
  ·
    refine ⟨30645578090514102029304461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20430385393676068019536307 30645578090514102029304461)
    ·
      refine ⟨11492091783942788260989173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30645578090514102029304461 11492091783942788260989173)
      ·
        refine ⟨1077383604744636399467735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11492091783942788260989173 1077383604744636399467735)
        ·
          refine ⟨1616075407116954599201603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077383604744636399467735 1616075407116954599201603)
          ·
            refine ⟨2424113110675431898802405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616075407116954599201603 2424113110675431898802405)
            ·
              refine ⟨454521208251643481025451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2424113110675431898802405 454521208251643481025451)
              ·
                refine ⟨681781812377465221538177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454521208251643481025451 681781812377465221538177)
                ·
                  refine ⟨511336359283098916153633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 681781812377465221538177 511336359283098916153633)
                  ·
                    refine ⟨383502269462324187115225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511336359283098916153633 383502269462324187115225)
                    ·
                      refine ⟨287626702096743140336419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383502269462324187115225 287626702096743140336419)
                      ·
                        rfl

theorem cell23_560151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_560151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560151 prefixEnd_560151 := by exact prefixLift 560151
  have htrace : WordTrace (prefixWord ++ tailWord_560151) baseStart_560151 baseEnd_560151 := by
    simpa [prefixWord, tailWord_560151, baseEnd_560151] using wordTrace_append hprefix tailTrace_560151
  have hstable : (prefixWord ++ tailWord_560151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560151).length < 2 ^ (prefixWord ++ tailWord_560151).sum := by decide
  have hdescent : baseEnd_560151 < baseStart_560151 := by decide
  rcases family_descends (prefixWord ++ tailWord_560151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560200 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_560200 : Nat := 118140960795 + 560200 * 2 ^ 59
def prefixEnd_560200 : Nat := 4983230072969 + 3 ^ 40 * 560200 * 2
def baseEnd_560200 : Nat := 95883954216271149541231

theorem tailTrace_560200 : CollatzResearch.WordTrace tailWord_560200 prefixEnd_560200 95883954216271149541231 := by
  unfold tailWord_560200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10216086285249274694035027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13621448380332366258713369 10216086285249274694035027)
  ·
    refine ⟨15324129427873912041052541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10216086285249274694035027 15324129427873912041052541)
    ·
      refine ⟨5746548535452717015394703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15324129427873912041052541 5746548535452717015394703)
      ·
        refine ⟨8619822803179075523092055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746548535452717015394703 8619822803179075523092055)
        ·
          refine ⟨12929734204768613284638083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619822803179075523092055 12929734204768613284638083)
          ·
            refine ⟨19394601307152919926957125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12929734204768613284638083 19394601307152919926957125)
            ·
              refine ⟨3636487745091172486304461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19394601307152919926957125 3636487745091172486304461)
              ·
                refine ⟨1363682904409189682364173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3636487745091172486304461 1363682904409189682364173)
                ·
                  refine ⟨511381089153446130886565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1363682904409189682364173 511381089153446130886565)
                  ·
                    refine ⟨95883954216271149541231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511381089153446130886565 95883954216271149541231)
                    ·
                      rfl

theorem cell23_560200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_560200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560200 prefixEnd_560200 := by exact prefixLift 560200
  have htrace : WordTrace (prefixWord ++ tailWord_560200) baseStart_560200 baseEnd_560200 := by
    simpa [prefixWord, tailWord_560200, baseEnd_560200] using wordTrace_append hprefix tailTrace_560200
  have hstable : (prefixWord ++ tailWord_560200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560200).length < 2 ^ (prefixWord ++ tailWord_560200).sum := by decide
  have hdescent : baseEnd_560200 < baseStart_560200 := by decide
  rcases family_descends (prefixWord ++ tailWord_560200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560221 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_560221 : Nat := 118140960795 + 560221 * 2 ^ 59
def prefixEnd_560221 : Nat := 4983230072969 + 3 ^ 40 * 560221 * 2
def baseEnd_560221 : Nat := 95887548580852622153699

theorem tailTrace_560221 : CollatzResearch.WordTrace tailWord_560221 prefixEnd_560221 95887548580852622153699 := by
  unfold tailWord_560221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20432938503422469974584517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13621959002281646649723011 20432938503422469974584517)
  ·
    refine ⟨3831175969391713120234597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20432938503422469974584517 3831175969391713120234597)
    ·
      refine ⟨718345494260946210043987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3831175969391713120234597 718345494260946210043987)
      ·
        refine ⟨1077518241391419315065981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718345494260946210043987 1077518241391419315065981)
        ·
          refine ⟨404069340521782243149743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1077518241391419315065981 404069340521782243149743)
          ·
            refine ⟨606104010782673364724615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404069340521782243149743 606104010782673364724615)
            ·
              refine ⟨909156016174010047086923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606104010782673364724615 909156016174010047086923)
              ·
                refine ⟨1363734024261015070630385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909156016174010047086923 1363734024261015070630385)
                ·
                  refine ⟨1022800518195761302972789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363734024261015070630385 1022800518195761302972789)
                  ·
                    refine ⟨95887548580852622153699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1022800518195761302972789 95887548580852622153699)
                    ·
                      rfl

theorem cell23_560221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_560221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560221 prefixEnd_560221 := by exact prefixLift 560221
  have htrace : WordTrace (prefixWord ++ tailWord_560221) baseStart_560221 baseEnd_560221 := by
    simpa [prefixWord, tailWord_560221, baseEnd_560221] using wordTrace_append hprefix tailTrace_560221
  have hstable : (prefixWord ++ tailWord_560221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560221).length < 2 ^ (prefixWord ++ tailWord_560221).sum := by decide
  have hdescent : baseEnd_560221 < baseStart_560221 := by decide
  rcases family_descends (prefixWord ++ tailWord_560221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560234 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_560234 : Nat := 118140960795 + 560234 * 2 ^ 59
def prefixEnd_560234 : Nat := 4983230072969 + 3 ^ 40 * 560234 * 2
def baseEnd_560234 : Nat := 95889773663688771866179

theorem tailTrace_560234 : CollatzResearch.WordTrace tailWord_560234 prefixEnd_560234 95889773663688771866179 := by
  unfold tailWord_560234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108353163093843298701939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13622275101583582129871837 5108353163093843298701939)
  ·
    refine ⟨7662529744640764948052909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108353163093843298701939 7662529744640764948052909)
    ·
      refine ⟨2873448654240286855519841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7662529744640764948052909 2873448654240286855519841)
      ·
        refine ⟨2155086490680215141639881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2873448654240286855519841 2155086490680215141639881)
        ·
          refine ⟨1616314868010161356229911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155086490680215141639881 1616314868010161356229911)
          ·
            refine ⟨2424472302015242034344867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616314868010161356229911 2424472302015242034344867)
            ·
              refine ⟨3636708453022863051517301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424472302015242034344867 3636708453022863051517301)
              ·
                refine ⟨340941417470893411079747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3636708453022863051517301 340941417470893411079747)
                ·
                  refine ⟨511412126206340116619621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340941417470893411079747 511412126206340116619621)
                  ·
                    refine ⟨95889773663688771866179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511412126206340116619621 95889773663688771866179)
                    ·
                      rfl

theorem cell23_560234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_560234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560234 prefixEnd_560234 := by exact prefixLift 560234
  have htrace : WordTrace (prefixWord ++ tailWord_560234) baseStart_560234 baseEnd_560234 := by
    simpa [prefixWord, tailWord_560234, baseEnd_560234] using wordTrace_append hprefix tailTrace_560234
  have hstable : (prefixWord ++ tailWord_560234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560234).length < 2 ^ (prefixWord ++ tailWord_560234).sum := by decide
  have hdescent : baseEnd_560234 < baseStart_560234 := by decide
  rcases family_descends (prefixWord ++ tailWord_560234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560264 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 6]
def baseStart_560264 : Nat := 118140960795 + 560264 * 2 ^ 59
def prefixEnd_560264 : Nat := 4983230072969 + 3 ^ 40 * 560264 * 2
def baseEnd_560264 : Nat := 31964969490077910913711

theorem tailTrace_560264 : CollatzResearch.WordTrace tailWord_560264 prefixEnd_560264 31964969490077910913711 := by
  unfold tailWord_560264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217253421133344159199923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13623004561511125545599897 10217253421133344159199923)
  ·
    refine ⟨15325880131700016238799885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217253421133344159199923 15325880131700016238799885)
    ·
      refine ⟨5747205049387506089549957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15325880131700016238799885 5747205049387506089549957)
      ·
        refine ⟨1077600946760157391790617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5747205049387506089549957 1077600946760157391790617)
        ·
          refine ⟨808200710070118043842963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077600946760157391790617 808200710070118043842963)
          ·
            refine ⟨1212301065105177065764445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808200710070118043842963 1212301065105177065764445)
            ·
              refine ⟨454612899414441399661667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212301065105177065764445 454612899414441399661667)
              ·
                refine ⟨681919349121662099492501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454612899414441399661667 681919349121662099492501)
                ·
                  refine ⟨31964969490077910913711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 681919349121662099492501 31964969490077910913711)
                  ·
                    rfl

theorem cell23_560264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_560264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560264 prefixEnd_560264 := by exact prefixLift 560264
  have htrace : WordTrace (prefixWord ++ tailWord_560264) baseStart_560264 baseEnd_560264 := by
    simpa [prefixWord, tailWord_560264, baseEnd_560264] using wordTrace_append hprefix tailTrace_560264
  have hstable : (prefixWord ++ tailWord_560264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560264).length < 2 ^ (prefixWord ++ tailWord_560264).sum := by decide
  have hdescent : baseEnd_560264 < baseStart_560264 := by decide
  rcases family_descends (prefixWord ++ tailWord_560264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560274 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_560274 : Nat := 118140960795 + 560274 * 2 ^ 59
def prefixEnd_560274 : Nat := 4983230072969 + 3 ^ 40 * 560274 * 2
def baseEnd_560274 : Nat := 287689860217246159098353

theorem tailTrace_560274 : CollatzResearch.WordTrace tailWord_560274 prefixEnd_560274 287689860217246159098353 := by
  unfold tailWord_560274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108717893057615006565969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13623247714820306684175917 5108717893057615006565969)
  ·
    refine ⟨3831538419793211254924477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5108717893057615006565969 3831538419793211254924477)
    ·
      refine ⟨1436826907422454220596679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3831538419793211254924477 1436826907422454220596679)
      ·
        refine ⟨2155240361133681330895019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436826907422454220596679 2155240361133681330895019)
        ·
          refine ⟨3232860541700521996342529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155240361133681330895019 3232860541700521996342529)
          ·
            refine ⟨2424645406275391497256897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232860541700521996342529 2424645406275391497256897)
            ·
              refine ⟨1818484054706543622942673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424645406275391497256897 1818484054706543622942673)
              ·
                refine ⟨1363863041029907717207005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818484054706543622942673 1363863041029907717207005)
                ·
                  refine ⟨511448640386215393952627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1363863041029907717207005 511448640386215393952627)
                  ·
                    refine ⟨767172960579323090928941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511448640386215393952627 767172960579323090928941)
                    ·
                      refine ⟨287689860217246159098353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767172960579323090928941 287689860217246159098353)
                      ·
                        rfl

theorem cell23_560274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_560274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560274 prefixEnd_560274 := by exact prefixLift 560274
  have htrace : WordTrace (prefixWord ++ tailWord_560274) baseStart_560274 baseEnd_560274 := by
    simpa [prefixWord, tailWord_560274, baseEnd_560274] using wordTrace_append hprefix tailTrace_560274
  have hstable : (prefixWord ++ tailWord_560274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560274).length < 2 ^ (prefixWord ++ tailWord_560274).sum := by decide
  have hdescent : baseEnd_560274 < baseStart_560274 := by decide
  rcases family_descends (prefixWord ++ tailWord_560274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560283 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_560283 : Nat := 118140960795 + 560283 * 2 ^ 59
def prefixEnd_560283 : Nat := 4983230072969 + 3 ^ 40 * 560283 * 2
def baseEnd_560283 : Nat := 287694481543136623885811

theorem tailTrace_560283 : CollatzResearch.WordTrace tailWord_560283 prefixEnd_560283 287694481543136623885811 := by
  unfold tailWord_560283
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435199829197854563341503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13623466552798569708894335 20435199829197854563341503)
  ·
    refine ⟨30652799743796781845012255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20435199829197854563341503 30652799743796781845012255)
    ·
      refine ⟨45979199615695172767518383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30652799743796781845012255 45979199615695172767518383)
      ·
        refine ⟨68968799423542759151277575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45979199615695172767518383 68968799423542759151277575)
        ·
          refine ⟨103453199135314138726916363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68968799423542759151277575 103453199135314138726916363)
          ·
            refine ⟨155179798702971208090374545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103453199135314138726916363 155179798702971208090374545)
            ·
              refine ⟨116384849027228406067780909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155179798702971208090374545 116384849027228406067780909)
              ·
                refine ⟨43644318385210652275417841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116384849027228406067780909 43644318385210652275417841)
                ·
                  refine ⟨32733238788907989206563381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43644318385210652275417841 32733238788907989206563381)
                  ·
                    refine ⟨3068741136460123988115317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32733238788907989206563381 3068741136460123988115317)
                    ·
                      refine ⟨287694481543136623885811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3068741136460123988115317 287694481543136623885811)
                      ·
                        rfl

theorem cell23_560283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_560283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560283 prefixEnd_560283 := by exact prefixLift 560283
  have htrace : WordTrace (prefixWord ++ tailWord_560283) baseStart_560283 baseEnd_560283 := by
    simpa [prefixWord, tailWord_560283, baseEnd_560283] using wordTrace_append hprefix tailTrace_560283
  have hstable : (prefixWord ++ tailWord_560283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560283).length < 2 ^ (prefixWord ++ tailWord_560283).sum := by decide
  have hdescent : baseEnd_560283 < baseStart_560283 := by decide
  rcases family_descends (prefixWord ++ tailWord_560283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560301 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_560301 : Nat := 118140960795 + 560301 * 2 ^ 59
def prefixEnd_560301 : Nat := 4983230072969 + 3 ^ 40 * 560301 * 2
def baseEnd_560301 : Nat := 287703724194917553460729

theorem tailTrace_560301 : CollatzResearch.WordTrace tailWord_560301 prefixEnd_560301 287703724194917553460729 := by
  unfold tailWord_560301
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435856343132643637496757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13623904228755095758331171 20435856343132643637496757)
  ·
    refine ⟨1915861532168685341015321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20435856343132643637496757 1915861532168685341015321)
    ·
      refine ⟨1436896149126514005761491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1915861532168685341015321 1436896149126514005761491)
      ·
        refine ⟨2155344223689771008642237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436896149126514005761491 2155344223689771008642237)
        ·
          refine ⟨808254083883664128240839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2155344223689771008642237 808254083883664128240839)
          ·
            refine ⟨1212381125825496192361259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808254083883664128240839 1212381125825496192361259)
            ·
              refine ⟨1818571688738244288541889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212381125825496192361259 1818571688738244288541889)
              ·
                refine ⟨1363928766553683216406417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818571688738244288541889 1363928766553683216406417)
                ·
                  refine ⟨1022946574915262412304813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363928766553683216406417 1022946574915262412304813)
                  ·
                    refine ⟨383604965593223404614305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022946574915262412304813 383604965593223404614305)
                    ·
                      refine ⟨287703724194917553460729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383604965593223404614305 287703724194917553460729)
                      ·
                        rfl

theorem cell23_560301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_560301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560301 prefixEnd_560301 := by exact prefixLift 560301
  have htrace : WordTrace (prefixWord ++ tailWord_560301) baseStart_560301 baseEnd_560301 := by
    simpa [prefixWord, tailWord_560301, baseEnd_560301] using wordTrace_append hprefix tailTrace_560301
  have hstable : (prefixWord ++ tailWord_560301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560301).length < 2 ^ (prefixWord ++ tailWord_560301).sum := by decide
  have hdescent : baseEnd_560301 < baseStart_560301 := by decide
  rcases family_descends (prefixWord ++ tailWord_560301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560303 : List Nat := [1, 1, 2, 1, 2, 3, 13]
def baseStart_560303 : Nat := 118140960795 + 560303 * 2 ^ 59
def prefixEnd_560303 : Nat := 4983230072969 + 3 ^ 40 * 560303 * 2
def baseEnd_560303 : Nat := 3551910508101562291799

theorem tailTrace_560303 : CollatzResearch.WordTrace tailWord_560303 prefixEnd_560303 3551910508101562291799 := by
  unfold tailWord_560303
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435929289125397979069563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13623952859416931986046375 20435929289125397979069563)
  ·
    refine ⟨30653893933688096968604345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20435929289125397979069563 30653893933688096968604345)
    ·
      refine ⟨22990420450266072726453259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30653893933688096968604345 22990420450266072726453259)
      ·
        refine ⟨34485630675399109089679889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22990420450266072726453259 34485630675399109089679889)
        ·
          refine ⟨25864223006549331817259917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34485630675399109089679889 25864223006549331817259917)
          ·
            refine ⟨9699083627455999431472469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25864223006549331817259917 9699083627455999431472469)
            ·
              refine ⟨3551910508101562291799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 9699083627455999431472469 3551910508101562291799)
              ·
                rfl

theorem cell23_560303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 13].length) (baseStart_560303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560303 prefixEnd_560303 := by exact prefixLift 560303
  have htrace : WordTrace (prefixWord ++ tailWord_560303) baseStart_560303 baseEnd_560303 := by
    simpa [prefixWord, tailWord_560303, baseEnd_560303] using wordTrace_append hprefix tailTrace_560303
  have hstable : (prefixWord ++ tailWord_560303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560303).length < 2 ^ (prefixWord ++ tailWord_560303).sum := by decide
  have hdescent : baseEnd_560303 < baseStart_560303 := by decide
  rcases family_descends (prefixWord ++ tailWord_560303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560334 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_560334 : Nat := 118140960795 + 560334 * 2 ^ 59
def prefixEnd_560334 : Nat := 4983230072969 + 3 ^ 40 * 560334 * 2
def baseEnd_560334 : Nat := 287720669056515924348077

theorem tailTrace_560334 : CollatzResearch.WordTrace tailWord_560334 prefixEnd_560334 287720669056515924348077 := by
  unfold tailWord_560334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554632494001636284181007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13624706634675393515632037 2554632494001636284181007)
  ·
    refine ⟨3831948741002454426271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2554632494001636284181007 3831948741002454426271511)
    ·
      refine ⟨5747923111503681639407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831948741002454426271511 5747923111503681639407267)
      ·
        refine ⟨8621884667255522459110901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747923111503681639407267 8621884667255522459110901)
        ·
          refine ⟨808301687555205230541647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8621884667255522459110901 808301687555205230541647)
          ·
            refine ⟨1212452531332807845812471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808301687555205230541647 1212452531332807845812471)
            ·
              refine ⟨1818678796999211768718707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212452531332807845812471 1818678796999211768718707)
              ·
                refine ⟨2728018195498817653078061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818678796999211768718707 2728018195498817653078061)
                ·
                  refine ⟨1023006823312056619904273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2728018195498817653078061 1023006823312056619904273)
                  ·
                    refine ⟨767255117484042464928205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023006823312056619904273 767255117484042464928205)
                    ·
                      refine ⟨287720669056515924348077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767255117484042464928205 287720669056515924348077)
                      ·
                        rfl

theorem cell23_560334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_560334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560334 prefixEnd_560334 := by exact prefixLift 560334
  have htrace : WordTrace (prefixWord ++ tailWord_560334) baseStart_560334 baseEnd_560334 := by
    simpa [prefixWord, tailWord_560334, baseEnd_560334] using wordTrace_append hprefix tailTrace_560334
  have hstable : (prefixWord ++ tailWord_560334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560334).length < 2 ^ (prefixWord ++ tailWord_560334).sum := by decide
  have hdescent : baseEnd_560334 < baseStart_560334 := by decide
  rcases family_descends (prefixWord ++ tailWord_560334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560364 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_560364 : Nat := 118140960795 + 560364 * 2 ^ 59
def prefixEnd_560364 : Nat := 4983230072969 + 3 ^ 40 * 560364 * 2
def baseEnd_560364 : Nat := 287736073476150806972939

theorem tailTrace_560364 : CollatzResearch.WordTrace tailWord_560364 prefixEnd_560364 287736073476150806972939 := by
  unfold tailWord_560364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219077070952202698520073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13625436094602936931360097 10219077070952202698520073)
  ·
    refine ⟨7664307803214152023890055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10219077070952202698520073 7664307803214152023890055)
    ·
      refine ⟨11496461704821228035835083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7664307803214152023890055 11496461704821228035835083)
      ·
        refine ⟨17244692557231842053752625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11496461704821228035835083 17244692557231842053752625)
        ·
          refine ⟨12933519417923881540314469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17244692557231842053752625 12933519417923881540314469)
          ·
            refine ⟨2425034890860727788808963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12933519417923881540314469 2425034890860727788808963)
            ·
              refine ⟨3637552336291091683213445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425034890860727788808963 3637552336291091683213445)
              ·
                refine ⟨682041063054579690602521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3637552336291091683213445 682041063054579690602521)
                ·
                  refine ⟨511530797290934767951891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682041063054579690602521 511530797290934767951891)
                  ·
                    refine ⟨767296195936402151927837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511530797290934767951891 767296195936402151927837)
                    ·
                      refine ⟨287736073476150806972939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767296195936402151927837 287736073476150806972939)
                      ·
                        rfl

theorem cell23_560364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_560364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560364 prefixEnd_560364 := by exact prefixLift 560364
  have htrace : WordTrace (prefixWord ++ tailWord_560364) baseStart_560364 baseEnd_560364 := by
    simpa [prefixWord, tailWord_560364, baseEnd_560364] using wordTrace_append hprefix tailTrace_560364
  have hstable : (prefixWord ++ tailWord_560364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560364).length < 2 ^ (prefixWord ++ tailWord_560364).sum := by decide
  have hdescent : baseEnd_560364 < baseStart_560364 := by decide
  rcases family_descends (prefixWord ++ tailWord_560364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560365 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_560365 : Nat := 118140960795 + 560365 * 2 ^ 59
def prefixEnd_560365 : Nat := 4983230072969 + 3 ^ 40 * 560365 * 2
def baseEnd_560365 : Nat := 287736586956805303060435

theorem tailTrace_560365 : CollatzResearch.WordTrace tailWord_560365 prefixEnd_560365 287736586956805303060435 := by
  unfold tailWord_560365
  simp only [CollatzResearch.WordTrace]
  refine ⟨20438190614900782567826549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13625460409933855045217699 20438190614900782567826549)
  ·
    refine ⟨1916080370146948365733739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20438190614900782567826549 1916080370146948365733739)
    ·
      refine ⟨2874120555220422548600609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916080370146948365733739 2874120555220422548600609)
      ·
        refine ⟨2155590416415316911450457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2874120555220422548600609 2155590416415316911450457)
        ·
          refine ⟨1616692812311487683587843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155590416415316911450457 1616692812311487683587843)
          ·
            refine ⟨2425039218467231525381765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616692812311487683587843 2425039218467231525381765)
            ·
              refine ⟨454694853462605911009081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2425039218467231525381765 454694853462605911009081)
              ·
                refine ⟨341021140096954433256811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454694853462605911009081 341021140096954433256811)
                ·
                  refine ⟨511531710145431649885217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341021140096954433256811 511531710145431649885217)
                  ·
                    refine ⟨383648782609073737413913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511531710145431649885217 383648782609073737413913)
                    ·
                      refine ⟨287736586956805303060435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383648782609073737413913 287736586956805303060435)
                      ·
                        rfl

theorem cell23_560365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_560365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560365 prefixEnd_560365 := by exact prefixLift 560365
  have htrace : WordTrace (prefixWord ++ tailWord_560365) baseStart_560365 baseEnd_560365 := by
    simpa [prefixWord, tailWord_560365, baseEnd_560365] using wordTrace_append hprefix tailTrace_560365
  have hstable : (prefixWord ++ tailWord_560365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560365).length < 2 ^ (prefixWord ++ tailWord_560365).sum := by decide
  have hdescent : baseEnd_560365 < baseStart_560365 := by decide
  rcases family_descends (prefixWord ++ tailWord_560365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560402 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_560402 : Nat := 118140960795 + 560402 * 2 ^ 59
def prefixEnd_560402 : Nat := 4983230072969 + 3 ^ 40 * 560402 * 2
def baseEnd_560402 : Nat := 287755585741021658297765

theorem tailTrace_560402 : CollatzResearch.WordTrace tailWord_560402 prefixEnd_560402 287755585741021658297765 := by
  unfold tailWord_560402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109885028941684471730865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13626360077177825257948973 5109885028941684471730865)
  ·
    refine ⟨3832413771706263353798149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5109885028941684471730865 3832413771706263353798149)
    ·
      refine ⟨718577582194924378837153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3832413771706263353798149 718577582194924378837153)
      ·
        refine ⟨538933186646193284127865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718577582194924378837153 538933186646193284127865)
        ·
          refine ⟨404199889984644963095899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538933186646193284127865 404199889984644963095899)
          ·
            refine ⟨606299834976967444643849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404199889984644963095899 606299834976967444643849)
            ·
              refine ⟨454724876232725583482887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606299834976967444643849 454724876232725583482887)
              ·
                refine ⟨682087314349088375224331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454724876232725583482887 682087314349088375224331)
                ·
                  refine ⟨1023130971523632562836497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682087314349088375224331 1023130971523632562836497)
                  ·
                    refine ⟨767348228642724422127373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023130971523632562836497 767348228642724422127373)
                    ·
                      refine ⟨287755585741021658297765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767348228642724422127373 287755585741021658297765)
                      ·
                        rfl

theorem cell23_560402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_560402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560402 prefixEnd_560402 := by exact prefixLift 560402
  have htrace : WordTrace (prefixWord ++ tailWord_560402) baseStart_560402 baseEnd_560402 := by
    simpa [prefixWord, tailWord_560402, baseEnd_560402] using wordTrace_append hprefix tailTrace_560402
  have hstable : (prefixWord ++ tailWord_560402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560402).length < 2 ^ (prefixWord ++ tailWord_560402).sum := by decide
  have hdescent : baseEnd_560402 < baseStart_560402 := by decide
  rcases family_descends (prefixWord ++ tailWord_560402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560408 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_560408 : Nat := 118140960795 + 560408 * 2 ^ 59
def prefixEnd_560408 : Nat := 4983230072969 + 3 ^ 40 * 560408 * 2
def baseEnd_560408 : Nat := 287758666624948634822737

theorem tailTrace_560408 : CollatzResearch.WordTrace tailWord_560408 prefixEnd_560408 287758666624948634822737 := by
  unfold tailWord_560408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219879476872500455820939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13626505969163333941094585 10219879476872500455820939)
  ·
    refine ⟨15329819215308750683731409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10219879476872500455820939 15329819215308750683731409)
    ·
      refine ⟨11497364411481563012798557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15329819215308750683731409 11497364411481563012798557)
      ·
        refine ⟨4311511654305586129799459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11497364411481563012798557 4311511654305586129799459)
        ·
          refine ⟨6467267481458379194699189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311511654305586129799459 6467267481458379194699189)
          ·
            refine ⟨606306326386723049503049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6467267481458379194699189 606306326386723049503049)
            ·
              refine ⟨454729744790042287127287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606306326386723049503049 454729744790042287127287)
              ·
                refine ⟨682094617185063430690931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454729744790042287127287 682094617185063430690931)
                ·
                  refine ⟨1023141925777595146036397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682094617185063430690931 1023141925777595146036397)
                  ·
                    refine ⟨383678222166598179763649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023141925777595146036397 383678222166598179763649)
                    ·
                      refine ⟨287758666624948634822737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383678222166598179763649 287758666624948634822737)
                      ·
                        rfl

theorem cell23_560408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_560408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560408 prefixEnd_560408 := by exact prefixLift 560408
  have htrace : WordTrace (prefixWord ++ tailWord_560408) baseStart_560408 baseEnd_560408 := by
    simpa [prefixWord, tailWord_560408, baseEnd_560408] using wordTrace_append hprefix tailTrace_560408
  have hstable : (prefixWord ++ tailWord_560408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560408).length < 2 ^ (prefixWord ++ tailWord_560408).sum := by decide
  have hdescent : baseEnd_560408 < baseStart_560408 := by decide
  rcases family_descends (prefixWord ++ tailWord_560408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560421 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_560421 : Nat := 118140960795 + 560421 * 2 ^ 59
def prefixEnd_560421 : Nat := 4983230072969 + 3 ^ 40 * 560421 * 2
def baseEnd_560421 : Nat := 287765341873457083960177

theorem tailTrace_560421 : CollatzResearch.WordTrace tailWord_560421 prefixEnd_560421 287765341873457083960177 := by
  unfold tailWord_560421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20440233102697904131865117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13626822068465269421243411 20440233102697904131865117)
  ·
    refine ⟨7665087413511714049449419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20440233102697904131865117 7665087413511714049449419)
    ·
      refine ⟨11497631120267571074174129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665087413511714049449419 11497631120267571074174129)
      ·
        refine ⟨8623223340200678305630597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11497631120267571074174129 8623223340200678305630597)
        ·
          refine ⟨1616854376287627182305737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8623223340200678305630597 1616854376287627182305737)
          ·
            refine ⟨1212640782215720386729303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616854376287627182305737 1212640782215720386729303)
            ·
              refine ⟨1818961173323580580093955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212640782215720386729303 1818961173323580580093955)
              ·
                refine ⟨2728441759985370870140933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818961173323580580093955 2728441759985370870140933)
                ·
                  refine ⟨511582829997257038151425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2728441759985370870140933 511582829997257038151425)
                  ·
                    refine ⟨383687122497942778613569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511582829997257038151425 383687122497942778613569)
                    ·
                      refine ⟨287765341873457083960177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383687122497942778613569 287765341873457083960177)
                      ·
                        rfl

theorem cell23_560421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_560421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560421 prefixEnd_560421 := by exact prefixLift 560421
  have htrace : WordTrace (prefixWord ++ tailWord_560421) baseStart_560421 baseEnd_560421 := by
    simpa [prefixWord, tailWord_560421, baseEnd_560421] using wordTrace_append hprefix tailTrace_560421
  have hstable : (prefixWord ++ tailWord_560421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560421).length < 2 ^ (prefixWord ++ tailWord_560421).sum := by decide
  have hdescent : baseEnd_560421 < baseStart_560421 := by decide
  rcases family_descends (prefixWord ++ tailWord_560421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560497 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_560497 : Nat := 118140960795 + 560497 * 2 ^ 59
def prefixEnd_560497 : Nat := 4983230072969 + 3 ^ 40 * 560497 * 2
def baseEnd_560497 : Nat := 287804366403198786609827

theorem tailTrace_560497 : CollatzResearch.WordTrace tailWord_560497 prefixEnd_560497 287804366403198786609827 := by
  unfold tailWord_560497
  simp only [CollatzResearch.WordTrace]
  refine ⟨20443005050422569111631745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13628670033615046074421163 20443005050422569111631745)
  ·
    refine ⟨15332253787816926833723809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20443005050422569111631745 15332253787816926833723809)
    ·
      refine ⟨11499190340862695125292857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15332253787816926833723809 11499190340862695125292857)
      ·
        refine ⟨8624392755647021343969643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11499190340862695125292857 8624392755647021343969643)
        ·
          refine ⟨12936589133470532015954465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624392755647021343969643 12936589133470532015954465)
          ·
            refine ⟨9702441850102899011965849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936589133470532015954465 9702441850102899011965849)
            ·
              refine ⟨7276831387577174258974387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9702441850102899011965849 7276831387577174258974387)
              ·
                refine ⟨10915247081365761388461581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7276831387577174258974387 10915247081365761388461581)
                ·
                  refine ⟨4093217655512160520673093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10915247081365761388461581 4093217655512160520673093)
                  ·
                    refine ⟨767478310408530097626205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093217655512160520673093 767478310408530097626205)
                    ·
                      refine ⟨287804366403198786609827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767478310408530097626205 287804366403198786609827)
                      ·
                        rfl

theorem cell23_560497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_560497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560497 prefixEnd_560497 := by exact prefixLift 560497
  have htrace : WordTrace (prefixWord ++ tailWord_560497) baseStart_560497 baseEnd_560497 := by
    simpa [prefixWord, tailWord_560497, baseEnd_560497] using wordTrace_append hprefix tailTrace_560497
  have hstable : (prefixWord ++ tailWord_560497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560497).length < 2 ^ (prefixWord ++ tailWord_560497).sum := by decide
  have hdescent : baseEnd_560497 < baseStart_560497 := by decide
  rcases family_descends (prefixWord ++ tailWord_560497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560547 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 5, 5]
def baseStart_560547 : Nat := 118140960795 + 560547 * 2 ^ 59
def prefixEnd_560547 : Nat := 4983230072969 + 3 ^ 40 * 560547 * 2
def baseEnd_560547 : Nat := 95943346811974530328199

theorem tailTrace_560547 : CollatzResearch.WordTrace tailWord_560547 prefixEnd_560547 95943346811974530328199 := by
  unfold tailWord_560547
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444828700241427650951895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13629885800160951767301263 20444828700241427650951895)
  ·
    refine ⟨30667243050362141476427843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20444828700241427650951895 30667243050362141476427843)
    ·
      refine ⟨46000864575543212214641765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30667243050362141476427843 46000864575543212214641765)
      ·
        refine ⟨8625162107914352290245331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46000864575543212214641765 8625162107914352290245331)
        ·
          refine ⟨12937743161871528435367997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8625162107914352290245331 12937743161871528435367997)
          ·
            refine ⟨4851653685701823163262999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12937743161871528435367997 4851653685701823163262999)
            ·
              refine ⟨7277480528552734744894499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851653685701823163262999 7277480528552734744894499)
              ·
                refine ⟨10916220792829102117341749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277480528552734744894499 10916220792829102117341749)
                ·
                  refine ⟨1023395699327728323500789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10916220792829102117341749 1023395699327728323500789)
                  ·
                    refine ⟨95943346811974530328199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1023395699327728323500789 95943346811974530328199)
                    ·
                      rfl

theorem cell23_560547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].length) (baseStart_560547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560547 prefixEnd_560547 := by exact prefixLift 560547
  have htrace : WordTrace (prefixWord ++ tailWord_560547) baseStart_560547 baseEnd_560547 := by
    simpa [prefixWord, tailWord_560547, baseEnd_560547] using wordTrace_append hprefix tailTrace_560547
  have hstable : (prefixWord ++ tailWord_560547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560547).length < 2 ^ (prefixWord ++ tailWord_560547).sum := by decide
  have hdescent : baseEnd_560547 < baseStart_560547 := by decide
  rcases family_descends (prefixWord ++ tailWord_560547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560561 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_560561 : Nat := 118140960795 + 560561 * 2 ^ 59
def prefixEnd_560561 : Nat := 4983230072969 + 3 ^ 40 * 560561 * 2
def baseEnd_560561 : Nat := 287837229165086536209533

theorem tailTrace_560561 : CollatzResearch.WordTrace tailWord_560561 prefixEnd_560561 287837229165086536209533 := by
  unfold tailWord_560561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445339322190708041961537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13630226214793805361307691 20445339322190708041961537)
  ·
    refine ⟨15334004491643031031471153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20445339322190708041961537 15334004491643031031471153)
    ·
      refine ⟨11500503368732273273603365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15334004491643031031471153 11500503368732273273603365)
      ·
        refine ⟨2156344381637301238800631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11500503368732273273603365 2156344381637301238800631)
        ·
          refine ⟨3234516572455951858200947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156344381637301238800631 3234516572455951858200947)
          ·
            refine ⟨4851774858683927787301421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234516572455951858200947 4851774858683927787301421)
            ·
              refine ⟨1819415572006472920238033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4851774858683927787301421 1819415572006472920238033)
              ·
                refine ⟨1364561679004854690178525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819415572006472920238033 1364561679004854690178525)
                ·
                  refine ⟨511710629626820508816947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1364561679004854690178525 511710629626820508816947)
                  ·
                    refine ⟨767565944440230763225421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511710629626820508816947 767565944440230763225421)
                    ·
                      refine ⟨287837229165086536209533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767565944440230763225421 287837229165086536209533)
                      ·
                        rfl

theorem cell23_560561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_560561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560561 prefixEnd_560561 := by exact prefixLift 560561
  have htrace : WordTrace (prefixWord ++ tailWord_560561) baseStart_560561 baseEnd_560561 := by
    simpa [prefixWord, tailWord_560561, baseEnd_560561] using wordTrace_append hprefix tailTrace_560561
  have hstable : (prefixWord ++ tailWord_560561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560561).length < 2 ^ (prefixWord ++ tailWord_560561).sum := by decide
  have hdescent : baseEnd_560561 < baseStart_560561 := by decide
  rcases family_descends (prefixWord ++ tailWord_560561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560607 : List Nat := [1, 1, 2, 3, 3, 1, 2, 10]
def baseStart_560607 : Nat := 118140960795 + 560607 * 2 ^ 59
def prefixEnd_560607 : Nat := 4983230072969 + 3 ^ 40 * 560607 * 2
def baseEnd_560607 : Nat := 10661512936118272453123

theorem tailTrace_560607 : CollatzResearch.WordTrace tailWord_560607 prefixEnd_560607 10661512936118272453123 := by
  unfold tailWord_560607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447017080024057898136075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13631344720016038598757383 20447017080024057898136075)
  ·
    refine ⟨30670525620036086847204113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447017080024057898136075 30670525620036086847204113)
    ·
      refine ⟨23002894215027065135403085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30670525620036086847204113 23002894215027065135403085)
      ·
        refine ⟨8626085330635149425776157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23002894215027065135403085 8626085330635149425776157)
        ·
          refine ⟨3234781998988181034666059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8626085330635149425776157 3234781998988181034666059)
          ·
            refine ⟨4852172998482271551999089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234781998988181034666059 4852172998482271551999089)
            ·
              refine ⟨3639129748861703663999317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4852172998482271551999089 3639129748861703663999317)
              ·
                refine ⟨10661512936118272453123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3639129748861703663999317 10661512936118272453123)
                ·
                  rfl

theorem cell23_560607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 10].length) (baseStart_560607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560607 prefixEnd_560607 := by exact prefixLift 560607
  have htrace : WordTrace (prefixWord ++ tailWord_560607) baseStart_560607 baseEnd_560607 := by
    simpa [prefixWord, tailWord_560607, baseEnd_560607] using wordTrace_append hprefix tailTrace_560607
  have hstable : (prefixWord ++ tailWord_560607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560607).length < 2 ^ (prefixWord ++ tailWord_560607).sum := by decide
  have hdescent : baseEnd_560607 < baseStart_560607 := by decide
  rcases family_descends (prefixWord ++ tailWord_560607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560611 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 6]
def baseStart_560611 : Nat := 118140960795 + 560611 * 2 ^ 59
def prefixEnd_560611 : Nat := 4983230072969 + 3 ^ 40 * 560611 * 2
def baseEnd_560611 : Nat := 95954301065937113528101

theorem tailTrace_560611 : CollatzResearch.WordTrace tailWord_560611 prefixEnd_560611 95954301065937113528101 := by
  unfold tailWord_560611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447162972009566581281687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13631441981339711054187791 20447162972009566581281687)
  ·
    refine ⟨30670744458014349871922531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447162972009566581281687 30670744458014349871922531)
    ·
      refine ⟨46006116687021524807883797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30670744458014349871922531 46006116687021524807883797)
      ·
        refine ⟨2156536719704133975369553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46006116687021524807883797 2156536719704133975369553)
        ·
          refine ⟨1617402539778100481527165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2156536719704133975369553 1617402539778100481527165)
          ·
            refine ⟨606525952416787680572687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1617402539778100481527165 606525952416787680572687)
            ·
              refine ⟨909788928625181520859031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606525952416787680572687 909788928625181520859031)
              ·
                refine ⟨1364683392937772281288547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909788928625181520859031 1364683392937772281288547)
                ·
                  refine ⟨2047025089406658421932821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364683392937772281288547 2047025089406658421932821)
                  ·
                    refine ⟨95954301065937113528101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2047025089406658421932821 95954301065937113528101)
                    ·
                      rfl

theorem cell23_560611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 6].length) (baseStart_560611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560611 prefixEnd_560611 := by exact prefixLift 560611
  have htrace : WordTrace (prefixWord ++ tailWord_560611) baseStart_560611 baseEnd_560611 := by
    simpa [prefixWord, tailWord_560611, baseEnd_560611] using wordTrace_append hprefix tailTrace_560611
  have hstable : (prefixWord ++ tailWord_560611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560611).length < 2 ^ (prefixWord ++ tailWord_560611).sum := by decide
  have hdescent : baseEnd_560611 < baseStart_560611 := by decide
  rcases family_descends (prefixWord ++ tailWord_560611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560618 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_560618 : Nat := 118140960795 + 560618 * 2 ^ 59
def prefixEnd_560618 : Nat := 4983230072969 + 3 ^ 40 * 560618 * 2
def baseEnd_560618 : Nat := 287866497562392813196771

theorem tailTrace_560618 : CollatzResearch.WordTrace tailWord_560618 prefixEnd_560618 287866497562392813196771 := by
  unfold tailWord_560618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111854570746051694196627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13631612188656137851191005 5111854570746051694196627)
  ·
    refine ⟨7667781856119077541294941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5111854570746051694196627 7667781856119077541294941)
    ·
      refine ⟨2875418196044654077985603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7667781856119077541294941 2875418196044654077985603)
      ·
        refine ⟨4313127294066981116978405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875418196044654077985603 4313127294066981116978405)
        ·
          refine ⟨808711367637558959433451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4313127294066981116978405 808711367637558959433451)
          ·
            refine ⟨1213067051456338439150177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808711367637558959433451 1213067051456338439150177)
            ·
              refine ⟨909800288592253829362633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213067051456338439150177 909800288592253829362633)
              ·
                refine ⟨682350216444190372021975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909800288592253829362633 682350216444190372021975)
                ·
                  refine ⟨1023525324666285558032963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682350216444190372021975 1023525324666285558032963)
                  ·
                    refine ⟨1535287986999428337049445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1023525324666285558032963 1535287986999428337049445)
                    ·
                      refine ⟨287866497562392813196771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1535287986999428337049445 287866497562392813196771)
                      ·
                        rfl

theorem cell23_560618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_560618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560618 prefixEnd_560618 := by exact prefixLift 560618
  have htrace : WordTrace (prefixWord ++ tailWord_560618) baseStart_560618 baseEnd_560618 := by
    simpa [prefixWord, tailWord_560618, baseEnd_560618] using wordTrace_append hprefix tailTrace_560618
  have hstable : (prefixWord ++ tailWord_560618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560618).length < 2 ^ (prefixWord ++ tailWord_560618).sum := by decide
  have hdescent : baseEnd_560618 < baseStart_560618 := by decide
  rcases family_descends (prefixWord ++ tailWord_560618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560624 : List Nat := [2, 1, 1, 1, 3, 4, 4, 7]
def baseStart_560624 : Nat := 118140960795 + 560624 * 2 ^ 59
def prefixEnd_560624 : Nat := 4983230072969 + 3 ^ 40 * 560624 * 2
def baseEnd_560624 : Nat := 10661836238752584804509

theorem tailTrace_560624 : CollatzResearch.WordTrace tailWord_560624 prefixEnd_560624 10661836238752584804509 := by
  unfold tailWord_560624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223818560481234900752463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13631758080641646534336617 10223818560481234900752463)
  ·
    refine ⟨15335727840721852351128695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10223818560481234900752463 15335727840721852351128695)
    ·
      refine ⟨23003591761082778526693043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15335727840721852351128695 23003591761082778526693043)
      ·
        refine ⟨34505387641624167790039565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23003591761082778526693043 34505387641624167790039565)
        ·
          refine ⟨12939520365609062921264837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34505387641624167790039565 12939520365609062921264837)
          ·
            refine ⟨2426160068551699297737157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12939520365609062921264837 2426160068551699297737157)
            ·
              refine ⟨454905012853443618325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2426160068551699297737157 454905012853443618325717)
              ·
                refine ⟨10661836238752584804509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 454905012853443618325717 10661836238752584804509)
                ·
                  rfl

theorem cell23_560624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 7].length) (baseStart_560624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560624 prefixEnd_560624 := by exact prefixLift 560624
  have htrace : WordTrace (prefixWord ++ tailWord_560624) baseStart_560624 baseEnd_560624 := by
    simpa [prefixWord, tailWord_560624, baseEnd_560624] using wordTrace_append hprefix tailTrace_560624
  have hstable : (prefixWord ++ tailWord_560624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560624).length < 2 ^ (prefixWord ++ tailWord_560624).sum := by decide
  have hdescent : baseEnd_560624 < baseStart_560624 := by decide
  rcases family_descends (prefixWord ++ tailWord_560624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560634 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_560634 : Nat := 118140960795 + 560634 * 2 ^ 59
def prefixEnd_560634 : Nat := 4983230072969 + 3 ^ 40 * 560634 * 2
def baseEnd_560634 : Nat := 287874713252864750596697

theorem tailTrace_560634 : CollatzResearch.WordTrace tailWord_560634 prefixEnd_560634 287874713252864750596697 := by
  unfold tailWord_560634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112000462731560377342239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13632001233950827672912637 5112000462731560377342239)
  ·
    refine ⟨7668000694097340566013359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112000462731560377342239 7668000694097340566013359)
    ·
      refine ⟨11502001041146010849020039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668000694097340566013359 11502001041146010849020039)
      ·
        refine ⟨17253001561719016273530059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502001041146010849020039 17253001561719016273530059)
        ·
          refine ⟨25879502342578524410295089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17253001561719016273530059 25879502342578524410295089)
          ·
            refine ⟨19409626756933893307721317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25879502342578524410295089 19409626756933893307721317)
            ·
              refine ⟨3639305016925104995197747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19409626756933893307721317 3639305016925104995197747)
              ·
                refine ⟨5458957525387657492796621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639305016925104995197747 5458957525387657492796621)
                ·
                  refine ⟨2047109072020371559798733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5458957525387657492796621 2047109072020371559798733)
                  ·
                    refine ⟨767665902007639334924525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047109072020371559798733 767665902007639334924525)
                    ·
                      refine ⟨287874713252864750596697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767665902007639334924525 287874713252864750596697)
                      ·
                        rfl

theorem cell23_560634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_560634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560634 prefixEnd_560634 := by exact prefixLift 560634
  have htrace : WordTrace (prefixWord ++ tailWord_560634) baseStart_560634 baseEnd_560634 := by
    simpa [prefixWord, tailWord_560634, baseEnd_560634] using wordTrace_append hprefix tailTrace_560634
  have hstable : (prefixWord ++ tailWord_560634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560634).length < 2 ^ (prefixWord ++ tailWord_560634).sum := by decide
  have hdescent : baseEnd_560634 < baseStart_560634 := by decide
  rcases family_descends (prefixWord ++ tailWord_560634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560641 : List Nat := [1, 2, 4, 1, 5, 1, 9]
def baseStart_560641 : Nat := 118140960795 + 560641 * 2 ^ 59
def prefixEnd_560641 : Nat := 4983230072969 + 3 ^ 40 * 560641 * 2
def baseEnd_560641 : Nat := 3554053180462299051965

theorem tailTrace_560641 : CollatzResearch.WordTrace tailWord_560641 prefixEnd_560641 3554053180462299051965 := by
  unfold tailWord_560641
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448257161900881704873777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13632171441267254469915851 20448257161900881704873777)
  ·
    refine ⟨15336192871425661278655333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20448257161900881704873777 15336192871425661278655333)
    ·
      refine ⟨2875536163392311489747875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15336192871425661278655333 2875536163392311489747875)
      ·
        refine ⟨4313304245088467234621813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875536163392311489747875 4313304245088467234621813)
        ·
          refine ⟨404372272977043803245795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4313304245088467234621813 404372272977043803245795)
          ·
            refine ⟨606558409465565704868693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404372272977043803245795 606558409465565704868693)
            ·
              refine ⟨3554053180462299051965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 606558409465565704868693 3554053180462299051965)
              ·
                rfl

theorem cell23_560641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 9].length) (baseStart_560641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560641 prefixEnd_560641 := by exact prefixLift 560641
  have htrace : WordTrace (prefixWord ++ tailWord_560641) baseStart_560641 baseEnd_560641 := by
    simpa [prefixWord, tailWord_560641, baseEnd_560641] using wordTrace_append hprefix tailTrace_560641
  have hstable : (prefixWord ++ tailWord_560641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560641).length < 2 ^ (prefixWord ++ tailWord_560641).sum := by decide
  have hdescent : baseEnd_560641 < baseStart_560641 := by decide
  rcases family_descends (prefixWord ++ tailWord_560641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560646 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_560646 : Nat := 118140960795 + 560646 * 2 ^ 59
def prefixEnd_560646 : Nat := 4983230072969 + 3 ^ 40 * 560646 * 2
def baseEnd_560646 : Nat := 287880875020718703646643

theorem tailTrace_560646 : CollatzResearch.WordTrace tailWord_560646 prefixEnd_560646 287880875020718703646643 := by
  unfold tailWord_560646
  simp only [CollatzResearch.WordTrace]
  refine ⟨639013735215086486212681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13632293017921845039203861 639013735215086486212681)
  ·
    refine ⟨479260301411314864659511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 639013735215086486212681 479260301411314864659511)
    ·
      refine ⟨718890452116972296989267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479260301411314864659511 718890452116972296989267)
      ·
        refine ⟨1078335678175458445483901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718890452116972296989267 1078335678175458445483901)
        ·
          refine ⟨404375879315796917056463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1078335678175458445483901 404375879315796917056463)
          ·
            refine ⟨606563818973695375584695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404375879315796917056463 606563818973695375584695)
            ·
              refine ⟨909845728460543063377043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606563818973695375584695 909845728460543063377043)
              ·
                refine ⟨1364768592690814595065565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909845728460543063377043 1364768592690814595065565)
                ·
                  refine ⟨511788222259055473149587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1364768592690814595065565 511788222259055473149587)
                  ·
                    refine ⟨767682333388583209724381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511788222259055473149587 767682333388583209724381)
                    ·
                      refine ⟨287880875020718703646643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767682333388583209724381 287880875020718703646643)
                      ·
                        rfl

theorem cell23_560646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_560646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560646 prefixEnd_560646 := by exact prefixLift 560646
  have htrace : WordTrace (prefixWord ++ tailWord_560646) baseStart_560646 baseEnd_560646 := by
    simpa [prefixWord, tailWord_560646, baseEnd_560646] using wordTrace_append hprefix tailTrace_560646
  have hstable : (prefixWord ++ tailWord_560646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560646).length < 2 ^ (prefixWord ++ tailWord_560646).sum := by decide
  have hdescent : baseEnd_560646 < baseStart_560646 := by decide
  rcases family_descends (prefixWord ++ tailWord_560646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560652 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_560652 : Nat := 118140960795 + 560652 * 2 ^ 59
def prefixEnd_560652 : Nat := 4983230072969 + 3 ^ 40 * 560652 * 2
def baseEnd_560652 : Nat := 287883955904645680171615

theorem tailTrace_560652 : CollatzResearch.WordTrace tailWord_560652 prefixEnd_560652 287883955904645680171615 := by
  unfold tailWord_560652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224329182430515291762105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13632438909907353722349473 10224329182430515291762105)
  ·
    refine ⟨7668246886822886468821579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10224329182430515291762105 7668246886822886468821579)
    ·
      refine ⟨11502370330234329703232369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668246886822886468821579 11502370330234329703232369)
      ·
        refine ⟨8626777747675747277424277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11502370330234329703232369 8626777747675747277424277)
        ·
          refine ⟨404380206922300653629263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8626777747675747277424277 404380206922300653629263)
          ·
            refine ⟨606570310383450980443895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404380206922300653629263 606570310383450980443895)
            ·
              refine ⟨909855465575176470665843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606570310383450980443895 909855465575176470665843)
              ·
                refine ⟨1364783198362764705998765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909855465575176470665843 1364783198362764705998765)
                ·
                  refine ⟨511793699386036764749537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1364783198362764705998765 511793699386036764749537)
                  ·
                    refine ⟨383845274539527573562153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511793699386036764749537 383845274539527573562153)
                    ·
                      refine ⟨287883955904645680171615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383845274539527573562153 287883955904645680171615)
                      ·
                        rfl

theorem cell23_560652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_560652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560652 prefixEnd_560652 := by exact prefixLift 560652
  have htrace : WordTrace (prefixWord ++ tailWord_560652) baseStart_560652 baseEnd_560652 := by
    simpa [prefixWord, tailWord_560652, baseEnd_560652] using wordTrace_append hprefix tailTrace_560652
  have hstable : (prefixWord ++ tailWord_560652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560652).length < 2 ^ (prefixWord ++ tailWord_560652).sum := by decide
  have hdescent : baseEnd_560652 < baseStart_560652 := by decide
  rcases family_descends (prefixWord ++ tailWord_560652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560668 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_560668 : Nat := 118140960795 + 560668 * 2 ^ 59
def prefixEnd_560668 : Nat := 4983230072969 + 3 ^ 40 * 560668 * 2
def baseEnd_560668 : Nat := 287892171595117617571541

theorem tailTrace_560668 : CollatzResearch.WordTrace tailWord_560668 prefixEnd_560668 287892171595117617571541 := by
  unfold tailWord_560668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224620966401532658053329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13632827955202043544071105 10224620966401532658053329)
  ·
    refine ⟨7668465724801149493539997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10224620966401532658053329 7668465724801149493539997)
    ·
      refine ⟨2875674646800431060077499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7668465724801149493539997 2875674646800431060077499)
      ·
        refine ⟨4313511970200646590116249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875674646800431060077499 4313511970200646590116249)
        ·
          refine ⟨3235133977650484942587187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4313511970200646590116249 3235133977650484942587187)
          ·
            refine ⟨4852700966475727413880781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235133977650484942587187 4852700966475727413880781)
            ·
              refine ⟨1819762862428397780205293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852700966475727413880781 1819762862428397780205293)
              ·
                refine ⟨682411073410649167576985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1819762862428397780205293 682411073410649167576985)
                ·
                  refine ⟨511808305057986875682739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682411073410649167576985 511808305057986875682739)
                  ·
                    refine ⟨767712457586980313524109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511808305057986875682739 767712457586980313524109)
                    ·
                      refine ⟨287892171595117617571541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767712457586980313524109 287892171595117617571541)
                      ·
                        rfl

theorem cell23_560668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_560668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560668 prefixEnd_560668 := by exact prefixLift 560668
  have htrace : WordTrace (prefixWord ++ tailWord_560668) baseStart_560668 baseEnd_560668 := by
    simpa [prefixWord, tailWord_560668, baseEnd_560668] using wordTrace_append hprefix tailTrace_560668
  have hstable : (prefixWord ++ tailWord_560668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560668).length < 2 ^ (prefixWord ++ tailWord_560668).sum := by decide
  have hdescent : baseEnd_560668 < baseStart_560668 := by decide
  rcases family_descends (prefixWord ++ tailWord_560668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560691 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 4, 2]
def baseStart_560691 : Nat := 118140960795 + 560691 * 2 ^ 59
def prefixEnd_560691 : Nat := 4983230072969 + 3 ^ 40 * 560691 * 2
def baseEnd_560691 : Nat := 287903981650171027583935

theorem tailTrace_560691 : CollatzResearch.WordTrace tailWord_560691 prefixEnd_560691 287903981650171027583935 := by
  unfold tailWord_560691
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450080811719740244193927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13633387207813160162795951 20450080811719740244193927)
  ·
    refine ⟨30675121217579610366290891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20450080811719740244193927 30675121217579610366290891)
    ·
      refine ⟨46012681826369415549436337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30675121217579610366290891 46012681826369415549436337)
      ·
        refine ⟨34509511369777061662077253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46012681826369415549436337 34509511369777061662077253)
        ·
          refine ⟨6470533381833199061639485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34509511369777061662077253 6470533381833199061639485)
          ·
            refine ⟨2426450018187449648114807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6470533381833199061639485 2426450018187449648114807)
            ·
              refine ⟨3639675027281174472172211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426450018187449648114807 3639675027281174472172211)
              ·
                refine ⟨5459512540921761708258317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639675027281174472172211 5459512540921761708258317)
                ·
                  refine ⟨2047317202845660640596869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5459512540921761708258317 2047317202845660640596869)
                  ·
                    refine ⟨383871975533561370111913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047317202845660640596869 383871975533561370111913)
                    ·
                      refine ⟨287903981650171027583935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383871975533561370111913 287903981650171027583935)
                      ·
                        rfl

theorem cell23_560691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4, 2].length) (baseStart_560691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560691 prefixEnd_560691 := by exact prefixLift 560691
  have htrace : WordTrace (prefixWord ++ tailWord_560691) baseStart_560691 baseEnd_560691 := by
    simpa [prefixWord, tailWord_560691, baseEnd_560691] using wordTrace_append hprefix tailTrace_560691
  have hstable : (prefixWord ++ tailWord_560691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560691).length < 2 ^ (prefixWord ++ tailWord_560691).sum := by decide
  have hdescent : baseEnd_560691 < baseStart_560691 := by decide
  rcases family_descends (prefixWord ++ tailWord_560691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560695 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_560695 : Nat := 118140960795 + 560695 * 2 ^ 59
def prefixEnd_560695 : Nat := 4983230072969 + 3 ^ 40 * 560695 * 2
def baseEnd_560695 : Nat := 287906035572789011933917

theorem tailTrace_560695 : CollatzResearch.WordTrace tailWord_560695 prefixEnd_560695 287906035572789011933917 := by
  unfold tailWord_560695
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450226703705248927339539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13633484469136832618226359 20450226703705248927339539)
  ·
    refine ⟨30675340055557873391009309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20450226703705248927339539 30675340055557873391009309)
    ·
      refine ⟨11503252520834202521628491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30675340055557873391009309 11503252520834202521628491)
      ·
        refine ⟨17254878781251303782442737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503252520834202521628491 17254878781251303782442737)
        ·
          refine ⟨12941159085938477836832053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17254878781251303782442737 12941159085938477836832053)
          ·
            refine ⟨1213233664306732297203005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12941159085938477836832053 1213233664306732297203005)
            ·
              refine ⟨454962624115024611451127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1213233664306732297203005 454962624115024611451127)
              ·
                refine ⟨682443936172536917176691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454962624115024611451127 682443936172536917176691)
                ·
                  refine ⟨1023665904258805375765037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682443936172536917176691 1023665904258805375765037)
                  ·
                    refine ⟨383874714097052015911889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023665904258805375765037 383874714097052015911889)
                    ·
                      refine ⟨287906035572789011933917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 383874714097052015911889 287906035572789011933917)
                      ·
                        rfl

theorem cell23_560695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_560695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560695 prefixEnd_560695 := by exact prefixLift 560695
  have htrace : WordTrace (prefixWord ++ tailWord_560695) baseStart_560695 baseEnd_560695 := by
    simpa [prefixWord, tailWord_560695, baseEnd_560695] using wordTrace_append hprefix tailTrace_560695
  have hstable : (prefixWord ++ tailWord_560695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560695).length < 2 ^ (prefixWord ++ tailWord_560695).sum := by decide
  have hdescent : baseEnd_560695 < baseStart_560695 := by decide
  rcases family_descends (prefixWord ++ tailWord_560695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560704 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_560704 : Nat := 118140960795 + 560704 * 2 ^ 59
def prefixEnd_560704 : Nat := 4983230072969 + 3 ^ 40 * 560704 * 2
def baseEnd_560704 : Nat := 287910656898679476721375

theorem tailTrace_560704 : CollatzResearch.WordTrace tailWord_560704 prefixEnd_560704 287910656898679476721375 := by
  unfold tailWord_560704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225277480336321732208583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13633703307115095642944777 10225277480336321732208583)
  ·
    refine ⟨15337916220504482598312875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10225277480336321732208583 15337916220504482598312875)
    ·
      refine ⟨23006874330756723897469313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15337916220504482598312875 23006874330756723897469313)
      ·
        refine ⟨17255155748067542923101985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23006874330756723897469313 17255155748067542923101985)
        ·
          refine ⟨12941366811050657192326489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17255155748067542923101985 12941366811050657192326489)
          ·
            refine ⟨9706025108287992894244867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12941366811050657192326489 9706025108287992894244867)
            ·
              refine ⟨14559037662431989341367301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706025108287992894244867 14559037662431989341367301)
              ·
                refine ⟨2729819561705998001506369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14559037662431989341367301 2729819561705998001506369)
                ·
                  refine ⟨2047364671279498501129777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729819561705998001506369 2047364671279498501129777)
                  ·
                    refine ⟨1535523503459623875847333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2047364671279498501129777 1535523503459623875847333)
                    ·
                      refine ⟨287910656898679476721375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1535523503459623875847333 287910656898679476721375)
                      ·
                        rfl

theorem cell23_560704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_560704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560704 prefixEnd_560704 := by exact prefixLift 560704
  have htrace : WordTrace (prefixWord ++ tailWord_560704) baseStart_560704 baseEnd_560704 := by
    simpa [prefixWord, tailWord_560704, baseEnd_560704] using wordTrace_append hprefix tailTrace_560704
  have hstable : (prefixWord ++ tailWord_560704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560704).length < 2 ^ (prefixWord ++ tailWord_560704).sum := by decide
  have hdescent : baseEnd_560704 < baseStart_560704 := by decide
  rcases family_descends (prefixWord ++ tailWord_560704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560714 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_560714 : Nat := 118140960795 + 560714 * 2 ^ 59
def prefixEnd_560714 : Nat := 4983230072969 + 3 ^ 40 * 560714 * 2
def baseEnd_560714 : Nat := 31990643522802715288481

theorem tailTrace_560714 : CollatzResearch.WordTrace tailWord_560714 prefixEnd_560714 31990643522802715288481 := by
  unfold tailWord_560714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112729922659103793070299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13633946460424276781520797 5112729922659103793070299)
  ·
    refine ⟨7669094883988655689605449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112729922659103793070299 7669094883988655689605449)
    ·
      refine ⟨5751821162991491767204087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7669094883988655689605449 5751821162991491767204087)
      ·
        refine ⟨8627731744487237650806131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751821162991491767204087 8627731744487237650806131)
        ·
          refine ⟨12941597616730856476209197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8627731744487237650806131 12941597616730856476209197)
          ·
            refine ⟨4853099106274071178578449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12941597616730856476209197 4853099106274071178578449)
            ·
              refine ⟨3639824329705553383933837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4853099106274071178578449 3639824329705553383933837)
              ·
                refine ⟨1364934123639582518975189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3639824329705553383933837 1364934123639582518975189)
                ·
                  refine ⟨31990643522802715288481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1364934123639582518975189 31990643522802715288481)
                  ·
                    rfl

theorem cell23_560714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_560714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560714 prefixEnd_560714 := by exact prefixLift 560714
  have htrace : WordTrace (prefixWord ++ tailWord_560714) baseStart_560714 baseEnd_560714 := by
    simpa [prefixWord, tailWord_560714, baseEnd_560714] using wordTrace_append hprefix tailTrace_560714
  have hstable : (prefixWord ++ tailWord_560714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560714).length < 2 ^ (prefixWord ++ tailWord_560714).sum := by decide
  have hdescent : baseEnd_560714 < baseStart_560714 := by decide
  rcases family_descends (prefixWord ++ tailWord_560714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560758 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_560758 : Nat := 118140960795 + 560758 * 2 ^ 59
def prefixEnd_560758 : Nat := 4983230072969 + 3 ^ 40 * 560758 * 2
def baseEnd_560758 : Nat := 287938384854022265446127

theorem tailTrace_560758 : CollatzResearch.WordTrace tailWord_560758 prefixEnd_560758 287938384854022265446127 := by
  unfold tailWord_560758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278282781404813167930183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13635016334984673791255285 1278282781404813167930183)
  ·
    refine ⟨1917424172107219751895275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278282781404813167930183 1917424172107219751895275)
    ·
      refine ⟨2876136258160829627842913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917424172107219751895275 2876136258160829627842913)
      ·
        refine ⟨2157102193620622220882185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2876136258160829627842913 2157102193620622220882185)
        ·
          refine ⟨1617826645215466665661639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157102193620622220882185 1617826645215466665661639)
          ·
            refine ⟨2426739967823199998492459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617826645215466665661639 2426739967823199998492459)
            ·
              refine ⟨3640109951734799997738689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426739967823199998492459 3640109951734799997738689)
              ·
                refine ⟨2730082463801099998304017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640109951734799997738689 2730082463801099998304017)
                ·
                  refine ⟨2047561847850824998728013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730082463801099998304017 2047561847850824998728013)
                  ·
                    refine ⟨767835692944059374523005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047561847850824998728013 767835692944059374523005)
                    ·
                      refine ⟨287938384854022265446127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 767835692944059374523005 287938384854022265446127)
                      ·
                        rfl

theorem cell23_560758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_560758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560758 prefixEnd_560758 := by exact prefixLift 560758
  have htrace : WordTrace (prefixWord ++ tailWord_560758) baseStart_560758 baseEnd_560758 := by
    simpa [prefixWord, tailWord_560758, baseEnd_560758] using wordTrace_append hprefix tailTrace_560758
  have hstable : (prefixWord ++ tailWord_560758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560758).length < 2 ^ (prefixWord ++ tailWord_560758).sum := by decide
  have hdescent : baseEnd_560758 < baseStart_560758 := by decide
  rcases family_descends (prefixWord ++ tailWord_560758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560798 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_560798 : Nat := 118140960795 + 560798 * 2 ^ 59
def prefixEnd_560798 : Nat := 4983230072969 + 3 ^ 40 * 560798 * 2
def baseEnd_560798 : Nat := 287958924080202108945943

theorem tailTrace_560798 : CollatzResearch.WordTrace tailWord_560798 prefixEnd_560798 287958924080202108945943 := by
  unfold tailWord_560798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556747927791512189792381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13635988948221398345559365 2556747927791512189792381)
  ·
    refine ⟨958780472921817071172143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2556747927791512189792381 958780472921817071172143)
    ·
      refine ⟨1438170709382725606758215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958780472921817071172143 1438170709382725606758215)
      ·
        refine ⟨2157256064074088410137323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438170709382725606758215 2157256064074088410137323)
        ·
          refine ⟨3235884096111132615205985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157256064074088410137323 3235884096111132615205985)
          ·
            refine ⟨2426913072083349461404489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235884096111132615205985 2426913072083349461404489)
            ·
              refine ⟨1820184804062512096053367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426913072083349461404489 1820184804062512096053367)
              ·
                refine ⟨2730277206093768144080051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820184804062512096053367 2730277206093768144080051)
                ·
                  refine ⟨4095415809140652216120077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730277206093768144080051 4095415809140652216120077)
                  ·
                    refine ⟨1535780928427744581045029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4095415809140652216120077 1535780928427744581045029)
                    ·
                      refine ⟨287958924080202108945943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1535780928427744581045029 287958924080202108945943)
                      ·
                        rfl

theorem cell23_560798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_560798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560798 prefixEnd_560798 := by exact prefixLift 560798
  have htrace : WordTrace (prefixWord ++ tailWord_560798) baseStart_560798 baseEnd_560798 := by
    simpa [prefixWord, tailWord_560798, baseEnd_560798] using wordTrace_append hprefix tailTrace_560798
  have hstable : (prefixWord ++ tailWord_560798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560798).length < 2 ^ (prefixWord ++ tailWord_560798).sum := by decide
  have hdescent : baseEnd_560798 < baseStart_560798 := by decide
  rcases family_descends (prefixWord ++ tailWord_560798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560824 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_560824 : Nat := 118140960795 + 560824 * 2 ^ 59
def prefixEnd_560824 : Nat := 4983230072969 + 3 ^ 40 * 560824 * 2
def baseEnd_560824 : Nat := 287972274577219007220823

theorem tailTrace_560824 : CollatzResearch.WordTrace tailWord_560824 prefixEnd_560824 287972274577219007220823 := by
  unfold tailWord_560824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227465860118951979392763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13636621146825269305857017 10227465860118951979392763)
  ·
    refine ⟨15341198790178427969089145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227465860118951979392763 15341198790178427969089145)
    ·
      refine ⟨11505899092633820976816859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15341198790178427969089145 11505899092633820976816859)
      ·
        refine ⟨17258848638950731465225289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11505899092633820976816859 17258848638950731465225289)
        ·
          refine ⟨12944136479213048598918967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17258848638950731465225289 12944136479213048598918967)
          ·
            refine ⟨19416204718819572898378451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12944136479213048598918967 19416204718819572898378451)
            ·
              refine ⟨29124307078229359347567677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19416204718819572898378451 29124307078229359347567677)
              ·
                refine ⟨10921615154336009755337879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29124307078229359347567677 10921615154336009755337879)
                ·
                  refine ⟨16382422731504014633006819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10921615154336009755337879 16382422731504014633006819)
                  ·
                    refine ⟨24573634097256021949510229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16382422731504014633006819 24573634097256021949510229)
                    ·
                      refine ⟨287972274577219007220823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24573634097256021949510229 287972274577219007220823)
                      ·
                        rfl

theorem cell23_560824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_560824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560824 prefixEnd_560824 := by exact prefixLift 560824
  have htrace : WordTrace (prefixWord ++ tailWord_560824) baseStart_560824 baseEnd_560824 := by
    simpa [prefixWord, tailWord_560824, baseEnd_560824] using wordTrace_append hprefix tailTrace_560824
  have hstable : (prefixWord ++ tailWord_560824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560824).length < 2 ^ (prefixWord ++ tailWord_560824).sum := by decide
  have hdescent : baseEnd_560824 < baseStart_560824 := by decide
  rcases family_descends (prefixWord ++ tailWord_560824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560882 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_560882 : Nat := 118140960795 + 560882 * 2 ^ 59
def prefixEnd_560882 : Nat := 4983230072969 + 3 ^ 40 * 560882 * 2
def baseEnd_560882 : Nat := 288002056455179780295557

theorem tailTrace_560882 : CollatzResearch.WordTrace tailWord_560882 prefixEnd_560882 288002056455179780295557 := by
  unfold tailWord_560882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114261788506944966099225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13638031436018519909597933 5114261788506944966099225)
  ·
    refine ⟨3835696341380208724574419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5114261788506944966099225 3835696341380208724574419)
    ·
      refine ⟨5753544512070313086861629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3835696341380208724574419 5753544512070313086861629)
      ·
        refine ⟨2157579192026367407573111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5753544512070313086861629 2157579192026367407573111)
        ·
          refine ⟨3236368788039551111359667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157579192026367407573111 3236368788039551111359667)
          ·
            refine ⟨4854553182059326667039501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236368788039551111359667 4854553182059326667039501)
            ·
              refine ⟨1820457443272247500139813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854553182059326667039501 1820457443272247500139813)
              ·
                refine ⟨341335770613546406276215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1820457443272247500139813 341335770613546406276215)
                ·
                  refine ⟨512003655920319609414323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341335770613546406276215 512003655920319609414323)
                  ·
                    refine ⟨768005483880479414121485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512003655920319609414323 768005483880479414121485)
                    ·
                      refine ⟨288002056455179780295557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768005483880479414121485 288002056455179780295557)
                      ·
                        rfl

theorem cell23_560882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_560882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560882 prefixEnd_560882 := by exact prefixLift 560882
  have htrace : WordTrace (prefixWord ++ tailWord_560882) baseStart_560882 baseEnd_560882 := by
    simpa [prefixWord, tailWord_560882, baseEnd_560882] using wordTrace_append hprefix tailTrace_560882
  have hstable : (prefixWord ++ tailWord_560882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560882).length < 2 ^ (prefixWord ++ tailWord_560882).sum := by decide
  have hdescent : baseEnd_560882 < baseStart_560882 := by decide
  rcases family_descends (prefixWord ++ tailWord_560882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560908 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_560908 : Nat := 118140960795 + 560908 * 2 ^ 59
def prefixEnd_560908 : Nat := 4983230072969 + 3 ^ 40 * 560908 * 2
def baseEnd_560908 : Nat := 288015406952196678570437

theorem tailTrace_560908 : CollatzResearch.WordTrace tailWord_560908 prefixEnd_560908 288015406952196678570437 := by
  unfold tailWord_560908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228997725966793152421689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13638663634622390869895585 10228997725966793152421689)
  ·
    refine ⟨7671748294475094864316267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10228997725966793152421689 7671748294475094864316267)
    ·
      refine ⟨11507622441712642296474401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671748294475094864316267 11507622441712642296474401)
      ·
        refine ⟨8630716831284481722355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507622441712642296474401 8630716831284481722355801)
        ·
          refine ⟨6473037623463361291766851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630716831284481722355801 6473037623463361291766851)
          ·
            refine ⟨9709556435195041937650277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473037623463361291766851 9709556435195041937650277)
            ·
              refine ⟨1820541831599070363309427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9709556435195041937650277 1820541831599070363309427)
              ·
                refine ⟨2730812747398605544964141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820541831599070363309427 2730812747398605544964141)
                ·
                  refine ⟨1024054780274477079361553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2730812747398605544964141 1024054780274477079361553)
                  ·
                    refine ⟨768041085205857809521165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024054780274477079361553 768041085205857809521165)
                    ·
                      refine ⟨288015406952196678570437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768041085205857809521165 288015406952196678570437)
                      ·
                        rfl

theorem cell23_560908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_560908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560908 prefixEnd_560908 := by exact prefixLift 560908
  have htrace : WordTrace (prefixWord ++ tailWord_560908) baseStart_560908 baseEnd_560908 := by
    simpa [prefixWord, tailWord_560908, baseEnd_560908] using wordTrace_append hprefix tailTrace_560908
  have hstable : (prefixWord ++ tailWord_560908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560908).length < 2 ^ (prefixWord ++ tailWord_560908).sum := by decide
  have hdescent : baseEnd_560908 < baseStart_560908 := by decide
  rcases family_descends (prefixWord ++ tailWord_560908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560921 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_560921 : Nat := 118140960795 + 560921 * 2 ^ 59
def prefixEnd_560921 : Nat := 4983230072969 + 3 ^ 40 * 560921 * 2
def baseEnd_560921 : Nat := 288022082200705127707877

theorem tailTrace_560921 : CollatzResearch.WordTrace tailWord_560921 prefixEnd_560921 288022082200705127707877 := by
  unfold tailWord_560921
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458469600886489525066617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13638979733924326350044411 20458469600886489525066617)
  ·
    refine ⟨15343852200664867143799963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20458469600886489525066617 15343852200664867143799963)
    ·
      refine ⟨23015778300997300715699945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15343852200664867143799963 23015778300997300715699945)
      ·
        refine ⟨17261833725747975536774959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23015778300997300715699945 17261833725747975536774959)
        ·
          refine ⟨25892750588621963305162439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17261833725747975536774959 25892750588621963305162439)
          ·
            refine ⟨38839125882932944957743659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25892750588621963305162439 38839125882932944957743659)
            ·
              refine ⟨58258688824399417436615489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38839125882932944957743659 58258688824399417436615489)
              ·
                refine ⟨43694016618299563077461617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58258688824399417436615489 43694016618299563077461617)
                ·
                  refine ⟨32770512463724672308096213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43694016618299563077461617 32770512463724672308096213)
                  ·
                    refine ⟨768058885868547007221005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32770512463724672308096213 768058885868547007221005)
                    ·
                      refine ⟨288022082200705127707877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768058885868547007221005 288022082200705127707877)
                      ·
                        rfl

theorem cell23_560921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_560921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560921 prefixEnd_560921 := by exact prefixLift 560921
  have htrace : WordTrace (prefixWord ++ tailWord_560921) baseStart_560921 baseEnd_560921 := by
    simpa [prefixWord, tailWord_560921, baseEnd_560921] using wordTrace_append hprefix tailTrace_560921
  have hstable : (prefixWord ++ tailWord_560921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560921).length < 2 ^ (prefixWord ++ tailWord_560921).sum := by decide
  have hdescent : baseEnd_560921 < baseStart_560921 := by decide
  rcases family_descends (prefixWord ++ tailWord_560921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560922 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_560922 : Nat := 118140960795 + 560922 * 2 ^ 59
def prefixEnd_560922 : Nat := 4983230072969 + 3 ^ 40 * 560922 * 2
def baseEnd_560922 : Nat := 288022595681359623795373

theorem tailTrace_560922 : CollatzResearch.WordTrace tailWord_560922 prefixEnd_560922 288022595681359623795373 := by
  unfold tailWord_560922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114626518470716673963255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13639004049255244463902013 5114626518470716673963255)
  ·
    refine ⟨7671939777706075010944883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114626518470716673963255 7671939777706075010944883)
    ·
      refine ⟨11507909666559112516417325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671939777706075010944883 11507909666559112516417325)
      ·
        refine ⟨4315466124959667193656497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11507909666559112516417325 4315466124959667193656497)
        ·
          refine ⟨3236599593719750395242373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315466124959667193656497 3236599593719750395242373)
          ·
            refine ⟨606862423822453199107945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3236599593719750395242373 606862423822453199107945)
            ·
              refine ⟨455146817866839899330959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606862423822453199107945 455146817866839899330959)
              ·
                refine ⟨682720226800259848996439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455146817866839899330959 682720226800259848996439)
                ·
                  refine ⟨1024080340200389773494659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682720226800259848996439 1024080340200389773494659)
                  ·
                    refine ⟨1536120510300584660241989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024080340200389773494659 1536120510300584660241989)
                    ·
                      refine ⟨288022595681359623795373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1536120510300584660241989 288022595681359623795373)
                      ·
                        rfl

theorem cell23_560922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_560922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560922 prefixEnd_560922 := by exact prefixLift 560922
  have htrace : WordTrace (prefixWord ++ tailWord_560922) baseStart_560922 baseEnd_560922 := by
    simpa [prefixWord, tailWord_560922, baseEnd_560922] using wordTrace_append hprefix tailTrace_560922
  have hstable : (prefixWord ++ tailWord_560922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560922).length < 2 ^ (prefixWord ++ tailWord_560922).sum := by decide
  have hdescent : baseEnd_560922 < baseStart_560922 := by decide
  rcases family_descends (prefixWord ++ tailWord_560922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560932 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_560932 : Nat := 118140960795 + 560932 * 2 ^ 59
def prefixEnd_560932 : Nat := 4983230072969 + 3 ^ 40 * 560932 * 2
def baseEnd_560932 : Nat := 96009243495968194890109

theorem tailTrace_560932 : CollatzResearch.WordTrace tailWord_560932 prefixEnd_560932 96009243495968194890109 := by
  unfold tailWord_560932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229435401923319201858525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13639247202564425602478033 10229435401923319201858525)
  ·
    refine ⟨3836038275721244700696947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10229435401923319201858525 3836038275721244700696947)
    ·
      refine ⟨5754057413581867051045421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3836038275721244700696947 5754057413581867051045421)
      ·
        refine ⟨2157771530093200144142033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5754057413581867051045421 2157771530093200144142033)
        ·
          refine ⟨1618328647569900108106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157771530093200144142033 1618328647569900108106525)
          ·
            refine ⟨606873242838712540539947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618328647569900108106525 606873242838712540539947)
            ·
              refine ⟨910309864258068810809921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606873242838712540539947 910309864258068810809921)
              ·
                refine ⟨682732398193551608107441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910309864258068810809921 682732398193551608107441)
                ·
                  refine ⟨512049298645163706080581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682732398193551608107441 512049298645163706080581)
                  ·
                    refine ⟨96009243495968194890109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512049298645163706080581 96009243495968194890109)
                    ·
                      rfl

theorem cell23_560932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_560932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560932 prefixEnd_560932 := by exact prefixLift 560932
  have htrace : WordTrace (prefixWord ++ tailWord_560932) baseStart_560932 baseEnd_560932 := by
    simpa [prefixWord, tailWord_560932, baseEnd_560932] using wordTrace_append hprefix tailTrace_560932
  have hstable : (prefixWord ++ tailWord_560932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560932).length < 2 ^ (prefixWord ++ tailWord_560932).sum := by decide
  have hdescent : baseEnd_560932 < baseStart_560932 := by decide
  rcases family_descends (prefixWord ++ tailWord_560932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560973 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_560973 : Nat := 118140960795 + 560973 * 2 ^ 59
def prefixEnd_560973 : Nat := 4983230072969 + 3 ^ 40 * 560973 * 2
def baseEnd_560973 : Nat := 288048783194738924257639

theorem tailTrace_560973 : CollatzResearch.WordTrace tailWord_560973 prefixEnd_560973 288048783194738924257639 := by
  unfold tailWord_560973
  simp only [CollatzResearch.WordTrace]
  refine ⟨20460366196698102405959573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13640244131132068270639715 20460366196698102405959573)
  ·
    refine ⟨959079665470223550279355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20460366196698102405959573 959079665470223550279355)
    ·
      refine ⟨1438619498205335325419033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959079665470223550279355 1438619498205335325419033)
      ·
        refine ⟨1078964623654001494064275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1438619498205335325419033 1078964623654001494064275)
        ·
          refine ⟨1618446935481002241096413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078964623654001494064275 1618446935481002241096413)
          ·
            refine ⟨606917600805375840411155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618446935481002241096413 606917600805375840411155)
            ·
              refine ⟨910376401208063760616733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606917600805375840411155 910376401208063760616733)
              ·
                refine ⟨341391150453023910231275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 910376401208063760616733 341391150453023910231275)
                ·
                  refine ⟨512086725679535865346913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341391150453023910231275 512086725679535865346913)
                  ·
                    refine ⟨384065044259651899010185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 512086725679535865346913 384065044259651899010185)
                    ·
                      refine ⟨288048783194738924257639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384065044259651899010185 288048783194738924257639)
                      ·
                        rfl

theorem cell23_560973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_560973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_560973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_560973 prefixEnd_560973 := by exact prefixLift 560973
  have htrace : WordTrace (prefixWord ++ tailWord_560973) baseStart_560973 baseEnd_560973 := by
    simpa [prefixWord, tailWord_560973, baseEnd_560973] using wordTrace_append hprefix tailTrace_560973
  have hstable : (prefixWord ++ tailWord_560973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560973).length < 2 ^ (prefixWord ++ tailWord_560973).sum := by decide
  have hdescent : baseEnd_560973 < baseStart_560973 := by decide
  rcases family_descends (prefixWord ++ tailWord_560973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561006 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_561006 : Nat := 118140960795 + 561006 * 2 ^ 59
def prefixEnd_561006 : Nat := 4983230072969 + 3 ^ 40 * 561006 * 2
def baseEnd_561006 : Nat := 288065728056337295144987

theorem tailTrace_561006 : CollatzResearch.WordTrace tailWord_561006 prefixEnd_561006 288065728056337295144987 := by
  unfold tailWord_561006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557696225697318630238859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13641046537052366027940581 2557696225697318630238859)
  ·
    refine ⟨3836544338545977945358289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557696225697318630238859 3836544338545977945358289)
    ·
      refine ⟨2877408253909483459018717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3836544338545977945358289 2877408253909483459018717)
      ·
        refine ⟨1079028095216056297132019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2877408253909483459018717 1079028095216056297132019)
        ·
          refine ⟨1618542142824084445698029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079028095216056297132019 1618542142824084445698029)
          ·
            refine ⟨606953303559031667136761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618542142824084445698029 606953303559031667136761)
            ·
              refine ⟨455214977669273750352571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606953303559031667136761 455214977669273750352571)
              ·
                refine ⟨682822466503910625528857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455214977669273750352571 682822466503910625528857)
                ·
                  refine ⟨512116849877932969146643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682822466503910625528857 512116849877932969146643)
                  ·
                    refine ⟨768175274816899453719965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512116849877932969146643 768175274816899453719965)
                    ·
                      refine ⟨288065728056337295144987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768175274816899453719965 288065728056337295144987)
                      ·
                        rfl

theorem cell23_561006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_561006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561006 prefixEnd_561006 := by exact prefixLift 561006
  have htrace : WordTrace (prefixWord ++ tailWord_561006) baseStart_561006 baseEnd_561006 := by
    simpa [prefixWord, tailWord_561006, baseEnd_561006] using wordTrace_append hprefix tailTrace_561006
  have hstable : (prefixWord ++ tailWord_561006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561006).length < 2 ^ (prefixWord ++ tailWord_561006).sum := by decide
  have hdescent : baseEnd_561006 < baseStart_561006 := by decide
  rcases family_descends (prefixWord ++ tailWord_561006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561052 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 5]
def baseStart_561052 : Nat := 118140960795 + 561052 * 2 ^ 59
def prefixEnd_561052 : Nat := 4983230072969 + 3 ^ 40 * 561052 * 2
def baseEnd_561052 : Nat := 32009927574049346129975

theorem tailTrace_561052 : CollatzResearch.WordTrace tailWord_561052 prefixEnd_561052 32009927574049346129975 := by
  unfold tailWord_561052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231623781705949449042705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13642165042274599265390273 10231623781705949449042705)
  ·
    refine ⟨7673717836279462086782029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10231623781705949449042705 7673717836279462086782029)
    ·
      refine ⟨2877644188604798282543261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7673717836279462086782029 2877644188604798282543261)
      ·
        refine ⟨1079116570726799355953723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2877644188604798282543261 1079116570726799355953723)
        ·
          refine ⟨1618674856090199033930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079116570726799355953723 1618674856090199033930585)
          ·
            refine ⟨1214006142067649275447939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618674856090199033930585 1214006142067649275447939)
            ·
              refine ⟨1821009213101473913171909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214006142067649275447939 1821009213101473913171909)
              ·
                refine ⟨341439227456526358719733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1821009213101473913171909 341439227456526358719733)
                ·
                  refine ⟨32009927574049346129975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341439227456526358719733 32009927574049346129975)
                  ·
                    rfl

theorem cell23_561052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_561052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561052 prefixEnd_561052 := by exact prefixLift 561052
  have htrace : WordTrace (prefixWord ++ tailWord_561052) baseStart_561052 baseEnd_561052 := by
    simpa [prefixWord, tailWord_561052, baseEnd_561052] using wordTrace_append hprefix tailTrace_561052
  have hstable : (prefixWord ++ tailWord_561052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561052).length < 2 ^ (prefixWord ++ tailWord_561052).sum := by decide
  have hdescent : baseEnd_561052 < baseStart_561052 := by decide
  rcases family_descends (prefixWord ++ tailWord_561052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561085 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_561085 : Nat := 118140960795 + 561085 * 2 ^ 59
def prefixEnd_561085 : Nat := 4983230072969 + 3 ^ 40 * 561085 * 2
def baseEnd_561085 : Nat := 288106293028042486057123

theorem tailTrace_561085 : CollatzResearch.WordTrace tailWord_561085 prefixEnd_561085 288106293028042486057123 := by
  unfold tailWord_561085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20464451172292345534036709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13642967448194897022691139 20464451172292345534036709)
  ·
    refine ⟨3837084594804814787631883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20464451172292345534036709 3837084594804814787631883)
    ·
      refine ⟨5755626892207222181447825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837084594804814787631883 5755626892207222181447825)
      ·
        refine ⟨4316720169155416636085869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5755626892207222181447825 4316720169155416636085869)
        ·
          refine ⟨1618770063433281238532201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4316720169155416636085869 1618770063433281238532201)
          ·
            refine ⟨1214077547574960928899151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618770063433281238532201 1214077547574960928899151)
            ·
              refine ⟨1821116321362441393348727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214077547574960928899151 1821116321362441393348727)
              ·
                refine ⟨2731674482043662090023091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821116321362441393348727 2731674482043662090023091)
                ·
                  refine ⟨4097511723065493135034637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731674482043662090023091 4097511723065493135034637)
                  ·
                    refine ⟨1536566896149559925637989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4097511723065493135034637 1536566896149559925637989)
                    ·
                      refine ⟨288106293028042486057123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1536566896149559925637989 288106293028042486057123)
                      ·
                        rfl

theorem cell23_561085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_561085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561085 prefixEnd_561085 := by exact prefixLift 561085
  have htrace : WordTrace (prefixWord ++ tailWord_561085) baseStart_561085 baseEnd_561085 := by
    simpa [prefixWord, tailWord_561085, baseEnd_561085] using wordTrace_append hprefix tailTrace_561085
  have hstable : (prefixWord ++ tailWord_561085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561085).length < 2 ^ (prefixWord ++ tailWord_561085).sum := by decide
  have hdescent : baseEnd_561085 < baseStart_561085 := by decide
  rcases family_descends (prefixWord ++ tailWord_561085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561098 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_561098 : Nat := 118140960795 + 561098 * 2 ^ 59
def prefixEnd_561098 : Nat := 4983230072969 + 3 ^ 40 * 561098 * 2
def baseEnd_561098 : Nat := 288112968276550935194563

theorem tailTrace_561098 : CollatzResearch.WordTrace tailWord_561098 prefixEnd_561098 288112968276550935194563 := by
  unfold tailWord_561098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116231330311312188564987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13643283547496832502839965 5116231330311312188564987)
  ·
    refine ⟨7674346995466968282847481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5116231330311312188564987 7674346995466968282847481)
    ·
      refine ⟨5755760246600226212135611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7674346995466968282847481 5755760246600226212135611)
      ·
        refine ⟨8633640369900339318203417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5755760246600226212135611 8633640369900339318203417)
        ·
          refine ⟨6475230277425254488652563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8633640369900339318203417 6475230277425254488652563)
          ·
            refine ⟨9712845416137881732978845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475230277425254488652563 9712845416137881732978845)
            ·
              refine ⟨3642317031051705649867067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9712845416137881732978845 3642317031051705649867067)
              ·
                refine ⟨5463475546577558474800601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3642317031051705649867067 5463475546577558474800601)
                ·
                  refine ⟨4097606659933168856100451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5463475546577558474800601 4097606659933168856100451)
                  ·
                    refine ⟨6146409989899753284150677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097606659933168856100451 6146409989899753284150677)
                    ·
                      refine ⟨288112968276550935194563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6146409989899753284150677 288112968276550935194563)
                      ·
                        rfl

theorem cell23_561098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_561098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561098 prefixEnd_561098 := by exact prefixLift 561098
  have htrace : WordTrace (prefixWord ++ tailWord_561098) baseStart_561098 baseEnd_561098 := by
    simpa [prefixWord, tailWord_561098, baseEnd_561098] using wordTrace_append hprefix tailTrace_561098
  have hstable : (prefixWord ++ tailWord_561098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561098).length < 2 ^ (prefixWord ++ tailWord_561098).sum := by decide
  have hdescent : baseEnd_561098 < baseStart_561098 := by decide
  rcases family_descends (prefixWord ++ tailWord_561098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561112 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 1, 4]
def baseStart_561112 : Nat := 118140960795 + 561112 * 2 ^ 59
def prefixEnd_561112 : Nat := 4983230072969 + 3 ^ 40 * 561112 * 2
def baseEnd_561112 : Nat := 96040052335237960139833

theorem tailTrace_561112 : CollatzResearch.WordTrace tailWord_561112 prefixEnd_561112 96040052335237960139833 := by
  unfold tailWord_561112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232717971597264572634795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13643623962129686096846393 10232717971597264572634795)
  ·
    refine ⟨15349076957395896858952193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10232717971597264572634795 15349076957395896858952193)
    ·
      refine ⟨11511807718046922644214145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15349076957395896858952193 11511807718046922644214145)
      ·
        refine ⟨8633855788535191983160609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11511807718046922644214145 8633855788535191983160609)
        ·
          refine ⟨6475391841401393987370457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8633855788535191983160609 6475391841401393987370457)
          ·
            refine ⟨4856543881051045490527843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475391841401393987370457 4856543881051045490527843)
            ·
              refine ⟨7284815821576568235791765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856543881051045490527843 7284815821576568235791765)
              ·
                refine ⟨341475741636401636052739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7284815821576568235791765 341475741636401636052739)
                ·
                  refine ⟨512213612454602454079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341475741636401636052739 512213612454602454079109)
                  ·
                    refine ⟨96040052335237960139833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512213612454602454079109 96040052335237960139833)
                    ·
                      rfl

theorem cell23_561112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_561112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561112 prefixEnd_561112 := by exact prefixLift 561112
  have htrace : WordTrace (prefixWord ++ tailWord_561112) baseStart_561112 baseEnd_561112 := by
    simpa [prefixWord, tailWord_561112, baseEnd_561112] using wordTrace_append hprefix tailTrace_561112
  have hstable : (prefixWord ++ tailWord_561112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561112).length < 2 ^ (prefixWord ++ tailWord_561112).sum := by decide
  have hdescent : baseEnd_561112 < baseStart_561112 := by decide
  rcases family_descends (prefixWord ++ tailWord_561112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_561128 : Nat := 118140960795 + 561128 * 2 ^ 59
def prefixEnd_561128 : Nat := 4983230072969 + 3 ^ 40 * 561128 * 2
def baseEnd_561128 : Nat := 288128372696185817819425

theorem tailTrace_561128 : CollatzResearch.WordTrace tailWord_561128 prefixEnd_561128 288128372696185817819425 := by
  unfold tailWord_561128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233009755568281938926019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13644013007424375918568025 10233009755568281938926019)
  ·
    refine ⟨15349514633352422908389029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233009755568281938926019 15349514633352422908389029)
    ·
      refine ⟨2878033993753579295322943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15349514633352422908389029 2878033993753579295322943)
      ·
        refine ⟨4317050990630368942984415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878033993753579295322943 4317050990630368942984415)
        ·
          refine ⟨6475576485945553414476623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317050990630368942984415 6475576485945553414476623)
          ·
            refine ⟨9713364728918330121714935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475576485945553414476623 9713364728918330121714935)
            ·
              refine ⟨14570047093377495182572403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9713364728918330121714935 14570047093377495182572403)
              ·
                refine ⟨21855070640066242773858605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14570047093377495182572403 21855070640066242773858605)
                ·
                  refine ⟨8195651490024841040196977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21855070640066242773858605 8195651490024841040196977)
                  ·
                    refine ⟨6146738617518630780147733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8195651490024841040196977 6146738617518630780147733)
                    ·
                      refine ⟨288128372696185817819425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6146738617518630780147733 288128372696185817819425)
                      ·
                        rfl

theorem cell23_561128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_561128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561128 prefixEnd_561128 := by exact prefixLift 561128
  have htrace : WordTrace (prefixWord ++ tailWord_561128) baseStart_561128 baseEnd_561128 := by
    simpa [prefixWord, tailWord_561128, baseEnd_561128] using wordTrace_append hprefix tailTrace_561128
  have hstable : (prefixWord ++ tailWord_561128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561128).length < 2 ^ (prefixWord ++ tailWord_561128).sum := by decide
  have hdescent : baseEnd_561128 < baseStart_561128 := by decide
  rcases family_descends (prefixWord ++ tailWord_561128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_561168 : Nat := 118140960795 + 561168 * 2 ^ 59
def prefixEnd_561168 : Nat := 4983230072969 + 3 ^ 40 * 561168 * 2
def baseEnd_561168 : Nat := 96049637307455220439747

theorem tailTrace_561168 : CollatzResearch.WordTrace tailWord_561168 prefixEnd_561168 96049637307455220439747 := by
  unfold tailWord_561168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233739215495825354654079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13644985620661100472872105 10233739215495825354654079)
  ·
    refine ⟨15350608823243738031981119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233739215495825354654079 15350608823243738031981119)
    ·
      refine ⟨23025913234865607047971679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15350608823243738031981119 23025913234865607047971679)
      ·
        refine ⟨34538869852298410571957519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23025913234865607047971679 34538869852298410571957519)
        ·
          refine ⟨51808304778447615857936279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34538869852298410571957519 51808304778447615857936279)
          ·
            refine ⟨77712457167671423786904419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51808304778447615857936279 77712457167671423786904419)
            ·
              refine ⟨116568685751507135680356629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77712457167671423786904419 116568685751507135680356629)
              ·
                refine ⟨5464157144601896985016717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116568685751507135680356629 5464157144601896985016717)
                ·
                  refine ⟨2049058929225711369381269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5464157144601896985016717 2049058929225711369381269)
                  ·
                    refine ⟨96049637307455220439747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2049058929225711369381269 96049637307455220439747)
                    ·
                      rfl

theorem cell23_561168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_561168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561168 prefixEnd_561168 := by exact prefixLift 561168
  have htrace : WordTrace (prefixWord ++ tailWord_561168) baseStart_561168 baseEnd_561168 := by
    simpa [prefixWord, tailWord_561168, baseEnd_561168] using wordTrace_append hprefix tailTrace_561168
  have hstable : (prefixWord ++ tailWord_561168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561168).length < 2 ^ (prefixWord ++ tailWord_561168).sum := by decide
  have hdescent : baseEnd_561168 < baseStart_561168 := by decide
  rcases family_descends (prefixWord ++ tailWord_561168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561205 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_561205 : Nat := 118140960795 + 561205 * 2 ^ 59
def prefixEnd_561205 : Nat := 4983230072969 + 3 ^ 40 * 561205 * 2
def baseEnd_561205 : Nat := 288167910706582016556571

theorem tailTrace_561205 : CollatzResearch.WordTrace tailWord_561205 prefixEnd_561205 288167910706582016556571 := by
  unfold tailWord_561205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468827931857606028405069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13645885287905070685603379 20468827931857606028405069)
  ·
    refine ⟨7675810474446602260651901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20468827931857606028405069 7675810474446602260651901)
    ·
      refine ⟨2878428927917475847744463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7675810474446602260651901 2878428927917475847744463)
      ·
        refine ⟨4317643391876213771616695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878428927917475847744463 4317643391876213771616695)
        ·
          refine ⟨6476465087814320657425043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317643391876213771616695 6476465087814320657425043)
          ·
            refine ⟨9714697631721480986137565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476465087814320657425043 9714697631721480986137565)
            ·
              refine ⟨3643011611895555369801587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9714697631721480986137565 3643011611895555369801587)
              ·
                refine ⟨5464517417843333054702381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643011611895555369801587 5464517417843333054702381)
                ·
                  refine ⟨2049194031691249895513393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5464517417843333054702381 2049194031691249895513393)
                  ·
                    refine ⟨1536895523768437421635045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049194031691249895513393 1536895523768437421635045)
                    ·
                      refine ⟨288167910706582016556571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1536895523768437421635045 288167910706582016556571)
                      ·
                        rfl

theorem cell23_561205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_561205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561205 prefixEnd_561205 := by exact prefixLift 561205
  have htrace : WordTrace (prefixWord ++ tailWord_561205) baseStart_561205 baseEnd_561205 := by
    simpa [prefixWord, tailWord_561205, baseEnd_561205] using wordTrace_append hprefix tailTrace_561205
  have hstable : (prefixWord ++ tailWord_561205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561205).length < 2 ^ (prefixWord ++ tailWord_561205).sum := by decide
  have hdescent : baseEnd_561205 < baseStart_561205 := by decide
  rcases family_descends (prefixWord ++ tailWord_561205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561225 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_561225 : Nat := 118140960795 + 561225 * 2 ^ 59
def prefixEnd_561225 : Nat := 4983230072969 + 3 ^ 40 * 561225 * 2
def baseEnd_561225 : Nat := 288178180319671938306479

theorem tailTrace_561225 : CollatzResearch.WordTrace tailWord_561225 prefixEnd_561225 288178180319671938306479 := by
  unfold tailWord_561225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20469557391785149444133129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13646371594523432962755419 20469557391785149444133129)
  ·
    refine ⟨15352168043838862083099847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20469557391785149444133129 15352168043838862083099847)
    ·
      refine ⟨23028252065758293124649771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15352168043838862083099847 23028252065758293124649771)
      ·
        refine ⟨34542378098637439686974657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23028252065758293124649771 34542378098637439686974657)
        ·
          refine ⟨25906783573978079765230993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34542378098637439686974657 25906783573978079765230993)
          ·
            refine ⟨19430087680483559823923245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25906783573978079765230993 19430087680483559823923245)
            ·
              refine ⟨7286282880181334933971217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19430087680483559823923245 7286282880181334933971217)
              ·
                refine ⟨5464712160136001200478413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7286282880181334933971217 5464712160136001200478413)
                ·
                  refine ⟨2049267060051000450179405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5464712160136001200478413 2049267060051000450179405)
                  ·
                    refine ⟨768475147519125168817277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049267060051000450179405 768475147519125168817277)
                    ·
                      refine ⟨288178180319671938306479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768475147519125168817277 288178180319671938306479)
                      ·
                        rfl

theorem cell23_561225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_561225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561225 prefixEnd_561225 := by exact prefixLift 561225
  have htrace : WordTrace (prefixWord ++ tailWord_561225) baseStart_561225 baseEnd_561225 := by
    simpa [prefixWord, tailWord_561225, baseEnd_561225] using wordTrace_append hprefix tailTrace_561225
  have hstable : (prefixWord ++ tailWord_561225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561225).length < 2 ^ (prefixWord ++ tailWord_561225).sum := by decide
  have hdescent : baseEnd_561225 < baseStart_561225 := by decide
  rcases family_descends (prefixWord ++ tailWord_561225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561242 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_561242 : Nat := 118140960795 + 561242 * 2 ^ 59
def prefixEnd_561242 : Nat := 4983230072969 + 3 ^ 40 * 561242 * 2
def baseEnd_561242 : Nat := 288186909490798371793901

theorem tailTrace_561242 : CollatzResearch.WordTrace tailWord_561242 prefixEnd_561242 288186909490798371793901 := by
  unfold tailWord_561242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117544358180890336875495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13646784955149040898334653 5117544358180890336875495)
  ·
    refine ⟨7676316537271335505313243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5117544358180890336875495 7676316537271335505313243)
    ·
      refine ⟨11514474805907003257969865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676316537271335505313243 11514474805907003257969865)
      ·
        refine ⟨8635856104430252443477399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11514474805907003257969865 8635856104430252443477399)
        ·
          refine ⟨12953784156645378665216099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635856104430252443477399 12953784156645378665216099)
          ·
            refine ⟨19430676234968067997824149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12953784156645378665216099 19430676234968067997824149)
            ·
              refine ⟨910812948514128187398007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19430676234968067997824149 910812948514128187398007)
              ·
                refine ⟨1366219422771192281097011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910812948514128187398007 1366219422771192281097011)
                ·
                  refine ⟨2049329134156788421645517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366219422771192281097011 2049329134156788421645517)
                  ·
                    refine ⟨768498425308795658117069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049329134156788421645517 768498425308795658117069)
                    ·
                      refine ⟨288186909490798371793901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768498425308795658117069 288186909490798371793901)
                      ·
                        rfl

theorem cell23_561242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_561242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561242 prefixEnd_561242 := by exact prefixLift 561242
  have htrace : WordTrace (prefixWord ++ tailWord_561242) baseStart_561242 baseEnd_561242 := by
    simpa [prefixWord, tailWord_561242, baseEnd_561242] using wordTrace_append hprefix tailTrace_561242
  have hstable : (prefixWord ++ tailWord_561242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561242).length < 2 ^ (prefixWord ++ tailWord_561242).sum := by decide
  have hdescent : baseEnd_561242 < baseStart_561242 := by decide
  rcases family_descends (prefixWord ++ tailWord_561242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561255 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_561255 : Nat := 118140960795 + 561255 * 2 ^ 59
def prefixEnd_561255 : Nat := 4983230072969 + 3 ^ 40 * 561255 * 2
def baseEnd_561255 : Nat := 288193584739306820931341

theorem tailTrace_561255 : CollatzResearch.WordTrace tailWord_561255 prefixEnd_561255 288193584739306820931341 := by
  unfold tailWord_561255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470651581676464567725219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13647101054450976378483479 20470651581676464567725219)
  ·
    refine ⟨30705977372514696851587829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20470651581676464567725219 30705977372514696851587829)
    ·
      refine ⟨2878685378673252829836359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30705977372514696851587829 2878685378673252829836359)
      ·
        refine ⟨4318028068009879244754539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878685378673252829836359 4318028068009879244754539)
        ·
          refine ⟨6477042102014818867131809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318028068009879244754539 6477042102014818867131809)
          ·
            refine ⟨4857781576511114150348857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6477042102014818867131809 4857781576511114150348857)
            ·
              refine ⟨3643336182383335612761643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857781576511114150348857 3643336182383335612761643)
              ·
                refine ⟨5465004273575003419142465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643336182383335612761643 5465004273575003419142465)
                ·
                  refine ⟨4098753205181252564356849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5465004273575003419142465 4098753205181252564356849)
                  ·
                    refine ⟨3074064903885939423267637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4098753205181252564356849 3074064903885939423267637)
                    ·
                      refine ⟨288193584739306820931341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3074064903885939423267637 288193584739306820931341)
                      ·
                        rfl

theorem cell23_561255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_561255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561255 prefixEnd_561255 := by exact prefixLift 561255
  have htrace : WordTrace (prefixWord ++ tailWord_561255) baseStart_561255 baseEnd_561255 := by
    simpa [prefixWord, tailWord_561255, baseEnd_561255] using wordTrace_append hprefix tailTrace_561255
  have hstable : (prefixWord ++ tailWord_561255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561255).length < 2 ^ (prefixWord ++ tailWord_561255).sum := by decide
  have hdescent : baseEnd_561255 < baseStart_561255 := by decide
  rcases family_descends (prefixWord ++ tailWord_561255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561276 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_561276 : Nat := 118140960795 + 561276 * 2 ^ 59
def prefixEnd_561276 : Nat := 4983230072969 + 3 ^ 40 * 561276 * 2
def baseEnd_561276 : Nat := 288204367833051238768745

theorem tailTrace_561276 : CollatzResearch.WordTrace tailWord_561276 prefixEnd_561276 288204367833051238768745 := by
  unfold tailWord_561276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235708757300192577119841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13647611676400256769493121 10235708757300192577119841)
  ·
    refine ⟨7676781567975144432839881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10235708757300192577119841 7676781567975144432839881)
    ·
      refine ⟨5757586175981358324629911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7676781567975144432839881 5757586175981358324629911)
      ·
        refine ⟨8636379263972037486944867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757586175981358324629911 8636379263972037486944867)
        ·
          refine ⟨12954568895958056230417301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8636379263972037486944867 12954568895958056230417301)
          ·
            refine ⟨607245416998033885800811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12954568895958056230417301 607245416998033885800811)
            ·
              refine ⟨910868125497050828701217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607245416998033885800811 910868125497050828701217)
              ·
                refine ⟨683151094122788121525913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910868125497050828701217 683151094122788121525913)
                ·
                  refine ⟨512363320592091091144435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683151094122788121525913 512363320592091091144435)
                  ·
                    refine ⟨768544980888136636716653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512363320592091091144435 768544980888136636716653)
                    ·
                      refine ⟨288204367833051238768745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768544980888136636716653 288204367833051238768745)
                      ·
                        rfl

theorem cell23_561276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_561276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561276 prefixEnd_561276 := by exact prefixLift 561276
  have htrace : WordTrace (prefixWord ++ tailWord_561276) baseStart_561276 baseEnd_561276 := by
    simpa [prefixWord, tailWord_561276, baseEnd_561276] using wordTrace_append hprefix tailTrace_561276
  have hstable : (prefixWord ++ tailWord_561276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561276).length < 2 ^ (prefixWord ++ tailWord_561276).sum := by decide
  have hdescent : baseEnd_561276 < baseStart_561276 := by decide
  rcases family_descends (prefixWord ++ tailWord_561276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561319 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_561319 : Nat := 118140960795 + 561319 * 2 ^ 59
def prefixEnd_561319 : Nat := 4983230072969 + 3 ^ 40 * 561319 * 2
def baseEnd_561319 : Nat := 288226447501194570531047

theorem tailTrace_561319 : CollatzResearch.WordTrace tailWord_561319 prefixEnd_561319 288226447501194570531047 := by
  unfold tailWord_561319
  simp only [CollatzResearch.WordTrace]
  refine ⟨20472985853444603498055011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13648657235629735665370007 20472985853444603498055011)
  ·
    refine ⟨30709478780166905247082517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20472985853444603498055011 30709478780166905247082517)
    ·
      refine ⟨1439506817820323683456993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30709478780166905247082517 1439506817820323683456993)
      ·
        refine ⟨1079630113365242762592745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1439506817820323683456993 1079630113365242762592745)
        ·
          refine ⟨809722585023932071944559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079630113365242762592745 809722585023932071944559)
          ·
            refine ⟨1214583877535898107916839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809722585023932071944559 1214583877535898107916839)
            ·
              refine ⟨1821875816303847161875259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214583877535898107916839 1821875816303847161875259)
              ·
                refine ⟨2732813724455770742812889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821875816303847161875259 2732813724455770742812889)
                ·
                  refine ⟨2049610293341828057109667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2732813724455770742812889 2049610293341828057109667)
                  ·
                    refine ⟨3074415440012742085664501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049610293341828057109667 3074415440012742085664501)
                    ·
                      refine ⟨288226447501194570531047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3074415440012742085664501 288226447501194570531047)
                      ·
                        rfl

theorem cell23_561319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_561319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561319 prefixEnd_561319 := by exact prefixLift 561319
  have htrace : WordTrace (prefixWord ++ tailWord_561319) baseStart_561319 baseEnd_561319 := by
    simpa [prefixWord, tailWord_561319, baseEnd_561319] using wordTrace_append hprefix tailTrace_561319
  have hstable : (prefixWord ++ tailWord_561319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561319).length < 2 ^ (prefixWord ++ tailWord_561319).sum := by decide
  have hdescent : baseEnd_561319 < baseStart_561319 := by decide
  rcases family_descends (prefixWord ++ tailWord_561319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561339 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 5]
def baseStart_561339 : Nat := 118140960795 + 561339 * 2 ^ 59
def prefixEnd_561339 : Nat := 4983230072969 + 3 ^ 40 * 561339 * 2
def baseEnd_561339 : Nat := 32026301901587165808995

theorem tailTrace_561339 : CollatzResearch.WordTrace tailWord_561339 prefixEnd_561339 32026301901587165808995 := by
  unfold tailWord_561339
  simp only [CollatzResearch.WordTrace]
  refine ⟨20473715313372146913783071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13649143542248097942522047 20473715313372146913783071)
  ·
    refine ⟨30710572970058220370674607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20473715313372146913783071 30710572970058220370674607)
    ·
      refine ⟨46065859455087330556011911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30710572970058220370674607 46065859455087330556011911)
      ·
        refine ⟨69098789182630995834017867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46065859455087330556011911 69098789182630995834017867)
        ·
          refine ⟨103648183773946493751026801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69098789182630995834017867 103648183773946493751026801)
          ·
            refine ⟨77736137830459870313270101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103648183773946493751026801 77736137830459870313270101)
            ·
              refine ⟨455485182600350802616817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 77736137830459870313270101 455485182600350802616817)
              ·
                refine ⟨341613886950263101962613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455485182600350802616817 341613886950263101962613)
                ·
                  refine ⟨32026301901587165808995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341613886950263101962613 32026301901587165808995)
                  ·
                    rfl

theorem cell23_561339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 5].length) (baseStart_561339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561339 prefixEnd_561339 := by exact prefixLift 561339
  have htrace : WordTrace (prefixWord ++ tailWord_561339) baseStart_561339 baseEnd_561339 := by
    simpa [prefixWord, tailWord_561339, baseEnd_561339] using wordTrace_append hprefix tailTrace_561339
  have hstable : (prefixWord ++ tailWord_561339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561339).length < 2 ^ (prefixWord ++ tailWord_561339).sum := by decide
  have hdescent : baseEnd_561339 < baseStart_561339 := by decide
  rcases family_descends (prefixWord ++ tailWord_561339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561385 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_561385 : Nat := 118140960795 + 561385 * 2 ^ 59
def prefixEnd_561385 : Nat := 4983230072969 + 3 ^ 40 * 561385 * 2
def baseEnd_561385 : Nat := 288260337224391312305743

theorem tailTrace_561385 : CollatzResearch.WordTrace tailWord_561385 prefixEnd_561385 288260337224391312305743 := by
  unfold tailWord_561385
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475393071205496769957609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650262047470331179971739 20475393071205496769957609)
  ·
    refine ⟨15356544803404122577468207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20475393071205496769957609 15356544803404122577468207)
    ·
      refine ⟨23034817205106183866202311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15356544803404122577468207 23034817205106183866202311)
      ·
        refine ⟨34552225807659275799303467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23034817205106183866202311 34552225807659275799303467)
        ·
          refine ⟨51828338711488913698955201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34552225807659275799303467 51828338711488913698955201)
          ·
            refine ⟨38871254033616685274216401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51828338711488913698955201 38871254033616685274216401)
            ·
              refine ⟨29153440525212513955662301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38871254033616685274216401 29153440525212513955662301)
              ·
                refine ⟨10932540196954692733373363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29153440525212513955662301 10932540196954692733373363)
                ·
                  refine ⟨16398810295432039100060045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10932540196954692733373363 16398810295432039100060045)
                  ·
                    refine ⟨6149553860787014662522517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16398810295432039100060045 6149553860787014662522517)
                    ·
                      refine ⟨288260337224391312305743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6149553860787014662522517 288260337224391312305743)
                      ·
                        rfl

theorem cell23_561385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_561385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561385 prefixEnd_561385 := by exact prefixLift 561385
  have htrace : WordTrace (prefixWord ++ tailWord_561385) baseStart_561385 baseEnd_561385 := by
    simpa [prefixWord, tailWord_561385, baseEnd_561385] using wordTrace_append hprefix tailTrace_561385
  have hstable : (prefixWord ++ tailWord_561385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561385).length < 2 ^ (prefixWord ++ tailWord_561385).sum := by decide
  have hdescent : baseEnd_561385 < baseStart_561385 := by decide
  rcases family_descends (prefixWord ++ tailWord_561385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561406 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_561406 : Nat := 118140960795 + 561406 * 2 ^ 59
def prefixEnd_561406 : Nat := 4983230072969 + 3 ^ 40 * 561406 * 2
def baseEnd_561406 : Nat := 288271120318135730143147

theorem tailTrace_561406 : CollatzResearch.WordTrace tailWord_561406 prefixEnd_561406 288271120318135730143147 := by
  unfold tailWord_561406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559519875516177169559009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13650772669419611570981381 2559519875516177169559009)
  ·
    refine ⟨1919639906637132877169257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2559519875516177169559009 1919639906637132877169257)
    ·
      refine ⟨1439729929977849657876943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919639906637132877169257 1439729929977849657876943)
      ·
        refine ⟨2159594894966774486815415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439729929977849657876943 2159594894966774486815415)
        ·
          refine ⟨3239392342450161730223123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159594894966774486815415 3239392342450161730223123)
          ·
            refine ⟨4859088513675242595334685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239392342450161730223123 4859088513675242595334685)
            ·
              refine ⟨1822158192628215973250507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4859088513675242595334685 1822158192628215973250507)
              ·
                refine ⟨2733237288942323959875761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822158192628215973250507 2733237288942323959875761)
                ·
                  refine ⟨2049927966706742969906821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733237288942323959875761 2049927966706742969906821)
                  ·
                    refine ⟨384361493757514306857529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049927966706742969906821 384361493757514306857529)
                    ·
                      refine ⟨288271120318135730143147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384361493757514306857529 288271120318135730143147)
                      ·
                        rfl

theorem cell23_561406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_561406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561406 prefixEnd_561406 := by exact prefixLift 561406
  have htrace : WordTrace (prefixWord ++ tailWord_561406) baseStart_561406 baseEnd_561406 := by
    simpa [prefixWord, tailWord_561406, baseEnd_561406] using wordTrace_append hprefix tailTrace_561406
  have hstable : (prefixWord ++ tailWord_561406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561406).length < 2 ^ (prefixWord ++ tailWord_561406).sum := by decide
  have hdescent : baseEnd_561406 < baseStart_561406 := by decide
  rcases family_descends (prefixWord ++ tailWord_561406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561472 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_561472 : Nat := 118140960795 + 561472 * 2 ^ 59
def prefixEnd_561472 : Nat := 4983230072969 + 3 ^ 40 * 561472 * 2
def baseEnd_561472 : Nat := 96101670013777490639281

theorem tailTrace_561472 : CollatzResearch.WordTrace tailWord_561472 prefixEnd_561472 96101670013777490639281 := by
  unfold tailWord_561472
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239283110945155314187335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13652377481260207085583113 10239283110945155314187335)
  ·
    refine ⟨15358924666417732971281003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10239283110945155314187335 15358924666417732971281003)
    ·
      refine ⟨23038386999626599456921505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358924666417732971281003 23038386999626599456921505)
      ·
        refine ⟨17278790249719949592691129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23038386999626599456921505 17278790249719949592691129)
        ·
          refine ⟨12959092687289962194518347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17278790249719949592691129 12959092687289962194518347)
          ·
            refine ⟨19438639030934943291777521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12959092687289962194518347 19438639030934943291777521)
            ·
              refine ⟨14578979273201207468833141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19438639030934943291777521 14578979273201207468833141)
              ·
                refine ⟨1366779306862613200203107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14578979273201207468833141 1366779306862613200203107)
                ·
                  refine ⟨2050168960293919800304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366779306862613200203107 2050168960293919800304661)
                  ·
                    refine ⟨96101670013777490639281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2050168960293919800304661 96101670013777490639281)
                    ·
                      rfl

theorem cell23_561472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_561472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561472 prefixEnd_561472 := by exact prefixLift 561472
  have htrace : WordTrace (prefixWord ++ tailWord_561472) baseStart_561472 baseEnd_561472 := by
    simpa [prefixWord, tailWord_561472, baseEnd_561472] using wordTrace_append hprefix tailTrace_561472
  have hstable : (prefixWord ++ tailWord_561472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561472).length < 2 ^ (prefixWord ++ tailWord_561472).sum := by decide
  have hdescent : baseEnd_561472 < baseStart_561472 := by decide
  rcases family_descends (prefixWord ++ tailWord_561472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561479 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_561479 : Nat := 118140960795 + 561479 * 2 ^ 59
def prefixEnd_561479 : Nat := 4983230072969 + 3 ^ 40 * 561479 * 2
def baseEnd_561479 : Nat := 288308604405913944530311

theorem tailTrace_561479 : CollatzResearch.WordTrace tailWord_561479 prefixEnd_561479 288308604405913944530311 := by
  unfold tailWord_561479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478821532864950823879491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13652547688576633882586327 20478821532864950823879491)
  ·
    refine ⟨30718232299297426235819237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20478821532864950823879491 30718232299297426235819237)
    ·
      refine ⟨5759668556118267419216107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30718232299297426235819237 5759668556118267419216107)
      ·
        refine ⟨8639502834177401128824161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759668556118267419216107 8639502834177401128824161)
        ·
          refine ⟨6479627125633050846618121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8639502834177401128824161 6479627125633050846618121)
          ·
            refine ⟨4859720344224788134963591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6479627125633050846618121 4859720344224788134963591)
            ·
              refine ⟨7289580516337182202445387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859720344224788134963591 7289580516337182202445387)
              ·
                refine ⟨10934370774505773303668081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7289580516337182202445387 10934370774505773303668081)
                ·
                  refine ⟨8200778080879329977751061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10934370774505773303668081 8200778080879329977751061)
                  ·
                    refine ⟨384411472541218592707081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8200778080879329977751061 384411472541218592707081)
                    ·
                      refine ⟨288308604405913944530311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384411472541218592707081 288308604405913944530311)
                      ·
                        rfl

theorem cell23_561479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_561479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561479 prefixEnd_561479 := by exact prefixLift 561479
  have htrace : WordTrace (prefixWord ++ tailWord_561479) baseStart_561479 baseEnd_561479 := by
    simpa [prefixWord, tailWord_561479, baseEnd_561479] using wordTrace_append hprefix tailTrace_561479
  have hstable : (prefixWord ++ tailWord_561479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561479).length < 2 ^ (prefixWord ++ tailWord_561479).sum := by decide
  have hdescent : baseEnd_561479 < baseStart_561479 := by decide
  rcases family_descends (prefixWord ++ tailWord_561479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561489 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_561489 : Nat := 118140960795 + 561489 * 2 ^ 59
def prefixEnd_561489 : Nat := 4983230072969 + 3 ^ 40 * 561489 * 2
def baseEnd_561489 : Nat := 96104579737486301801755

theorem tailTrace_561489 : CollatzResearch.WordTrace tailWord_561489 prefixEnd_561489 96104579737486301801755 := by
  unfold tailWord_561489
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479186262828722531743521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13652790841885815021162347 20479186262828722531743521)
  ·
    refine ⟨15359389697121541898807641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20479186262828722531743521 15359389697121541898807641)
    ·
      refine ⟨11519542272841156424105731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15359389697121541898807641 11519542272841156424105731)
      ·
        refine ⟨17279313409261734636158597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519542272841156424105731 17279313409261734636158597)
        ·
          refine ⟨3239871264236575244279737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17279313409261734636158597 3239871264236575244279737)
          ·
            refine ⟨2429903448177431433209803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239871264236575244279737 2429903448177431433209803)
            ·
              refine ⟨3644855172266147149814705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429903448177431433209803 3644855172266147149814705)
              ·
                refine ⟨2733641379199610362361029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644855172266147149814705 2733641379199610362361029)
                ·
                  refine ⟨512557758599926942942693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2733641379199610362361029 512557758599926942942693)
                  ·
                    refine ⟨96104579737486301801755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512557758599926942942693 96104579737486301801755)
                    ·
                      rfl

theorem cell23_561489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_561489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561489 prefixEnd_561489 := by exact prefixLift 561489
  have htrace : WordTrace (prefixWord ++ tailWord_561489) baseStart_561489 baseEnd_561489 := by
    simpa [prefixWord, tailWord_561489, baseEnd_561489] using wordTrace_append hprefix tailTrace_561489
  have hstable : (prefixWord ++ tailWord_561489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561489).length < 2 ^ (prefixWord ++ tailWord_561489).sum := by decide
  have hdescent : baseEnd_561489 < baseStart_561489 := by decide
  rcases family_descends (prefixWord ++ tailWord_561489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561500 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_561500 : Nat := 118140960795 + 561500 * 2 ^ 59
def prefixEnd_561500 : Nat := 4983230072969 + 3 ^ 40 * 561500 * 2
def baseEnd_561500 : Nat := 288319387499658362367715

theorem tailTrace_561500 : CollatzResearch.WordTrace tailWord_561500 prefixEnd_561500 288319387499658362367715 := by
  unfold tailWord_561500
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239793732894435705196977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13653058310525914273595969 10239793732894435705196977)
  ·
    refine ⟨7679845299670826778897733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10239793732894435705196977 7679845299670826778897733)
    ·
      refine ⟨1439970993688280021043325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7679845299670826778897733 1439970993688280021043325)
      ·
        refine ⟨539989122633105007891247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1439970993688280021043325 539989122633105007891247)
        ·
          refine ⟨809983683949657511836871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539989122633105007891247 809983683949657511836871)
          ·
            refine ⟨1214975525924486267755307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809983683949657511836871 1214975525924486267755307)
            ·
              refine ⟨1822463288886729401632961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214975525924486267755307 1822463288886729401632961)
              ·
                refine ⟨1366847466665047051224721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822463288886729401632961 1366847466665047051224721)
                ·
                  refine ⟨1025135599998785288418541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366847466665047051224721 1025135599998785288418541)
                  ·
                    refine ⟨384425849999544483156953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025135599998785288418541 384425849999544483156953)
                    ·
                      refine ⟨288319387499658362367715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384425849999544483156953 288319387499658362367715)
                      ·
                        rfl

theorem cell23_561500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_561500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561500 prefixEnd_561500 := by exact prefixLift 561500
  have htrace : WordTrace (prefixWord ++ tailWord_561500) baseStart_561500 baseEnd_561500 := by
    simpa [prefixWord, tailWord_561500, baseEnd_561500] using wordTrace_append hprefix tailTrace_561500
  have hstable : (prefixWord ++ tailWord_561500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561500).length < 2 ^ (prefixWord ++ tailWord_561500).sum := by decide
  have hdescent : baseEnd_561500 < baseStart_561500 := by decide
  rcases family_descends (prefixWord ++ tailWord_561500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561506 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_561506 : Nat := 118140960795 + 561506 * 2 ^ 59
def prefixEnd_561506 : Nat := 4983230072969 + 3 ^ 40 * 561506 * 2
def baseEnd_561506 : Nat := 96107489461195112964229

theorem tailTrace_561506 : CollatzResearch.WordTrace tailWord_561506 prefixEnd_561506 96107489461195112964229 := by
  unfold tailWord_561506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119951575941783608778093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13653204202511422956741581 5119951575941783608778093)
  ·
    refine ⟨1919981840978168853291785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5119951575941783608778093 1919981840978168853291785)
    ·
      refine ⟨1439986380733626639968839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919981840978168853291785 1439986380733626639968839)
      ·
        refine ⟨2159979571100439959953259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439986380733626639968839 2159979571100439959953259)
        ·
          refine ⟨3239969356650659939929889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159979571100439959953259 3239969356650659939929889)
          ·
            refine ⟨2429977017487994954947417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239969356650659939929889 2429977017487994954947417)
            ·
              refine ⟨1822482763115996216210563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2429977017487994954947417 1822482763115996216210563)
              ·
                refine ⟨2733724144673994324315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822482763115996216210563 2733724144673994324315845)
                ·
                  refine ⟨512573277126373935809221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2733724144673994324315845 512573277126373935809221)
                  ·
                    refine ⟨96107489461195112964229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512573277126373935809221 96107489461195112964229)
                    ·
                      rfl

theorem cell23_561506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_561506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561506 prefixEnd_561506 := by exact prefixLift 561506
  have htrace : WordTrace (prefixWord ++ tailWord_561506) baseStart_561506 baseEnd_561506 := by
    simpa [prefixWord, tailWord_561506, baseEnd_561506] using wordTrace_append hprefix tailTrace_561506
  have hstable : (prefixWord ++ tailWord_561506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561506).length < 2 ^ (prefixWord ++ tailWord_561506).sum := by decide
  have hdescent : baseEnd_561506 < baseStart_561506 := by decide
  rcases family_descends (prefixWord ++ tailWord_561506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561529 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_561529 : Nat := 118140960795 + 561529 * 2 ^ 59
def prefixEnd_561529 : Nat := 4983230072969 + 3 ^ 40 * 561529 * 2
def baseEnd_561529 : Nat := 288334278438638748905081

theorem tailTrace_561529 : CollatzResearch.WordTrace tailWord_561529 prefixEnd_561529 288334278438638748905081 := by
  unfold tailWord_561529
  simp only [CollatzResearch.WordTrace]
  refine ⟨20480645182683809363199641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13653763455122539575466427 20480645182683809363199641)
  ·
    refine ⟨15360483887012857022399731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20480645182683809363199641 15360483887012857022399731)
    ·
      refine ⟨23040725830519285533599597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15360483887012857022399731 23040725830519285533599597)
      ·
        refine ⟨8640272186444732075099849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23040725830519285533599597 8640272186444732075099849)
        ·
          refine ⟨6480204139833549056324887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640272186444732075099849 6480204139833549056324887)
          ·
            refine ⟨9720306209750323584487331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6480204139833549056324887 9720306209750323584487331)
            ·
              refine ⟨14580459314625485376730997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9720306209750323584487331 14580459314625485376730997)
              ·
                refine ⟨1366918060746139254068531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14580459314625485376730997 1366918060746139254068531)
                ·
                  refine ⟨2050377091119208881102797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366918060746139254068531 2050377091119208881102797)
                  ·
                    refine ⟨768891409169703330413549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050377091119208881102797 768891409169703330413549)
                    ·
                      refine ⟨288334278438638748905081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768891409169703330413549 288334278438638748905081)
                      ·
                        rfl

theorem cell23_561529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_561529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561529 prefixEnd_561529 := by exact prefixLift 561529
  have htrace : WordTrace (prefixWord ++ tailWord_561529) baseStart_561529 baseEnd_561529 := by
    simpa [prefixWord, tailWord_561529, baseEnd_561529] using wordTrace_append hprefix tailTrace_561529
  have hstable : (prefixWord ++ tailWord_561529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561529).length < 2 ^ (prefixWord ++ tailWord_561529).sum := by decide
  have hdescent : baseEnd_561529 < baseStart_561529 := by decide
  rcases family_descends (prefixWord ++ tailWord_561529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561532 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_561532 : Nat := 118140960795 + 561532 * 2 ^ 59
def prefixEnd_561532 : Nat := 4983230072969 + 3 ^ 40 * 561532 * 2
def baseEnd_561532 : Nat := 96111939626867412389189

theorem tailTrace_561532 : CollatzResearch.WordTrace tailWord_561532 prefixEnd_561532 96111939626867412389189 := by
  unfold tailWord_561532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240377300836470437779425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13653836401115293917039233 10240377300836470437779425)
  ·
    refine ⟨7680282975627352828334569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10240377300836470437779425 7680282975627352828334569)
    ·
      refine ⟨5760212231720514621250927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7680282975627352828334569 5760212231720514621250927)
      ·
        refine ⟨8640318347580771931876391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760212231720514621250927 8640318347580771931876391)
        ·
          refine ⟨12960477521371157897814587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640318347580771931876391 12960477521371157897814587)
          ·
            refine ⟨19440716282056736846721881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12960477521371157897814587 19440716282056736846721881)
            ·
              refine ⟨14580537211542552635041411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19440716282056736846721881 14580537211542552635041411)
              ·
                refine ⟨21870805817313828952562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14580537211542552635041411 21870805817313828952562117)
                ·
                  refine ⟨4100776090746342928605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21870805817313828952562117 4100776090746342928605397)
                  ·
                    refine ⟨96111939626867412389189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4100776090746342928605397 96111939626867412389189)
                    ·
                      rfl

theorem cell23_561532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_561532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561532 prefixEnd_561532 := by exact prefixLift 561532
  have htrace : WordTrace (prefixWord ++ tailWord_561532) baseStart_561532 baseEnd_561532 := by
    simpa [prefixWord, tailWord_561532, baseEnd_561532] using wordTrace_append hprefix tailTrace_561532
  have hstable : (prefixWord ++ tailWord_561532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561532).length < 2 ^ (prefixWord ++ tailWord_561532).sum := by decide
  have hdescent : baseEnd_561532 < baseStart_561532 := by decide
  rcases family_descends (prefixWord ++ tailWord_561532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561533 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_561533 : Nat := 118140960795 + 561533 * 2 ^ 59
def prefixEnd_561533 : Nat := 4983230072969 + 3 ^ 40 * 561533 * 2
def baseEnd_561533 : Nat := 288336332361256733255063

theorem tailTrace_561533 : CollatzResearch.WordTrace tailWord_561533 prefixEnd_561533 288336332361256733255063 := by
  unfold tailWord_561533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20480791074669318046345253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13653860716446212030896835 20480791074669318046345253)
  ·
    refine ⟨3840148326500497133689735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20480791074669318046345253 3840148326500497133689735)
    ·
      refine ⟨5760222489750745700534603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840148326500497133689735 5760222489750745700534603)
      ·
        refine ⟨8640333734626118550801905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760222489750745700534603 8640333734626118550801905)
        ·
          refine ⟨6480250300969588913101429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640333734626118550801905 6480250300969588913101429)
          ·
            refine ⟨607523465715898960603259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6480250300969588913101429 607523465715898960603259)
            ·
              refine ⟨911285198573848440904889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607523465715898960603259 911285198573848440904889)
              ·
                refine ⟨683463898930386330678667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911285198573848440904889 683463898930386330678667)
                ·
                  refine ⟨1025195848395579496018001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683463898930386330678667 1025195848395579496018001)
                  ·
                    refine ⟨768896886296684622013501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025195848395579496018001 768896886296684622013501)
                    ·
                      refine ⟨288336332361256733255063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768896886296684622013501 288336332361256733255063)
                      ·
                        rfl

theorem cell23_561533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_561533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561533 prefixEnd_561533 := by exact prefixLift 561533
  have htrace : WordTrace (prefixWord ++ tailWord_561533) baseStart_561533 baseEnd_561533 := by
    simpa [prefixWord, tailWord_561533, baseEnd_561533] using wordTrace_append hprefix tailTrace_561533
  have hstable : (prefixWord ++ tailWord_561533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561533).length < 2 ^ (prefixWord ++ tailWord_561533).sum := by decide
  have hdescent : baseEnd_561533 < baseStart_561533 := by decide
  rcases family_descends (prefixWord ++ tailWord_561533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561550 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_561550 : Nat := 118140960795 + 561550 * 2 ^ 59
def prefixEnd_561550 : Nat := 4983230072969 + 3 ^ 40 * 561550 * 2
def baseEnd_561550 : Nat := 288345061532383166742485

theorem tailTrace_561550 : CollatzResearch.WordTrace tailWord_561550 prefixEnd_561550 288345061532383166742485 := by
  unfold tailWord_561550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560176389450966243714263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13654274077071819966476069 2560176389450966243714263)
  ·
    refine ⟨3840264584176449365571395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560176389450966243714263 3840264584176449365571395)
    ·
      refine ⟨5760396876264674048357093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840264584176449365571395 5760396876264674048357093)
      ·
        refine ⟨1080074414299626384066955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5760396876264674048357093 1080074414299626384066955)
        ·
          refine ⟨1620111621449439576100433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080074414299626384066955 1620111621449439576100433)
          ·
            refine ⟨1215083716087079682075325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620111621449439576100433 1215083716087079682075325)
            ·
              refine ⟨455656393532654880778247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215083716087079682075325 455656393532654880778247)
              ·
                refine ⟨683484590298982321167371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455656393532654880778247 683484590298982321167371)
                ·
                  refine ⟨1025226885448473481751057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683484590298982321167371 1025226885448473481751057)
                  ·
                    refine ⟨768920164086355111313293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025226885448473481751057 768920164086355111313293)
                    ·
                      refine ⟨288345061532383166742485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768920164086355111313293 288345061532383166742485)
                      ·
                        rfl

theorem cell23_561550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_561550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561550 prefixEnd_561550 := by exact prefixLift 561550
  have htrace : WordTrace (prefixWord ++ tailWord_561550) baseStart_561550 baseEnd_561550 := by
    simpa [prefixWord, tailWord_561550, baseEnd_561550] using wordTrace_append hprefix tailTrace_561550
  have hstable : (prefixWord ++ tailWord_561550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561550).length < 2 ^ (prefixWord ++ tailWord_561550).sum := by decide
  have hdescent : baseEnd_561550 < baseStart_561550 := by decide
  rcases family_descends (prefixWord ++ tailWord_561550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561558 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_561558 : Nat := 118140960795 + 561558 * 2 ^ 59
def prefixEnd_561558 : Nat := 4983230072969 + 3 ^ 40 * 561558 * 2
def baseEnd_561558 : Nat := 288349169377619135442449

theorem tailTrace_561558 : CollatzResearch.WordTrace tailWord_561558 prefixEnd_561558 288349169377619135442449 := by
  unfold tailWord_561558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280106431223671707250333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13654468599719164877336885 1280106431223671707250333)
  ·
    refine ⟨480039911708876890218875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1280106431223671707250333 480039911708876890218875)
    ·
      refine ⟨720059867563315335328313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480039911708876890218875 720059867563315335328313)
      ·
        refine ⟨540044900672486501496235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720059867563315335328313 540044900672486501496235)
        ·
          refine ⟨810067351008729752244353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540044900672486501496235 810067351008729752244353)
          ·
            refine ⟨607550513256547314183265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810067351008729752244353 607550513256547314183265)
            ·
              refine ⟨455662884942410485637449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607550513256547314183265 455662884942410485637449)
              ·
                refine ⟨341747163706807864228087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455662884942410485637449 341747163706807864228087)
                ·
                  refine ⟨512620745560211796342131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341747163706807864228087 512620745560211796342131)
                  ·
                    refine ⟨768931118340317694513197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512620745560211796342131 768931118340317694513197)
                    ·
                      refine ⟨288349169377619135442449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768931118340317694513197 288349169377619135442449)
                      ·
                        rfl

theorem cell23_561558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_561558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561558 prefixEnd_561558 := by exact prefixLift 561558
  have htrace : WordTrace (prefixWord ++ tailWord_561558) baseStart_561558 baseEnd_561558 := by
    simpa [prefixWord, tailWord_561558, baseEnd_561558] using wordTrace_append hprefix tailTrace_561558
  have hstable : (prefixWord ++ tailWord_561558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561558).length < 2 ^ (prefixWord ++ tailWord_561558).sum := by decide
  have hdescent : baseEnd_561558 < baseStart_561558 := by decide
  rcases family_descends (prefixWord ++ tailWord_561558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561566 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_561566 : Nat := 118140960795 + 561566 * 2 ^ 59
def prefixEnd_561566 : Nat := 4983230072969 + 3 ^ 40 * 561566 * 2
def baseEnd_561566 : Nat := 96117759074285034714137

theorem tailTrace_561566 : CollatzResearch.WordTrace tailWord_561566 prefixEnd_561566 96117759074285034714137 := by
  unfold tailWord_561566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560249335443720585287069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13654663122366509788197701 2560249335443720585287069)
  ·
    refine ⟨960093500791395219482651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2560249335443720585287069 960093500791395219482651)
    ·
      refine ⟨1440140251187092829223977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960093500791395219482651 1440140251187092829223977)
      ·
        refine ⟨1080105188390319621917983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440140251187092829223977 1080105188390319621917983)
        ·
          refine ⟨1620157782585479432876975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080105188390319621917983 1620157782585479432876975)
          ·
            refine ⟨2430236673878219149315463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620157782585479432876975 2430236673878219149315463)
            ·
              refine ⟨3645355010817328723973195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430236673878219149315463 3645355010817328723973195)
              ·
                refine ⟨5468032516225993085959793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645355010817328723973195 5468032516225993085959793)
                ·
                  refine ⟨4101024387169494814469845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468032516225993085959793 4101024387169494814469845)
                  ·
                    refine ⟨96117759074285034714137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4101024387169494814469845 96117759074285034714137)
                    ·
                      rfl

theorem cell23_561566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_561566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561566 prefixEnd_561566 := by exact prefixLift 561566
  have htrace : WordTrace (prefixWord ++ tailWord_561566) baseStart_561566 baseEnd_561566 := by
    simpa [prefixWord, tailWord_561566, baseEnd_561566] using wordTrace_append hprefix tailTrace_561566
  have hstable : (prefixWord ++ tailWord_561566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561566).length < 2 ^ (prefixWord ++ tailWord_561566).sum := by decide
  have hdescent : baseEnd_561566 < baseStart_561566 := by decide
  rcases family_descends (prefixWord ++ tailWord_561566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561601 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_561601 : Nat := 118140960795 + 561601 * 2 ^ 59
def prefixEnd_561601 : Nat := 4983230072969 + 3 ^ 40 * 561601 * 2
def baseEnd_561601 : Nat := 288371249045762467204751

theorem tailTrace_561601 : CollatzResearch.WordTrace tailWord_561601 prefixEnd_561601 288371249045762467204751 := by
  unfold tailWord_561601
  simp only [CollatzResearch.WordTrace]
  refine ⟨20483271238422965659820657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13655514158948643773213771 20483271238422965659820657)
  ·
    refine ⟨15362453428817224244865493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20483271238422965659820657 15362453428817224244865493)
    ·
      refine ⟨360057502237903693239035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15362453428817224244865493 360057502237903693239035)
      ·
        refine ⟨540086253356855539858553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360057502237903693239035 540086253356855539858553)
        ·
          refine ⟨405064690017641654893915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540086253356855539858553 405064690017641654893915)
          ·
            refine ⟨607597035026462482340873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405064690017641654893915 607597035026462482340873)
            ·
              refine ⟨455697776269846861755655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607597035026462482340873 455697776269846861755655)
              ·
                refine ⟨683546664404770292633483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455697776269846861755655 683546664404770292633483)
                ·
                  refine ⟨1025319996607155438950225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683546664404770292633483 1025319996607155438950225)
                  ·
                    refine ⟨768989997455366579212669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025319996607155438950225 768989997455366579212669)
                    ·
                      refine ⟨288371249045762467204751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 768989997455366579212669 288371249045762467204751)
                      ·
                        rfl

theorem cell23_561601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_561601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561601 prefixEnd_561601 := by exact prefixLift 561601
  have htrace : WordTrace (prefixWord ++ tailWord_561601) baseStart_561601 baseEnd_561601 := by
    simpa [prefixWord, tailWord_561601, baseEnd_561601] using wordTrace_append hprefix tailTrace_561601
  have hstable : (prefixWord ++ tailWord_561601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561601).length < 2 ^ (prefixWord ++ tailWord_561601).sum := by decide
  have hdescent : baseEnd_561601 < baseStart_561601 := by decide
  rcases family_descends (prefixWord ++ tailWord_561601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561620 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_561620 : Nat := 118140960795 + 561620 * 2 ^ 59
def prefixEnd_561620 : Nat := 4983230072969 + 3 ^ 40 * 561620 * 2
def baseEnd_561620 : Nat := 288381005178197892867163

theorem tailTrace_561620 : CollatzResearch.WordTrace tailWord_561620 prefixEnd_561620 288381005178197892867163 := by
  unfold tailWord_561620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10241982112677065952381157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13655976150236087936508209 10241982112677065952381157)
  ·
    refine ⟨1920371646126949866071467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10241982112677065952381157 1920371646126949866071467)
    ·
      refine ⟨2880557469190424799107201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920371646126949866071467 2880557469190424799107201)
      ·
        refine ⟨2160418101892818599330401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880557469190424799107201 2160418101892818599330401)
        ·
          refine ⟨1620313576419613949497801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160418101892818599330401 1620313576419613949497801)
          ·
            refine ⟨1215235182314710462123351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620313576419613949497801 1215235182314710462123351)
            ·
              refine ⟨1822852773472065693185027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215235182314710462123351 1822852773472065693185027)
              ·
                refine ⟨2734279160208098539777541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822852773472065693185027 2734279160208098539777541)
                ·
                  refine ⟨512677342539018476208289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2734279160208098539777541 512677342539018476208289)
                  ·
                    refine ⟨384508006904263857156217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 512677342539018476208289 384508006904263857156217)
                    ·
                      refine ⟨288381005178197892867163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384508006904263857156217 288381005178197892867163)
                      ·
                        rfl

theorem cell23_561620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_561620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561620 prefixEnd_561620 := by exact prefixLift 561620
  have htrace : WordTrace (prefixWord ++ tailWord_561620) baseStart_561620 baseEnd_561620 := by
    simpa [prefixWord, tailWord_561620, baseEnd_561620] using wordTrace_append hprefix tailTrace_561620
  have hstable : (prefixWord ++ tailWord_561620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561620).length < 2 ^ (prefixWord ++ tailWord_561620).sum := by decide
  have hdescent : baseEnd_561620 < baseStart_561620 := by decide
  rcases family_descends (prefixWord ++ tailWord_561620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561626 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_561626 : Nat := 118140960795 + 561626 * 2 ^ 59
def prefixEnd_561626 : Nat := 4983230072969 + 3 ^ 40 * 561626 * 2
def baseEnd_561626 : Nat := 32042676229124985488015

theorem tailTrace_561626 : CollatzResearch.WordTrace tailWord_561626 prefixEnd_561626 32042676229124985488015 := by
  unfold tailWord_561626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121045765833098732370183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13656122042221596619653821 5121045765833098732370183)
  ·
    refine ⟨7681568648749648098555275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5121045765833098732370183 7681568648749648098555275)
    ·
      refine ⟨11522352973124472147832913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681568648749648098555275 11522352973124472147832913)
      ·
        refine ⟨8641764729843354110874685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11522352973124472147832913 8641764729843354110874685)
        ·
          refine ⟨3240661773691257791578007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8641764729843354110874685 3240661773691257791578007)
          ·
            refine ⟨4860992660536886687367011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240661773691257791578007 4860992660536886687367011)
            ·
              refine ⟨7291488990805330031050517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860992660536886687367011 7291488990805330031050517)
              ·
                refine ⟨341788546443999845205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7291488990805330031050517 341788546443999845205493)
                ·
                  refine ⟨32042676229124985488015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341788546443999845205493 32042676229124985488015)
                  ·
                    rfl

theorem cell23_561626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_561626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561626 prefixEnd_561626 := by exact prefixLift 561626
  have htrace : WordTrace (prefixWord ++ tailWord_561626) baseStart_561626 baseEnd_561626 := by
    simpa [prefixWord, tailWord_561626, baseEnd_561626] using wordTrace_append hprefix tailTrace_561626
  have hstable : (prefixWord ++ tailWord_561626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561626).length < 2 ^ (prefixWord ++ tailWord_561626).sum := by decide
  have hdescent : baseEnd_561626 < baseStart_561626 := by decide
  rcases family_descends (prefixWord ++ tailWord_561626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561637 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_561637 : Nat := 118140960795 + 561637 * 2 ^ 59
def prefixEnd_561637 : Nat := 4983230072969 + 3 ^ 40 * 561637 * 2
def baseEnd_561637 : Nat := 288389734349324326354585

theorem tailTrace_561637 : CollatzResearch.WordTrace tailWord_561637 prefixEnd_561637 288389734349324326354585 := by
  unfold tailWord_561637
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484584266292543808131165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13656389510861695872087443 20484584266292543808131165)
  ·
    refine ⟨7681719099859703928049187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20484584266292543808131165 7681719099859703928049187)
    ·
      refine ⟨11522578649789555892073781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681719099859703928049187 11522578649789555892073781)
      ·
        refine ⟨1080241748417770864881917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11522578649789555892073781 1080241748417770864881917)
        ·
          refine ⟨405090655656664074330719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1080241748417770864881917 405090655656664074330719)
          ·
            refine ⟨607635983484996111496079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405090655656664074330719 607635983484996111496079)
            ·
              refine ⟨911453975227494167244119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607635983484996111496079 911453975227494167244119)
              ·
                refine ⟨1367180962841241250866179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911453975227494167244119 1367180962841241250866179)
                ·
                  refine ⟨2050771444261861876299269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367180962841241250866179 2050771444261861876299269)
                  ·
                    refine ⟨384519645799099101806113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050771444261861876299269 384519645799099101806113)
                    ·
                      refine ⟨288389734349324326354585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384519645799099101806113 288389734349324326354585)
                      ·
                        rfl

theorem cell23_561637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_561637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561637 prefixEnd_561637 := by exact prefixLift 561637
  have htrace : WordTrace (prefixWord ++ tailWord_561637) baseStart_561637 baseEnd_561637 := by
    simpa [prefixWord, tailWord_561637, baseEnd_561637] using wordTrace_append hprefix tailTrace_561637
  have hstable : (prefixWord ++ tailWord_561637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561637).length < 2 ^ (prefixWord ++ tailWord_561637).sum := by decide
  have hdescent : baseEnd_561637 < baseStart_561637 := by decide
  rcases family_descends (prefixWord ++ tailWord_561637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561639 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 7]
def baseStart_561639 : Nat := 118140960795 + 561639 * 2 ^ 59
def prefixEnd_561639 : Nat := 4983230072969 + 3 ^ 40 * 561639 * 2
def baseEnd_561639 : Nat := 96130253770211106176525

theorem tailTrace_561639 : CollatzResearch.WordTrace tailWord_561639 prefixEnd_561639 96130253770211106176525 := by
  unfold tailWord_561639
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484657212285298149703971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13656438141523532099802647 20484657212285298149703971)
  ·
    refine ⟨30726985818427947224555957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20484657212285298149703971 30726985818427947224555957)
    ·
      refine ⟨2880654920477620052302121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30726985818427947224555957 2880654920477620052302121)
      ·
        refine ⟨2160491190358215039226591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880654920477620052302121 2160491190358215039226591)
        ·
          refine ⟨3240736785537322558839887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160491190358215039226591 3240736785537322558839887)
          ·
            refine ⟨4861105178305983838259831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240736785537322558839887 4861105178305983838259831)
            ·
              refine ⟨7291657767458975757389747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861105178305983838259831 7291657767458975757389747)
              ·
                refine ⟨10937486651188463636084621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291657767458975757389747 10937486651188463636084621)
                ·
                  refine ⟨4101557494195673863531733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10937486651188463636084621 4101557494195673863531733)
                  ·
                    refine ⟨96130253770211106176525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4101557494195673863531733 96130253770211106176525)
                    ·
                      rfl

theorem cell23_561639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_561639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561639 prefixEnd_561639 := by exact prefixLift 561639
  have htrace : WordTrace (prefixWord ++ tailWord_561639) baseStart_561639 baseEnd_561639 := by
    simpa [prefixWord, tailWord_561639, baseEnd_561639] using wordTrace_append hprefix tailTrace_561639
  have hstable : (prefixWord ++ tailWord_561639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561639).length < 2 ^ (prefixWord ++ tailWord_561639).sum := by decide
  have hdescent : baseEnd_561639 < baseStart_561639 := by decide
  rcases family_descends (prefixWord ++ tailWord_561639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561676 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_561676 : Nat := 118140960795 + 561676 * 2 ^ 59
def prefixEnd_561676 : Nat := 4983230072969 + 3 ^ 40 * 561676 * 2
def baseEnd_561676 : Nat := 288409760094849673766905

theorem tailTrace_561676 : CollatzResearch.WordTrace tailWord_561676 prefixEnd_561676 288409760094849673766905 := by
  unfold tailWord_561676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243003356575626734400441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13657337808767502312533921 10243003356575626734400441)
  ·
    refine ⟨7682252517431720050800331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10243003356575626734400441 7682252517431720050800331)
    ·
      refine ⟨11523378776147580076200497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7682252517431720050800331 11523378776147580076200497)
      ·
        refine ⟨8642534082110685057150373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11523378776147580076200497 8642534082110685057150373)
        ·
          refine ⟨1620475140395753448215695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8642534082110685057150373 1620475140395753448215695)
          ·
            refine ⟨2430712710593630172323543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620475140395753448215695 2430712710593630172323543)
            ·
              refine ⟨3646069065890445258485315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430712710593630172323543 3646069065890445258485315)
              ·
                refine ⟨5469103598835667887727973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646069065890445258485315 5469103598835667887727973)
                ·
                  refine ⟨1025456924781687728948995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5469103598835667887727973 1025456924781687728948995)
                  ·
                    refine ⟨1538185387172531593423493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025456924781687728948995 1538185387172531593423493)
                    ·
                      refine ⟨288409760094849673766905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1538185387172531593423493 288409760094849673766905)
                      ·
                        rfl

theorem cell23_561676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_561676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561676 prefixEnd_561676 := by exact prefixLift 561676
  have htrace : WordTrace (prefixWord ++ tailWord_561676) baseStart_561676 baseEnd_561676 := by
    simpa [prefixWord, tailWord_561676, baseEnd_561676] using wordTrace_append hprefix tailTrace_561676
  have hstable : (prefixWord ++ tailWord_561676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561676).length < 2 ^ (prefixWord ++ tailWord_561676).sum := by decide
  have hdescent : baseEnd_561676 < baseStart_561676 := by decide
  rcases family_descends (prefixWord ++ tailWord_561676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561710 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_561710 : Nat := 118140960795 + 561710 * 2 ^ 59
def prefixEnd_561710 : Nat := 4983230072969 + 3 ^ 40 * 561710 * 2
def baseEnd_561710 : Nat := 288427218437102540741749

theorem tailTrace_561710 : CollatzResearch.WordTrace tailWord_561710 prefixEnd_561710 288427218437102540741749 := by
  unfold tailWord_561710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560905849378509659442323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13658164530018718183692389 2560905849378509659442323)
  ·
    refine ⟨3841358774067764489163485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560905849378509659442323 3841358774067764489163485)
    ·
      refine ⟨1440509540275411683436307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3841358774067764489163485 1440509540275411683436307)
      ·
        refine ⟨2160764310413117525154461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440509540275411683436307 2160764310413117525154461)
        ·
          refine ⟨810286616404919071932923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2160764310413117525154461 810286616404919071932923)
          ·
            refine ⟨1215429924607378607899385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810286616404919071932923 1215429924607378607899385)
            ·
              refine ⟨911572443455533955924539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215429924607378607899385 911572443455533955924539)
              ·
                refine ⟨1367358665183300933886809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911572443455533955924539 1367358665183300933886809)
                ·
                  refine ⟨1025518998887475700415107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367358665183300933886809 1025518998887475700415107)
                  ·
                    refine ⟨1538278498331213550622661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025518998887475700415107 1538278498331213550622661)
                    ·
                      refine ⟨288427218437102540741749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1538278498331213550622661 288427218437102540741749)
                      ·
                        rfl

theorem cell23_561710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_561710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561710 prefixEnd_561710 := by exact prefixLift 561710
  have htrace : WordTrace (prefixWord ++ tailWord_561710) baseStart_561710 baseEnd_561710 := by
    simpa [prefixWord, tailWord_561710, baseEnd_561710] using wordTrace_append hprefix tailTrace_561710
  have hstable : (prefixWord ++ tailWord_561710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561710).length < 2 ^ (prefixWord ++ tailWord_561710).sum := by decide
  have hdescent : baseEnd_561710 < baseStart_561710 := by decide
  rcases family_descends (prefixWord ++ tailWord_561710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561746 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_561746 : Nat := 118140960795 + 561746 * 2 ^ 59
def prefixEnd_561746 : Nat := 4983230072969 + 3 ^ 40 * 561746 * 2
def baseEnd_561746 : Nat := 96148567913554799963861

theorem tailTrace_561746 : CollatzResearch.WordTrace tailWord_561746 prefixEnd_561746 96148567913554799963861 := by
  unfold tailWord_561746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122139955724413855962273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13659039881931770282566061 5122139955724413855962273)
  ·
    refine ⟨3841604966793310391971705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5122139955724413855962273 3841604966793310391971705)
    ·
      refine ⟨2881203725094982793978779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3841604966793310391971705 2881203725094982793978779)
      ·
        refine ⟨4321805587642474190968169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881203725094982793978779 4321805587642474190968169)
        ·
          refine ⟨3241354190731855643226127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321805587642474190968169 3241354190731855643226127)
          ·
            refine ⟨4862031286097783464839191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241354190731855643226127 4862031286097783464839191)
            ·
              refine ⟨7293046929146675197258787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862031286097783464839191 7293046929146675197258787)
              ·
                refine ⟨10939570393720012795888181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7293046929146675197258787 10939570393720012795888181)
                ·
                  refine ⟨1025584724411251199614517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10939570393720012795888181 1025584724411251199614517)
                  ·
                    refine ⟨96148567913554799963861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1025584724411251199614517 96148567913554799963861)
                    ·
                      rfl

theorem cell23_561746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_561746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561746 prefixEnd_561746 := by exact prefixLift 561746
  have htrace : WordTrace (prefixWord ++ tailWord_561746) baseStart_561746 baseEnd_561746 := by
    simpa [prefixWord, tailWord_561746, baseEnd_561746] using wordTrace_append hprefix tailTrace_561746
  have hstable : (prefixWord ++ tailWord_561746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561746).length < 2 ^ (prefixWord ++ tailWord_561746).sum := by decide
  have hdescent : baseEnd_561746 < baseStart_561746 := by decide
  rcases family_descends (prefixWord ++ tailWord_561746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561793 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_561793 : Nat := 118140960795 + 561793 * 2 ^ 59
def prefixEnd_561793 : Nat := 4983230072969 + 3 ^ 40 * 561793 * 2
def baseEnd_561793 : Nat := 96156612443808572001289

theorem tailTrace_561793 : CollatzResearch.WordTrace tailWord_561793 prefixEnd_561793 96156612443808572001289 := by
  unfold tailWord_561793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20490274053727382450810033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13660182702484921633873355 20490274053727382450810033)
  ·
    refine ⟨15367705540295536838107525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20490274053727382450810033 15367705540295536838107525)
    ·
      refine ⟨2881444788805413157145161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15367705540295536838107525 2881444788805413157145161)
      ·
        refine ⟨2161083591604059867858871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881444788805413157145161 2161083591604059867858871)
        ·
          refine ⟨3241625387406089801788307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161083591604059867858871 3241625387406089801788307)
          ·
            refine ⟨4862438081109134702682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241625387406089801788307 4862438081109134702682461)
            ·
              refine ⟨1823414280415925513505923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4862438081109134702682461 1823414280415925513505923)
              ·
                refine ⟨2735121420623888270258885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823414280415925513505923 2735121420623888270258885)
                ·
                  refine ⟨512835266366979050673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2735121420623888270258885 512835266366979050673541)
                  ·
                    refine ⟨96156612443808572001289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512835266366979050673541 96156612443808572001289)
                    ·
                      rfl

theorem cell23_561793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_561793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561793 prefixEnd_561793 := by exact prefixLift 561793
  have htrace : WordTrace (prefixWord ++ tailWord_561793) baseStart_561793 baseEnd_561793 := by
    simpa [prefixWord, tailWord_561793, baseEnd_561793] using wordTrace_append hprefix tailTrace_561793
  have hstable : (prefixWord ++ tailWord_561793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561793).length < 2 ^ (prefixWord ++ tailWord_561793).sum := by decide
  have hdescent : baseEnd_561793 < baseStart_561793 := by decide
  rcases family_descends (prefixWord ++ tailWord_561793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561806 : List Nat := [4, 1, 1, 3, 1, 1, 2, 10]
def baseStart_561806 : Nat := 118140960795 + 561806 * 2 ^ 59
def prefixEnd_561806 : Nat := 4983230072969 + 3 ^ 40 * 561806 * 2
def baseEnd_561806 : Nat := 10684315280738302412641

theorem tailTrace_561806 : CollatzResearch.WordTrace tailWord_561806 prefixEnd_561806 10684315280738302412641 := by
  unfold tailWord_561806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561343525335035708879159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13660498801786857114022181 2561343525335035708879159)
  ·
    refine ⟨3842015288002553563318739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2561343525335035708879159 3842015288002553563318739)
    ·
      refine ⟨5763022932003830344978109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842015288002553563318739 5763022932003830344978109)
      ·
        refine ⟨2161133599501436379366791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5763022932003830344978109 2161133599501436379366791)
        ·
          refine ⟨3241700399252154569050187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161133599501436379366791 3241700399252154569050187)
          ·
            refine ⟨4862550598878231853575281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241700399252154569050187 4862550598878231853575281)
            ·
              refine ⟨3646912949158673890181461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862550598878231853575281 3646912949158673890181461)
              ·
                refine ⟨10684315280738302412641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3646912949158673890181461 10684315280738302412641)
                ·
                  rfl

theorem cell23_561806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_561806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561806 prefixEnd_561806 := by exact prefixLift 561806
  have htrace : WordTrace (prefixWord ++ tailWord_561806) baseStart_561806 baseEnd_561806 := by
    simpa [prefixWord, tailWord_561806, baseEnd_561806] using wordTrace_append hprefix tailTrace_561806
  have hstable : (prefixWord ++ tailWord_561806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561806).length < 2 ^ (prefixWord ++ tailWord_561806).sum := by decide
  have hdescent : baseEnd_561806 < baseStart_561806 := by decide
  rcases family_descends (prefixWord ++ tailWord_561806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561810 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_561810 : Nat := 118140960795 + 561810 * 2 ^ 59
def prefixEnd_561810 : Nat := 4983230072969 + 3 ^ 40 * 561810 * 2
def baseEnd_561810 : Nat := 96159522167517383163763

theorem tailTrace_561810 : CollatzResearch.WordTrace tailWord_561810 prefixEnd_561810 96159522167517383163763 := by
  unfold tailWord_561810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122723523666448588544721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13660596063110529569452589 5122723523666448588544721)
  ·
    refine ⟨3842042642749836441408541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5122723523666448588544721 3842042642749836441408541)
    ·
      refine ⟨1440765991031188665528203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3842042642749836441408541 1440765991031188665528203)
      ·
        refine ⟨2161148986546782998292305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440765991031188665528203 2161148986546782998292305)
        ·
          refine ⟨1620861739910087248719229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161148986546782998292305 1620861739910087248719229)
          ·
            refine ⟨607823152466282718269711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1620861739910087248719229 607823152466282718269711)
            ·
              refine ⟨911734728699424077404567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607823152466282718269711 911734728699424077404567)
              ·
                refine ⟨1367602093049136116106851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911734728699424077404567 1367602093049136116106851)
                ·
                  refine ⟨2051403139573704174160277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367602093049136116106851 2051403139573704174160277)
                  ·
                    refine ⟨96159522167517383163763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2051403139573704174160277 96159522167517383163763)
                    ·
                      rfl

theorem cell23_561810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_561810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561810 prefixEnd_561810 := by exact prefixLift 561810
  have htrace : WordTrace (prefixWord ++ tailWord_561810) baseStart_561810 baseEnd_561810 := by
    simpa [prefixWord, tailWord_561810, baseEnd_561810] using wordTrace_append hprefix tailTrace_561810
  have hstable : (prefixWord ++ tailWord_561810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561810).length < 2 ^ (prefixWord ++ tailWord_561810).sum := by decide
  have hdescent : baseEnd_561810 < baseStart_561810 := by decide
  rcases family_descends (prefixWord ++ tailWord_561810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561820 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_561820 : Nat := 118140960795 + 561820 * 2 ^ 59
def prefixEnd_561820 : Nat := 4983230072969 + 3 ^ 40 * 561820 * 2
def baseEnd_561820 : Nat := 288483701309097110366243

theorem tailTrace_561820 : CollatzResearch.WordTrace tailWord_561820 prefixEnd_561820 288483701309097110366243 := by
  unfold tailWord_561820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245629412314783031021457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13660839216419710708028609 10245629412314783031021457)
  ·
    refine ⟨7684222059236087273266093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10245629412314783031021457 7684222059236087273266093)
    ·
      refine ⟨2881583272213532727474785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7684222059236087273266093 2881583272213532727474785)
      ·
        refine ⟨2161187454160149545606089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881583272213532727474785 2161187454160149545606089)
        ·
          refine ⟨1620890590620112159204567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161187454160149545606089 1620890590620112159204567)
          ·
            refine ⟨2431335885930168238806851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620890590620112159204567 2431335885930168238806851)
            ·
              refine ⟨3647003828895252358210277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431335885930168238806851 3647003828895252358210277)
              ·
                refine ⟨683813217917859817164427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3647003828895252358210277 683813217917859817164427)
                ·
                  refine ⟨1025719826876789725746641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683813217917859817164427 1025719826876789725746641)
                  ·
                    refine ⟨769289870157592294309981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025719826876789725746641 769289870157592294309981)
                    ·
                      refine ⟨288483701309097110366243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769289870157592294309981 288483701309097110366243)
                      ·
                        rfl

theorem cell23_561820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_561820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561820 prefixEnd_561820 := by exact prefixLift 561820
  have htrace : WordTrace (prefixWord ++ tailWord_561820) baseStart_561820 baseEnd_561820 := by
    simpa [prefixWord, tailWord_561820, baseEnd_561820] using wordTrace_append hprefix tailTrace_561820
  have hstable : (prefixWord ++ tailWord_561820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561820).length < 2 ^ (prefixWord ++ tailWord_561820).sum := by decide
  have hdescent : baseEnd_561820 < baseStart_561820 := by decide
  rcases family_descends (prefixWord ++ tailWord_561820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_561833 : Nat := 118140960795 + 561833 * 2 ^ 59
def prefixEnd_561833 : Nat := 4983230072969 + 3 ^ 40 * 561833 * 2
def baseEnd_561833 : Nat := 288490376557605559503683

theorem tailTrace_561833 : CollatzResearch.WordTrace tailWord_561833 prefixEnd_561833 288490376557605559503683 := by
  unfold tailWord_561833
  simp only [CollatzResearch.WordTrace]
  refine ⟨20491732973582469282266153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13661155315721646188177435 20491732973582469282266153)
  ·
    refine ⟨15368799730186851961699615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20491732973582469282266153 15368799730186851961699615)
    ·
      refine ⟨23053199595280277942549423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15368799730186851961699615 23053199595280277942549423)
      ·
        refine ⟨34579799392920416913824135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23053199595280277942549423 34579799392920416913824135)
        ·
          refine ⟨51869699089380625370736203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34579799392920416913824135 51869699089380625370736203)
          ·
            refine ⟨77804548634070938056104305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51869699089380625370736203 77804548634070938056104305)
            ·
              refine ⟨58353411475553203542078229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77804548634070938056104305 58353411475553203542078229)
              ·
                refine ⟨2735316162916556416034917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58353411475553203542078229 2735316162916556416034917)
                ·
                  refine ⟨512871780546854328006547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2735316162916556416034917 512871780546854328006547)
                  ·
                    refine ⟨769307670820281492009821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512871780546854328006547 769307670820281492009821)
                    ·
                      refine ⟨288490376557605559503683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769307670820281492009821 288490376557605559503683)
                      ·
                        rfl

theorem cell23_561833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_561833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561833 prefixEnd_561833 := by exact prefixLift 561833
  have htrace : WordTrace (prefixWord ++ tailWord_561833) baseStart_561833 baseEnd_561833 := by
    simpa [prefixWord, tailWord_561833, baseEnd_561833] using wordTrace_append hprefix tailTrace_561833
  have hstable : (prefixWord ++ tailWord_561833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561833).length < 2 ^ (prefixWord ++ tailWord_561833).sum := by decide
  have hdescent : baseEnd_561833 < baseStart_561833 := by decide
  rcases family_descends (prefixWord ++ tailWord_561833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561850 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_561850 : Nat := 118140960795 + 561850 * 2 ^ 59
def prefixEnd_561850 : Nat := 4983230072969 + 3 ^ 40 * 561850 * 2
def baseEnd_561850 : Nat := 288499105728731992991105

theorem tailTrace_561850 : CollatzResearch.WordTrace tailWord_561850 prefixEnd_561850 288499105728731992991105 := by
  unfold tailWord_561850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123088253630220296408751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13661568676347254123756669 5123088253630220296408751)
  ·
    refine ⟨7684632380445330444613127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123088253630220296408751 7684632380445330444613127)
    ·
      refine ⟨11526948570667995666919691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7684632380445330444613127 11526948570667995666919691)
      ·
        refine ⟨17290422856001993500379537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11526948570667995666919691 17290422856001993500379537)
        ·
          refine ⟨12967817142001495125284653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17290422856001993500379537 12967817142001495125284653)
          ·
            refine ⟨4862931428250560671981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12967817142001495125284653 4862931428250560671981745)
            ·
              refine ⟨3647198571187920503986309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862931428250560671981745 3647198571187920503986309)
              ·
                refine ⟨683849732097735094497433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3647198571187920503986309 683849732097735094497433)
                ·
                  refine ⟨512887299073301320873075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683849732097735094497433 512887299073301320873075)
                  ·
                    refine ⟨769330948609951981309613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512887299073301320873075 769330948609951981309613)
                    ·
                      refine ⟨288499105728731992991105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769330948609951981309613 288499105728731992991105)
                      ·
                        rfl

theorem cell23_561850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_561850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561850 prefixEnd_561850 := by exact prefixLift 561850
  have htrace : WordTrace (prefixWord ++ tailWord_561850) baseStart_561850 baseEnd_561850 := by
    simpa [prefixWord, tailWord_561850, baseEnd_561850] using wordTrace_append hprefix tailTrace_561850
  have hstable : (prefixWord ++ tailWord_561850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561850).length < 2 ^ (prefixWord ++ tailWord_561850).sum := by decide
  have hdescent : baseEnd_561850 < baseStart_561850 := by decide
  rcases family_descends (prefixWord ++ tailWord_561850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561893 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_561893 : Nat := 118140960795 + 561893 * 2 ^ 59
def prefixEnd_561893 : Nat := 4983230072969 + 3 ^ 40 * 561893 * 2
def baseEnd_561893 : Nat := 288521185396875324753407

theorem tailTrace_561893 : CollatzResearch.WordTrace tailWord_561893 prefixEnd_561893 288521185396875324753407 := by
  unfold tailWord_561893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20493921353365099529450333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13662614235576733019633555 20493921353365099529450333)
  ·
    refine ⟨7685220507511912323543875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20493921353365099529450333 7685220507511912323543875)
    ·
      refine ⟨11527830761267868485315813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7685220507511912323543875 11527830761267868485315813)
      ·
        refine ⟨2161468267737725340996715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11527830761267868485315813 2161468267737725340996715)
        ·
          refine ⟨3242202401606588011495073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161468267737725340996715 3242202401606588011495073)
          ·
            refine ⟨2431651801204941008621305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242202401606588011495073 2431651801204941008621305)
            ·
              refine ⟨1823738850903705756465979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431651801204941008621305 1823738850903705756465979)
              ·
                refine ⟨2735608276355558634698969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823738850903705756465979 2735608276355558634698969)
                ·
                  refine ⟨2051706207266668976024227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735608276355558634698969 2051706207266668976024227)
                  ·
                    refine ⟨3077559310900003464036341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051706207266668976024227 3077559310900003464036341)
                    ·
                      refine ⟨288521185396875324753407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3077559310900003464036341 288521185396875324753407)
                      ·
                        rfl

theorem cell23_561893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_561893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561893 prefixEnd_561893 := by exact prefixLift 561893
  have htrace : WordTrace (prefixWord ++ tailWord_561893) baseStart_561893 baseEnd_561893 := by
    simpa [prefixWord, tailWord_561893, baseEnd_561893] using wordTrace_append hprefix tailTrace_561893
  have hstable : (prefixWord ++ tailWord_561893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561893).length < 2 ^ (prefixWord ++ tailWord_561893).sum := by decide
  have hdescent : baseEnd_561893 < baseStart_561893 := by decide
  rcases family_descends (prefixWord ++ tailWord_561893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561936 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_561936 : Nat := 118140960795 + 561936 * 2 ^ 59
def prefixEnd_561936 : Nat := 4983230072969 + 3 ^ 40 * 561936 * 2
def baseEnd_561936 : Nat := 288543265065018656515709

theorem tailTrace_561936 : CollatzResearch.WordTrace tailWord_561936 prefixEnd_561936 288543265065018656515709 := by
  unfold tailWord_561936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247744846104658936632831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13663659794806211915510441 10247744846104658936632831)
  ·
    refine ⟨15371617269156988404949247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10247744846104658936632831 15371617269156988404949247)
    ·
      refine ⟨23057425903735482607423871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15371617269156988404949247 23057425903735482607423871)
      ·
        refine ⟨34586138855603223911135807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23057425903735482607423871 34586138855603223911135807)
        ·
          refine ⟨51879208283404835866703711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586138855603223911135807 51879208283404835866703711)
          ·
            refine ⟨77818812425107253800055567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51879208283404835866703711 77818812425107253800055567)
            ·
              refine ⟨116728218637660880700083351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77818812425107253800055567 116728218637660880700083351)
              ·
                refine ⟨175092327956491321050125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116728218637660880700083351 175092327956491321050125027)
                ·
                  refine ⟨262638491934736981575187541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175092327956491321050125027 262638491934736981575187541)
                  ·
                    refine ⟨3077794827360199002834229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 262638491934736981575187541 3077794827360199002834229)
                    ·
                      refine ⟨288543265065018656515709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3077794827360199002834229 288543265065018656515709)
                      ·
                        rfl

theorem cell23_561936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_561936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_561936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_561936 prefixEnd_561936 := by exact prefixLift 561936
  have htrace : WordTrace (prefixWord ++ tailWord_561936) baseStart_561936 baseEnd_561936 := by
    simpa [prefixWord, tailWord_561936, baseEnd_561936] using wordTrace_append hprefix tailTrace_561936
  have hstable : (prefixWord ++ tailWord_561936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561936).length < 2 ^ (prefixWord ++ tailWord_561936).sum := by decide
  have hdescent : baseEnd_561936 < baseStart_561936 := by decide
  rcases family_descends (prefixWord ++ tailWord_561936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562037 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 6]
def baseStart_562037 : Nat := 118140960795 + 562037 * 2 ^ 59
def prefixEnd_562037 : Nat := 4983230072969 + 3 ^ 40 * 562037 * 2
def baseEnd_562037 : Nat := 32066125179013640150305

theorem tailTrace_562037 : CollatzResearch.WordTrace tailWord_562037 prefixEnd_562037 32066125179013640150305 := by
  unfold tailWord_562037
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499173464843412122692365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13666115643228941415128243 20499173464843412122692365)
  ·
    refine ⟨7687190049316279546009637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20499173464843412122692365 7687190049316279546009637)
    ·
      refine ⟨1441348134246802414876807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7687190049316279546009637 1441348134246802414876807)
      ·
        refine ⟨2162022201370203622315211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441348134246802414876807 2162022201370203622315211)
        ·
          refine ⟨3243033302055305433472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162022201370203622315211 3243033302055305433472817)
          ·
            refine ⟨2432274976541479075104613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243033302055305433472817 2432274976541479075104613)
            ·
              refine ⟨456051558101527326582115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2432274976541479075104613 456051558101527326582115)
              ·
                refine ⟨684077337152290989873173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456051558101527326582115 684077337152290989873173)
                ·
                  refine ⟨32066125179013640150305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 684077337152290989873173 32066125179013640150305)
                  ·
                    rfl

theorem cell23_562037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_562037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562037 prefixEnd_562037 := by exact prefixLift 562037
  have htrace : WordTrace (prefixWord ++ tailWord_562037) baseStart_562037 baseEnd_562037 := by
    simpa [prefixWord, tailWord_562037, baseEnd_562037] using wordTrace_append hprefix tailTrace_562037
  have hstable : (prefixWord ++ tailWord_562037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562037).length < 2 ^ (prefixWord ++ tailWord_562037).sum := by decide
  have hdescent : baseEnd_562037 < baseStart_562037 := by decide
  rcases family_descends (prefixWord ++ tailWord_562037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562040 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_562040 : Nat := 118140960795 + 562040 * 2 ^ 59
def prefixEnd_562040 : Nat := 4983230072969 + 3 ^ 40 * 562040 * 2
def baseEnd_562040 : Nat := 288596667053086249615231

theorem tailTrace_562040 : CollatzResearch.WordTrace tailWord_562040 prefixEnd_562040 288596667053086249615231 := by
  unfold tailWord_562040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10249641441916271817525787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13666188589221695756701049 10249641441916271817525787)
  ·
    refine ⟨15374462162874407726288681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10249641441916271817525787 15374462162874407726288681)
    ·
      refine ⟨11530846622155805794716511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15374462162874407726288681 11530846622155805794716511)
      ·
        refine ⟨17296269933233708692074767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11530846622155805794716511 17296269933233708692074767)
        ·
          refine ⟨25944404899850563038112151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17296269933233708692074767 25944404899850563038112151)
          ·
            refine ⟨38916607349775844557168227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25944404899850563038112151 38916607349775844557168227)
            ·
              refine ⟨58374911024663766835752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38916607349775844557168227 58374911024663766835752341)
              ·
                refine ⟨2736323954281114070425891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58374911024663766835752341 2736323954281114070425891)
                ·
                  refine ⟨4104485931421671105638837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736323954281114070425891 4104485931421671105638837)
                  ·
                    refine ⟨384795556070781666153641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4104485931421671105638837 384795556070781666153641)
                    ·
                      refine ⟨288596667053086249615231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384795556070781666153641 288596667053086249615231)
                      ·
                        rfl

theorem cell23_562040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_562040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562040 prefixEnd_562040 := by exact prefixLift 562040
  have htrace : WordTrace (prefixWord ++ tailWord_562040) baseStart_562040 baseEnd_562040 := by
    simpa [prefixWord, tailWord_562040, baseEnd_562040] using wordTrace_append hprefix tailTrace_562040
  have hstable : (prefixWord ++ tailWord_562040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562040).length < 2 ^ (prefixWord ++ tailWord_562040).sum := by decide
  have hdescent : baseEnd_562040 < baseStart_562040 := by decide
  rcases family_descends (prefixWord ++ tailWord_562040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562057 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 2, 3, 2]
def baseStart_562057 : Nat := 118140960795 + 562057 * 2 ^ 59
def prefixEnd_562057 : Nat := 4983230072969 + 3 ^ 40 * 562057 * 2
def baseEnd_562057 : Nat := 288605396224212683102653

theorem tailTrace_562057 : CollatzResearch.WordTrace tailWord_562057 prefixEnd_562057 288605396224212683102653 := by
  unfold tailWord_562057
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499902924770955538420425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13666601949847303692280283 20499902924770955538420425)
  ·
    refine ⟨15374927193578216653815319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20499902924770955538420425 15374927193578216653815319)
    ·
      refine ⟨23062390790367324980722979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15374927193578216653815319 23062390790367324980722979)
      ·
        refine ⟨34593586185550987471084469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23062390790367324980722979 34593586185550987471084469)
        ·
          refine ⟨3243148704895405075414169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34593586185550987471084469 3243148704895405075414169)
          ·
            refine ⟨2432361528671553806560627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243148704895405075414169 2432361528671553806560627)
            ·
              refine ⟨3648542293007330709840941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432361528671553806560627 3648542293007330709840941)
              ·
                refine ⟨1368203359877749016190353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3648542293007330709840941 1368203359877749016190353)
                ·
                  refine ⟨1026152519908311762142765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1368203359877749016190353 1026152519908311762142765)
                  ·
                    refine ⟨384807194965616910803537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026152519908311762142765 384807194965616910803537)
                    ·
                      refine ⟨288605396224212683102653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384807194965616910803537 288605396224212683102653)
                      ·
                        rfl

theorem cell23_562057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3, 2].length) (baseStart_562057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562057 prefixEnd_562057 := by exact prefixLift 562057
  have htrace : WordTrace (prefixWord ++ tailWord_562057) baseStart_562057 baseEnd_562057 := by
    simpa [prefixWord, tailWord_562057, baseEnd_562057] using wordTrace_append hprefix tailTrace_562057
  have hstable : (prefixWord ++ tailWord_562057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562057).length < 2 ^ (prefixWord ++ tailWord_562057).sum := by decide
  have hdescent : baseEnd_562057 < baseStart_562057 := by decide
  rcases family_descends (prefixWord ++ tailWord_562057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562080 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_562080 : Nat := 118140960795 + 562080 * 2 ^ 59
def prefixEnd_562080 : Nat := 4983230072969 + 3 ^ 40 * 562080 * 2
def baseEnd_562080 : Nat := 96205735426422031038349

theorem tailTrace_562080 : CollatzResearch.WordTrace tailWord_562080 prefixEnd_562080 96205735426422031038349 := by
  unfold tailWord_562080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250370901843815233253847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13667161202458420311005129 10250370901843815233253847)
  ·
    refine ⟨15375556352765722849880771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10250370901843815233253847 15375556352765722849880771)
    ·
      refine ⟨23063334529148584274821157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15375556352765722849880771 23063334529148584274821157)
      ·
        refine ⟨4324375224215359551528967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23063334529148584274821157 4324375224215359551528967)
        ·
          refine ⟨6486562836323039327293451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324375224215359551528967 6486562836323039327293451)
          ·
            refine ⟨9729844254484558990940177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486562836323039327293451 9729844254484558990940177)
            ·
              refine ⟨7297383190863419243205133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9729844254484558990940177 7297383190863419243205133)
              ·
                refine ⟨2736518696573782216201925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7297383190863419243205133 2736518696573782216201925)
                ·
                  refine ⟨513097255607584165537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2736518696573782216201925 513097255607584165537861)
                  ·
                    refine ⟨96205735426422031038349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 513097255607584165537861 96205735426422031038349)
                    ·
                      rfl

theorem cell23_562080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_562080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562080 prefixEnd_562080 := by exact prefixLift 562080
  have htrace : WordTrace (prefixWord ++ tailWord_562080) baseStart_562080 baseEnd_562080 := by
    simpa [prefixWord, tailWord_562080, baseEnd_562080] using wordTrace_append hprefix tailTrace_562080
  have hstable : (prefixWord ++ tailWord_562080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562080).length < 2 ^ (prefixWord ++ tailWord_562080).sum := by decide
  have hdescent : baseEnd_562080 < baseStart_562080 := by decide
  rcases family_descends (prefixWord ++ tailWord_562080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562081 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_562081 : Nat := 118140960795 + 562081 * 2 ^ 59
def prefixEnd_562081 : Nat := 4983230072969 + 3 ^ 40 * 562081 * 2
def baseEnd_562081 : Nat := 288617719759920589202543

theorem tailTrace_562081 : CollatzResearch.WordTrace tailWord_562081 prefixEnd_562081 288617719759920589202543 := by
  unfold tailWord_562081
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500778276684007637294097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667185517789338424862731 20500778276684007637294097)
  ·
    refine ⟨15375583707513005727970573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20500778276684007637294097 15375583707513005727970573)
    ·
      refine ⟨5765843890317377147988965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15375583707513005727970573 5765843890317377147988965)
      ·
        refine ⟨1081095729434508215247931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5765843890317377147988965 1081095729434508215247931)
        ·
          refine ⟨1621643594151762322871897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081095729434508215247931 1621643594151762322871897)
          ·
            refine ⟨1216232695613821742153923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621643594151762322871897 1216232695613821742153923)
            ·
              refine ⟨1824349043420732613230885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216232695613821742153923 1824349043420732613230885)
              ·
                refine ⟨342065445641387364980791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1824349043420732613230885 342065445641387364980791)
                ·
                  refine ⟨513098168462081047471187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342065445641387364980791 513098168462081047471187)
                  ·
                    refine ⟨769647252693121571206781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513098168462081047471187 769647252693121571206781)
                    ·
                      refine ⟨288617719759920589202543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769647252693121571206781 288617719759920589202543)
                      ·
                        rfl

theorem cell23_562081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_562081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562081 prefixEnd_562081 := by exact prefixLift 562081
  have htrace : WordTrace (prefixWord ++ tailWord_562081) baseStart_562081 baseEnd_562081 := by
    simpa [prefixWord, tailWord_562081, baseEnd_562081] using wordTrace_append hprefix tailTrace_562081
  have hstable : (prefixWord ++ tailWord_562081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562081).length < 2 ^ (prefixWord ++ tailWord_562081).sum := by decide
  have hdescent : baseEnd_562081 < baseStart_562081 := by decide
  rcases family_descends (prefixWord ++ tailWord_562081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562083 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_562083 : Nat := 118140960795 + 562083 * 2 ^ 59
def prefixEnd_562083 : Nat := 4983230072969 + 3 ^ 40 * 562083 * 2
def baseEnd_562083 : Nat := 288618746721229581377533

theorem tailTrace_562083 : CollatzResearch.WordTrace tailWord_562083 prefixEnd_562083 288618746721229581377533 := by
  unfold tailWord_562083
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500851222676761978866903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667234148451174652577935 20500851222676761978866903)
  ·
    refine ⟨30751276834015142968300355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20500851222676761978866903 30751276834015142968300355)
    ·
      refine ⟨46126915251022714452450533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30751276834015142968300355 46126915251022714452450533)
      ·
        refine ⟨8648796609566758959834475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46126915251022714452450533 8648796609566758959834475)
        ·
          refine ⟨12973194914350138439751713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8648796609566758959834475 12973194914350138439751713)
          ·
            refine ⟨9729896185762603829813785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12973194914350138439751713 9729896185762603829813785)
            ·
              refine ⟨7297422139321952872360339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9729896185762603829813785 7297422139321952872360339)
              ·
                refine ⟨10946133208982929308540509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7297422139321952872360339 10946133208982929308540509)
                ·
                  refine ⟨4104799953368598490702691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10946133208982929308540509 4104799953368598490702691)
                  ·
                    refine ⟨6157199930052897736054037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4104799953368598490702691 6157199930052897736054037)
                    ·
                      refine ⟨288618746721229581377533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6157199930052897736054037 288618746721229581377533)
                      ·
                        rfl

theorem cell23_562083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_562083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562083 prefixEnd_562083 := by exact prefixLift 562083
  have htrace : WordTrace (prefixWord ++ tailWord_562083) baseStart_562083 baseEnd_562083 := by
    simpa [prefixWord, tailWord_562083, baseEnd_562083] using wordTrace_append hprefix tailTrace_562083
  have hstable : (prefixWord ++ tailWord_562083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562083).length < 2 ^ (prefixWord ++ tailWord_562083).sum := by decide
  have hdescent : baseEnd_562083 < baseStart_562083 := by decide
  rcases family_descends (prefixWord ++ tailWord_562083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562097 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_562097 : Nat := 118140960795 + 562097 * 2 ^ 59
def prefixEnd_562097 : Nat := 4983230072969 + 3 ^ 40 * 562097 * 2
def baseEnd_562097 : Nat := 96208645150130842200823

theorem tailTrace_562097 : CollatzResearch.WordTrace tailWord_562097 prefixEnd_562097 96208645150130842200823 := by
  unfold tailWord_562097
  simp only [CollatzResearch.WordTrace]
  refine ⟨20501361844626042369876545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667574563084028246584363 20501361844626042369876545)
  ·
    refine ⟨15376021383469531777407409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20501361844626042369876545 15376021383469531777407409)
    ·
      refine ⟨11532016037602148833055557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15376021383469531777407409 11532016037602148833055557)
      ·
        refine ⟨2162253007050402906197917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11532016037602148833055557 2162253007050402906197917)
        ·
          refine ⟨810844877643901089824219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2162253007050402906197917 810844877643901089824219)
          ·
            refine ⟨1216267316465851634736329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810844877643901089824219 1216267316465851634736329)
            ·
              refine ⟨912200487349388726052247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216267316465851634736329 912200487349388726052247)
              ·
                refine ⟨1368300731024083089078371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912200487349388726052247 1368300731024083089078371)
                ·
                  refine ⟨2052451096536124633617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368300731024083089078371 2052451096536124633617557)
                  ·
                    refine ⟨96208645150130842200823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2052451096536124633617557 96208645150130842200823)
                    ·
                      rfl

theorem cell23_562097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_562097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562097 prefixEnd_562097 := by exact prefixLift 562097
  have htrace : WordTrace (prefixWord ++ tailWord_562097) baseStart_562097 baseEnd_562097 := by
    simpa [prefixWord, tailWord_562097, baseEnd_562097] using wordTrace_append hprefix tailTrace_562097
  have hstable : (prefixWord ++ tailWord_562097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562097).length < 2 ^ (prefixWord ++ tailWord_562097).sum := by decide
  have hdescent : baseEnd_562097 < baseStart_562097 := by decide
  rcases family_descends (prefixWord ++ tailWord_562097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562104 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_562104 : Nat := 118140960795 + 562104 * 2 ^ 59
def prefixEnd_562104 : Nat := 4983230072969 + 3 ^ 40 * 562104 * 2
def baseEnd_562104 : Nat := 288629529814973999214937

theorem tailTrace_562104 : CollatzResearch.WordTrace tailWord_562104 prefixEnd_562104 288629529814973999214937 := by
  unfold tailWord_562104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250808577800341282690683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13667744770400455043587577 10250808577800341282690683)
  ·
    refine ⟨15376212866700511924036025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10250808577800341282690683 15376212866700511924036025)
    ·
      refine ⟨11532159650025383943027019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15376212866700511924036025 11532159650025383943027019)
      ·
        refine ⟨17298239475038075914540529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11532159650025383943027019 17298239475038075914540529)
        ·
          refine ⟨12973679606278556935905397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17298239475038075914540529 12973679606278556935905397)
          ·
            refine ⟨1216282463088614712741131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12973679606278556935905397 1216282463088614712741131)
            ·
              refine ⟨1824423694632922069111697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216282463088614712741131 1824423694632922069111697)
              ·
                refine ⟨1368317770974691551833773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824423694632922069111697 1368317770974691551833773)
                ·
                  refine ⟨513119164115509331937665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1368317770974691551833773 513119164115509331937665)
                  ·
                    refine ⟨384839373086631998953249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513119164115509331937665 384839373086631998953249)
                    ·
                      refine ⟨288629529814973999214937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384839373086631998953249 288629529814973999214937)
                      ·
                        rfl

theorem cell23_562104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_562104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562104 prefixEnd_562104 := by exact prefixLift 562104
  have htrace : WordTrace (prefixWord ++ tailWord_562104) baseStart_562104 baseEnd_562104 := by
    simpa [prefixWord, tailWord_562104, baseEnd_562104] using wordTrace_append hprefix tailTrace_562104
  have hstable : (prefixWord ++ tailWord_562104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562104).length < 2 ^ (prefixWord ++ tailWord_562104).sum := by decide
  have hdescent : baseEnd_562104 < baseStart_562104 := by decide
  rcases family_descends (prefixWord ++ tailWord_562104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562154 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_562154 : Nat := 118140960795 + 562154 * 2 ^ 59
def prefixEnd_562154 : Nat := 4983230072969 + 3 ^ 40 * 562154 * 2
def baseEnd_562154 : Nat := 288655203847698803589707

theorem tailTrace_562154 : CollatzResearch.WordTrace tailWord_562154 prefixEnd_562154 288655203847698803589707 := by
  unfold tailWord_562154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125860201354885276175379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13668960536946360736467677 5125860201354885276175379)
  ·
    refine ⟨7688790302032327914263069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125860201354885276175379 7688790302032327914263069)
    ·
      refine ⟨2883296363262122967848651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7688790302032327914263069 2883296363262122967848651)
      ·
        refine ⟨4324944544893184451772977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883296363262122967848651 4324944544893184451772977)
        ·
          refine ⟨3243708408669888338829733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4324944544893184451772977 3243708408669888338829733)
          ·
            refine ⟨608195326625604063530575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3243708408669888338829733 608195326625604063530575)
            ·
              refine ⟨912292989938406095295863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608195326625604063530575 912292989938406095295863)
              ·
                refine ⟨1368439484907609142943795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912292989938406095295863 1368439484907609142943795)
                ·
                  refine ⟨2052659227361413714415693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368439484907609142943795 2052659227361413714415693)
                  ·
                    refine ⟨769747210260530142905885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052659227361413714415693 769747210260530142905885)
                    ·
                      refine ⟨288655203847698803589707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769747210260530142905885 288655203847698803589707)
                      ·
                        rfl

theorem cell23_562154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_562154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562154 prefixEnd_562154 := by exact prefixLift 562154
  have htrace : WordTrace (prefixWord ++ tailWord_562154) baseStart_562154 baseEnd_562154 := by
    simpa [prefixWord, tailWord_562154, baseEnd_562154] using wordTrace_append hprefix tailTrace_562154
  have hstable : (prefixWord ++ tailWord_562154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562154).length < 2 ^ (prefixWord ++ tailWord_562154).sum := by decide
  have hdescent : baseEnd_562154 < baseStart_562154 := by decide
  rcases family_descends (prefixWord ++ tailWord_562154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562205 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_562205 : Nat := 118140960795 + 562205 * 2 ^ 59
def prefixEnd_562205 : Nat := 4983230072969 + 3 ^ 40 * 562205 * 2
def baseEnd_562205 : Nat := 288681391361078104051973

theorem tailTrace_562205 : CollatzResearch.WordTrace tailWord_562205 prefixEnd_562205 288681391361078104051973 := by
  unfold tailWord_562205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20505300928234776814808069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13670200618823184543205379 20505300928234776814808069)
  ·
    refine ⟨3844743924044020652776513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20505300928234776814808069 3844743924044020652776513)
    ·
      refine ⟨2883557943033015489582385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3844743924044020652776513 2883557943033015489582385)
      ·
        refine ⟨2162668457274761617186789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883557943033015489582385 2162668457274761617186789)
        ·
          refine ⟨405500335739017803222523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2162668457274761617186789 405500335739017803222523)
          ·
            refine ⟨608250503608526704833785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405500335739017803222523 608250503608526704833785)
            ·
              refine ⟨456187877706395028625339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608250503608526704833785 456187877706395028625339)
              ·
                refine ⟨684281816559592542938009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456187877706395028625339 684281816559592542938009)
                ·
                  refine ⟨513211362419694407203507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684281816559592542938009 513211362419694407203507)
                  ·
                    refine ⟨769817043629541610805261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513211362419694407203507 769817043629541610805261)
                    ·
                      refine ⟨288681391361078104051973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769817043629541610805261 288681391361078104051973)
                      ·
                        rfl

theorem cell23_562205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_562205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562205 prefixEnd_562205 := by exact prefixLift 562205
  have htrace : WordTrace (prefixWord ++ tailWord_562205) baseStart_562205 baseEnd_562205 := by
    simpa [prefixWord, tailWord_562205, baseEnd_562205] using wordTrace_append hprefix tailTrace_562205
  have hstable : (prefixWord ++ tailWord_562205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562205).length < 2 ^ (prefixWord ++ tailWord_562205).sum := by decide
  have hdescent : baseEnd_562205 < baseStart_562205 := by decide
  rcases family_descends (prefixWord ++ tailWord_562205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562211 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 2, 2, 2]
def baseStart_562211 : Nat := 118140960795 + 562211 * 2 ^ 59
def prefixEnd_562211 : Nat := 4983230072969 + 3 ^ 40 * 562211 * 2
def baseEnd_562211 : Nat := 288684472245005080576945

theorem tailTrace_562211 : CollatzResearch.WordTrace tailWord_562211 prefixEnd_562211 288684472245005080576945 := by
  unfold tailWord_562211
  simp only [CollatzResearch.WordTrace]
  refine ⟨20505519766213039839526487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13670346510808693226350991 20505519766213039839526487)
  ·
    refine ⟨30758279649319559759289731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20505519766213039839526487 30758279649319559759289731)
    ·
      refine ⟨46137419473979339638934597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30758279649319559759289731 46137419473979339638934597)
      ·
        refine ⟨8650766151371126182300237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46137419473979339638934597 8650766151371126182300237)
        ·
          refine ⟨3244037306764172318362589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8650766151371126182300237 3244037306764172318362589)
          ·
            refine ⟨1216513990036564619385971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3244037306764172318362589 1216513990036564619385971)
            ·
              refine ⟨1824770985054846929078957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216513990036564619385971 1824770985054846929078957)
              ·
                refine ⟨684289119395567598404609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1824770985054846929078957 684289119395567598404609)
                ·
                  refine ⟨513216839546675698803457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684289119395567598404609 513216839546675698803457)
                  ·
                    refine ⟨384912629660006774102593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513216839546675698803457 384912629660006774102593)
                    ·
                      refine ⟨288684472245005080576945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 384912629660006774102593 288684472245005080576945)
                      ·
                        rfl

theorem cell23_562211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_562211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562211 prefixEnd_562211 := by exact prefixLift 562211
  have htrace : WordTrace (prefixWord ++ tailWord_562211) baseStart_562211 baseEnd_562211 := by
    simpa [prefixWord, tailWord_562211, baseEnd_562211] using wordTrace_append hprefix tailTrace_562211
  have hstable : (prefixWord ++ tailWord_562211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562211).length < 2 ^ (prefixWord ++ tailWord_562211).sum := by decide
  have hdescent : baseEnd_562211 < baseStart_562211 := by decide
  rcases family_descends (prefixWord ++ tailWord_562211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562240 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_562240 : Nat := 118140960795 + 562240 * 2 ^ 59
def prefixEnd_562240 : Nat := 4983230072969 + 3 ^ 40 * 562240 * 2
def baseEnd_562240 : Nat := 288699363183985467114311

theorem tailTrace_562240 : CollatzResearch.WordTrace tailWord_562240 prefixEnd_562240 288699363183985467114311 := by
  unfold tailWord_562240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253288741553988896166087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13671051655405318528221449 10253288741553988896166087)
  ·
    refine ⟨15379933112330983344249131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10253288741553988896166087 15379933112330983344249131)
    ·
      refine ⟨23069899668496475016373697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15379933112330983344249131 23069899668496475016373697)
      ·
        refine ⟨17302424751372356262280273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23069899668496475016373697 17302424751372356262280273)
        ·
          refine ⟨12976818563529267196710205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17302424751372356262280273 12976818563529267196710205)
          ·
            refine ⟨4866306961323475198766327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12976818563529267196710205 4866306961323475198766327)
            ·
              refine ⟨7299460441985212798149491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866306961323475198766327 7299460441985212798149491)
              ·
                refine ⟨10949190662977819197224237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299460441985212798149491 10949190662977819197224237)
                ·
                  refine ⟨4105946498616682198959089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10949190662977819197224237 4105946498616682198959089)
                  ·
                    refine ⟨3079459873962511649219317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105946498616682198959089 3079459873962511649219317)
                    ·
                      refine ⟨288699363183985467114311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3079459873962511649219317 288699363183985467114311)
                      ·
                        rfl

theorem cell23_562240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_562240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562240 prefixEnd_562240 := by exact prefixLift 562240
  have htrace : WordTrace (prefixWord ++ tailWord_562240) baseStart_562240 baseEnd_562240 := by
    simpa [prefixWord, tailWord_562240, baseEnd_562240] using wordTrace_append hprefix tailTrace_562240
  have hstable : (prefixWord ++ tailWord_562240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562240).length < 2 ^ (prefixWord ++ tailWord_562240).sum := by decide
  have hdescent : baseEnd_562240 < baseStart_562240 := by decide
  rcases family_descends (prefixWord ++ tailWord_562240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562247 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 2, 5]
def baseStart_562247 : Nat := 118140960795 + 562247 * 2 ^ 59
def prefixEnd_562247 : Nat := 4983230072969 + 3 ^ 40 * 562247 * 2
def baseEnd_562247 : Nat := 96234319182855646575593

theorem tailTrace_562247 : CollatzResearch.WordTrace tailWord_562247 prefixEnd_562247 96234319182855646575593 := by
  unfold tailWord_562247
  simp only [CollatzResearch.WordTrace]
  refine ⟨20506832794082617987836995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13671221862721745325224663 20506832794082617987836995)
  ·
    refine ⟨30760249191123926981755493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20506832794082617987836995 30760249191123926981755493)
    ·
      refine ⟨5767546723335736309079155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30760249191123926981755493 5767546723335736309079155)
      ·
        refine ⟨8651320085003604463618733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767546723335736309079155 8651320085003604463618733)
        ·
          refine ⟨3244245031876351673857025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8651320085003604463618733 3244245031876351673857025)
          ·
            refine ⟨2433183773907263755392769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244245031876351673857025 2433183773907263755392769)
            ·
              refine ⟨1824887830430447816544577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433183773907263755392769 1824887830430447816544577)
              ·
                refine ⟨1368665872822835862408433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824887830430447816544577 1368665872822835862408433)
                ·
                  refine ⟨1026499404617126896806325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1368665872822835862408433 1026499404617126896806325)
                  ·
                    refine ⟨96234319182855646575593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1026499404617126896806325 96234319182855646575593)
                    ·
                      rfl

theorem cell23_562247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_562247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562247 prefixEnd_562247 := by exact prefixLift 562247
  have htrace : WordTrace (prefixWord ++ tailWord_562247) baseStart_562247 baseEnd_562247 := by
    simpa [prefixWord, tailWord_562247, baseEnd_562247] using wordTrace_append hprefix tailTrace_562247
  have hstable : (prefixWord ++ tailWord_562247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562247).length < 2 ^ (prefixWord ++ tailWord_562247).sum := by decide
  have hdescent : baseEnd_562247 < baseStart_562247 := by decide
  rcases family_descends (prefixWord ++ tailWord_562247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562287 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_562287 : Nat := 118140960795 + 562287 * 2 ^ 59
def prefixEnd_562287 : Nat := 4983230072969 + 3 ^ 40 * 562287 * 2
def baseEnd_562287 : Nat := 288723496774746783226595

theorem tailTrace_562287 : CollatzResearch.WordTrace tailWord_562287 prefixEnd_562287 288723496774746783226595 := by
  unfold tailWord_562287
  simp only [CollatzResearch.WordTrace]
  refine ⟨20508291713937704819293115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13672194475958469879528743 20508291713937704819293115)
  ·
    refine ⟨30762437570906557228939673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20508291713937704819293115 30762437570906557228939673)
    ·
      refine ⟨23071828178179917921704755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30762437570906557228939673 23071828178179917921704755)
      ·
        refine ⟨34607742267269876882557133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23071828178179917921704755 34607742267269876882557133)
        ·
          refine ⟨12977903350226203830958925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34607742267269876882557133 12977903350226203830958925)
          ·
            refine ⟨4866713756334826436609597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12977903350226203830958925 4866713756334826436609597)
            ·
              refine ⟨1825017658625559913728599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4866713756334826436609597 1825017658625559913728599)
              ·
                refine ⟨2737526487938339870592899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825017658625559913728599 2737526487938339870592899)
                ·
                  refine ⟨4106289731907509805889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737526487938339870592899 4106289731907509805889349)
                  ·
                    refine ⟨769929324732658088604253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106289731907509805889349 769929324732658088604253)
                    ·
                      refine ⟨288723496774746783226595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 769929324732658088604253 288723496774746783226595)
                      ·
                        rfl

theorem cell23_562287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_562287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562287 prefixEnd_562287 := by exact prefixLift 562287
  have htrace : WordTrace (prefixWord ++ tailWord_562287) baseStart_562287 baseEnd_562287 := by
    simpa [prefixWord, tailWord_562287, baseEnd_562287] using wordTrace_append hprefix tailTrace_562287
  have hstable : (prefixWord ++ tailWord_562287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562287).length < 2 ^ (prefixWord ++ tailWord_562287).sum := by decide
  have hdescent : baseEnd_562287 < baseStart_562287 := by decide
  rcases family_descends (prefixWord ++ tailWord_562287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562294 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_562294 : Nat := 118140960795 + 562294 * 2 ^ 59
def prefixEnd_562294 : Nat := 4983230072969 + 3 ^ 40 * 562294 * 2
def baseEnd_562294 : Nat := 96242363713109418613021

theorem tailTrace_562294 : CollatzResearch.WordTrace tailWord_562294 prefixEnd_562294 96242363713109418613021 := by
  unfold tailWord_562294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281784189057021563424871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13672364683274896676531957 1281784189057021563424871)
  ·
    refine ⟨1922676283585532345137307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281784189057021563424871 1922676283585532345137307)
    ·
      refine ⟨2884014425378298517705961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922676283585532345137307 2884014425378298517705961)
      ·
        refine ⟨2163010819033723888279471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2884014425378298517705961 2163010819033723888279471)
        ·
          refine ⟨3244516228550585832419207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163010819033723888279471 3244516228550585832419207)
          ·
            refine ⟨4866774342825878748628811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244516228550585832419207 4866774342825878748628811)
            ·
              refine ⟨7300161514238818122943217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866774342825878748628811 7300161514238818122943217)
              ·
                refine ⟨5475121135679113592207413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7300161514238818122943217 5475121135679113592207413)
                ·
                  refine ⟨513292606469916899269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5475121135679113592207413 513292606469916899269445)
                  ·
                    refine ⟨96242363713109418613021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 513292606469916899269445 96242363713109418613021)
                    ·
                      rfl

theorem cell23_562294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_562294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562294 prefixEnd_562294 := by exact prefixLift 562294
  have htrace : WordTrace (prefixWord ++ tailWord_562294) baseStart_562294 baseEnd_562294 := by
    simpa [prefixWord, tailWord_562294, baseEnd_562294] using wordTrace_append hprefix tailTrace_562294
  have hstable : (prefixWord ++ tailWord_562294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562294).length < 2 ^ (prefixWord ++ tailWord_562294).sum := by decide
  have hdescent : baseEnd_562294 < baseStart_562294 := by decide
  rcases family_descends (prefixWord ++ tailWord_562294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562320 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_562320 : Nat := 118140960795 + 562320 * 2 ^ 59
def prefixEnd_562320 : Nat := 4983230072969 + 3 ^ 40 * 562320 * 2
def baseEnd_562320 : Nat := 96246813878781718037981

theorem tailTrace_562320 : CollatzResearch.WordTrace tailWord_562320 prefixEnd_562320 96246813878781718037981 := by
  unfold tailWord_562320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10254747661409075727622207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13672996881878767636829609 10254747661409075727622207)
  ·
    refine ⟨15382121492113613591433311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10254747661409075727622207 15382121492113613591433311)
    ·
      refine ⟨23073182238170420387149967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15382121492113613591433311 23073182238170420387149967)
      ·
        refine ⟨34609773357255630580724951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23073182238170420387149967 34609773357255630580724951)
        ·
          refine ⟨51914660035883445871087427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34609773357255630580724951 51914660035883445871087427)
          ·
            refine ⟨77871990053825168806631141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51914660035883445871087427 77871990053825168806631141)
            ·
              refine ⟨14600998135092219151243339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77871990053825168806631141 14600998135092219151243339)
              ·
                refine ⟨21901497202638328726865009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600998135092219151243339 21901497202638328726865009)
                ·
                  refine ⟨16426122901978746545148757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21901497202638328726865009 16426122901978746545148757)
                  ·
                    refine ⟨96246813878781718037981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16426122901978746545148757 96246813878781718037981)
                    ·
                      rfl

theorem cell23_562320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_562320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562320 prefixEnd_562320 := by exact prefixLift 562320
  have htrace : WordTrace (prefixWord ++ tailWord_562320) baseStart_562320 baseEnd_562320 := by
    simpa [prefixWord, tailWord_562320, baseEnd_562320] using wordTrace_append hprefix tailTrace_562320
  have hstable : (prefixWord ++ tailWord_562320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562320).length < 2 ^ (prefixWord ++ tailWord_562320).sum := by decide
  have hdescent : baseEnd_562320 < baseStart_562320 := by decide
  rcases family_descends (prefixWord ++ tailWord_562320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562354 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_562354 : Nat := 118140960795 + 562354 * 2 ^ 59
def prefixEnd_562354 : Nat := 4983230072969 + 3 ^ 40 * 562354 * 2
def baseEnd_562354 : Nat := 96252633326199340362929

theorem tailTrace_562354 : CollatzResearch.WordTrace tailWord_562354 prefixEnd_562354 96252633326199340362929 := by
  unfold tailWord_562354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127683851173743815495529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13673823603129983507988077 5127683851173743815495529)
  ·
    refine ⟨3845762888380307861621647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5127683851173743815495529 3845762888380307861621647)
    ·
      refine ⟨5768644332570461792432471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845762888380307861621647 5768644332570461792432471)
      ·
        refine ⟨8652966498855692688648707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768644332570461792432471 8652966498855692688648707)
        ·
          refine ⟨12979449748283539032973061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8652966498855692688648707 12979449748283539032973061)
          ·
            refine ⟨2433646827803163568682449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12979449748283539032973061 2433646827803163568682449)
            ·
              refine ⟨1825235120852372676511837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433646827803163568682449 1825235120852372676511837)
              ·
                refine ⟨684463170319639753691939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1825235120852372676511837 684463170319639753691939)
                ·
                  refine ⟨1026694755479459630537909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684463170319639753691939 1026694755479459630537909)
                  ·
                    refine ⟨96252633326199340362929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1026694755479459630537909 96252633326199340362929)
                    ·
                      rfl

theorem cell23_562354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_562354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562354 prefixEnd_562354 := by exact prefixLift 562354
  have htrace : WordTrace (prefixWord ++ tailWord_562354) baseStart_562354 baseEnd_562354 := by
    simpa [prefixWord, tailWord_562354, baseEnd_562354] using wordTrace_append hprefix tailTrace_562354
  have hstable : (prefixWord ++ tailWord_562354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562354).length < 2 ^ (prefixWord ++ tailWord_562354).sum := by decide
  have hdescent : baseEnd_562354 < baseStart_562354 := by decide
  rcases family_descends (prefixWord ++ tailWord_562354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562361 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 2, 3, 2]
def baseStart_562361 : Nat := 118140960795 + 562361 * 2 ^ 59
def prefixEnd_562361 : Nat := 4983230072969 + 3 ^ 40 * 562361 * 2
def baseEnd_562361 : Nat := 288761494343179493701255

theorem tailTrace_562361 : CollatzResearch.WordTrace tailWord_562361 prefixEnd_562361 288761494343179493701255 := by
  unfold tailWord_562361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510990715669615457486937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13673993810446410304991291 20510990715669615457486937)
  ·
    refine ⟨15383243036752211593115203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20510990715669615457486937 15383243036752211593115203)
    ·
      refine ⟨23074864555128317389672805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15383243036752211593115203 23074864555128317389672805)
      ·
        refine ⟨4326537104086559510563651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23074864555128317389672805 4326537104086559510563651)
        ·
          refine ⟨6489805656129839265845477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326537104086559510563651 6489805656129839265845477)
          ·
            refine ⟨1216838560524344862346027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6489805656129839265845477 1216838560524344862346027)
            ·
              refine ⟨1825257840786517293519041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216838560524344862346027 1825257840786517293519041)
              ·
                refine ⟨1368943380589887970139281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825257840786517293519041 1368943380589887970139281)
                ·
                  refine ⟨1026707535442415977604461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1368943380589887970139281 1026707535442415977604461)
                  ·
                    refine ⟨385015325790905991601673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026707535442415977604461 385015325790905991601673)
                    ·
                      refine ⟨288761494343179493701255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385015325790905991601673 288761494343179493701255)
                      ·
                        rfl

theorem cell23_562361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_562361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562361 prefixEnd_562361 := by exact prefixLift 562361
  have htrace : WordTrace (prefixWord ++ tailWord_562361) baseStart_562361 baseEnd_562361 := by
    simpa [prefixWord, tailWord_562361, baseEnd_562361] using wordTrace_append hprefix tailTrace_562361
  have hstable : (prefixWord ++ tailWord_562361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562361).length < 2 ^ (prefixWord ++ tailWord_562361).sum := by decide
  have hdescent : baseEnd_562361 < baseStart_562361 := by decide
  rcases family_descends (prefixWord ++ tailWord_562361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562368 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_562368 : Nat := 118140960795 + 562368 * 2 ^ 59
def prefixEnd_562368 : Nat := 4983230072969 + 3 ^ 40 * 562368 * 2
def baseEnd_562368 : Nat := 288765088707760966313723

theorem tailTrace_562368 : CollatzResearch.WordTrace tailWord_562368 prefixEnd_562368 288765088707760966313723 := by
  unfold tailWord_562368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10255623013322127826495879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13674164017762837101994505 10255623013322127826495879)
  ·
    refine ⟨15383434519983191739743819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10255623013322127826495879 15383434519983191739743819)
    ·
      refine ⟨23075151779974787609615729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15383434519983191739743819 23075151779974787609615729)
      ·
        refine ⟨17306363834981090707211797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23075151779974787609615729 17306363834981090707211797)
        ·
          refine ⟨811235804764738626900553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17306363834981090707211797 811235804764738626900553)
          ·
            refine ⟨608426853573553970175415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811235804764738626900553 608426853573553970175415)
            ·
              refine ⟨912640280360330955263123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608426853573553970175415 912640280360330955263123)
              ·
                refine ⟨1368960420540496432894685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912640280360330955263123 1368960420540496432894685)
                ·
                  refine ⟨513360157702686162335507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1368960420540496432894685 513360157702686162335507)
                  ·
                    refine ⟨770040236554029243503261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513360157702686162335507 770040236554029243503261)
                    ·
                      refine ⟨288765088707760966313723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 770040236554029243503261 288765088707760966313723)
                      ·
                        rfl

theorem cell23_562368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_562368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562368 prefixEnd_562368 := by exact prefixLift 562368
  have htrace : WordTrace (prefixWord ++ tailWord_562368) baseStart_562368 baseEnd_562368 := by
    simpa [prefixWord, tailWord_562368, baseEnd_562368] using wordTrace_append hprefix tailTrace_562368
  have hstable : (prefixWord ++ tailWord_562368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562368).length < 2 ^ (prefixWord ++ tailWord_562368).sum := by decide
  have hdescent : baseEnd_562368 < baseStart_562368 := by decide
  rcases family_descends (prefixWord ++ tailWord_562368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562391 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_562391 : Nat := 118140960795 + 562391 * 2 ^ 59
def prefixEnd_562391 : Nat := 4983230072969 + 3 ^ 40 * 562391 * 2
def baseEnd_562391 : Nat := 288776898762814376326117

theorem tailTrace_562391 : CollatzResearch.WordTrace tailWord_562391 prefixEnd_562391 288776898762814376326117 := by
  unfold tailWord_562391
  simp only [CollatzResearch.WordTrace]
  refine ⟨20512084905560930581079027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13674723270373953720719351 20512084905560930581079027)
  ·
    refine ⟨30768127358341395871618541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20512084905560930581079027 30768127358341395871618541)
    ·
      refine ⟨11538047759378023451856953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30768127358341395871618541 11538047759378023451856953)
      ·
        refine ⟨8653535819533517588892715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11538047759378023451856953 8653535819533517588892715)
        ·
          refine ⟨12980303729300276383339073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8653535819533517588892715 12980303729300276383339073)
          ·
            refine ⟨9735227796975207287504305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12980303729300276383339073 9735227796975207287504305)
            ·
              refine ⟨7301420847731405465628229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735227796975207287504305 7301420847731405465628229)
              ·
                refine ⟨1369016408949638524805293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7301420847731405465628229 1369016408949638524805293)
                ·
                  refine ⟨513381153356114446801985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1369016408949638524805293 513381153356114446801985)
                  ·
                    refine ⟨385035865017085835101489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513381153356114446801985 385035865017085835101489)
                    ·
                      refine ⟨288776898762814376326117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385035865017085835101489 288776898762814376326117)
                      ·
                        rfl

theorem cell23_562391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_562391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562391 prefixEnd_562391 := by exact prefixLift 562391
  have htrace : WordTrace (prefixWord ++ tailWord_562391) baseStart_562391 baseEnd_562391 := by
    simpa [prefixWord, tailWord_562391, baseEnd_562391] using wordTrace_append hprefix tailTrace_562391
  have hstable : (prefixWord ++ tailWord_562391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562391).length < 2 ^ (prefixWord ++ tailWord_562391).sum := by decide
  have hdescent : baseEnd_562391 < baseStart_562391 := by decide
  rcases family_descends (prefixWord ++ tailWord_562391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562418 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_562418 : Nat := 118140960795 + 562418 * 2 ^ 59
def prefixEnd_562418 : Nat := 4983230072969 + 3 ^ 40 * 562418 * 2
def baseEnd_562418 : Nat := 96263587580161923562831

theorem tailTrace_562418 : CollatzResearch.WordTrace tailWord_562418 prefixEnd_562418 96263587580161923562831 := by
  unfold tailWord_562418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128267419115778548077977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13675379784308742794874605 5128267419115778548077977)
  ·
    refine ⟨3846200564336833911058483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5128267419115778548077977 3846200564336833911058483)
    ·
      refine ⟨5769300846505250866587725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846200564336833911058483 5769300846505250866587725)
      ·
        refine ⟨2163487817439469074970397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5769300846505250866587725 2163487817439469074970397)
        ·
          refine ⟨811307931539800903113899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2163487817439469074970397 811307931539800903113899)
          ·
            refine ⟨1216961897309701354670849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811307931539800903113899 1216961897309701354670849)
            ·
              refine ⟨912721422982276016003137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216961897309701354670849 912721422982276016003137)
              ·
                refine ⟨684541067236707012002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912721422982276016003137 684541067236707012002353)
                ·
                  refine ⟨513405800427530259001765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684541067236707012002353 513405800427530259001765)
                  ·
                    refine ⟨96263587580161923562831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 513405800427530259001765 96263587580161923562831)
                    ·
                      rfl

theorem cell23_562418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_562418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562418 prefixEnd_562418 := by exact prefixLift 562418
  have htrace : WordTrace (prefixWord ++ tailWord_562418) baseStart_562418 baseEnd_562418 := by
    simpa [prefixWord, tailWord_562418, baseEnd_562418] using wordTrace_append hprefix tailTrace_562418
  have hstable : (prefixWord ++ tailWord_562418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562418).length < 2 ^ (prefixWord ++ tailWord_562418).sum := by decide
  have hdescent : baseEnd_562418 < baseStart_562418 := by decide
  rcases family_descends (prefixWord ++ tailWord_562418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562441 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_562441 : Nat := 118140960795 + 562441 * 2 ^ 59
def prefixEnd_562441 : Nat := 4983230072969 + 3 ^ 40 * 562441 * 2
def baseEnd_562441 : Nat := 288802572795539180700887

theorem tailTrace_562441 : CollatzResearch.WordTrace tailWord_562441 prefixEnd_562441 288802572795539180700887 := by
  unfold tailWord_562441
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513908555379789120399177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13675939036919859413599451 20513908555379789120399177)
  ·
    refine ⟨15385431416534841840299383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20513908555379789120399177 15385431416534841840299383)
    ·
      refine ⟨23078147124802262760449075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15385431416534841840299383 23078147124802262760449075)
      ·
        refine ⟨34617220687203394140673613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23078147124802262760449075 34617220687203394140673613)
        ·
          refine ⟨12981457757701272802752605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34617220687203394140673613 12981457757701272802752605)
          ·
            refine ⟨4868046659137977301032227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12981457757701272802752605 4868046659137977301032227)
            ·
              refine ⟨7302069988706965951548341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868046659137977301032227 7302069988706965951548341)
              ·
                refine ⟨684569061441278057957657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7302069988706965951548341 684569061441278057957657)
                ·
                  refine ⟨513426796080958543468243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684569061441278057957657 513426796080958543468243)
                  ·
                    refine ⟨770140194121437815202365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513426796080958543468243 770140194121437815202365)
                    ·
                      refine ⟨288802572795539180700887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 770140194121437815202365 288802572795539180700887)
                      ·
                        rfl

theorem cell23_562441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_562441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562441 prefixEnd_562441 := by exact prefixLift 562441
  have htrace : WordTrace (prefixWord ++ tailWord_562441) baseStart_562441 baseEnd_562441 := by
    simpa [prefixWord, tailWord_562441, baseEnd_562441] using wordTrace_append hprefix tailTrace_562441
  have hstable : (prefixWord ++ tailWord_562441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562441).length < 2 ^ (prefixWord ++ tailWord_562441).sum := by decide
  have hdescent : baseEnd_562441 < baseStart_562441 := by decide
  rcases family_descends (prefixWord ++ tailWord_562441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562468 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_562468 : Nat := 118140960795 + 562468 * 2 ^ 59
def prefixEnd_562468 : Nat := 4983230072969 + 3 ^ 40 * 562468 * 2
def baseEnd_562468 : Nat := 288816436773210575063263

theorem tailTrace_562468 : CollatzResearch.WordTrace tailWord_562468 prefixEnd_562468 288816436773210575063263 := by
  unfold tailWord_562468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257446663140986365816029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13676595550854648487754705 10257446663140986365816029)
  ·
    refine ⟨3846542498677869887181011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10257446663140986365816029 3846542498677869887181011)
    ·
      refine ⟨5769813748016804830771517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846542498677869887181011 5769813748016804830771517)
      ·
        refine ⟨2163680155506301811539319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5769813748016804830771517 2163680155506301811539319)
        ·
          refine ⟨3245520233259452717308979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163680155506301811539319 3245520233259452717308979)
          ·
            refine ⟨4868280349889179075963469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245520233259452717308979 4868280349889179075963469)
            ·
              refine ⟨1825605131208442153486301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868280349889179075963469 1825605131208442153486301)
              ·
                refine ⟨684601924203165807557363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1825605131208442153486301 684601924203165807557363)
                ·
                  refine ⟨1026902886304748711336045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684601924203165807557363 1026902886304748711336045)
                  ·
                    refine ⟨385088582364280766751017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026902886304748711336045 385088582364280766751017)
                    ·
                      refine ⟨288816436773210575063263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385088582364280766751017 288816436773210575063263)
                      ·
                        rfl

theorem cell23_562468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_562468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562468 prefixEnd_562468 := by exact prefixLift 562468
  have htrace : WordTrace (prefixWord ++ tailWord_562468) baseStart_562468 baseEnd_562468 := by
    simpa [prefixWord, tailWord_562468, baseEnd_562468] using wordTrace_append hprefix tailTrace_562468
  have hstable : (prefixWord ++ tailWord_562468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562468).length < 2 ^ (prefixWord ++ tailWord_562468).sum := by decide
  have hdescent : baseEnd_562468 < baseStart_562468 := by decide
  rcases family_descends (prefixWord ++ tailWord_562468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562507 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_562507 : Nat := 118140960795 + 562507 * 2 ^ 59
def prefixEnd_562507 : Nat := 4983230072969 + 3 ^ 40 * 562507 * 2
def baseEnd_562507 : Nat := 288836462518735922475583

theorem tailTrace_562507 : CollatzResearch.WordTrace tailWord_562507 prefixEnd_562507 288836462518735922475583 := by
  unfold tailWord_562507
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516315773140682392301775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677543848760454928201183 20516315773140682392301775)
  ·
    refine ⟨30774473659711023588452663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20516315773140682392301775 30774473659711023588452663)
    ·
      refine ⟨46161710489566535382678995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30774473659711023588452663 46161710489566535382678995)
      ·
        refine ⟨69242565734349803074018493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46161710489566535382678995 69242565734349803074018493)
        ·
          refine ⟨25965962150381176152756935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69242565734349803074018493 25965962150381176152756935)
          ·
            refine ⟨38948943225571764229135403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25965962150381176152756935 38948943225571764229135403)
            ·
              refine ⟨58423414838357646343703105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38948943225571764229135403 58423414838357646343703105)
              ·
                refine ⟨43817561128768234757777329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58423414838357646343703105 43817561128768234757777329)
                ·
                  refine ⟨32863170846576176068332997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43817561128768234757777329 32863170846576176068332997)
                  ·
                    refine ⟨6161844533733033012812437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32863170846576176068332997 6161844533733033012812437)
                    ·
                      refine ⟨288836462518735922475583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6161844533733033012812437 288836462518735922475583)
                      ·
                        rfl

theorem cell23_562507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_562507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562507 prefixEnd_562507 := by exact prefixLift 562507
  have htrace : WordTrace (prefixWord ++ tailWord_562507) baseStart_562507 baseEnd_562507 := by
    simpa [prefixWord, tailWord_562507, baseEnd_562507] using wordTrace_append hprefix tailTrace_562507
  have hstable : (prefixWord ++ tailWord_562507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562507).length < 2 ^ (prefixWord ++ tailWord_562507).sum := by decide
  have hdescent : baseEnd_562507 < baseStart_562507 := by decide
  rcases family_descends (prefixWord ++ tailWord_562507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562521 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 5]
def baseStart_562521 : Nat := 118140960795 + 562521 * 2 ^ 59
def prefixEnd_562521 : Nat := 4983230072969 + 3 ^ 40 * 562521 * 2
def baseEnd_562521 : Nat := 32093739027544318633391

theorem tailTrace_562521 : CollatzResearch.WordTrace tailWord_562521 prefixEnd_562521 32093739027544318633391 := by
  unfold tailWord_562521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516826395089962783311417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677884263393308522207611 20516826395089962783311417)
  ·
    refine ⟨15387619796317472087483563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20516826395089962783311417 15387619796317472087483563)
    ·
      refine ⟨23081429694476208131225345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387619796317472087483563 23081429694476208131225345)
      ·
        refine ⟨17311072270857156098419009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23081429694476208131225345 17311072270857156098419009)
        ·
          refine ⟨12983304203142867073814257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17311072270857156098419009 12983304203142867073814257)
          ·
            refine ⟨9737478152357150305360693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12983304203142867073814257 9737478152357150305360693)
            ·
              refine ⟨912888576783482841127565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9737478152357150305360693 912888576783482841127565)
              ·
                refine ⟨342333216293806065422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912888576783482841127565 342333216293806065422837)
                ·
                  refine ⟨32093739027544318633391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 342333216293806065422837 32093739027544318633391)
                  ·
                    rfl

theorem cell23_562521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 5].length) (baseStart_562521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562521 prefixEnd_562521 := by exact prefixLift 562521
  have htrace : WordTrace (prefixWord ++ tailWord_562521) baseStart_562521 baseEnd_562521 := by
    simpa [prefixWord, tailWord_562521, baseEnd_562521] using wordTrace_append hprefix tailTrace_562521
  have hstable : (prefixWord ++ tailWord_562521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562521).length < 2 ^ (prefixWord ++ tailWord_562521).sum := by decide
  have hdescent : baseEnd_562521 < baseStart_562521 := by decide
  rcases family_descends (prefixWord ++ tailWord_562521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562538 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_562538 : Nat := 118140960795 + 562538 * 2 ^ 59
def prefixEnd_562538 : Nat := 4983230072969 + 3 ^ 40 * 562538 * 2
def baseEnd_562538 : Nat := 32094708935447255687549

theorem tailTrace_562538 : CollatzResearch.WordTrace tailWord_562538 prefixEnd_562538 32094708935447255687549 := by
  unfold tailWord_562538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129361609007093671670067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13678297624018916457786845 5129361609007093671670067)
  ·
    refine ⟨7694042413510640507505101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129361609007093671670067 7694042413510640507505101)
    ·
      refine ⟨2885265905066490190314413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7694042413510640507505101 2885265905066490190314413)
      ·
        refine ⟨1081974714399933821367905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2885265905066490190314413 1081974714399933821367905)
        ·
          refine ⟨811481035799950366025929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081974714399933821367905 811481035799950366025929)
          ·
            refine ⟨608610776849962774519447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811481035799950366025929 608610776849962774519447)
            ·
              refine ⟨912916165274944161779171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608610776849962774519447 912916165274944161779171)
              ·
                refine ⟨1369374247912416242668757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912916165274944161779171 1369374247912416242668757)
                ·
                  refine ⟨32094708935447255687549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1369374247912416242668757 32094708935447255687549)
                  ·
                    rfl

theorem cell23_562538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_562538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562538 prefixEnd_562538 := by exact prefixLift 562538
  have htrace : WordTrace (prefixWord ++ tailWord_562538) baseStart_562538 baseEnd_562538 := by
    simpa [prefixWord, tailWord_562538, baseEnd_562538] using wordTrace_append hprefix tailTrace_562538
  have hstable : (prefixWord ++ tailWord_562538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562538).length < 2 ^ (prefixWord ++ tailWord_562538).sum := by decide
  have hdescent : baseEnd_562538 < baseStart_562538 := by decide
  rcases family_descends (prefixWord ++ tailWord_562538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562544 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_562544 : Nat := 118140960795 + 562544 * 2 ^ 59
def prefixEnd_562544 : Nat := 4983230072969 + 3 ^ 40 * 562544 * 2
def baseEnd_562544 : Nat := 288855461302952277712913

theorem tailTrace_562544 : CollatzResearch.WordTrace tailWord_562544 prefixEnd_562544 288855461302952277712913 := by
  unfold tailWord_562544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258832637003318855699343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13678443516004425140932457 10258832637003318855699343)
  ·
    refine ⟨15388248955504978283549015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258832637003318855699343 15388248955504978283549015)
    ·
      refine ⟨23082373433257467425323523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388248955504978283549015 23082373433257467425323523)
      ·
        refine ⟨34623560149886201137985285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23082373433257467425323523 34623560149886201137985285)
        ·
          refine ⟨6491917528103662713372241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34623560149886201137985285 6491917528103662713372241)
          ·
            refine ⟨4868938146077747035029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6491917528103662713372241 4868938146077747035029181)
            ·
              refine ⟨1825851804779155138135943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868938146077747035029181 1825851804779155138135943)
              ·
                refine ⟨2738777707168732707203915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825851804779155138135943 2738777707168732707203915)
                ·
                  refine ⟨4108166560753099060805873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738777707168732707203915 4108166560753099060805873)
                  ·
                    refine ⟨3081124920564824295604405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108166560753099060805873 3081124920564824295604405)
                    ·
                      refine ⟨288855461302952277712913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3081124920564824295604405 288855461302952277712913)
                      ·
                        rfl

theorem cell23_562544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_562544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562544 prefixEnd_562544 := by exact prefixLift 562544
  have htrace : WordTrace (prefixWord ++ tailWord_562544) baseStart_562544 baseEnd_562544 := by
    simpa [prefixWord, tailWord_562544, baseEnd_562544] using wordTrace_append hprefix tailTrace_562544
  have hstable : (prefixWord ++ tailWord_562544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562544).length < 2 ^ (prefixWord ++ tailWord_562544).sum := by decide
  have hdescent : baseEnd_562544 < baseStart_562544 := by decide
  rcases family_descends (prefixWord ++ tailWord_562544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562549 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_562549 : Nat := 118140960795 + 562549 * 2 ^ 59
def prefixEnd_562549 : Nat := 4983230072969 + 3 ^ 40 * 562549 * 2
def baseEnd_562549 : Nat := 288858028706224758150391

theorem tailTrace_562549 : CollatzResearch.WordTrace tailWord_562549 prefixEnd_562549 288858028706224758150391 := by
  unfold tailWord_562549
  simp only [CollatzResearch.WordTrace]
  refine ⟨20517847638988523565330701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13678565092659015710220467 20517847638988523565330701)
  ·
    refine ⟨7694192864620696336999013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20517847638988523565330701 7694192864620696336999013)
    ·
      refine ⟨1442661162116380563187315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7694192864620696336999013 1442661162116380563187315)
      ·
        refine ⟨2163991743174570844780973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442661162116380563187315 2163991743174570844780973)
        ·
          refine ⟨811496903690464066792865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2163991743174570844780973 811496903690464066792865)
          ·
            refine ⟨608622677767848050094649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811496903690464066792865 608622677767848050094649)
            ·
              refine ⟨456467008325886037570987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608622677767848050094649 456467008325886037570987)
              ·
                refine ⟨684700512488829056356481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456467008325886037570987 684700512488829056356481)
                ·
                  refine ⟨513525384366621792267361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684700512488829056356481 513525384366621792267361)
                  ·
                    refine ⟨385144038274966344200521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513525384366621792267361 385144038274966344200521)
                    ·
                      refine ⟨288858028706224758150391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385144038274966344200521 288858028706224758150391)
                      ·
                        rfl

theorem cell23_562549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_562549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562549 prefixEnd_562549 := by exact prefixLift 562549
  have htrace : WordTrace (prefixWord ++ tailWord_562549) baseStart_562549 baseEnd_562549 := by
    simpa [prefixWord, tailWord_562549, baseEnd_562549] using wordTrace_append hprefix tailTrace_562549
  have hstable : (prefixWord ++ tailWord_562549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562549).length < 2 ^ (prefixWord ++ tailWord_562549).sum := by decide
  have hdescent : baseEnd_562549 < baseStart_562549 := by decide
  rcases family_descends (prefixWord ++ tailWord_562549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562571 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4]
def baseStart_562571 : Nat := 118140960795 + 562571 * 2 ^ 59
def prefixEnd_562571 : Nat := 4983230072969 + 3 ^ 40 * 562571 * 2
def baseEnd_562571 : Nat := 288869325280623672075289

theorem tailTrace_562571 : CollatzResearch.WordTrace tailWord_562571 prefixEnd_562571 288869325280623672075289 := by
  unfold tailWord_562571
  simp only [CollatzResearch.WordTrace]
  refine ⟨20518650044908821322631567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13679100029939214215087711 20518650044908821322631567)
  ·
    refine ⟨30777975067363231983947351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20518650044908821322631567 30777975067363231983947351)
    ·
      refine ⟨46166962601044847975921027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30777975067363231983947351 46166962601044847975921027)
      ·
        refine ⟨69250443901567271963881541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46166962601044847975921027 69250443901567271963881541)
        ·
          refine ⟨12984458231543863493227789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69250443901567271963881541 12984458231543863493227789)
          ·
            refine ⟨4869171836828948809960421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12984458231543863493227789 4869171836828948809960421)
            ·
              refine ⟨912969719405427901867579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4869171836828948809960421 912969719405427901867579)
              ·
                refine ⟨1369454579108141852801369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912969719405427901867579 1369454579108141852801369)
                ·
                  refine ⟨1027090934331106389601027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1369454579108141852801369 1027090934331106389601027)
                  ·
                    refine ⟨1540636401496659584401541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027090934331106389601027 1540636401496659584401541)
                    ·
                      refine ⟨288869325280623672075289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1540636401496659584401541 288869325280623672075289)
                      ·
                        rfl

theorem cell23_562571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].length) (baseStart_562571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562571 prefixEnd_562571 := by exact prefixLift 562571
  have htrace : WordTrace (prefixWord ++ tailWord_562571) baseStart_562571 baseEnd_562571 := by
    simpa [prefixWord, tailWord_562571, baseEnd_562571] using wordTrace_append hprefix tailTrace_562571
  have hstable : (prefixWord ++ tailWord_562571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562571).length < 2 ^ (prefixWord ++ tailWord_562571).sum := by decide
  have hdescent : baseEnd_562571 < baseStart_562571 := by decide
  rcases family_descends (prefixWord ++ tailWord_562571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562605 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_562605 : Nat := 118140960795 + 562605 * 2 ^ 59
def prefixEnd_562605 : Nat := 4983230072969 + 3 ^ 40 * 562605 * 2
def baseEnd_562605 : Nat := 288886783622876539050133

theorem tailTrace_562605 : CollatzResearch.WordTrace tailWord_562605 prefixEnd_562605 288886783622876539050133 := by
  unfold tailWord_562605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20519890126785645129369269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13679926751190430086246179 20519890126785645129369269)
  ·
    refine ⟨1923739699386154230878369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20519890126785645129369269 1923739699386154230878369)
    ·
      refine ⟨1442804774539615673158777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1923739699386154230878369 1442804774539615673158777)
      ·
        refine ⟨1082103580904711754869083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442804774539615673158777 1082103580904711754869083)
        ·
          refine ⟨1623155371357067632303625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082103580904711754869083 1623155371357067632303625)
          ·
            refine ⟨1217366528517800724227719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623155371357067632303625 1217366528517800724227719)
            ·
              refine ⟨1826049792776701086341579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217366528517800724227719 1826049792776701086341579)
              ·
                refine ⟨2739074689165051629512369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826049792776701086341579 2739074689165051629512369)
                ·
                  refine ⟨2054306016873788722134277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739074689165051629512369 2054306016873788722134277)
                  ·
                    refine ⟨385182378163835385400177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054306016873788722134277 385182378163835385400177)
                    ·
                      refine ⟨288886783622876539050133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385182378163835385400177 288886783622876539050133)
                      ·
                        rfl

theorem cell23_562605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_562605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562605 prefixEnd_562605 := by exact prefixLift 562605
  have htrace : WordTrace (prefixWord ++ tailWord_562605) baseStart_562605 baseEnd_562605 := by
    simpa [prefixWord, tailWord_562605, baseEnd_562605] using wordTrace_append hprefix tailTrace_562605
  have hstable : (prefixWord ++ tailWord_562605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562605).length < 2 ^ (prefixWord ++ tailWord_562605).sum := by decide
  have hdescent : baseEnd_562605 < baseStart_562605 := by decide
  rcases family_descends (prefixWord ++ tailWord_562605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562648 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_562648 : Nat := 118140960795 + 562648 * 2 ^ 59
def prefixEnd_562648 : Nat := 4983230072969 + 3 ^ 40 * 562648 * 2
def baseEnd_562648 : Nat := 288908863291019870812435

theorem tailTrace_562648 : CollatzResearch.WordTrace tailWord_562648 prefixEnd_562648 288908863291019870812435 := by
  unfold tailWord_562648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260729232814931736592299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13680972310419908982123065 10260729232814931736592299)
  ·
    refine ⟨15391093849222397604888449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10260729232814931736592299 15391093849222397604888449)
    ·
      refine ⟨11543320386916798203666337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15391093849222397604888449 11543320386916798203666337)
      ·
        refine ⟨8657490290187598652749753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11543320386916798203666337 8657490290187598652749753)
        ·
          refine ⟨6493117717640698989562315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8657490290187598652749753 6493117717640698989562315)
          ·
            refine ⟨9739676576461048484343473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493117717640698989562315 9739676576461048484343473)
            ·
              refine ⟨7304757432345786363257605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9739676576461048484343473 7304757432345786363257605)
              ·
                refine ⟨1369642018564834943110801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7304757432345786363257605 1369642018564834943110801)
                ·
                  refine ⟨1027231513923626207333101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1369642018564834943110801 1027231513923626207333101)
                  ·
                    refine ⟨385211817721359827749913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027231513923626207333101 385211817721359827749913)
                    ·
                      refine ⟨288908863291019870812435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385211817721359827749913 288908863291019870812435)
                      ·
                        rfl

theorem cell23_562648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_562648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562648 prefixEnd_562648 := by exact prefixLift 562648
  have htrace : WordTrace (prefixWord ++ tailWord_562648) baseStart_562648 baseEnd_562648 := by
    simpa [prefixWord, tailWord_562648, baseEnd_562648] using wordTrace_append hprefix tailTrace_562648
  have hstable : (prefixWord ++ tailWord_562648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562648).length < 2 ^ (prefixWord ++ tailWord_562648).sum := by decide
  have hdescent : baseEnd_562648 < baseStart_562648 := by decide
  rcases family_descends (prefixWord ++ tailWord_562648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562655 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 1, 1, 3]
def baseStart_562655 : Nat := 118140960795 + 562655 * 2 ^ 59
def prefixEnd_562655 : Nat := 4983230072969 + 3 ^ 40 * 562655 * 2
def baseEnd_562655 : Nat := 288912457655601343424903

theorem tailTrace_562655 : CollatzResearch.WordTrace tailWord_562655 prefixEnd_562655 288912457655601343424903 := by
  unfold tailWord_562655
  simp only [CollatzResearch.WordTrace]
  refine ⟨20521713776604503668689419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13681142517736335779126279 20521713776604503668689419)
  ·
    refine ⟨30782570664906755503034129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20521713776604503668689419 30782570664906755503034129)
    ·
      refine ⟨23086927998680066627275597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30782570664906755503034129 23086927998680066627275597)
      ·
        refine ⟨8657597999505024985228349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23086927998680066627275597 8657597999505024985228349)
        ·
          refine ⟨3246599249814384369460631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8657597999505024985228349 3246599249814384369460631)
          ·
            refine ⟨4869898874721576554190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246599249814384369460631 4869898874721576554190947)
            ·
              refine ⟨7304848312082364831286421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4869898874721576554190947 7304848312082364831286421)
              ·
                refine ⟨342414764628860851466551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7304848312082364831286421 342414764628860851466551)
                ·
                  refine ⟨513622146943291277199827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342414764628860851466551 513622146943291277199827)
                  ·
                    refine ⟨770433220414936915799741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513622146943291277199827 770433220414936915799741)
                    ·
                      refine ⟨288912457655601343424903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 770433220414936915799741 288912457655601343424903)
                      ·
                        rfl

theorem cell23_562655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_562655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562655 prefixEnd_562655 := by exact prefixLift 562655
  have htrace : WordTrace (prefixWord ++ tailWord_562655) baseStart_562655 baseEnd_562655 := by
    simpa [prefixWord, tailWord_562655, baseEnd_562655] using wordTrace_append hprefix tailTrace_562655
  have hstable : (prefixWord ++ tailWord_562655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562655).length < 2 ^ (prefixWord ++ tailWord_562655).sum := by decide
  have hdescent : baseEnd_562655 < baseStart_562655 := by decide
  rcases family_descends (prefixWord ++ tailWord_562655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562671 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 6]
def baseStart_562671 : Nat := 118140960795 + 562671 * 2 ^ 59
def prefixEnd_562671 : Nat := 4983230072969 + 3 ^ 40 * 562671 * 2
def baseEnd_562671 : Nat := 96306891115357760274943

theorem tailTrace_562671 : CollatzResearch.WordTrace tailWord_562671 prefixEnd_562671 96306891115357760274943 := by
  unfold tailWord_562671
  simp only [CollatzResearch.WordTrace]
  refine ⟨20522297344546538401271867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13681531563031025600847911 20522297344546538401271867)
  ·
    refine ⟨30783446016819807601907801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20522297344546538401271867 30783446016819807601907801)
    ·
      refine ⟨23087584512614855701430851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30783446016819807601907801 23087584512614855701430851)
      ·
        refine ⟨34631376768922283552146277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23087584512614855701430851 34631376768922283552146277)
        ·
          refine ⟨6493383144172928166027427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34631376768922283552146277 6493383144172928166027427)
          ·
            refine ⟨9740074716259392249041141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493383144172928166027427 9740074716259392249041141)
            ·
              refine ⟨913132004649318023347607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9740074716259392249041141 913132004649318023347607)
              ·
                refine ⟨1369698006973977035021411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913132004649318023347607 1369698006973977035021411)
                ·
                  refine ⟨2054547010460965552532117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369698006973977035021411 2054547010460965552532117)
                  ·
                    refine ⟨96306891115357760274943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2054547010460965552532117 96306891115357760274943)
                    ·
                      rfl

theorem cell23_562671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_562671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562671 prefixEnd_562671 := by exact prefixLift 562671
  have htrace : WordTrace (prefixWord ++ tailWord_562671) baseStart_562671 baseEnd_562671 := by
    simpa [prefixWord, tailWord_562671, baseEnd_562671] using wordTrace_append hprefix tailTrace_562671
  have hstable : (prefixWord ++ tailWord_562671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562671).length < 2 ^ (prefixWord ++ tailWord_562671).sum := by decide
  have hdescent : baseEnd_562671 < baseStart_562671 := by decide
  rcases family_descends (prefixWord ++ tailWord_562671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562689 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_562689 : Nat := 118140960795 + 562689 * 2 ^ 59
def prefixEnd_562689 : Nat := 4983230072969 + 3 ^ 40 * 562689 * 2
def baseEnd_562689 : Nat := 288929915997854210399747

theorem tailTrace_562689 : CollatzResearch.WordTrace tailWord_562689 prefixEnd_562689 288929915997854210399747 := by
  unfold tailWord_562689
  simp only [CollatzResearch.WordTrace]
  refine ⟨20522953858481327475427121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13681969238987551650284747 20522953858481327475427121)
  ·
    refine ⟨15392215393860995606570341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20522953858481327475427121 15392215393860995606570341)
    ·
      refine ⟨2886040386348936676231939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15392215393860995606570341 2886040386348936676231939)
      ·
        refine ⟨4329060579523405014347909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886040386348936676231939 4329060579523405014347909)
        ·
          refine ⟨811698858660638440190233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4329060579523405014347909 811698858660638440190233)
          ·
            refine ⟨608774143995478830142675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811698858660638440190233 608774143995478830142675)
            ·
              refine ⟨913161215993218245214013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608774143995478830142675 913161215993218245214013)
              ·
                refine ⟨342435455997456841955255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913161215993218245214013 342435455997456841955255)
                ·
                  refine ⟨513653183996185262932883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342435455997456841955255 513653183996185262932883)
                  ·
                    refine ⟨770479775994277894399325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513653183996185262932883 770479775994277894399325)
                    ·
                      refine ⟨288929915997854210399747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 770479775994277894399325 288929915997854210399747)
                      ·
                        rfl

theorem cell23_562689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_562689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562689 prefixEnd_562689 := by exact prefixLift 562689
  have htrace : WordTrace (prefixWord ++ tailWord_562689) baseStart_562689 baseEnd_562689 := by
    simpa [prefixWord, tailWord_562689, baseEnd_562689] using wordTrace_append hprefix tailTrace_562689
  have hstable : (prefixWord ++ tailWord_562689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562689).length < 2 ^ (prefixWord ++ tailWord_562689).sum := by decide
  have hdescent : baseEnd_562689 < baseStart_562689 := by decide
  rcases family_descends (prefixWord ++ tailWord_562689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562698 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_562698 : Nat := 118140960795 + 562698 * 2 ^ 59
def prefixEnd_562698 : Nat := 4983230072969 + 3 ^ 40 * 562698 * 2
def baseEnd_562698 : Nat := 288934537323744675187205

theorem tailTrace_562698 : CollatzResearch.WordTrace tailWord_562698 prefixEnd_562698 288934537323744675187205 := by
  unfold tailWord_562698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5130820528862180503126187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13682188076965814675003165 5130820528862180503126187)
  ·
    refine ⟨7696230793293270754689281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5130820528862180503126187 7696230793293270754689281)
    ·
      refine ⟨5772173094969953066016961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7696230793293270754689281 5772173094969953066016961)
      ·
        refine ⟨4329129821227464799512721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5772173094969953066016961 4329129821227464799512721)
        ·
          refine ⟨3246847365920598599634541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4329129821227464799512721 3246847365920598599634541)
          ·
            refine ⟨1217567762220224474862953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3246847365920598599634541 1217567762220224474862953)
            ·
              refine ⟨913175821665168356147215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217567762220224474862953 913175821665168356147215)
              ·
                refine ⟨1369763732497752534220823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913175821665168356147215 1369763732497752534220823)
                ·
                  refine ⟨2054645598746628801331235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369763732497752534220823 2054645598746628801331235)
                  ·
                    refine ⟨3081968398119943201996853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054645598746628801331235 3081968398119943201996853)
                    ·
                      refine ⟨288934537323744675187205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3081968398119943201996853 288934537323744675187205)
                      ·
                        rfl

theorem cell23_562698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_562698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562698 prefixEnd_562698 := by exact prefixLift 562698
  have htrace : WordTrace (prefixWord ++ tailWord_562698) baseStart_562698 baseEnd_562698 := by
    simpa [prefixWord, tailWord_562698, baseEnd_562698] using wordTrace_append hprefix tailTrace_562698
  have hstable : (prefixWord ++ tailWord_562698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562698).length < 2 ^ (prefixWord ++ tailWord_562698).sum := by decide
  have hdescent : baseEnd_562698 < baseStart_562698 := by decide
  rcases family_descends (prefixWord ++ tailWord_562698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562768 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2]
def baseStart_562768 : Nat := 118140960795 + 562768 * 2 ^ 59
def prefixEnd_562768 : Nat := 4983230072969 + 3 ^ 40 * 562768 * 2
def baseEnd_562768 : Nat := 288970480969559401311883

theorem tailTrace_562768 : CollatzResearch.WordTrace tailWord_562768 prefixEnd_562768 288970480969559401311883 := by
  unfold tailWord_562768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262917612597561983776479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13683890150130082645035305 10262917612597561983776479)
  ·
    refine ⟨15394376418896342975664719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10262917612597561983776479 15394376418896342975664719)
    ·
      refine ⟨23091564628344514463497079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15394376418896342975664719 23091564628344514463497079)
      ·
        refine ⟨34637346942516771695245619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23091564628344514463497079 34637346942516771695245619)
        ·
          refine ⟨51956020413775157542868429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34637346942516771695245619 51956020413775157542868429)
          ·
            refine ⟨19483507655165684078575661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51956020413775157542868429 19483507655165684078575661)
            ·
              refine ⟨7306315370687131529465873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19483507655165684078575661 7306315370687131529465873)
              ·
                refine ⟨5479736528015348647099405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7306315370687131529465873 5479736528015348647099405)
                ·
                  refine ⟨2054901198005755742662277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5479736528015348647099405 2054901198005755742662277)
                  ·
                    refine ⟨385293974626079201749177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054901198005755742662277 385293974626079201749177)
                    ·
                      refine ⟨288970480969559401311883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385293974626079201749177 288970480969559401311883)
                      ·
                        rfl

theorem cell23_562768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2].length) (baseStart_562768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562768 prefixEnd_562768 := by exact prefixLift 562768
  have htrace : WordTrace (prefixWord ++ tailWord_562768) baseStart_562768 baseEnd_562768 := by
    simpa [prefixWord, tailWord_562768, baseEnd_562768] using wordTrace_append hprefix tailTrace_562768
  have hstable : (prefixWord ++ tailWord_562768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562768).length < 2 ^ (prefixWord ++ tailWord_562768).sum := by decide
  have hdescent : baseEnd_562768 < baseStart_562768 := by decide
  rcases family_descends (prefixWord ++ tailWord_562768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562785 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_562785 : Nat := 118140960795 + 562785 * 2 ^ 59
def prefixEnd_562785 : Nat := 4983230072969 + 3 ^ 40 * 562785 * 2
def baseEnd_562785 : Nat := 288979210140685834799305

theorem tailTrace_562785 : CollatzResearch.WordTrace tailWord_562785 prefixEnd_562785 288979210140685834799305 := by
  unfold tailWord_562785
  simp only [CollatzResearch.WordTrace]
  refine ⟨20526455266133535870921809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13684303510755690580614539 20526455266133535870921809)
  ·
    refine ⟨15394841449600151903191357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20526455266133535870921809 15394841449600151903191357)
    ·
      refine ⟨5773065543600056963696759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15394841449600151903191357 5773065543600056963696759)
      ·
        refine ⟨8659598315400085445545139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773065543600056963696759 8659598315400085445545139)
        ·
          refine ⟨12989397473100128168317709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8659598315400085445545139 12989397473100128168317709)
          ·
            refine ⟨4871024052412548063119141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12989397473100128168317709 4871024052412548063119141)
            ·
              refine ⟨913317009827352761834839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4871024052412548063119141 913317009827352761834839)
              ·
                refine ⟨1369975514741029142752259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913317009827352761834839 1369975514741029142752259)
                ·
                  refine ⟨2054963272111543714128389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369975514741029142752259 2054963272111543714128389)
                  ·
                    refine ⟨385305613520914446399073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054963272111543714128389 385305613520914446399073)
                    ·
                      refine ⟨288979210140685834799305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385305613520914446399073 288979210140685834799305)
                      ·
                        rfl

theorem cell23_562785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_562785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562785 prefixEnd_562785 := by exact prefixLift 562785
  have htrace : WordTrace (prefixWord ++ tailWord_562785) baseStart_562785 baseEnd_562785 := by
    simpa [prefixWord, tailWord_562785, baseEnd_562785] using wordTrace_append hprefix tailTrace_562785
  have hstable : (prefixWord ++ tailWord_562785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562785).length < 2 ^ (prefixWord ++ tailWord_562785).sum := by decide
  have hdescent : baseEnd_562785 < baseStart_562785 := by decide
  rcases family_descends (prefixWord ++ tailWord_562785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562791 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 9]
def baseStart_562791 : Nat := 118140960795 + 562791 * 2 ^ 59
def prefixEnd_562791 : Nat := 4983230072969 + 3 ^ 40 * 562791 * 2
def baseEnd_562791 : Nat := 32109143447179201258253

theorem tailTrace_562791 : CollatzResearch.WordTrace tailWord_562791 prefixEnd_562791 32109143447179201258253 := by
  unfold tailWord_562791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20526674104111798895640227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13684449402741199263760151 20526674104111798895640227)
  ·
    refine ⟨30790011156167698343460341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20526674104111798895640227 30790011156167698343460341)
    ·
      refine ⟨2886563545890721719699407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30790011156167698343460341 2886563545890721719699407)
      ·
        refine ⟨4329845318836082579549111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886563545890721719699407 4329845318836082579549111)
        ·
          refine ⟨6494767978254123869323667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329845318836082579549111 6494767978254123869323667)
          ·
            refine ⟨9742151967381185803985501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494767978254123869323667 9742151967381185803985501)
            ·
              refine ⟨3653306987767944676494563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9742151967381185803985501 3653306987767944676494563)
              ·
                refine ⟨5479960481651917014741845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653306987767944676494563 5479960481651917014741845)
                ·
                  refine ⟨32109143447179201258253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5479960481651917014741845 32109143447179201258253)
                  ·
                    rfl

theorem cell23_562791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 9].length) (baseStart_562791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562791 prefixEnd_562791 := by exact prefixLift 562791
  have htrace : WordTrace (prefixWord ++ tailWord_562791) baseStart_562791 baseEnd_562791 := by
    simpa [prefixWord, tailWord_562791, baseEnd_562791] using wordTrace_append hprefix tailTrace_562791
  have hstable : (prefixWord ++ tailWord_562791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562791).length < 2 ^ (prefixWord ++ tailWord_562791).sum := by decide
  have hdescent : baseEnd_562791 < baseStart_562791 := by decide
  rcases family_descends (prefixWord ++ tailWord_562791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562806 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_562806 : Nat := 118140960795 + 562806 * 2 ^ 59
def prefixEnd_562806 : Nat := 4983230072969 + 3 ^ 40 * 562806 * 2
def baseEnd_562806 : Nat := 288989993234430252636709

theorem tailTrace_562806 : CollatzResearch.WordTrace tailWord_562806 prefixEnd_562806 288989993234430252636709 := by
  unfold tailWord_562806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282951324941091028589767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13684814132704970971624181 1282951324941091028589767)
  ·
    refine ⟨1924426987411636542884651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1282951324941091028589767 1924426987411636542884651)
    ·
      refine ⟨2886640481117454814326977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1924426987411636542884651 2886640481117454814326977)
      ·
        refine ⟨2164980360838091110745233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2886640481117454814326977 2164980360838091110745233)
        ·
          refine ⟨1623735270628568333058925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164980360838091110745233 1623735270628568333058925)
          ·
            refine ⟨608900726485713124897097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1623735270628568333058925 608900726485713124897097)
            ·
              refine ⟨456675544864284843672823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608900726485713124897097 456675544864284843672823)
              ·
                refine ⟨685013317296427265509235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456675544864284843672823 685013317296427265509235)
                ·
                  refine ⟨1027519975944640898263853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685013317296427265509235 1027519975944640898263853)
                  ·
                    refine ⟨385319990979240336848945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027519975944640898263853 385319990979240336848945)
                    ·
                      refine ⟨288989993234430252636709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385319990979240336848945 288989993234430252636709)
                      ·
                        rfl

theorem cell23_562806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_562806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562806 prefixEnd_562806 := by exact prefixLift 562806
  have htrace : WordTrace (prefixWord ++ tailWord_562806) baseStart_562806 baseEnd_562806 := by
    simpa [prefixWord, tailWord_562806, baseEnd_562806] using wordTrace_append hprefix tailTrace_562806
  have hstable : (prefixWord ++ tailWord_562806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562806).length < 2 ^ (prefixWord ++ tailWord_562806).sum := by decide
  have hdescent : baseEnd_562806 < baseStart_562806 := by decide
  rcases family_descends (prefixWord ++ tailWord_562806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562836 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_562836 : Nat := 118140960795 + 562836 * 2 ^ 59
def prefixEnd_562836 : Nat := 4983230072969 + 3 ^ 40 * 562836 * 2
def baseEnd_562836 : Nat := 289005397654065135261571

theorem tailTrace_562836 : CollatzResearch.WordTrace tailWord_562836 prefixEnd_562836 289005397654065135261571 := by
  unfold tailWord_562836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264157694474385790514181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13685543592632514387352241 10264157694474385790514181)
  ·
    refine ⟨1924529567713947335721409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10264157694474385790514181 1924529567713947335721409)
    ·
      refine ⟨1443397175785460501791057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1924529567713947335721409 1443397175785460501791057)
      ·
        refine ⟨1082547881839095376343293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443397175785460501791057 1082547881839095376343293)
        ·
          refine ⟨405955455689660766128735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1082547881839095376343293 405955455689660766128735)
          ·
            refine ⟨608933183534491149193103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405955455689660766128735 608933183534491149193103)
            ·
              refine ⟨913399775301736723789655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608933183534491149193103 913399775301736723789655)
              ·
                refine ⟨1370099662952605085684483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913399775301736723789655 1370099662952605085684483)
                ·
                  refine ⟨2055149494428907628526725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370099662952605085684483 2055149494428907628526725)
                  ·
                    refine ⟨385340530205420180348761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2055149494428907628526725 385340530205420180348761)
                    ·
                      refine ⟨289005397654065135261571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385340530205420180348761 289005397654065135261571)
                      ·
                        rfl

theorem cell23_562836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_562836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562836 prefixEnd_562836 := by exact prefixLift 562836
  have htrace : WordTrace (prefixWord ++ tailWord_562836) baseStart_562836 baseEnd_562836 := by
    simpa [prefixWord, tailWord_562836, baseEnd_562836] using wordTrace_append hprefix tailTrace_562836
  have hstable : (prefixWord ++ tailWord_562836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562836).length < 2 ^ (prefixWord ++ tailWord_562836).sum := by decide
  have hdescent : baseEnd_562836 < baseStart_562836 := by decide
  rcases family_descends (prefixWord ++ tailWord_562836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562851 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 8]
def baseStart_562851 : Nat := 118140960795 + 562851 * 2 ^ 59
def prefixEnd_562851 : Nat := 4983230072969 + 3 ^ 40 * 562851 * 2
def baseEnd_562851 : Nat := 96337699954627525524667

theorem tailTrace_562851 : CollatzResearch.WordTrace tailWord_562851 prefixEnd_562851 96337699954627525524667 := by
  unfold tailWord_562851
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528862483894429142824407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13685908322596286095216271 20528862483894429142824407)
  ·
    refine ⟨30793293725841643714236611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20528862483894429142824407 30793293725841643714236611)
    ·
      refine ⟨46189940588762465571354917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30793293725841643714236611 46189940588762465571354917)
      ·
        refine ⟨8660613860392962294629047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46189940588762465571354917 8660613860392962294629047)
        ·
          refine ⟨12990920790589443441943571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660613860392962294629047 12990920790589443441943571)
          ·
            refine ⟨19486381185884165162915357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12990920790589443441943571 19486381185884165162915357)
            ·
              refine ⟨7307392944706561936093259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19486381185884165162915357 7307392944706561936093259)
              ·
                refine ⟨10961089417059842904139889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7307392944706561936093259 10961089417059842904139889)
                ·
                  refine ⟨8220817062794882178104917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10961089417059842904139889 8220817062794882178104917)
                  ·
                    refine ⟨96337699954627525524667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8220817062794882178104917 96337699954627525524667)
                    ·
                      rfl

theorem cell23_562851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_562851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562851 prefixEnd_562851 := by exact prefixLift 562851
  have htrace : WordTrace (prefixWord ++ tailWord_562851) baseStart_562851 baseEnd_562851 := by
    simpa [prefixWord, tailWord_562851, baseEnd_562851] using wordTrace_append hprefix tailTrace_562851
  have hstable : (prefixWord ++ tailWord_562851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562851).length < 2 ^ (prefixWord ++ tailWord_562851).sum := by decide
  have hdescent : baseEnd_562851 < baseStart_562851 := by decide
  rcases family_descends (prefixWord ++ tailWord_562851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562909 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_562909 : Nat := 118140960795 + 562909 * 2 ^ 59
def prefixEnd_562909 : Nat := 4983230072969 + 3 ^ 40 * 562909 * 2
def baseEnd_562909 : Nat := 289042881741843349648735

theorem tailTrace_562909 : CollatzResearch.WordTrace tailWord_562909 prefixEnd_562909 289042881741843349648735 := by
  unfold tailWord_562909
  simp only [CollatzResearch.WordTrace]
  refine ⟨20530977917684305048435781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13687318611789536698957187 20530977917684305048435781)
  ·
    refine ⟨3849558359565807196581709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20530977917684305048435781 3849558359565807196581709)
    ·
      refine ⟨1443584384837177698718141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3849558359565807196581709 1443584384837177698718141)
      ·
        refine ⟨541344144313941637019303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1443584384837177698718141 541344144313941637019303)
        ·
          refine ⟨812016216470912455528955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541344144313941637019303 812016216470912455528955)
          ·
            refine ⟨1218024324706368683293433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812016216470912455528955 1218024324706368683293433)
            ·
              refine ⟨913518243529776512470075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218024324706368683293433 913518243529776512470075)
              ·
                refine ⟨1370277365294664768705113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913518243529776512470075 1370277365294664768705113)
                ·
                  refine ⟨1027708023970998576528835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370277365294664768705113 1027708023970998576528835)
                  ·
                    refine ⟨1541562035956497864793253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027708023970998576528835 1541562035956497864793253)
                    ·
                      refine ⟨289042881741843349648735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1541562035956497864793253 289042881741843349648735)
                      ·
                        rfl

theorem cell23_562909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_562909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562909 prefixEnd_562909 := by exact prefixLift 562909
  have htrace : WordTrace (prefixWord ++ tailWord_562909) baseStart_562909 baseEnd_562909 := by
    simpa [prefixWord, tailWord_562909, baseEnd_562909] using wordTrace_append hprefix tailTrace_562909
  have hstable : (prefixWord ++ tailWord_562909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562909).length < 2 ^ (prefixWord ++ tailWord_562909).sum := by decide
  have hdescent : baseEnd_562909 < baseStart_562909 := by decide
  rcases family_descends (prefixWord ++ tailWord_562909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562962 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_562962 : Nat := 118140960795 + 562962 * 2 ^ 59
def prefixEnd_562962 : Nat := 4983230072969 + 3 ^ 40 * 562962 * 2
def baseEnd_562962 : Nat := 96356698738843880761997

theorem tailTrace_562962 : CollatzResearch.WordTrace tailWord_562962 prefixEnd_562962 96356698738843880761997 := by
  unfold tailWord_562962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5133227746623073775028785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13688607324328196733410093 5133227746623073775028785)
  ·
    refine ⟨3849920809967305331271589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5133227746623073775028785 3849920809967305331271589)
    ·
      refine ⟨721860151868869749613423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3849920809967305331271589 721860151868869749613423)
      ·
        refine ⟨1082790227803304624420135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721860151868869749613423 1082790227803304624420135)
        ·
          refine ⟨1624185341704956936630203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082790227803304624420135 1624185341704956936630203)
          ·
            refine ⟨2436278012557435404945305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624185341704956936630203 2436278012557435404945305)
            ·
              refine ⟨1827208509418076553708979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436278012557435404945305 1827208509418076553708979)
              ·
                refine ⟨2740812764127114830563469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827208509418076553708979 2740812764127114830563469)
                ·
                  refine ⟨1027804786547668061461301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2740812764127114830563469 1027804786547668061461301)
                  ·
                    refine ⟨96356698738843880761997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1027804786547668061461301 96356698738843880761997)
                    ·
                      rfl

theorem cell23_562962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_562962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562962 prefixEnd_562962 := by exact prefixLift 562962
  have htrace : WordTrace (prefixWord ++ tailWord_562962) baseStart_562962 baseEnd_562962 := by
    simpa [prefixWord, tailWord_562962, baseEnd_562962] using wordTrace_append hprefix tailTrace_562962
  have hstable : (prefixWord ++ tailWord_562962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562962).length < 2 ^ (prefixWord ++ tailWord_562962).sum := by decide
  have hdescent : baseEnd_562962 < baseStart_562962 := by decide
  rcases family_descends (prefixWord ++ tailWord_562962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562965 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_562965 : Nat := 118140960795 + 562965 * 2 ^ 59
def prefixEnd_562965 : Nat := 4983230072969 + 3 ^ 40 * 562965 * 2
def baseEnd_562965 : Nat := 289071636658495130548477

theorem tailTrace_562965 : CollatzResearch.WordTrace tailWord_562965 prefixEnd_562965 289071636658495130548477 := by
  unfold tailWord_562965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533020405481426612474349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13688680270320951074982899 20533020405481426612474349)
  ·
    refine ⟨7699882652055534979677881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20533020405481426612474349 7699882652055534979677881)
    ·
      refine ⟨5774911989041651234758411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7699882652055534979677881 5774911989041651234758411)
      ·
        refine ⟨8662367983562476852137617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5774911989041651234758411 8662367983562476852137617)
        ·
          refine ⟨6496775987671857639103213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8662367983562476852137617 6496775987671857639103213)
          ·
            refine ⟨2436290995376946614663705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6496775987671857639103213 2436290995376946614663705)
            ·
              refine ⟨1827218246532709960997779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436290995376946614663705 1827218246532709960997779)
              ·
                refine ⟨2740827369799064941496669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827218246532709960997779 2740827369799064941496669)
                ·
                  refine ⟨1027810263674649353061251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2740827369799064941496669 1027810263674649353061251)
                  ·
                    refine ⟨1541715395511974029591877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027810263674649353061251 1541715395511974029591877)
                    ·
                      refine ⟨289071636658495130548477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1541715395511974029591877 289071636658495130548477)
                      ·
                        rfl

theorem cell23_562965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_562965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562965 prefixEnd_562965 := by exact prefixLift 562965
  have htrace : WordTrace (prefixWord ++ tailWord_562965) baseStart_562965 baseEnd_562965 := by
    simpa [prefixWord, tailWord_562965, baseEnd_562965] using wordTrace_append hprefix tailTrace_562965
  have hstable : (prefixWord ++ tailWord_562965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562965).length < 2 ^ (prefixWord ++ tailWord_562965).sum := by decide
  have hdescent : baseEnd_562965 < baseStart_562965 := by decide
  rcases family_descends (prefixWord ++ tailWord_562965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562975 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 4, 4]
def baseStart_562975 : Nat := 118140960795 + 562975 * 2 ^ 59
def prefixEnd_562975 : Nat := 4983230072969 + 3 ^ 40 * 562975 * 2
def baseEnd_562975 : Nat := 96358923821680030474477

theorem tailTrace_562975 : CollatzResearch.WordTrace tailWord_562975 prefixEnd_562975 96358923821680030474477 := by
  unfold tailWord_562975
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533385135445198320338379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13688923423630132213558919 20533385135445198320338379)
  ·
    refine ⟨30800077703167797480507569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20533385135445198320338379 30800077703167797480507569)
    ·
      refine ⟨23100058277375848110380677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30800077703167797480507569 23100058277375848110380677)
      ·
        refine ⟨4331260927007971520696377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23100058277375848110380677 4331260927007971520696377)
        ·
          refine ⟨3248445695255978640522283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4331260927007971520696377 3248445695255978640522283)
          ·
            refine ⟨4872668542883967960783425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248445695255978640522283 4872668542883967960783425)
            ·
              refine ⟨3654501407162975970587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4872668542883967960783425 3654501407162975970587569)
              ·
                refine ⟨2740876055372231977940677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654501407162975970587569 2740876055372231977940677)
                ·
                  refine ⟨513914260382293495863877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2740876055372231977940677 513914260382293495863877)
                  ·
                    refine ⟨96358923821680030474477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 513914260382293495863877 96358923821680030474477)
                    ·
                      rfl

theorem cell23_562975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_562975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562975 prefixEnd_562975 := by exact prefixLift 562975
  have htrace : WordTrace (prefixWord ++ tailWord_562975) baseStart_562975 baseEnd_562975 := by
    simpa [prefixWord, tailWord_562975, baseEnd_562975] using wordTrace_append hprefix tailTrace_562975
  have hstable : (prefixWord ++ tailWord_562975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562975).length < 2 ^ (prefixWord ++ tailWord_562975).sum := by decide
  have hdescent : baseEnd_562975 < baseStart_562975 := by decide
  rcases family_descends (prefixWord ++ tailWord_562975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562988 : List Nat := [2, 2, 1, 1, 1, 6, 10]
def baseStart_562988 : Nat := 118140960795 + 562988 * 2 ^ 59
def prefixEnd_562988 : Nat := 4983230072969 + 3 ^ 40 * 562988 * 2
def baseEnd_562988 : Nat := 3568931440908006673591

theorem tailTrace_562988 : CollatzResearch.WordTrace tailWord_562988 prefixEnd_562988 3568931440908006673591 := by
  unfold tailWord_562988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10266929642199050770280809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13689239522932067693707745 10266929642199050770280809)
  ·
    refine ⟨7700197231649288077710607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10266929642199050770280809 7700197231649288077710607)
    ·
      refine ⟨11550295847473932116565911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700197231649288077710607 11550295847473932116565911)
      ·
        refine ⟨17325443771210898174848867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11550295847473932116565911 17325443771210898174848867)
        ·
          refine ⟨25988165656816347262273301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17325443771210898174848867 25988165656816347262273301)
          ·
            refine ⟨1218195265163266277919061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25988165656816347262273301 1218195265163266277919061)
            ·
              refine ⟨3568931440908006673591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1218195265163266277919061 3568931440908006673591)
              ·
                rfl

theorem cell23_562988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 10].length) (baseStart_562988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_562988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_562988 prefixEnd_562988 := by exact prefixLift 562988
  have htrace : WordTrace (prefixWord ++ tailWord_562988) baseStart_562988 baseEnd_562988 := by
    simpa [prefixWord, tailWord_562988, baseEnd_562988] using wordTrace_append hprefix tailTrace_562988
  have hstable : (prefixWord ++ tailWord_562988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562988).length < 2 ^ (prefixWord ++ tailWord_562988).sum := by decide
  have hdescent : baseEnd_562988 < baseStart_562988 := by decide
  rcases family_descends (prefixWord ++ tailWord_562988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563050 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_563050 : Nat := 118140960795 + 563050 * 2 ^ 59
def prefixEnd_563050 : Nat := 4983230072969 + 3 ^ 40 * 563050 * 2
def baseEnd_563050 : Nat := 289115282514127297985587

theorem tailTrace_563050 : CollatzResearch.WordTrace tailWord_563050 prefixEnd_563050 289115282514127297985587 := by
  unfold tailWord_563050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134030152543371532329651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13690747073448990752879069 5134030152543371532329651)
  ·
    refine ⟨7701045228815057298494477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5134030152543371532329651 7701045228815057298494477)
    ·
      refine ⟨2887891960805646486935429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7701045228815057298494477 2887891960805646486935429)
      ·
        refine ⟨541479742651058716300393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2887891960805646486935429 541479742651058716300393)
        ·
          refine ⟨406109806988294037225295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541479742651058716300393 406109806988294037225295)
          ·
            refine ⟨609164710482441055837943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406109806988294037225295 609164710482441055837943)
            ·
              refine ⟨913747065723661583756915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609164710482441055837943 913747065723661583756915)
              ·
                refine ⟨1370620598585492375635373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913747065723661583756915 1370620598585492375635373)
                ·
                  refine ⟨513982724469559640863265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1370620598585492375635373 513982724469559640863265)
                  ·
                    refine ⟨385487043352169730647449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513982724469559640863265 385487043352169730647449)
                    ·
                      refine ⟨289115282514127297985587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385487043352169730647449 289115282514127297985587)
                      ·
                        rfl

theorem cell23_563050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_563050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563050 prefixEnd_563050 := by exact prefixLift 563050
  have htrace : WordTrace (prefixWord ++ tailWord_563050) baseStart_563050 baseEnd_563050 := by
    simpa [prefixWord, tailWord_563050, baseEnd_563050] using wordTrace_append hprefix tailTrace_563050
  have hstable : (prefixWord ++ tailWord_563050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563050).length < 2 ^ (prefixWord ++ tailWord_563050).sum := by decide
  have hdescent : baseEnd_563050 < baseStart_563050 := by decide
  rcases family_descends (prefixWord ++ tailWord_563050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563072 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2]
def baseStart_563072 : Nat := 118140960795 + 563072 * 2 ^ 59
def prefixEnd_563072 : Nat := 4983230072969 + 3 ^ 40 * 563072 * 2
def baseEnd_563072 : Nat := 289126579088526211910485

theorem tailTrace_563072 : CollatzResearch.WordTrace tailWord_563072 prefixEnd_563072 289126579088526211910485 := by
  unfold tailWord_563072
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268461508046891943309735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13691282010729189257746313 10268461508046891943309735)
  ·
    refine ⟨15402692262070337914964603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10268461508046891943309735 15402692262070337914964603)
    ·
      refine ⟨23104038393105506872446905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15402692262070337914964603 23104038393105506872446905)
      ·
        refine ⟨17328028794829130154335179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23104038393105506872446905 17328028794829130154335179)
        ·
          refine ⟨25992043192243695231502769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17328028794829130154335179 25992043192243695231502769)
          ·
            refine ⟨19494032394182771423627077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25992043192243695231502769 19494032394182771423627077)
            ·
              refine ⟨3655131073909269641930077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19494032394182771423627077 3655131073909269641930077)
              ·
                refine ⟨1370674152715976115723779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3655131073909269641930077 1370674152715976115723779)
                ·
                  refine ⟨2056011229073964173585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370674152715976115723779 2056011229073964173585669)
                  ·
                    refine ⟨385502105451368282547313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056011229073964173585669 385502105451368282547313)
                    ·
                      refine ⟨289126579088526211910485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385502105451368282547313 289126579088526211910485)
                      ·
                        rfl

theorem cell23_563072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_563072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563072 prefixEnd_563072 := by exact prefixLift 563072
  have htrace : WordTrace (prefixWord ++ tailWord_563072) baseStart_563072 baseEnd_563072 := by
    simpa [prefixWord, tailWord_563072, baseEnd_563072] using wordTrace_append hprefix tailTrace_563072
  have hstable : (prefixWord ++ tailWord_563072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563072).length < 2 ^ (prefixWord ++ tailWord_563072).sum := by decide
  have hdescent : baseEnd_563072 < baseStart_563072 := by decide
  rcases family_descends (prefixWord ++ tailWord_563072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563075 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_563075 : Nat := 118140960795 + 563075 * 2 ^ 59
def prefixEnd_563075 : Nat := 4983230072969 + 3 ^ 40 * 563075 * 2
def baseEnd_563075 : Nat := 289128119530489700172971

theorem tailTrace_563075 : CollatzResearch.WordTrace tailWord_563075 prefixEnd_563075 289128119530489700172971 := by
  unfold tailWord_563075
  simp only [CollatzResearch.WordTrace]
  refine ⟨20537032435082915398978679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13691354956721943599319119 20537032435082915398978679)
  ·
    refine ⟨30805548652624373098468019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20537032435082915398978679 30805548652624373098468019)
    ·
      refine ⟨46208322978936559647702029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30805548652624373098468019 46208322978936559647702029)
      ·
        refine ⟨17328121117101209867888261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46208322978936559647702029 17328121117101209867888261)
        ·
          refine ⟨3249022709456476850229049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17328121117101209867888261 3249022709456476850229049)
          ·
            refine ⟨2436767032092357637671787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249022709456476850229049 2436767032092357637671787)
            ·
              refine ⟨3655150548138536456507681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436767032092357637671787 3655150548138536456507681)
              ·
                refine ⟨2741362911103902342380761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655150548138536456507681 2741362911103902342380761)
                ·
                  refine ⟨2056022183327926756785571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741362911103902342380761 2056022183327926756785571)
                  ·
                    refine ⟨3084033274991890135178357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056022183327926756785571 3084033274991890135178357)
                    ·
                      refine ⟨289128119530489700172971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3084033274991890135178357 289128119530489700172971)
                      ·
                        rfl

theorem cell23_563075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_563075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563075 prefixEnd_563075 := by exact prefixLift 563075
  have htrace : WordTrace (prefixWord ++ tailWord_563075) baseStart_563075 baseEnd_563075 := by
    simpa [prefixWord, tailWord_563075, baseEnd_563075] using wordTrace_append hprefix tailTrace_563075
  have hstable : (prefixWord ++ tailWord_563075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563075).length < 2 ^ (prefixWord ++ tailWord_563075).sum := by decide
  have hdescent : baseEnd_563075 < baseStart_563075 := by decide
  rcases family_descends (prefixWord ++ tailWord_563075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563092 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_563092 : Nat := 118140960795 + 563092 * 2 ^ 59
def prefixEnd_563092 : Nat := 4983230072969 + 3 ^ 40 * 563092 * 2
def baseEnd_563092 : Nat := 289136848701616133660393

theorem tailTrace_563092 : CollatzResearch.WordTrace tailWord_563092 prefixEnd_563092 289136848701616133660393 := by
  unfold tailWord_563092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268826238010663651173765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13691768317347551534898353 10268826238010663651173765)
  ·
    refine ⟨1925404919626999434595081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10268826238010663651173765 1925404919626999434595081)
    ·
      refine ⟨1444053689720249575946311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1925404919626999434595081 1444053689720249575946311)
      ·
        refine ⟨2166080534580374363919467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444053689720249575946311 2166080534580374363919467)
        ·
          refine ⟨3249120801870561545879201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166080534580374363919467 3249120801870561545879201)
          ·
            refine ⟨2436840601402921159409401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249120801870561545879201 2436840601402921159409401)
            ·
              refine ⟨1827630451052190869557051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436840601402921159409401 1827630451052190869557051)
              ·
                refine ⟨2741445676578286304335577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827630451052190869557051 2741445676578286304335577)
                ·
                  refine ⟨2056084257433714728251683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741445676578286304335577 2056084257433714728251683)
                  ·
                    refine ⟨3084126386150572092377525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056084257433714728251683 3084126386150572092377525)
                    ·
                      refine ⟨289136848701616133660393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3084126386150572092377525 289136848701616133660393)
                      ·
                        rfl

theorem cell23_563092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_563092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563092 prefixEnd_563092 := by exact prefixLift 563092
  have htrace : WordTrace (prefixWord ++ tailWord_563092) baseStart_563092 baseEnd_563092 := by
    simpa [prefixWord, tailWord_563092, baseEnd_563092] using wordTrace_append hprefix tailTrace_563092
  have hstable : (prefixWord ++ tailWord_563092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563092).length < 2 ^ (prefixWord ++ tailWord_563092).sum := by decide
  have hdescent : baseEnd_563092 < baseStart_563092 := by decide
  rcases family_descends (prefixWord ++ tailWord_563092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563145 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_563145 : Nat := 118140960795 + 563145 * 2 ^ 59
def prefixEnd_563145 : Nat := 4983230072969 + 3 ^ 40 * 563145 * 2
def baseEnd_563145 : Nat := 289164063176304426297649

theorem tailTrace_563145 : CollatzResearch.WordTrace tailWord_563145 prefixEnd_563145 289164063176304426297649 := by
  unfold tailWord_563145
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539585544829317354026889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13693057029886211569351259 20539585544829317354026889)
  ·
    refine ⟨15404689158621988015520167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20539585544829317354026889 15404689158621988015520167)
    ·
      refine ⟨23107033737932982023280251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15404689158621988015520167 23107033737932982023280251)
      ·
        refine ⟨34660550606899473034920377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23107033737932982023280251 34660550606899473034920377)
        ·
          refine ⟨25995412955174604776190283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34660550606899473034920377 25995412955174604776190283)
          ·
            refine ⟨38993119432761907164285425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25995412955174604776190283 38993119432761907164285425)
            ·
              refine ⟨29244839574571430373214069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38993119432761907164285425 29244839574571430373214069)
              ·
                refine ⟨2741703710116071597488819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29244839574571430373214069 2741703710116071597488819)
                ·
                  refine ⟨4112555565174107396233229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741703710116071597488819 4112555565174107396233229)
                  ·
                    refine ⟨1542208336940290273587461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4112555565174107396233229 1542208336940290273587461)
                    ·
                      refine ⟨289164063176304426297649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1542208336940290273587461 289164063176304426297649)
                      ·
                        rfl

theorem cell23_563145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_563145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563145 prefixEnd_563145 := by exact prefixLift 563145
  have htrace : WordTrace (prefixWord ++ tailWord_563145) baseStart_563145 baseEnd_563145 := by
    simpa [prefixWord, tailWord_563145, baseEnd_563145] using wordTrace_append hprefix tailTrace_563145
  have hstable : (prefixWord ++ tailWord_563145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563145).length < 2 ^ (prefixWord ++ tailWord_563145).sum := by decide
  have hdescent : baseEnd_563145 < baseStart_563145 := by decide
  rcases family_descends (prefixWord ++ tailWord_563145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563223 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 3, 4]
def baseStart_563223 : Nat := 118140960795 + 563223 * 2 ^ 59
def prefixEnd_563223 : Nat := 4983230072969 + 3 ^ 40 * 563223 * 2
def baseEnd_563223 : Nat := 96401371555785040374097

theorem tailTrace_563223 : CollatzResearch.WordTrace tailWord_563223 prefixEnd_563223 96401371555785040374097 := by
  unfold tailWord_563223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542430438546736675366323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13694953625697824450244215 20542430438546736675366323)
  ·
    refine ⟨30813645657820105013049485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20542430438546736675366323 30813645657820105013049485)
    ·
      refine ⟨11555117121682539379893557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30813645657820105013049485 11555117121682539379893557)
      ·
        refine ⟨1083292230157738066865021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11555117121682539379893557 1083292230157738066865021)
        ·
          refine ⟨406234586309151775074383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1083292230157738066865021 406234586309151775074383)
          ·
            refine ⟨609351879463727662611575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406234586309151775074383 609351879463727662611575)
            ·
              refine ⟨914027819195591493917363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609351879463727662611575 914027819195591493917363)
              ·
                refine ⟨1371041728793387240876045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914027819195591493917363 1371041728793387240876045)
                ·
                  refine ⟨514140648297520215328517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1371041728793387240876045 514140648297520215328517)
                  ·
                    refine ⟨96401371555785040374097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514140648297520215328517 96401371555785040374097)
                    ·
                      rfl

theorem cell23_563223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_563223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563223 prefixEnd_563223 := by exact prefixLift 563223
  have htrace : WordTrace (prefixWord ++ tailWord_563223) baseStart_563223 baseEnd_563223 := by
    simpa [prefixWord, tailWord_563223, baseEnd_563223] using wordTrace_append hprefix tailTrace_563223
  have hstable : (prefixWord ++ tailWord_563223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563223).length < 2 ^ (prefixWord ++ tailWord_563223).sum := by decide
  have hdescent : baseEnd_563223 < baseStart_563223 := by decide
  rcases family_descends (prefixWord ++ tailWord_563223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563225 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_563225 : Nat := 118140960795 + 563225 * 2 ^ 59
def prefixEnd_563225 : Nat := 4983230072969 + 3 ^ 40 * 563225 * 2
def baseEnd_563225 : Nat := 289205141628664113297281

theorem tailTrace_563225 : CollatzResearch.WordTrace tailWord_563225 prefixEnd_563225 289205141628664113297281 := by
  unfold tailWord_563225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542503384539491016939129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13695002256359660677959419 20542503384539491016939129)
  ·
    refine ⟨15406877538404618262704347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20542503384539491016939129 15406877538404618262704347)
    ·
      refine ⟨23110316307606927394056521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15406877538404618262704347 23110316307606927394056521)
      ·
        refine ⟨17332737230705195545542391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23110316307606927394056521 17332737230705195545542391)
        ·
          refine ⟨25999105846057793318313587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17332737230705195545542391 25999105846057793318313587)
          ·
            refine ⟨38998658769086689977470381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25999105846057793318313587 38998658769086689977470381)
            ·
              refine ⟨14624497038407508741551393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38998658769086689977470381 14624497038407508741551393)
              ·
                refine ⟨10968372778805631556163545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14624497038407508741551393 10968372778805631556163545)
                ·
                  refine ⟨8226279584104223667122659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10968372778805631556163545 8226279584104223667122659)
                  ·
                    refine ⟨12339419376156335500683989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8226279584104223667122659 12339419376156335500683989)
                    ·
                      refine ⟨289205141628664113297281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12339419376156335500683989 289205141628664113297281)
                      ·
                        rfl

theorem cell23_563225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_563225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563225 prefixEnd_563225 := by exact prefixLift 563225
  have htrace : WordTrace (prefixWord ++ tailWord_563225) baseStart_563225 baseEnd_563225 := by
    simpa [prefixWord, tailWord_563225, baseEnd_563225] using wordTrace_append hprefix tailTrace_563225
  have hstable : (prefixWord ++ tailWord_563225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563225).length < 2 ^ (prefixWord ++ tailWord_563225).sum := by decide
  have hdescent : baseEnd_563225 < baseStart_563225 := by decide
  rcases family_descends (prefixWord ++ tailWord_563225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563249 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_563249 : Nat := 118140960795 + 563249 * 2 ^ 59
def prefixEnd_563249 : Nat := 4983230072969 + 3 ^ 40 * 563249 * 2
def baseEnd_563249 : Nat := 96405821721457339799057

theorem tailTrace_563249 : CollatzResearch.WordTrace tailWord_563249 prefixEnd_563249 96405821721457339799057 := by
  unfold tailWord_563249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20543378736452543115812801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13695585824301695410541867 20543378736452543115812801)
  ·
    refine ⟨15407534052339407336859601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20543378736452543115812801 15407534052339407336859601)
    ·
      refine ⟨11555650539254555502644701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15407534052339407336859601 11555650539254555502644701)
      ·
        refine ⟨4333368952220458313491763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11555650539254555502644701 4333368952220458313491763)
        ·
          refine ⟨6500053428330687470237645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333368952220458313491763 6500053428330687470237645)
          ·
            refine ⟨2437520035624007801339117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500053428330687470237645 2437520035624007801339117)
            ·
              refine ⟨914070013359002925502169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437520035624007801339117 914070013359002925502169)
              ·
                refine ⟨685552510019252194126627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914070013359002925502169 685552510019252194126627)
                ·
                  refine ⟨1028328765028878291189941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685552510019252194126627 1028328765028878291189941)
                  ·
                    refine ⟨96405821721457339799057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1028328765028878291189941 96405821721457339799057)
                    ·
                      rfl

theorem cell23_563249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_563249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563249 prefixEnd_563249 := by exact prefixLift 563249
  have htrace : WordTrace (prefixWord ++ tailWord_563249) baseStart_563249 baseEnd_563249 := by
    simpa [prefixWord, tailWord_563249, baseEnd_563249] using wordTrace_append hprefix tailTrace_563249
  have hstable : (prefixWord ++ tailWord_563249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563249).length < 2 ^ (prefixWord ++ tailWord_563249).sum := by decide
  have hdescent : baseEnd_563249 < baseStart_563249 := by decide
  rcases family_descends (prefixWord ++ tailWord_563249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563272 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_563272 : Nat := 118140960795 + 563272 * 2 ^ 59
def prefixEnd_563272 : Nat := 4983230072969 + 3 ^ 40 * 563272 * 2
def baseEnd_563272 : Nat := 289229275219425429409565

theorem tailTrace_563272 : CollatzResearch.WordTrace tailWord_563272 prefixEnd_563272 289229275219425429409565 := by
  unfold tailWord_563272
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272108807684609021950035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13696145076912812029266713 10272108807684609021950035)
  ·
    refine ⟨15408163211526913532925053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10272108807684609021950035 15408163211526913532925053)
    ·
      refine ⟨5778061204322592574846895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15408163211526913532925053 5778061204322592574846895)
      ·
        refine ⟨8667091806483888862270343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778061204322592574846895 8667091806483888862270343)
        ·
          refine ⟨13000637709725833293405515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667091806483888862270343 13000637709725833293405515)
          ·
            refine ⟨19500956564588749940108273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13000637709725833293405515 19500956564588749940108273)
            ·
              refine ⟨14625717423441562455081205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19500956564588749940108273 14625717423441562455081205)
              ·
                refine ⟨1371161008447646480163863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14625717423441562455081205 1371161008447646480163863)
                ·
                  refine ⟨2056741512671469720245795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371161008447646480163863 2056741512671469720245795)
                  ·
                    refine ⟨3085112269007204580368693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056741512671469720245795 3085112269007204580368693)
                    ·
                      refine ⟨289229275219425429409565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3085112269007204580368693 289229275219425429409565)
                      ·
                        rfl

theorem cell23_563272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_563272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563272 prefixEnd_563272 := by exact prefixLift 563272
  have htrace : WordTrace (prefixWord ++ tailWord_563272) baseStart_563272 baseEnd_563272 := by
    simpa [prefixWord, tailWord_563272, baseEnd_563272] using wordTrace_append hprefix tailTrace_563272
  have hstable : (prefixWord ++ tailWord_563272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563272).length < 2 ^ (prefixWord ++ tailWord_563272).sum := by decide
  have hdescent : baseEnd_563272 < baseStart_563272 := by decide
  rcases family_descends (prefixWord ++ tailWord_563272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563309 : List Nat := [1, 5, 1, 1, 2, 1, 5, 7]
def baseStart_563309 : Nat := 118140960795 + 563309 * 2 ^ 59
def prefixEnd_563309 : Nat := 4983230072969 + 3 ^ 40 * 563309 * 2
def baseEnd_563309 : Nat := 10712899037171917949885

theorem tailTrace_563309 : CollatzResearch.WordTrace tailWord_563309 prefixEnd_563309 10712899037171917949885 := by
  unfold tailWord_563309
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545567116235173362996981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697044744156782241997987 20545567116235173362996981)
  ·
    refine ⟨1926146917147047502780967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20545567116235173362996981 1926146917147047502780967)
    ·
      refine ⟨2889220375720571254171451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926146917147047502780967 2889220375720571254171451)
      ·
        refine ⟨4333830563580856881257177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889220375720571254171451 4333830563580856881257177)
        ·
          refine ⟨3250372922685642660942883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333830563580856881257177 3250372922685642660942883)
          ·
            refine ⟨4875559384028463991414325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250372922685642660942883 4875559384028463991414325)
            ·
              refine ⟨457083692252668499195093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4875559384028463991414325 457083692252668499195093)
              ·
                refine ⟨10712899037171917949885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 457083692252668499195093 10712899037171917949885)
                ·
                  rfl

theorem cell23_563309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 7].length) (baseStart_563309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563309 prefixEnd_563309 := by exact prefixLift 563309
  have htrace : WordTrace (prefixWord ++ tailWord_563309) baseStart_563309 baseEnd_563309 := by
    simpa [prefixWord, tailWord_563309, baseEnd_563309] using wordTrace_append hprefix tailTrace_563309
  have hstable : (prefixWord ++ tailWord_563309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563309).length < 2 ^ (prefixWord ++ tailWord_563309).sum := by decide
  have hdescent : baseEnd_563309 < baseStart_563309 := by decide
  rcases family_descends (prefixWord ++ tailWord_563309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563319 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_563319 : Nat := 118140960795 + 563319 * 2 ^ 59
def prefixEnd_563319 : Nat := 4983230072969 + 3 ^ 40 * 563319 * 2
def baseEnd_563319 : Nat := 289253408810186745521849

theorem tailTrace_563319 : CollatzResearch.WordTrace tailWord_563319 prefixEnd_563319 289253408810186745521849 := by
  unfold tailWord_563319
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545931846198945070861011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697287897465963380574007 20545931846198945070861011)
  ·
    refine ⟨30818897769298417606291517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20545931846198945070861011 30818897769298417606291517)
    ·
      refine ⟨11557086663486906602359319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30818897769298417606291517 11557086663486906602359319)
      ·
        refine ⟨17335629995230359903538979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11557086663486906602359319 17335629995230359903538979)
        ·
          refine ⟨26003444992845539855308469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17335629995230359903538979 26003444992845539855308469)
          ·
            refine ⟨2437822968079269361435169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26003444992845539855308469 2437822968079269361435169)
            ·
              refine ⟨1828367226059452021076377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437822968079269361435169 1828367226059452021076377)
              ·
                refine ⟨1371275419544589015807283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828367226059452021076377 1371275419544589015807283)
                ·
                  refine ⟨2056913129316883523710925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371275419544589015807283 2056913129316883523710925)
                  ·
                    refine ⟨771342423493831321391597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056913129316883523710925 771342423493831321391597)
                    ·
                      refine ⟨289253408810186745521849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 771342423493831321391597 289253408810186745521849)
                      ·
                        rfl

theorem cell23_563319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_563319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563319 prefixEnd_563319 := by exact prefixLift 563319
  have htrace : WordTrace (prefixWord ++ tailWord_563319) baseStart_563319 baseEnd_563319 := by
    simpa [prefixWord, tailWord_563319, baseEnd_563319] using wordTrace_append hprefix tailTrace_563319
  have hstable : (prefixWord ++ tailWord_563319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563319).length < 2 ^ (prefixWord ++ tailWord_563319).sum := by decide
  have hdescent : baseEnd_563319 < baseStart_563319 := by decide
  rcases family_descends (prefixWord ++ tailWord_563319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563404 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_563404 : Nat := 118140960795 + 563404 * 2 ^ 59
def prefixEnd_563404 : Nat := 4983230072969 + 3 ^ 40 * 563404 * 2
def baseEnd_563404 : Nat := 289297054665818912958959

theorem tailTrace_563404 : CollatzResearch.WordTrace tailWord_563404 prefixEnd_563404 289297054665818912958959 := by
  unfold tailWord_563404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10274516025445502293852633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13699354700594003058470177 10274516025445502293852633)
  ·
    refine ⟨7705887019084126720389475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10274516025445502293852633 7705887019084126720389475)
    ·
      refine ⟨11558830528626190080584213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7705887019084126720389475 11558830528626190080584213)
      ·
        refine ⟨541820181029352660027385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11558830528626190080584213 541820181029352660027385)
        ·
          refine ⟨406365135772014495020539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541820181029352660027385 406365135772014495020539)
          ·
            refine ⟨609547703658021742530809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406365135772014495020539 609547703658021742530809)
            ·
              refine ⟨457160777743516306898107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609547703658021742530809 457160777743516306898107)
              ·
                refine ⟨685741166615274460347161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457160777743516306898107 685741166615274460347161)
                ·
                  refine ⟨514305874961455845260371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685741166615274460347161 514305874961455845260371)
                  ·
                    refine ⟨771458812442183767890557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514305874961455845260371 771458812442183767890557)
                    ·
                      refine ⟨289297054665818912958959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 771458812442183767890557 289297054665818912958959)
                      ·
                        rfl

theorem cell23_563404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_563404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563404 prefixEnd_563404 := by exact prefixLift 563404
  have htrace : WordTrace (prefixWord ++ tailWord_563404) baseStart_563404 baseEnd_563404 := by
    simpa [prefixWord, tailWord_563404, baseEnd_563404] using wordTrace_append hprefix tailTrace_563404
  have hstable : (prefixWord ++ tailWord_563404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563404).length < 2 ^ (prefixWord ++ tailWord_563404).sum := by decide
  have hdescent : baseEnd_563404 < baseStart_563404 := by decide
  rcases family_descends (prefixWord ++ tailWord_563404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563409 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_563409 : Nat := 118140960795 + 563409 * 2 ^ 59
def prefixEnd_563409 : Nat := 4983230072969 + 3 ^ 40 * 563409 * 2
def baseEnd_563409 : Nat := 289299622069091393396435

theorem tailTrace_563409 : CollatzResearch.WordTrace tailWord_563409 prefixEnd_563409 289299622069091393396435 := by
  unfold tailWord_563409
  simp only [CollatzResearch.WordTrace]
  refine ⟨20549214415872890441637281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13699476277248593627758187 20549214415872890441637281)
  ·
    refine ⟨15411910811904667831227961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20549214415872890441637281 15411910811904667831227961)
    ·
      refine ⟨11558933108928500873420971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15411910811904667831227961 11558933108928500873420971)
      ·
        refine ⟨17338399663392751310131457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11558933108928500873420971 17338399663392751310131457)
        ·
          refine ⟨13003799747544563482598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17338399663392751310131457 13003799747544563482598593)
          ·
            refine ⟨9752849810658422611948945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13003799747544563482598593 9752849810658422611948945)
            ·
              refine ⟨7314637357993816958961709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9752849810658422611948945 7314637357993816958961709)
              ·
                refine ⟨2742989009247681359610641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314637357993816958961709 2742989009247681359610641)
                ·
                  refine ⟨2057241756935761019707981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742989009247681359610641 2057241756935761019707981)
                  ·
                    refine ⟨771465658850910382390493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057241756935761019707981 771465658850910382390493)
                    ·
                      refine ⟨289299622069091393396435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 771465658850910382390493 289299622069091393396435)
                      ·
                        rfl

theorem cell23_563409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_563409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563409 prefixEnd_563409 := by exact prefixLift 563409
  have htrace : WordTrace (prefixWord ++ tailWord_563409) baseStart_563409 baseEnd_563409 := by
    simpa [prefixWord, tailWord_563409, baseEnd_563409] using wordTrace_append hprefix tailTrace_563409
  have hstable : (prefixWord ++ tailWord_563409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563409).length < 2 ^ (prefixWord ++ tailWord_563409).sum := by decide
  have hdescent : baseEnd_563409 < baseStart_563409 := by decide
  rcases family_descends (prefixWord ++ tailWord_563409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563410 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_563410 : Nat := 118140960795 + 563410 * 2 ^ 59
def prefixEnd_563410 : Nat := 4983230072969 + 3 ^ 40 * 563410 * 2
def baseEnd_563410 : Nat := 289300135549745889483931

theorem tailTrace_563410 : CollatzResearch.WordTrace tailWord_563410 prefixEnd_563410 289300135549745889483931 := by
  unfold tailWord_563410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137312722217316903105921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13699500592579511741615789 5137312722217316903105921)
  ·
    refine ⟨3852984541662987677329441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5137312722217316903105921 3852984541662987677329441)
    ·
      refine ⟨2889738406247240757997081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3852984541662987677329441 2889738406247240757997081)
      ·
        refine ⟨2167303804685430568497811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889738406247240757997081 2167303804685430568497811)
        ·
          refine ⟨3250955707028145852746717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167303804685430568497811 3250955707028145852746717)
          ·
            refine ⟨1219108390135554694780019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3250955707028145852746717 1219108390135554694780019)
            ·
              refine ⟨1828662585203332042170029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219108390135554694780019 1828662585203332042170029)
              ·
                refine ⟨685748469451249515813761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1828662585203332042170029 685748469451249515813761)
                ·
                  refine ⟨514311352088437136860321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685748469451249515813761 514311352088437136860321)
                  ·
                    refine ⟨385733514066327852645241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514311352088437136860321 385733514066327852645241)
                    ·
                      refine ⟨289300135549745889483931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385733514066327852645241 289300135549745889483931)
                      ·
                        rfl

theorem cell23_563410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_563410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563410 prefixEnd_563410 := by exact prefixLift 563410
  have htrace : WordTrace (prefixWord ++ tailWord_563410) baseStart_563410 baseEnd_563410 := by
    simpa [prefixWord, tailWord_563410, baseEnd_563410] using wordTrace_append hprefix tailTrace_563410
  have hstable : (prefixWord ++ tailWord_563410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563410).length < 2 ^ (prefixWord ++ tailWord_563410).sum := by decide
  have hdescent : baseEnd_563410 < baseStart_563410 := by decide
  rcases family_descends (prefixWord ++ tailWord_563410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563439 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_563439 : Nat := 118140960795 + 563439 * 2 ^ 59
def prefixEnd_563439 : Nat := 4983230072969 + 3 ^ 40 * 563439 * 2
def baseEnd_563439 : Nat := 289315026488726276021297

theorem tailTrace_563439 : CollatzResearch.WordTrace tailWord_563439 prefixEnd_563439 289315026488726276021297 := by
  unfold tailWord_563439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20550308605764205565229371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13700205737176137043486247 20550308605764205565229371)
  ·
    refine ⟨30825462908646308347844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20550308605764205565229371 30825462908646308347844057)
    ·
      refine ⟨23119097181484731260883043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30825462908646308347844057 23119097181484731260883043)
      ·
        refine ⟨34678645772227096891324565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23119097181484731260883043 34678645772227096891324565)
        ·
          refine ⟨1625561520573145166780839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34678645772227096891324565 1625561520573145166780839)
          ·
            refine ⟨2438342280859717750171259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625561520573145166780839 2438342280859717750171259)
            ·
              refine ⟨3657513421289576625256889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438342280859717750171259 3657513421289576625256889)
              ·
                refine ⟨2743135065967182468942667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657513421289576625256889 2743135065967182468942667)
                ·
                  refine ⟨4114702598950773703414001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743135065967182468942667 4114702598950773703414001)
                  ·
                    refine ⟨3086026949213080277560501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4114702598950773703414001 3086026949213080277560501)
                    ·
                      refine ⟨289315026488726276021297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3086026949213080277560501 289315026488726276021297)
                      ·
                        rfl

theorem cell23_563439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_563439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563439 prefixEnd_563439 := by exact prefixLift 563439
  have htrace : WordTrace (prefixWord ++ tailWord_563439) baseStart_563439 baseEnd_563439 := by
    simpa [prefixWord, tailWord_563439, baseEnd_563439] using wordTrace_append hprefix tailTrace_563439
  have hstable : (prefixWord ++ tailWord_563439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563439).length < 2 ^ (prefixWord ++ tailWord_563439).sum := by decide
  have hdescent : baseEnd_563439 < baseStart_563439 := by decide
  rcases family_descends (prefixWord ++ tailWord_563439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563446 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_563446 : Nat := 118140960795 + 563446 * 2 ^ 59
def prefixEnd_563446 : Nat := 4983230072969 + 3 ^ 40 * 563446 * 2
def baseEnd_563446 : Nat := 96439540284435916211255

theorem tailTrace_563446 : CollatzResearch.WordTrace tailWord_563446 prefixEnd_563446 96439540284435916211255 := by
  unfold tailWord_563446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284410244796177860045887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13700375944492563840489461 1284410244796177860045887)
  ·
    refine ⟨1926615367194266790068831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1284410244796177860045887 1926615367194266790068831)
    ·
      refine ⟨2889923050791400185103247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926615367194266790068831 2889923050791400185103247)
      ·
        refine ⟨4334884576187100277654871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889923050791400185103247 4334884576187100277654871)
        ·
          refine ⟨6502326864280650416482307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334884576187100277654871 6502326864280650416482307)
          ·
            refine ⟨9753490296420975624723461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502326864280650416482307 9753490296420975624723461)
            ·
              refine ⟨1828779430578932929635649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9753490296420975624723461 1828779430578932929635649)
              ·
                refine ⟨1371584572934199697226737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828779430578932929635649 1371584572934199697226737)
                ·
                  refine ⟨1028688429700649772920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371584572934199697226737 1028688429700649772920053)
                  ·
                    refine ⟨96439540284435916211255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1028688429700649772920053 96439540284435916211255)
                    ·
                      rfl

theorem cell23_563446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_563446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563446 prefixEnd_563446 := by exact prefixLift 563446
  have htrace : WordTrace (prefixWord ++ tailWord_563446) baseStart_563446 baseEnd_563446 := by
    simpa [prefixWord, tailWord_563446, baseEnd_563446] using wordTrace_append hprefix tailTrace_563446
  have hstable : (prefixWord ++ tailWord_563446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563446).length < 2 ^ (prefixWord ++ tailWord_563446).sum := by decide
  have hdescent : baseEnd_563446 < baseStart_563446 := by decide
  rcases family_descends (prefixWord ++ tailWord_563446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563449 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_563449 : Nat := 118140960795 + 563449 * 2 ^ 59
def prefixEnd_563449 : Nat := 4983230072969 + 3 ^ 40 * 563449 * 2
def baseEnd_563449 : Nat := 289320161295271236896251

theorem tailTrace_563449 : CollatzResearch.WordTrace tailWord_563449 prefixEnd_563449 289320161295271236896251 := by
  unfold tailWord_563449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20550673335727977273093401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13700448890485318182062267 20550673335727977273093401)
  ·
    refine ⟨15413005001795982954820051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20550673335727977273093401 15413005001795982954820051)
    ·
      refine ⟨23119507502693974432230077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15413005001795982954820051 23119507502693974432230077)
      ·
        refine ⟨8669815313510240412086279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23119507502693974432230077 8669815313510240412086279)
        ·
          refine ⟨13004722970265360618129419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669815313510240412086279 13004722970265360618129419)
          ·
            refine ⟨19507084455398040927194129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13004722970265360618129419 19507084455398040927194129)
            ·
              refine ⟨14630313341548530695395597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19507084455398040927194129 14630313341548530695395597)
              ·
                refine ⟨5486367503080699010773349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14630313341548530695395597 5486367503080699010773349)
                ·
                  refine ⟨1028693906827631064520003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5486367503080699010773349 1028693906827631064520003)
                  ·
                    refine ⟨1543040860241446596780005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028693906827631064520003 1543040860241446596780005)
                    ·
                      refine ⟨289320161295271236896251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1543040860241446596780005 289320161295271236896251)
                      ·
                        rfl

theorem cell23_563449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_563449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563449 prefixEnd_563449 := by exact prefixLift 563449
  have htrace : WordTrace (prefixWord ++ tailWord_563449) baseStart_563449 baseEnd_563449 := by
    simpa [prefixWord, tailWord_563449, baseEnd_563449] using wordTrace_append hprefix tailTrace_563449
  have hstable : (prefixWord ++ tailWord_563449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563449).length < 2 ^ (prefixWord ++ tailWord_563449).sum := by decide
  have hdescent : baseEnd_563449 < baseStart_563449 := by decide
  rcases family_descends (prefixWord ++ tailWord_563449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563466 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_563466 : Nat := 118140960795 + 563466 * 2 ^ 59
def prefixEnd_563466 : Nat := 4983230072969 + 3 ^ 40 * 563466 * 2
def baseEnd_563466 : Nat := 289328890466397670383673

theorem tailTrace_563466 : CollatzResearch.WordTrace tailWord_563466 prefixEnd_563466 289328890466397670383673 := by
  unfold tailWord_563466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137823344166597294115563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13700862251110926117641501 5137823344166597294115563)
  ·
    refine ⟨7706735016249895941173345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137823344166597294115563 7706735016249895941173345)
    ·
      refine ⟨5780051262187421955880009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706735016249895941173345 5780051262187421955880009)
      ·
        refine ⟨4335038446640566466910007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5780051262187421955880009 4335038446640566466910007)
        ·
          refine ⟨6502557669960849700365011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335038446640566466910007 6502557669960849700365011)
          ·
            refine ⟨9753836504941274550547517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502557669960849700365011 9753836504941274550547517)
            ·
              refine ⟨3657688689352977956455319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9753836504941274550547517 3657688689352977956455319)
              ·
                refine ⟨5486533034029466934682979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657688689352977956455319 5486533034029466934682979)
                ·
                  refine ⟨8229799551044200402024469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486533034029466934682979 8229799551044200402024469)
                  ·
                    refine ⟨385771853955196893844897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8229799551044200402024469 385771853955196893844897)
                    ·
                      refine ⟨289328890466397670383673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385771853955196893844897 289328890466397670383673)
                      ·
                        rfl

theorem cell23_563466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_563466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563466 prefixEnd_563466 := by exact prefixLift 563466
  have htrace : WordTrace (prefixWord ++ tailWord_563466) baseStart_563466 baseEnd_563466 := by
    simpa [prefixWord, tailWord_563466, baseEnd_563466] using wordTrace_append hprefix tailTrace_563466
  have hstable : (prefixWord ++ tailWord_563466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563466).length < 2 ^ (prefixWord ++ tailWord_563466).sum := by decide
  have hdescent : baseEnd_563466 < baseStart_563466 := by decide
  rcases family_descends (prefixWord ++ tailWord_563466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563506 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_563506 : Nat := 118140960795 + 563506 * 2 ^ 59
def prefixEnd_563506 : Nat := 4983230072969 + 3 ^ 40 * 563506 * 2
def baseEnd_563506 : Nat := 32149936632508612653721

theorem tailTrace_563506 : CollatzResearch.WordTrace tailWord_563506 prefixEnd_563506 32149936632508612653721 := by
  unfold tailWord_563506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138188074130369001979593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13701834864347650671945581 5138188074130369001979593)
  ·
    refine ⟨3853641055597776751484695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5138188074130369001979593 3853641055597776751484695)
    ·
      refine ⟨5780461583396665127227043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853641055597776751484695 5780461583396665127227043)
      ·
        refine ⟨8670692375094997690840565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780461583396665127227043 8670692375094997690840565)
        ·
          refine ⟨812877410165156033516303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8670692375094997690840565 812877410165156033516303)
          ·
            refine ⟨1219316115247734050274455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812877410165156033516303 1219316115247734050274455)
            ·
              refine ⟨1828974172871601075411683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219316115247734050274455 1828974172871601075411683)
              ·
                refine ⟨2743461259307401613117525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828974172871601075411683 2743461259307401613117525)
                ·
                  refine ⟨32149936632508612653721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2743461259307401613117525 32149936632508612653721)
                  ·
                    rfl

theorem cell23_563506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_563506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563506 prefixEnd_563506 := by exact prefixLift 563506
  have htrace : WordTrace (prefixWord ++ tailWord_563506) baseStart_563506 baseEnd_563506 := by
    simpa [prefixWord, tailWord_563506, baseEnd_563506] using wordTrace_append hprefix tailTrace_563506
  have hstable : (prefixWord ++ tailWord_563506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563506).length < 2 ^ (prefixWord ++ tailWord_563506).sum := by decide
  have hdescent : baseEnd_563506 < baseStart_563506 := by decide
  rcases family_descends (prefixWord ++ tailWord_563506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563509 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_563509 : Nat := 118140960795 + 563509 * 2 ^ 59
def prefixEnd_563509 : Nat := 4983230072969 + 3 ^ 40 * 563509 * 2
def baseEnd_563509 : Nat := 289350970134541002145975

theorem tailTrace_563509 : CollatzResearch.WordTrace tailWord_563509 prefixEnd_563509 289350970134541002145975 := by
  unfold tailWord_563509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552861715510607520277581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13701907810340405013518387 20552861715510607520277581)
  ·
    refine ⟨7707323143316477820104093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20552861715510607520277581 7707323143316477820104093)
    ·
      refine ⟨2890246178743679182539035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7707323143316477820104093 2890246178743679182539035)
      ·
        refine ⟨4335369268115518773808553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890246178743679182539035 4335369268115518773808553)
        ·
          refine ⟨3251526951086639080356415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4335369268115518773808553 3251526951086639080356415)
          ·
            refine ⟨4877290426629958620534623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251526951086639080356415 4877290426629958620534623)
            ·
              refine ⟨7315935639944937930801935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877290426629958620534623 7315935639944937930801935)
              ·
                refine ⟨10973903459917406896202903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315935639944937930801935 10973903459917406896202903)
                ·
                  refine ⟨16460855189876110344304355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10973903459917406896202903 16460855189876110344304355)
                  ·
                    refine ⟨24691282784814165516456533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16460855189876110344304355 24691282784814165516456533)
                    ·
                      refine ⟨289350970134541002145975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24691282784814165516456533 289350970134541002145975)
                      ·
                        rfl

theorem cell23_563509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_563509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563509 prefixEnd_563509 := by exact prefixLift 563509
  have htrace : WordTrace (prefixWord ++ tailWord_563509) baseStart_563509 baseEnd_563509 := by
    simpa [prefixWord, tailWord_563509, baseEnd_563509] using wordTrace_append hprefix tailTrace_563509
  have hstable : (prefixWord ++ tailWord_563509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563509).length < 2 ^ (prefixWord ++ tailWord_563509).sum := by decide
  have hdescent : baseEnd_563509 < baseStart_563509 := by decide
  rcases family_descends (prefixWord ++ tailWord_563509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563536 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_563536 : Nat := 118140960795 + 563536 * 2 ^ 59
def prefixEnd_563536 : Nat := 4983230072969 + 3 ^ 40 * 563536 * 2
def baseEnd_563536 : Nat := 96454944704070798836117

theorem tailTrace_563536 : CollatzResearch.WordTrace tailWord_563536 prefixEnd_563536 96454944704070798836117 := by
  unfold tailWord_563536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276923243206395565755231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13702564324275194087673641 10276923243206395565755231)
  ·
    refine ⟨15415384864809593348632847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10276923243206395565755231 15415384864809593348632847)
    ·
      refine ⟨23123077297214390022949271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15415384864809593348632847 23123077297214390022949271)
      ·
        refine ⟨34684615945821585034423907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23123077297214390022949271 34684615945821585034423907)
        ·
          refine ⟨52026923918732377551635861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34684615945821585034423907 52026923918732377551635861)
          ·
            refine ⟨2438762058690580197732931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52026923918732377551635861 2438762058690580197732931)
            ·
              refine ⟨3658143088035870296599397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438762058690580197732931 3658143088035870296599397)
              ·
                refine ⟨685901829006725680612387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3658143088035870296599397 685901829006725680612387)
                ·
                  refine ⟨1028852743510088520918581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685901829006725680612387 1028852743510088520918581)
                  ·
                    refine ⟨96454944704070798836117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1028852743510088520918581 96454944704070798836117)
                    ·
                      rfl

theorem cell23_563536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_563536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563536 prefixEnd_563536 := by exact prefixLift 563536
  have htrace : WordTrace (prefixWord ++ tailWord_563536) baseStart_563536 baseEnd_563536 := by
    simpa [prefixWord, tailWord_563536, baseEnd_563536] using wordTrace_append hprefix tailTrace_563536
  have hstable : (prefixWord ++ tailWord_563536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563536).length < 2 ^ (prefixWord ++ tailWord_563536).sum := by decide
  have hdescent : baseEnd_563536 < baseStart_563536 := by decide
  rcases family_descends (prefixWord ++ tailWord_563536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563543 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_563543 : Nat := 118140960795 + 563543 * 2 ^ 59
def prefixEnd_563543 : Nat := 4983230072969 + 3 ^ 40 * 563543 * 2
def baseEnd_563543 : Nat := 289368428476793869120819

theorem tailTrace_563543 : CollatzResearch.WordTrace tailWord_563543 prefixEnd_563543 289368428476793869120819 := by
  unfold tailWord_563543
  simp only [CollatzResearch.WordTrace]
  refine ⟨20554101797387431327015283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13702734531591620884676855 20554101797387431327015283)
  ·
    refine ⟨30831152696081146990522925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20554101797387431327015283 30831152696081146990522925)
    ·
      refine ⟨11561682261030430121446097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30831152696081146990522925 11561682261030430121446097)
      ·
        refine ⟨8671261695772822591084573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11561682261030430121446097 8671261695772822591084573)
        ·
          refine ⟨3251723135914808471656715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8671261695772822591084573 3251723135914808471656715)
          ·
            refine ⟨4877584703872212707485073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251723135914808471656715 4877584703872212707485073)
            ·
              refine ⟨3658188527904159530613805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4877584703872212707485073 3658188527904159530613805)
              ·
                refine ⟨1371820697964059823980177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658188527904159530613805 1371820697964059823980177)
                ·
                  refine ⟨1028865523473044867985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371820697964059823980177 1028865523473044867985133)
                  ·
                    refine ⟨385824571302391825494425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028865523473044867985133 385824571302391825494425)
                    ·
                      refine ⟨289368428476793869120819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385824571302391825494425 289368428476793869120819)
                      ·
                        rfl

theorem cell23_563543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_563543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563543 prefixEnd_563543 := by exact prefixLift 563543
  have htrace : WordTrace (prefixWord ++ tailWord_563543) baseStart_563543 baseEnd_563543 := by
    simpa [prefixWord, tailWord_563543, baseEnd_563543] using wordTrace_append hprefix tailTrace_563543
  have hstable : (prefixWord ++ tailWord_563543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563543).length < 2 ^ (prefixWord ++ tailWord_563543).sum := by decide
  have hdescent : baseEnd_563543 < baseStart_563543 := by decide
  rcases family_descends (prefixWord ++ tailWord_563543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563560 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_563560 : Nat := 118140960795 + 563560 * 2 ^ 59
def prefixEnd_563560 : Nat := 4983230072969 + 3 ^ 40 * 563560 * 2
def baseEnd_563560 : Nat := 289377157647920302608241

theorem tailTrace_563560 : CollatzResearch.WordTrace tailWord_563560 prefixEnd_563560 289377157647920302608241 := by
  unfold tailWord_563560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10277360919162921615192067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13703147892217228820256089 10277360919162921615192067)
  ·
    refine ⟨15416041378744382422788101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10277360919162921615192067 15416041378744382422788101)
    ·
      refine ⟨2890507758514571704272769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15416041378744382422788101 2890507758514571704272769)
      ·
        refine ⟨2167880818885928778204577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890507758514571704272769 2167880818885928778204577)
        ·
          refine ⟨1625910614164446583653433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167880818885928778204577 1625910614164446583653433)
          ·
            refine ⟨1219432960623334937740075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625910614164446583653433 1219432960623334937740075)
            ·
              refine ⟨1829149440935002406610113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219432960623334937740075 1829149440935002406610113)
              ·
                refine ⟨1371862080701251804957585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829149440935002406610113 1371862080701251804957585)
                ·
                  refine ⟨1028896560525938853718189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371862080701251804957585 1028896560525938853718189)
                  ·
                    refine ⟨385836210197227070144321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028896560525938853718189 385836210197227070144321)
                    ·
                      refine ⟨289377157647920302608241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385836210197227070144321 289377157647920302608241)
                      ·
                        rfl

theorem cell23_563560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_563560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563560 prefixEnd_563560 := by exact prefixLift 563560
  have htrace : WordTrace (prefixWord ++ tailWord_563560) baseStart_563560 baseEnd_563560 := by
    simpa [prefixWord, tailWord_563560, baseEnd_563560] using wordTrace_append hprefix tailTrace_563560
  have hstable : (prefixWord ++ tailWord_563560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563560).length < 2 ^ (prefixWord ++ tailWord_563560).sum := by decide
  have hdescent : baseEnd_563560 < baseStart_563560 := by decide
  rcases family_descends (prefixWord ++ tailWord_563560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563574 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_563574 : Nat := 118140960795 + 563574 * 2 ^ 59
def prefixEnd_563574 : Nat := 4983230072969 + 3 ^ 40 * 563574 * 2
def baseEnd_563574 : Nat := 32153816264120360870353

theorem tailTrace_563574 : CollatzResearch.WordTrace tailWord_563574 prefixEnd_563574 32153816264120360870353 := by
  unfold tailWord_563574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284702028767195226337111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13703488306850082414262517 1284702028767195226337111)
  ·
    refine ⟨1927053043150792839505667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1284702028767195226337111 1927053043150792839505667)
    ·
      refine ⟨2890579564726189259258501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927053043150792839505667 2890579564726189259258501)
      ·
        refine ⟨541983668386160486110969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2890579564726189259258501 541983668386160486110969)
        ·
          refine ⟨406487751289620364583227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541983668386160486110969 406487751289620364583227)
          ·
            refine ⟨609731626934430546874841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406487751289620364583227 609731626934430546874841)
            ·
              refine ⟨457298720200822910156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609731626934430546874841 457298720200822910156131)
              ·
                refine ⟨685948080301234365234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457298720200822910156131 685948080301234365234197)
                ·
                  refine ⟨32153816264120360870353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 685948080301234365234197 32153816264120360870353)
                  ·
                    rfl

theorem cell23_563574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_563574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563574 prefixEnd_563574 := by exact prefixLift 563574
  have htrace : WordTrace (prefixWord ++ tailWord_563574) baseStart_563574 baseEnd_563574 := by
    simpa [prefixWord, tailWord_563574, baseEnd_563574] using wordTrace_append hprefix tailTrace_563574
  have hstable : (prefixWord ++ tailWord_563574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563574).length < 2 ^ (prefixWord ++ tailWord_563574).sum := by decide
  have hdescent : baseEnd_563574 < baseStart_563574 := by decide
  rcases family_descends (prefixWord ++ tailWord_563574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563579 : List Nat := [1, 1, 1, 1, 1, 7, 1, 10]
def baseStart_563579 : Nat := 118140960795 + 563579 * 2 ^ 59
def prefixEnd_563579 : Nat := 4983230072969 + 3 ^ 40 * 563579 * 2
def baseEnd_563579 : Nat := 10718033843716878824839

theorem tailTrace_563579 : CollatzResearch.WordTrace tailWord_563579 prefixEnd_563579 10718033843716878824839 := by
  unfold tailWord_563579
  simp only [CollatzResearch.WordTrace]
  refine ⟨20555414825257009475325791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13703609883504672983550527 20555414825257009475325791)
  ·
    refine ⟨30833122237885514212988687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20555414825257009475325791 30833122237885514212988687)
    ·
      refine ⟨46249683356828271319483031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30833122237885514212988687 46249683356828271319483031)
      ·
        refine ⟨69374525035242406979224547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46249683356828271319483031 69374525035242406979224547)
        ·
          refine ⟨104061787552863610468836821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69374525035242406979224547 104061787552863610468836821)
          ·
            refine ⟨2438948145770240870363363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104061787552863610468836821 2438948145770240870363363)
            ·
              refine ⟨3658422218655361305545045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438948145770240870363363 3658422218655361305545045)
              ·
                refine ⟨10718033843716878824839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3658422218655361305545045 10718033843716878824839)
                ·
                  rfl

theorem cell23_563579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 10].length) (baseStart_563579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563579 prefixEnd_563579 := by exact prefixLift 563579
  have htrace : WordTrace (prefixWord ++ tailWord_563579) baseStart_563579 baseEnd_563579 := by
    simpa [prefixWord, tailWord_563579, baseEnd_563579] using wordTrace_append hprefix tailTrace_563579
  have hstable : (prefixWord ++ tailWord_563579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563579).length < 2 ^ (prefixWord ++ tailWord_563579).sum := by decide
  have hdescent : baseEnd_563579 < baseStart_563579 := by decide
  rcases family_descends (prefixWord ++ tailWord_563579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563593 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_563593 : Nat := 118140960795 + 563593 * 2 ^ 59
def prefixEnd_563593 : Nat := 4983230072969 + 3 ^ 40 * 563593 * 2
def baseEnd_563593 : Nat := 289394102509518673495589

theorem tailTrace_563593 : CollatzResearch.WordTrace tailWord_563593 prefixEnd_563593 289394102509518673495589 := by
  unfold tailWord_563593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20555925447206289866335433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13703950298137526577556955 20555925447206289866335433)
  ·
    refine ⟨15416944085404717399751575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20555925447206289866335433 15416944085404717399751575)
    ·
      refine ⟨23125416128107076099627363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15416944085404717399751575 23125416128107076099627363)
      ·
        refine ⟨34688124192160614149441045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23125416128107076099627363 34688124192160614149441045)
        ·
          refine ⟨1626005821507528788255049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34688124192160614149441045 1626005821507528788255049)
          ·
            refine ⟨1219504366130646591191287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626005821507528788255049 1219504366130646591191287)
            ·
              refine ⟨1829256549195969886786931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219504366130646591191287 1829256549195969886786931)
              ·
                refine ⟨2743884823793954830180397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829256549195969886786931 2743884823793954830180397)
                ·
                  refine ⟨1028956808922733061317649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2743884823793954830180397 1028956808922733061317649)
                  ·
                    refine ⟨771717606692049795988237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1028956808922733061317649 771717606692049795988237)
                    ·
                      refine ⟨289394102509518673495589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 771717606692049795988237 289394102509518673495589)
                      ·
                        rfl

theorem cell23_563593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_563593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563593 prefixEnd_563593 := by exact prefixLift 563593
  have htrace : WordTrace (prefixWord ++ tailWord_563593) baseStart_563593 baseEnd_563593 := by
    simpa [prefixWord, tailWord_563593, baseEnd_563593] using wordTrace_append hprefix tailTrace_563593
  have hstable : (prefixWord ++ tailWord_563593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563593).length < 2 ^ (prefixWord ++ tailWord_563593).sum := by decide
  have hdescent : baseEnd_563593 < baseStart_563593 := by decide
  rcases family_descends (prefixWord ++ tailWord_563593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563617 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_563617 : Nat := 118140960795 + 563617 * 2 ^ 59
def prefixEnd_563617 : Nat := 4983230072969 + 3 ^ 40 * 563617 * 2
def baseEnd_563617 : Nat := 96468808681742193198493

theorem tailTrace_563617 : CollatzResearch.WordTrace tailWord_563617 prefixEnd_563617 96468808681742193198493 := by
  unfold tailWord_563617
  simp only [CollatzResearch.WordTrace]
  refine ⟨20556800799119341965209105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13704533866079561310139403 20556800799119341965209105)
  ·
    refine ⟨15417600599339506473906829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20556800799119341965209105 15417600599339506473906829)
    ·
      refine ⟨5781600224752314927715061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15417600599339506473906829 5781600224752314927715061)
      ·
        refine ⟨542025021070529524473287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5781600224752314927715061 542025021070529524473287)
        ·
          refine ⟨813037531605794286709931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542025021070529524473287 813037531605794286709931)
          ·
            refine ⟨1219556297408691430064897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813037531605794286709931 1219556297408691430064897)
            ·
              refine ⟨914667223056518572548673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219556297408691430064897 914667223056518572548673)
              ·
                refine ⟨686000417292388929411505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914667223056518572548673 686000417292388929411505)
                ·
                  refine ⟨514500312969291697058629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686000417292388929411505 514500312969291697058629)
                  ·
                    refine ⟨96468808681742193198493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514500312969291697058629 96468808681742193198493)
                    ·
                      rfl

theorem cell23_563617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_563617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563617 prefixEnd_563617 := by exact prefixLift 563617
  have htrace : WordTrace (prefixWord ++ tailWord_563617) baseStart_563617 baseEnd_563617 := by
    simpa [prefixWord, tailWord_563617, baseEnd_563617] using wordTrace_append hprefix tailTrace_563617
  have hstable : (prefixWord ++ tailWord_563617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563617).length < 2 ^ (prefixWord ++ tailWord_563617).sum := by decide
  have hdescent : baseEnd_563617 < baseStart_563617 := by decide
  rcases family_descends (prefixWord ++ tailWord_563617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563680 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2]
def baseStart_563680 : Nat := 118140960795 + 563680 * 2 ^ 59
def prefixEnd_563680 : Nat := 4983230072969 + 3 ^ 40 * 563680 * 2
def baseEnd_563680 : Nat := 289438775326459833107689

theorem tailTrace_563680 : CollatzResearch.WordTrace tailWord_563680 prefixEnd_563680 289438775326459833107689 := by
  unfold tailWord_563680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10279549298945551862376247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13706065731927402483168329 10279549298945551862376247)
  ·
    refine ⟨15419323948418327793564371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10279549298945551862376247 15419323948418327793564371)
    ·
      refine ⟨23128985922627491690346557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419323948418327793564371 23128985922627491690346557)
      ·
        refine ⟨8673369720985309383879959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23128985922627491690346557 8673369720985309383879959)
        ·
          refine ⟨13010054581477964075819939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8673369720985309383879959 13010054581477964075819939)
          ·
            refine ⟨19515081872216946113729909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13010054581477964075819939 19515081872216946113729909)
            ·
              refine ⟨1829538925520338698162179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19515081872216946113729909 1829538925520338698162179)
              ·
                refine ⟨2744308388280508047243269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829538925520338698162179 2744308388280508047243269)
                ·
                  refine ⟨514557822802595258858113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2744308388280508047243269 514557822802595258858113)
                  ·
                    refine ⟨385918367101946444143585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514557822802595258858113 385918367101946444143585)
                    ·
                      refine ⟨289438775326459833107689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385918367101946444143585 289438775326459833107689)
                      ·
                        rfl

theorem cell23_563680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_563680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563680 prefixEnd_563680 := by exact prefixLift 563680
  have htrace : WordTrace (prefixWord ++ tailWord_563680) baseStart_563680 baseEnd_563680 := by
    simpa [prefixWord, tailWord_563680, baseEnd_563680] using wordTrace_append hprefix tailTrace_563680
  have hstable : (prefixWord ++ tailWord_563680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563680).length < 2 ^ (prefixWord ++ tailWord_563680).sum := by decide
  have hdescent : baseEnd_563680 < baseStart_563680 := by decide
  rcases family_descends (prefixWord ++ tailWord_563680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
