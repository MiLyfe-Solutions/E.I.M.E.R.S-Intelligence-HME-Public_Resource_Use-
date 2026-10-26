import V185TrunkScan23Chunk1032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6115665 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_6115665 : Nat := 118140960795 + 6115665 * 2 ^ 59
def prefixEnd_6115665 : Nat := 4983230072969 + 3 ^ 40 * 6115665 * 2
def baseEnd_6115665 : Nat := 3140275666878920166262075

theorem tailTrace_6115665 : CollatzResearch.WordTrace tailWord_6115665 prefixEnd_6115665 3140275666878920166262075 := by
  unfold tailWord_6115665
  simp only [CollatzResearch.WordTrace]
  refine ⟨223056627388997652272412449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148704418259331768181608299 223056627388997652272412449)
  ·
    refine ⟨167292470541748239204309337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223056627388997652272412449 167292470541748239204309337)
    ·
      refine ⟨125469352906311179403232003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167292470541748239204309337 125469352906311179403232003)
      ·
        refine ⟨188204029359466769104848005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125469352906311179403232003 188204029359466769104848005)
        ·
          refine ⟨35288255504900019207159001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188204029359466769104848005 35288255504900019207159001)
          ·
            refine ⟨26466191628675014405369251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35288255504900019207159001 26466191628675014405369251)
            ·
              refine ⟨39699287443012521608053877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26466191628675014405369251 39699287443012521608053877)
              ·
                refine ⟨3721808197782423900755051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39699287443012521608053877 3721808197782423900755051)
                ·
                  refine ⟨5582712296673635851132577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721808197782423900755051 5582712296673635851132577)
                  ·
                    refine ⟨4187034222505226888349433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582712296673635851132577 4187034222505226888349433)
                    ·
                      refine ⟨3140275666878920166262075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187034222505226888349433 3140275666878920166262075)
                      ·
                        rfl

theorem cell23_6115665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_6115665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115665 prefixEnd_6115665 := by exact prefixLift 6115665
  have htrace : WordTrace (prefixWord ++ tailWord_6115665) baseStart_6115665 baseEnd_6115665 := by
    simpa [prefixWord, tailWord_6115665, baseEnd_6115665] using wordTrace_append hprefix tailTrace_6115665
  have hstable : (prefixWord ++ tailWord_6115665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115665).length < 2 ^ (prefixWord ++ tailWord_6115665).sum := by decide
  have hdescent : baseEnd_6115665 < baseStart_6115665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115667 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 9]
def baseStart_6115667 : Nat := 118140960795 + 6115667 * 2 ^ 59
def prefixEnd_6115667 : Nat := 4983230072969 + 3 ^ 40 * 6115667 * 2
def baseEnd_6115667 : Nat := 1046758897946743052812355

theorem tailTrace_6115667 : CollatzResearch.WordTrace tailWord_6115667 prefixEnd_6115667 1046758897946743052812355 := by
  unfold tailWord_6115667
  simp only [CollatzResearch.WordTrace]
  refine ⟨223056700334990406613985255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148704466889993604409323503 223056700334990406613985255)
  ·
    refine ⟨334585050502485609920977883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223056700334990406613985255 334585050502485609920977883)
    ·
      refine ⟨501877575753728414881466825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334585050502485609920977883 501877575753728414881466825)
      ·
        refine ⟨376408181815296311161100119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501877575753728414881466825 376408181815296311161100119)
        ·
          refine ⟨564612272722944466741650179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376408181815296311161100119 564612272722944466741650179)
          ·
            refine ⟨846918409084416700112475269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564612272722944466741650179 846918409084416700112475269)
            ·
              refine ⟨158797201703328131271089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 846918409084416700112475269 158797201703328131271089113)
              ·
                refine ⟨119097901277496098453316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158797201703328131271089113 119097901277496098453316835)
                ·
                  refine ⟨178646851916244147679975253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119097901277496098453316835 178646851916244147679975253)
                  ·
                    refine ⟨1046758897946743052812355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178646851916244147679975253 1046758897946743052812355)
                    ·
                      rfl

theorem cell23_6115667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_6115667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115667 prefixEnd_6115667 := by exact prefixLift 6115667
  have htrace : WordTrace (prefixWord ++ tailWord_6115667) baseStart_6115667 baseEnd_6115667 := by
    simpa [prefixWord, tailWord_6115667, baseEnd_6115667] using wordTrace_append hprefix tailTrace_6115667
  have hstable : (prefixWord ++ tailWord_6115667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115667).length < 2 ^ (prefixWord ++ tailWord_6115667).sum := by decide
  have hdescent : baseEnd_6115667 < baseStart_6115667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115668 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_6115668 : Nat := 118140960795 + 6115668 * 2 ^ 59
def prefixEnd_6115668 : Nat := 4983230072969 + 3 ^ 40 * 6115668 * 2
def baseEnd_6115668 : Nat := 3140277207320883654524561

theorem tailTrace_6115668 : CollatzResearch.WordTrace tailWord_6115668 prefixEnd_6115668 3140277207320883654524561 := by
  unfold tailWord_6115668
  simp only [CollatzResearch.WordTrace]
  refine ⟨111528368403993391892385829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148704491205324522523181105 111528368403993391892385829)
  ·
    refine ⟨20911569075748760979822343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111528368403993391892385829 20911569075748760979822343)
    ·
      refine ⟨31367353613623141469733515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20911569075748760979822343 31367353613623141469733515)
      ·
        refine ⟨47051030420434712204600273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31367353613623141469733515 47051030420434712204600273)
        ·
          refine ⟨35288272815326034153450205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47051030420434712204600273 35288272815326034153450205)
          ·
            refine ⟨13233102305747262807543827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35288272815326034153450205 13233102305747262807543827)
            ·
              refine ⟨19849653458620894211315741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233102305747262807543827 19849653458620894211315741)
              ·
                refine ⟨7443620046982835329243403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19849653458620894211315741 7443620046982835329243403)
                ·
                  refine ⟨11165430070474252993865105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443620046982835329243403 11165430070474252993865105)
                  ·
                    refine ⟨8374072552855689745398829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11165430070474252993865105 8374072552855689745398829)
                    ·
                      refine ⟨3140277207320883654524561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374072552855689745398829 3140277207320883654524561)
                      ·
                        rfl

theorem cell23_6115668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_6115668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115668 prefixEnd_6115668 := by exact prefixLift 6115668
  have htrace : WordTrace (prefixWord ++ tailWord_6115668) baseStart_6115668 baseEnd_6115668 := by
    simpa [prefixWord, tailWord_6115668, baseEnd_6115668] using wordTrace_append hprefix tailTrace_6115668
  have hstable : (prefixWord ++ tailWord_6115668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115668).length < 2 ^ (prefixWord ++ tailWord_6115668).sum := by decide
  have hdescent : baseEnd_6115668 < baseStart_6115668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115682 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6115682 : Nat := 118140960795 + 6115682 * 2 ^ 59
def prefixEnd_6115682 : Nat := 4983230072969 + 3 ^ 40 * 6115682 * 2
def baseEnd_6115682 : Nat := 3140284396050046599749497

theorem tailTrace_6115682 : CollatzResearch.WordTrace tailWord_6115682 prefixEnd_6115682 3140284396050046599749497 := by
  unfold tailWord_6115682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764311857484016043945325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148704831619957376117187533 55764311857484016043945325)
  ·
    refine ⟨20911616946556506016479497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55764311857484016043945325 20911616946556506016479497)
    ·
      refine ⟨15683712709917379512359623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20911616946556506016479497 15683712709917379512359623)
      ·
        refine ⟨23525569064876069268539435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15683712709917379512359623 23525569064876069268539435)
        ·
          refine ⟨35288353597314103902809153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23525569064876069268539435 35288353597314103902809153)
          ·
            refine ⟨26466265197985577927106865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35288353597314103902809153 26466265197985577927106865)
            ·
              refine ⟨19849698898489183445330149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26466265197985577927106865 19849698898489183445330149)
              ·
                refine ⟨3721818543466721895999403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19849698898489183445330149 3721818543466721895999403)
                ·
                  refine ⟨5582727815200082843999105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721818543466721895999403 5582727815200082843999105)
                  ·
                    refine ⟨4187045861400062132999329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582727815200082843999105 4187045861400062132999329)
                    ·
                      refine ⟨3140284396050046599749497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187045861400062132999329 3140284396050046599749497)
                      ·
                        rfl

theorem cell23_6115682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6115682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115682 prefixEnd_6115682 := by exact prefixLift 6115682
  have htrace : WordTrace (prefixWord ++ tailWord_6115682) baseStart_6115682 baseEnd_6115682 := by
    simpa [prefixWord, tailWord_6115682, baseEnd_6115682] using wordTrace_append hprefix tailTrace_6115682
  have hstable : (prefixWord ++ tailWord_6115682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115682).length < 2 ^ (prefixWord ++ tailWord_6115682).sum := by decide
  have hdescent : baseEnd_6115682 < baseStart_6115682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115698 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6115698 : Nat := 118140960795 + 6115698 * 2 ^ 59
def prefixEnd_6115698 : Nat := 4983230072969 + 3 ^ 40 * 6115698 * 2
def baseEnd_6115698 : Nat := 3140292611740518537149423

theorem tailTrace_6115698 : CollatzResearch.WordTrace tailWord_6115698 prefixEnd_6115698 3140292611740518537149423 := by
  unfold tailWord_6115698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764457749469524727090937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148705220665252065938909165 55764457749469524727090937)
  ·
    refine ⟨41823343312102143545318203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55764457749469524727090937 41823343312102143545318203)
    ·
      refine ⟨62735014968153215317977305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41823343312102143545318203 62735014968153215317977305)
      ·
        refine ⟨47051261226114911488482979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62735014968153215317977305 47051261226114911488482979)
        ·
          refine ⟨70576891839172367232724469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47051261226114911488482979 70576891839172367232724469)
          ·
            refine ⟨6616583609922409428067919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70576891839172367232724469 6616583609922409428067919)
            ·
              refine ⟨9924875414883614142101879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616583609922409428067919 9924875414883614142101879)
              ·
                refine ⟨14887313122325421213152819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9924875414883614142101879 14887313122325421213152819)
                ·
                  refine ⟨22330969683488131819729229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14887313122325421213152819 22330969683488131819729229)
                  ·
                    refine ⟨8374113631308049432398461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22330969683488131819729229 8374113631308049432398461)
                    ·
                      refine ⟨3140292611740518537149423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374113631308049432398461 3140292611740518537149423)
                      ·
                        rfl

theorem cell23_6115698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6115698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115698 prefixEnd_6115698 := by exact prefixLift 6115698
  have htrace : WordTrace (prefixWord ++ tailWord_6115698) baseStart_6115698 baseEnd_6115698 := by
    simpa [prefixWord, tailWord_6115698, baseEnd_6115698] using wordTrace_append hprefix tailTrace_6115698
  have hstable : (prefixWord ++ tailWord_6115698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115698).length < 2 ^ (prefixWord ++ tailWord_6115698).sum := by decide
  have hdescent : baseEnd_6115698 < baseStart_6115698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115702 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6115702 : Nat := 118140960795 + 6115702 * 2 ^ 59
def prefixEnd_6115702 : Nat := 4983230072969 + 3 ^ 40 * 6115702 * 2
def baseEnd_6115702 : Nat := 3140294665663136521499405

theorem tailTrace_6115702 : CollatzResearch.WordTrace tailWord_6115702 prefixEnd_6115702 3140294665663136521499405 := by
  unfold tailWord_6115702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941123555616475474469335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148705317926575738394339573 13941123555616475474469335)
  ·
    refine ⟨20911685333424713211704003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941123555616475474469335 20911685333424713211704003)
    ·
      refine ⟨31367528000137069817556005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20911685333424713211704003 31367528000137069817556005)
      ·
        refine ⟨5881411500025700590791751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31367528000137069817556005 5881411500025700590791751)
        ·
          refine ⟨8822117250038550886187627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881411500025700590791751 8822117250038550886187627)
          ·
            refine ⟨13233175875057826329281441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822117250038550886187627 13233175875057826329281441)
            ·
              refine ⟨9924881906293369746961081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13233175875057826329281441 9924881906293369746961081)
              ·
                refine ⟨7443661429720027310220811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9924881906293369746961081 7443661429720027310220811)
                ·
                  refine ⟨11165492144580040965331217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443661429720027310220811 11165492144580040965331217)
                  ·
                    refine ⟨8374119108435030723998413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11165492144580040965331217 8374119108435030723998413)
                    ·
                      refine ⟨3140294665663136521499405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374119108435030723998413 3140294665663136521499405)
                      ·
                        rfl

theorem cell23_6115702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6115702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115702 prefixEnd_6115702 := by exact prefixLift 6115702
  have htrace : WordTrace (prefixWord ++ tailWord_6115702) baseStart_6115702 baseEnd_6115702 := by
    simpa [prefixWord, tailWord_6115702, baseEnd_6115702] using wordTrace_append hprefix tailTrace_6115702
  have hstable : (prefixWord ++ tailWord_6115702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115702).length < 2 ^ (prefixWord ++ tailWord_6115702).sum := by decide
  have hdescent : baseEnd_6115702 < baseStart_6115702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115724 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6115724 : Nat := 118140960795 + 6115724 * 2 ^ 59
def prefixEnd_6115724 : Nat := 4983230072969 + 3 ^ 40 * 6115724 * 2
def baseEnd_6115724 : Nat := 3140305962237535435424303

theorem tailTrace_6115724 : CollatzResearch.WordTrace tailWord_6115724 prefixEnd_6115724 3140305962237535435424303 := by
  unfold tailWord_6115724
  simp only [CollatzResearch.WordTrace]
  refine ⟨111529389647891952674405113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148705852863855936899206817 111529389647891952674405113)
  ·
    refine ⟨83647042235918964505803835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111529389647891952674405113 83647042235918964505803835)
    ·
      refine ⟨125470563353878446758705753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83647042235918964505803835 125470563353878446758705753)
      ·
        refine ⟨94102922515408835069029315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125470563353878446758705753 94102922515408835069029315)
        ·
          refine ⟨141154383773113252603543973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94102922515408835069029315 141154383773113252603543973)
          ·
            refine ⟨26466446957458734863164495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141154383773113252603543973 26466446957458734863164495)
            ·
              refine ⟨39699670436188102294746743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26466446957458734863164495 39699670436188102294746743)
              ·
                refine ⟨59549505654282153442120115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39699670436188102294746743 59549505654282153442120115)
                ·
                  refine ⟨89324258481423230163180173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59549505654282153442120115 89324258481423230163180173)
                  ·
                    refine ⟨33496596930533711311192565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89324258481423230163180173 33496596930533711311192565)
                    ·
                      refine ⟨3140305962237535435424303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33496596930533711311192565 3140305962237535435424303)
                      ·
                        rfl

theorem cell23_6115724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6115724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115724 prefixEnd_6115724 := by exact prefixLift 6115724
  have htrace : WordTrace (prefixWord ++ tailWord_6115724) baseStart_6115724 baseEnd_6115724 := by
    simpa [prefixWord, tailWord_6115724, baseEnd_6115724] using wordTrace_append hprefix tailTrace_6115724
  have hstable : (prefixWord ++ tailWord_6115724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115724).length < 2 ^ (prefixWord ++ tailWord_6115724).sum := by decide
  have hdescent : baseEnd_6115724 < baseStart_6115724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115781 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_6115781 : Nat := 118140960795 + 6115781 * 2 ^ 59
def prefixEnd_6115781 : Nat := 4983230072969 + 3 ^ 40 * 6115781 * 2
def baseEnd_6115781 : Nat := 3140335230634841712411541

theorem tailTrace_6115781 : CollatzResearch.WordTrace tailWord_6115781 prefixEnd_6115781 3140335230634841712411541 := by
  unfold tailWord_6115781
  simp only [CollatzResearch.WordTrace]
  refine ⟨223060858256577404083635197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148707238837718269389090131 223060858256577404083635197)
  ·
    refine ⟨83647821846216526531363199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223060858256577404083635197 83647821846216526531363199)
    ·
      refine ⟨125471732769324789797044799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83647821846216526531363199 125471732769324789797044799)
      ·
        refine ⟨188207599153987184695567199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125471732769324789797044799 188207599153987184695567199)
        ·
          refine ⟨282311398730980777043350799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188207599153987184695567199 282311398730980777043350799)
          ·
            refine ⟨423467098096471165565026199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282311398730980777043350799 423467098096471165565026199)
            ·
              refine ⟨635200647144706748347539299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423467098096471165565026199 635200647144706748347539299)
              ·
                refine ⟨952800970717060122521308949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635200647144706748347539299 952800970717060122521308949)
                ·
                  refine ⟨44662545502362193243186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 952800970717060122521308949 44662545502362193243186357)
                  ·
                    refine ⟨4187113640846455616548721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44662545502362193243186357 4187113640846455616548721)
                    ·
                      refine ⟨3140335230634841712411541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187113640846455616548721 3140335230634841712411541)
                      ·
                        rfl

theorem cell23_6115781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_6115781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115781 prefixEnd_6115781 := by exact prefixLift 6115781
  have htrace : WordTrace (prefixWord ++ tailWord_6115781) baseStart_6115781 baseEnd_6115781 := by
    simpa [prefixWord, tailWord_6115781, baseEnd_6115781] using wordTrace_append hprefix tailTrace_6115781
  have hstable : (prefixWord ++ tailWord_6115781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115781).length < 2 ^ (prefixWord ++ tailWord_6115781).sum := by decide
  have hdescent : baseEnd_6115781 < baseStart_6115781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115841 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6115841 : Nat := 118140960795 + 6115841 * 2 ^ 59
def prefixEnd_6115841 : Nat := 4983230072969 + 3 ^ 40 * 6115841 * 2
def baseEnd_6115841 : Nat := 3140366039474111477661265

theorem tailTrace_6115841 : CollatzResearch.WordTrace tailWord_6115841 prefixEnd_6115841 3140366039474111477661265 := by
  unfold tailWord_6115841
  simp only [CollatzResearch.WordTrace]
  refine ⟨223063046636360034330819377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148708697757573356220546251 223063046636360034330819377)
  ·
    refine ⟨167297284977270025748114533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223063046636360034330819377 167297284977270025748114533)
    ·
      refine ⟨31368240933238129827771475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167297284977270025748114533 31368240933238129827771475)
      ·
        refine ⟨47052361399857194741657213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31368240933238129827771475 47052361399857194741657213)
        ·
          refine ⟨17644635524946448028121455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47052361399857194741657213 17644635524946448028121455)
          ·
            refine ⟨26466953287419672042182183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17644635524946448028121455 26466953287419672042182183)
            ·
              refine ⟨39700429931129508063273275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26466953287419672042182183 39700429931129508063273275)
              ·
                refine ⟨59550644896694262094909913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39700429931129508063273275 59550644896694262094909913)
                ·
                  refine ⟨44662983672520696571182435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59550644896694262094909913 44662983672520696571182435)
                  ·
                    refine ⟨66994475508781044856773653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44662983672520696571182435 66994475508781044856773653)
                    ·
                      refine ⟨3140366039474111477661265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66994475508781044856773653 3140366039474111477661265)
                      ·
                        rfl

theorem cell23_6115841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6115841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115841 prefixEnd_6115841 := by exact prefixLift 6115841
  have htrace : WordTrace (prefixWord ++ tailWord_6115841) baseStart_6115841 baseEnd_6115841 := by
    simpa [prefixWord, tailWord_6115841, baseEnd_6115841] using wordTrace_append hprefix tailTrace_6115841
  have hstable : (prefixWord ++ tailWord_6115841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115841).length < 2 ^ (prefixWord ++ tailWord_6115841).sum := by decide
  have hdescent : baseEnd_6115841 < baseStart_6115841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115851 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 8]
def baseStart_6115851 : Nat := 118140960795 + 6115851 * 2 ^ 59
def prefixEnd_6115851 : Nat := 4983230072969 + 3 ^ 40 * 6115851 * 2
def baseEnd_6115851 : Nat := 348930130475628493170691

theorem tailTrace_6115851 : CollatzResearch.WordTrace tailWord_6115851 prefixEnd_6115851 348930130475628493170691 := by
  unfold tailWord_6115851
  simp only [CollatzResearch.WordTrace]
  refine ⟨223063411366323806038683407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148708940910882537359122271 223063411366323806038683407)
  ·
    refine ⟨334595117049485709058025111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223063411366323806038683407 334595117049485709058025111)
    ·
      refine ⟨501892675574228563587037667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334595117049485709058025111 501892675574228563587037667)
      ·
        refine ⟨752839013361342845380556501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501892675574228563587037667 752839013361342845380556501)
        ·
          refine ⟨17644664375656472938606793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 752839013361342845380556501 17644664375656472938606793)
          ·
            refine ⟨13233498281742354703955095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17644664375656472938606793 13233498281742354703955095)
            ·
              refine ⟨19850247422613532055932643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233498281742354703955095 19850247422613532055932643)
              ·
                refine ⟨29775371133920298083898965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19850247422613532055932643 29775371133920298083898965)
                ·
                  refine ⟨348930130475628493170691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29775371133920298083898965 348930130475628493170691)
                  ·
                    rfl

theorem cell23_6115851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 8].length) (baseStart_6115851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115851 prefixEnd_6115851 := by exact prefixLift 6115851
  have htrace : WordTrace (prefixWord ++ tailWord_6115851) baseStart_6115851 baseEnd_6115851 := by
    simpa [prefixWord, tailWord_6115851, baseEnd_6115851] using wordTrace_append hprefix tailTrace_6115851
  have hstable : (prefixWord ++ tailWord_6115851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115851).length < 2 ^ (prefixWord ++ tailWord_6115851).sum := by decide
  have hdescent : baseEnd_6115851 < baseStart_6115851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115888 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2]
def baseStart_6115888 : Nat := 118140960795 + 6115888 * 2 ^ 59
def prefixEnd_6115888 : Nat := 4983230072969 + 3 ^ 40 * 6115888 * 2
def baseEnd_6115888 : Nat := 3140390173064872793773549

theorem tailTrace_6115888 : CollatzResearch.WordTrace tailWord_6115888 prefixEnd_6115888 3140390173064872793773549 := by
  unfold tailWord_6115888
  simp only [CollatzResearch.WordTrace]
  refine ⟨111532380433594880678890159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148709840578126507571853545 111532380433594880678890159)
  ·
    refine ⟨167298570650392321018335239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111532380433594880678890159 167298570650392321018335239)
    ·
      refine ⟨250947855975588481527502859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167298570650392321018335239 250947855975588481527502859)
      ·
        refine ⟨376421783963382722291254289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250947855975588481527502859 376421783963382722291254289)
        ·
          refine ⟨282316337972537041718440717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376421783963382722291254289 282316337972537041718440717)
          ·
            refine ⟨105868626739701390644415269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282316337972537041718440717 105868626739701390644415269)
            ·
              refine ⟨19850367513694010745827863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105868626739701390644415269 19850367513694010745827863)
              ·
                refine ⟨29775551270541016118741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19850367513694010745827863 29775551270541016118741795)
                ·
                  refine ⟨44663326905811524178112693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29775551270541016118741795 44663326905811524178112693)
                  ·
                    refine ⟨4187186897419830391698065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44663326905811524178112693 4187186897419830391698065)
                    ·
                      refine ⟨3140390173064872793773549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187186897419830391698065 3140390173064872793773549)
                      ·
                        rfl

theorem cell23_6115888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2].length) (baseStart_6115888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115888 prefixEnd_6115888 := by exact prefixLift 6115888
  have htrace : WordTrace (prefixWord ++ tailWord_6115888) baseStart_6115888 baseEnd_6115888 := by
    simpa [prefixWord, tailWord_6115888, baseEnd_6115888] using wordTrace_append hprefix tailTrace_6115888
  have hstable : (prefixWord ++ tailWord_6115888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115888).length < 2 ^ (prefixWord ++ tailWord_6115888).sum := by decide
  have hdescent : baseEnd_6115888 < baseStart_6115888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115898 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_6115898 : Nat := 118140960795 + 6115898 * 2 ^ 59
def prefixEnd_6115898 : Nat := 4983230072969 + 3 ^ 40 * 6115898 * 2
def baseEnd_6115898 : Nat := 1046798435957139251549501

theorem tailTrace_6115898 : CollatzResearch.WordTrace tailWord_6115898 prefixEnd_6115898 1046798435957139251549501 := by
  unfold tailWord_6115898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55766281399288383266411087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148710083731435688710429565 55766281399288383266411087)
  ·
    refine ⟨83649422098932574899616631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55766281399288383266411087 83649422098932574899616631)
    ·
      refine ⟨125474133148398862349424947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83649422098932574899616631 125474133148398862349424947)
      ·
        refine ⟨188211199722598293524137421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125474133148398862349424947 188211199722598293524137421)
        ·
          refine ⟨70579199895974360071551533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188211199722598293524137421 70579199895974360071551533)
          ·
            refine ⟨26467199960990385026831825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70579199895974360071551533 26467199960990385026831825)
            ·
              refine ⟨19850399970742788770123869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26467199960990385026831825 19850399970742788770123869)
              ·
                refine ⟨7443899989028545788796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19850399970742788770123869 7443899989028545788796451)
                ·
                  refine ⟨11165849983542818683194677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443899989028545788796451 11165849983542818683194677)
                  ·
                    refine ⟨1046798435957139251549501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11165849983542818683194677 1046798435957139251549501)
                    ·
                      rfl

theorem cell23_6115898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_6115898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115898 prefixEnd_6115898 := by exact prefixLift 6115898
  have htrace : WordTrace (prefixWord ++ tailWord_6115898) baseStart_6115898 baseEnd_6115898 := by
    simpa [prefixWord, tailWord_6115898, baseEnd_6115898] using wordTrace_append hprefix tailTrace_6115898
  have hstable : (prefixWord ++ tailWord_6115898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115898).length < 2 ^ (prefixWord ++ tailWord_6115898).sum := by decide
  have hdescent : baseEnd_6115898 < baseStart_6115898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115905 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6115905 : Nat := 118140960795 + 6115905 * 2 ^ 59
def prefixEnd_6115905 : Nat := 4983230072969 + 3 ^ 40 * 6115905 * 2
def baseEnd_6115905 : Nat := 3140398902235999227260971

theorem tailTrace_6115905 : CollatzResearch.WordTrace tailWord_6115905 prefixEnd_6115905 3140398902235999227260971 := by
  unfold tailWord_6115905
  simp only [CollatzResearch.WordTrace]
  refine ⟨223065380908128173261149169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148710253938752115507432779 223065380908128173261149169)
  ·
    refine ⟨167299035681096129945861877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223065380908128173261149169 167299035681096129945861877)
    ·
      refine ⟨15684284595102762182424551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167299035681096129945861877 15684284595102762182424551)
      ·
        refine ⟨23526426892654143273636827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684284595102762182424551 23526426892654143273636827)
        ·
          refine ⟨35289640338981214910455241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526426892654143273636827 35289640338981214910455241)
          ·
            refine ⟨26467230254235911182841431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35289640338981214910455241 26467230254235911182841431)
            ·
              refine ⟨39700845381353866774262147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26467230254235911182841431 39700845381353866774262147)
              ·
                refine ⟨59551268072030800161393221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39700845381353866774262147 59551268072030800161393221)
                ·
                  refine ⟨11165862763505775030261229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59551268072030800161393221 11165862763505775030261229)
                  ·
                    refine ⟨4187198536314665636347961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165862763505775030261229 4187198536314665636347961)
                    ·
                      refine ⟨3140398902235999227260971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187198536314665636347961 3140398902235999227260971)
                      ·
                        rfl

theorem cell23_6115905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6115905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115905 prefixEnd_6115905 := by exact prefixLift 6115905
  have htrace : WordTrace (prefixWord ++ tailWord_6115905) baseStart_6115905 baseEnd_6115905 := by
    simpa [prefixWord, tailWord_6115905, baseEnd_6115905] using wordTrace_append hprefix tailTrace_6115905
  have hstable : (prefixWord ++ tailWord_6115905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115905).length < 2 ^ (prefixWord ++ tailWord_6115905).sum := by decide
  have hdescent : baseEnd_6115905 < baseStart_6115905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115932 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6115932 : Nat := 118140960795 + 6115932 * 2 ^ 59
def prefixEnd_6115932 : Nat := 4983230072969 + 3 ^ 40 * 6115932 * 2
def baseEnd_6115932 : Nat := 1046804255404556873874449

theorem tailTrace_6115932 : CollatzResearch.WordTrace tailWord_6115932 prefixEnd_6115932 1046804255404556873874449 := by
  unfold tailWord_6115932
  simp only [CollatzResearch.WordTrace]
  refine ⟨111533182839515178436191025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148710910452686904581588033 111533182839515178436191025)
  ·
    refine ⟨83649887129636383827143269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111533182839515178436191025 83649887129636383827143269)
    ·
      refine ⟨15684353836806821967589363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83649887129636383827143269 15684353836806821967589363)
      ·
        refine ⟨23526530755210232951384045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684353836806821967589363 23526530755210232951384045)
        ·
          refine ⟨8822449033203837356769017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23526530755210232951384045 8822449033203837356769017)
          ·
            refine ⟨6616836774902878017576763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8822449033203837356769017 6616836774902878017576763)
            ·
              refine ⟨9925255162354317026365145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616836774902878017576763 9925255162354317026365145)
              ·
                refine ⟨7443941371765737769773859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9925255162354317026365145 7443941371765737769773859)
                ·
                  refine ⟨11165912057648606654660789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443941371765737769773859 11165912057648606654660789)
                  ·
                    refine ⟨1046804255404556873874449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11165912057648606654660789 1046804255404556873874449)
                    ·
                      rfl

theorem cell23_6115932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6115932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115932 prefixEnd_6115932 := by exact prefixLift 6115932
  have htrace : WordTrace (prefixWord ++ tailWord_6115932) baseStart_6115932 baseEnd_6115932 := by
    simpa [prefixWord, tailWord_6115932, baseEnd_6115932] using wordTrace_append hprefix tailTrace_6115932
  have hstable : (prefixWord ++ tailWord_6115932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115932).length < 2 ^ (prefixWord ++ tailWord_6115932).sum := by decide
  have hdescent : baseEnd_6115932 < baseStart_6115932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115935 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 3, 2, 2]
def baseStart_6115935 : Nat := 118140960795 + 6115935 * 2 ^ 59
def prefixEnd_6115935 : Nat := 4983230072969 + 3 ^ 40 * 6115935 * 2
def baseEnd_6115935 : Nat := 3140414306655634109885833

theorem tailTrace_6115935 : CollatzResearch.WordTrace tailWord_6115935 prefixEnd_6115935 3140414306655634109885833 := by
  unfold tailWord_6115935
  simp only [CollatzResearch.WordTrace]
  refine ⟨223066475098019488384741259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148710983398679658923160839 223066475098019488384741259)
  ·
    refine ⟨334599712647029232577111889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223066475098019488384741259 334599712647029232577111889)
    ·
      refine ⟨250949784485271924432833917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334599712647029232577111889 250949784485271924432833917)
      ·
        refine ⟨94106169181976971662312719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250949784485271924432833917 94106169181976971662312719)
        ·
          refine ⟨141159253772965457493469079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94106169181976971662312719 141159253772965457493469079)
          ·
            refine ⟨211738880659448186240203619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141159253772965457493469079 211738880659448186240203619)
            ·
              refine ⟨317608320989172279360305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211738880659448186240203619 317608320989172279360305429)
              ·
                refine ⟨14887890046367450595014317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317608320989172279360305429 14887890046367450595014317)
                ·
                  refine ⟨5582958767387793973130369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14887890046367450595014317 5582958767387793973130369)
                  ·
                    refine ⟨4187219075540845479847777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582958767387793973130369 4187219075540845479847777)
                    ·
                      refine ⟨3140414306655634109885833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187219075540845479847777 3140414306655634109885833)
                      ·
                        rfl

theorem cell23_6115935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_6115935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115935 prefixEnd_6115935 := by exact prefixLift 6115935
  have htrace : WordTrace (prefixWord ++ tailWord_6115935) baseStart_6115935 baseEnd_6115935 := by
    simpa [prefixWord, tailWord_6115935, baseEnd_6115935] using wordTrace_append hprefix tailTrace_6115935
  have hstable : (prefixWord ++ tailWord_6115935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115935).length < 2 ^ (prefixWord ++ tailWord_6115935).sum := by decide
  have hdescent : baseEnd_6115935 < baseStart_6115935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115952 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4]
def baseStart_6115952 : Nat := 118140960795 + 6115952 * 2 ^ 59
def prefixEnd_6115952 : Nat := 4983230072969 + 3 ^ 40 * 6115952 * 2
def baseEnd_6115952 : Nat := 3140423035826760543373255

theorem tailTrace_6115952 : CollatzResearch.WordTrace tailWord_6115952 prefixEnd_6115952 3140423035826760543373255 := by
  unfold tailWord_6115952
  simp only [CollatzResearch.WordTrace]
  refine ⟨111533547569478950144055055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148711396759305266858740073 111533547569478950144055055)
  ·
    refine ⟨167300321354218425216082583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111533547569478950144055055 167300321354218425216082583)
    ·
      refine ⟨250950482031327637824123875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167300321354218425216082583 250950482031327637824123875)
      ·
        refine ⟨376425723046991456736185813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250950482031327637824123875 376425723046991456736185813)
        ·
          refine ⟨8822477883913862267254355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 376425723046991456736185813 8822477883913862267254355)
          ·
            refine ⟨13233716825870793400881533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822477883913862267254355 13233716825870793400881533)
            ·
              refine ⟨4962643809701547525330575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13233716825870793400881533 4962643809701547525330575)
              ·
                refine ⟨7443965714552321287995863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962643809701547525330575 7443965714552321287995863)
                ·
                  refine ⟨11165948571828481931993795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443965714552321287995863 11165948571828481931993795)
                  ·
                    refine ⟨16748922857742722897990693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11165948571828481931993795 16748922857742722897990693)
                    ·
                      refine ⟨3140423035826760543373255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16748922857742722897990693 3140423035826760543373255)
                      ·
                        rfl

theorem cell23_6115952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4].length) (baseStart_6115952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115952 prefixEnd_6115952 := by exact prefixLift 6115952
  have htrace : WordTrace (prefixWord ++ tailWord_6115952) baseStart_6115952 baseEnd_6115952 := by
    simpa [prefixWord, tailWord_6115952, baseEnd_6115952] using wordTrace_append hprefix tailTrace_6115952
  have hstable : (prefixWord ++ tailWord_6115952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115952).length < 2 ^ (prefixWord ++ tailWord_6115952).sum := by decide
  have hdescent : baseEnd_6115952 < baseStart_6115952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115958 : List Nat := [5, 1, 1, 2, 3, 11]
def baseStart_6115958 : Nat := 118140960795 + 6115958 * 2 ^ 59
def prefixEnd_6115958 : Nat := 4983230072969 + 3 ^ 40 * 6115958 * 2
def baseEnd_6115958 : Nat := 12923564266299125596289

theorem tailTrace_6115958 : CollatzResearch.WordTrace tailWord_6115958 prefixEnd_6115958 12923564266299125596289 := by
  unfold tailWord_6115958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941707123558510207051783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148711542651290775541885685 13941707123558510207051783)
  ·
    refine ⟨20912560685337765310577675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941707123558510207051783 20912560685337765310577675)
    ·
      refine ⟨31368841028006647965866513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20912560685337765310577675 31368841028006647965866513)
      ·
        refine ⟨23526630771004985974399885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31368841028006647965866513 23526630771004985974399885)
        ·
          refine ⟨8822486539126869740399957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23526630771004985974399885 8822486539126869740399957)
          ·
            refine ⟨12923564266299125596289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8822486539126869740399957 12923564266299125596289)
            ·
              rfl

theorem cell23_6115958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 11].length) (baseStart_6115958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115958 prefixEnd_6115958 := by exact prefixLift 6115958
  have htrace : WordTrace (prefixWord ++ tailWord_6115958) baseStart_6115958 baseEnd_6115958 := by
    simpa [prefixWord, tailWord_6115958, baseEnd_6115958] using wordTrace_append hprefix tailTrace_6115958
  have hstable : (prefixWord ++ tailWord_6115958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115958).length < 2 ^ (prefixWord ++ tailWord_6115958).sum := by decide
  have hdescent : baseEnd_6115958 < baseStart_6115958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115969 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6115969 : Nat := 118140960795 + 6115969 * 2 ^ 59
def prefixEnd_6115969 : Nat := 4983230072969 + 3 ^ 40 * 6115969 * 2
def baseEnd_6115969 : Nat := 3140431764997886976860677

theorem tailTrace_6115969 : CollatzResearch.WordTrace tailWord_6115969 prefixEnd_6115969 3140431764997886976860677 := by
  unfold tailWord_6115969
  simp only [CollatzResearch.WordTrace]
  refine ⟨223067715179896312191478961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148711810119930874794319307 223067715179896312191478961)
  ·
    refine ⟨167300786384922234143609221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223067715179896312191478961 167300786384922234143609221)
    ·
      refine ⟨31368897447172918901926729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167300786384922234143609221 31368897447172918901926729)
      ·
        refine ⟨23526673085379689176445047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31368897447172918901926729 23526673085379689176445047)
        ·
          refine ⟨35290009628069533764667571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526673085379689176445047 35290009628069533764667571)
          ·
            refine ⟨52935014442104300647001357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35290009628069533764667571 52935014442104300647001357)
            ·
              refine ⟨19850630415789112742625509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52935014442104300647001357 19850630415789112742625509)
              ·
                refine ⟨3721993202960458639242283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19850630415789112742625509 3721993202960458639242283)
                ·
                  refine ⟨5582989804440687958863425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721993202960458639242283 5582989804440687958863425)
                  ·
                    refine ⟨4187242353330515969147569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582989804440687958863425 4187242353330515969147569)
                    ·
                      refine ⟨3140431764997886976860677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187242353330515969147569 3140431764997886976860677)
                      ·
                        rfl

theorem cell23_6115969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6115969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115969 prefixEnd_6115969 := by exact prefixLift 6115969
  have htrace : WordTrace (prefixWord ++ tailWord_6115969) baseStart_6115969 baseEnd_6115969 := by
    simpa [prefixWord, tailWord_6115969, baseEnd_6115969] using wordTrace_append hprefix tailTrace_6115969
  have hstable : (prefixWord ++ tailWord_6115969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115969).length < 2 ^ (prefixWord ++ tailWord_6115969).sum := by decide
  have hdescent : baseEnd_6115969 < baseStart_6115969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115971 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 7]
def baseStart_6115971 : Nat := 118140960795 + 6115971 * 2 ^ 59
def prefixEnd_6115971 : Nat := 4983230072969 + 3 ^ 40 * 6115971 * 2
def baseEnd_6115971 : Nat := 1046810930653065323011889

theorem tailTrace_6115971 : CollatzResearch.WordTrace tailWord_6115971 prefixEnd_6115971 1046810930653065323011889 := by
  unfold tailWord_6115971
  simp only [CollatzResearch.WordTrace]
  refine ⟨223067788125889066533051767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148711858750592711022034511 223067788125889066533051767)
  ·
    refine ⟨334601682188833599799577651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223067788125889066533051767 334601682188833599799577651)
    ·
      refine ⟨501902523283250399699366477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334601682188833599799577651 501902523283250399699366477)
      ·
        refine ⟨188213446231218899887262429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501902523283250399699366477 188213446231218899887262429)
        ·
          refine ⟨70580042336707087457723411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188213446231218899887262429 70580042336707087457723411)
          ·
            refine ⟨105870063505060631186585117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70580042336707087457723411 105870063505060631186585117)
            ·
              refine ⟨39701273814397736694969419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105870063505060631186585117 39701273814397736694969419)
              ·
                refine ⟨59551910721596605042454129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39701273814397736694969419 59551910721596605042454129)
                ·
                  refine ⟨44663933041197453781840597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59551910721596605042454129 44663933041197453781840597)
                  ·
                    refine ⟨1046810930653065323011889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44663933041197453781840597 1046810930653065323011889)
                    ·
                      rfl

theorem cell23_6115971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_6115971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115971 prefixEnd_6115971 := by exact prefixLift 6115971
  have htrace : WordTrace (prefixWord ++ tailWord_6115971) baseStart_6115971 baseEnd_6115971 := by
    simpa [prefixWord, tailWord_6115971, baseEnd_6115971] using wordTrace_append hprefix tailTrace_6115971
  have hstable : (prefixWord ++ tailWord_6115971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115971).length < 2 ^ (prefixWord ++ tailWord_6115971).sum := by decide
  have hdescent : baseEnd_6115971 < baseStart_6115971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116041 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_6116041 : Nat := 118140960795 + 6116041 * 2 ^ 59
def prefixEnd_6116041 : Nat := 4983230072969 + 3 ^ 40 * 6116041 * 2
def baseEnd_6116041 : Nat := 3140468735605010695160345

theorem tailTrace_6116041 : CollatzResearch.WordTrace tailWord_6116041 prefixEnd_6116041 3140468735605010695160345 := by
  unfold tailWord_6116041
  simp only [CollatzResearch.WordTrace]
  refine ⟨223070341235635468488099977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148713560823756978992066651 223070341235635468488099977)
  ·
    refine ⟨167302755926726601366074983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223070341235635468488099977 167302755926726601366074983)
    ·
      refine ⟨250954133890089902049112475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167302755926726601366074983 250954133890089902049112475)
      ·
        refine ⟨376431200835134853073668713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250954133890089902049112475 376431200835134853073668713)
        ·
          refine ⟨282323400626351139805251535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376431200835134853073668713 282323400626351139805251535)
          ·
            refine ⟨423485100939526709707877303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282323400626351139805251535 423485100939526709707877303)
            ·
              refine ⟨635227651409290064561815955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423485100939526709707877303 635227651409290064561815955)
              ·
                refine ⟨952841477113935096842723933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635227651409290064561815955 952841477113935096842723933)
                ·
                  refine ⟨357315553917725661316021475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952841477113935096842723933 357315553917725661316021475)
                  ·
                    refine ⟨535973330876588491974032213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 357315553917725661316021475 535973330876588491974032213)
                    ·
                      refine ⟨3140468735605010695160345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 535973330876588491974032213 3140468735605010695160345)
                      ·
                        rfl

theorem cell23_6116041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_6116041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116041 prefixEnd_6116041 := by exact prefixLift 6116041
  have htrace : WordTrace (prefixWord ++ tailWord_6116041) baseStart_6116041 baseEnd_6116041 := by
    simpa [prefixWord, tailWord_6116041, baseEnd_6116041] using wordTrace_append hprefix tailTrace_6116041
  have hstable : (prefixWord ++ tailWord_6116041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116041).length < 2 ^ (prefixWord ++ tailWord_6116041).sum := by decide
  have hdescent : baseEnd_6116041 < baseStart_6116041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116042 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_6116042 : Nat := 118140960795 + 6116042 * 2 ^ 59
def prefixEnd_6116042 : Nat := 4983230072969 + 3 ^ 40 * 6116042 * 2
def baseEnd_6116042 : Nat := 3140469249085665191247841

theorem tailTrace_6116042 : CollatzResearch.WordTrace tailWord_6116042 prefixEnd_6116042 3140469249085665191247841 := by
  unfold tailWord_6116042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55767594427157961414721595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148713585139087897105924253 55767594427157961414721595)
  ·
    refine ⟨83651391640736942122082393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55767594427157961414721595 83651391640736942122082393)
    ·
      refine ⟨62738543730552706591561795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83651391640736942122082393 62738543730552706591561795)
      ·
        refine ⟨94107815595829059887342693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62738543730552706591561795 94107815595829059887342693)
        ·
          refine ⟨17645215424217948728876755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94107815595829059887342693 17645215424217948728876755)
          ·
            refine ⟨26467823136326923093315133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17645215424217948728876755 26467823136326923093315133)
            ·
              refine ⟨9925433676122596159993175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26467823136326923093315133 9925433676122596159993175)
              ·
                refine ⟨14888150514183894239989763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925433676122596159993175 14888150514183894239989763)
                ·
                  refine ⟨22332225771275841359984645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14888150514183894239989763 22332225771275841359984645)
                  ·
                    refine ⟨4187292332114220254997121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22332225771275841359984645 4187292332114220254997121)
                    ·
                      refine ⟨3140469249085665191247841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187292332114220254997121 3140469249085665191247841)
                      ·
                        rfl

theorem cell23_6116042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_6116042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116042 prefixEnd_6116042 := by exact prefixLift 6116042
  have htrace : WordTrace (prefixWord ++ tailWord_6116042) baseStart_6116042 baseEnd_6116042 := by
    simpa [prefixWord, tailWord_6116042, baseEnd_6116042] using wordTrace_append hprefix tailTrace_6116042
  have hstable : (prefixWord ++ tailWord_6116042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116042).length < 2 ^ (prefixWord ++ tailWord_6116042).sum := by decide
  have hdescent : baseEnd_6116042 < baseStart_6116042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116088 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_6116088 : Nat := 118140960795 + 6116088 * 2 ^ 59
def prefixEnd_6116088 : Nat := 4983230072969 + 3 ^ 40 * 6116088 * 2
def baseEnd_6116088 : Nat := 3140492869195772011272629

theorem tailTrace_6116088 : CollatzResearch.WordTrace tailWord_6116088 prefixEnd_6116088 3140492869195772011272629 := by
  unfold tailWord_6116088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111536027733232597757530459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148714703644310130343373945 111536027733232597757530459)
  ·
    refine ⟨167304041599848896636295689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111536027733232597757530459 167304041599848896636295689)
    ·
      refine ⟨125478031199886672477221767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167304041599848896636295689 125478031199886672477221767)
      ·
        refine ⟨188217046799830008715832651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125478031199886672477221767 188217046799830008715832651)
        ·
          refine ⟨282325570199745013073748977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188217046799830008715832651 282325570199745013073748977)
          ·
            refine ⟨211744177649808759805311733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282325570199745013073748977 211744177649808759805311733)
            ·
              refine ⟨19851016654669571231747975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211744177649808759805311733 19851016654669571231747975)
              ·
                refine ⟨29776524982004356847621963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19851016654669571231747975 29776524982004356847621963)
                ·
                  refine ⟨44664787473006535271432945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29776524982004356847621963 44664787473006535271432945)
                  ·
                    refine ⟨33498590604754901453574709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44664787473006535271432945 33498590604754901453574709)
                    ·
                      refine ⟨3140492869195772011272629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33498590604754901453574709 3140492869195772011272629)
                      ·
                        rfl

theorem cell23_6116088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_6116088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116088 prefixEnd_6116088 := by exact prefixLift 6116088
  have htrace : WordTrace (prefixWord ++ tailWord_6116088) baseStart_6116088 baseEnd_6116088 := by
    simpa [prefixWord, tailWord_6116088, baseEnd_6116088] using wordTrace_append hprefix tailTrace_6116088
  have hstable : (prefixWord ++ tailWord_6116088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116088).length < 2 ^ (prefixWord ++ tailWord_6116088).sum := by decide
  have hdescent : baseEnd_6116088 < baseStart_6116088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116115 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4]
def baseStart_6116115 : Nat := 118140960795 + 6116115 * 2 ^ 59
def prefixEnd_6116115 : Nat := 4983230072969 + 3 ^ 40 * 6116115 * 2
def baseEnd_6116115 : Nat := 3140506733173443405635005

theorem tailTrace_6116115 : CollatzResearch.WordTrace tailWord_6116115 prefixEnd_6116115 3140506733173443405635005 := by
  unfold tailWord_6116115
  simp only [CollatzResearch.WordTrace]
  refine ⟨223073040237367379126293799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148715360158244919417529199 223073040237367379126293799)
  ·
    refine ⟨334609560356051068689440699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223073040237367379126293799 334609560356051068689440699)
    ·
      refine ⟨501914340534076603034161049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334609560356051068689440699 501914340534076603034161049)
      ·
        refine ⟨376435755400557452275620787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501914340534076603034161049 376435755400557452275620787)
        ·
          refine ⟨564653633100836178413431181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376435755400557452275620787 564653633100836178413431181)
          ·
            refine ⟨211745112412813566905036693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564653633100836178413431181 211745112412813566905036693)
            ·
              refine ⟨9925552144350635948673595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211745112412813566905036693 9925552144350635948673595)
              ·
                refine ⟨14888328216525953923010393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925552144350635948673595 14888328216525953923010393)
                ·
                  refine ⟨11166246162394465442257795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14888328216525953923010393 11166246162394465442257795)
                  ·
                    refine ⟨16749369243591698163386693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11166246162394465442257795 16749369243591698163386693)
                    ·
                      refine ⟨3140506733173443405635005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16749369243591698163386693 3140506733173443405635005)
                      ·
                        rfl

theorem cell23_6116115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_6116115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116115 prefixEnd_6116115 := by exact prefixLift 6116115
  have htrace : WordTrace (prefixWord ++ tailWord_6116115) baseStart_6116115 baseEnd_6116115 := by
    simpa [prefixWord, tailWord_6116115, baseEnd_6116115] using wordTrace_append hprefix tailTrace_6116115
  have hstable : (prefixWord ++ tailWord_6116115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116115).length < 2 ^ (prefixWord ++ tailWord_6116115).sum := by decide
  have hdescent : baseEnd_6116115 < baseStart_6116115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116192 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2]
def baseStart_6116192 : Nat := 118140960795 + 6116192 * 2 ^ 59
def prefixEnd_6116192 : Nat := 4983230072969 + 3 ^ 40 * 6116192 * 2
def baseEnd_6116192 : Nat := 3140546271183839604372151

theorem tailTrace_6116192 : CollatzResearch.WordTrace tailWord_6116192 prefixEnd_6116192 3140546271183839604372151 := by
  unfold tailWord_6116192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111537924329044210638423415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148717232438725614184564553 111537924329044210638423415)
  ·
    refine ⟨167306886493566315957635123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111537924329044210638423415 167306886493566315957635123)
    ·
      refine ⟨250960329740349473936452685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167306886493566315957635123 250960329740349473936452685)
      ·
        refine ⟨94110123652631052726169757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250960329740349473936452685 94110123652631052726169757)
        ·
          refine ⟨35291296369736644772313659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94110123652631052726169757 35291296369736644772313659)
          ·
            refine ⟨52936944554604967158470489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35291296369736644772313659 52936944554604967158470489)
            ·
              refine ⟨39702708415953725368852867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52936944554604967158470489 39702708415953725368852867)
              ·
                refine ⟨59554062623930588053279301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39702708415953725368852867 59554062623930588053279301)
                ·
                  refine ⟨11166386741986985259989869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59554062623930588053279301 11166386741986985259989869)
                  ·
                    refine ⟨4187395028245119472496201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11166386741986985259989869 4187395028245119472496201)
                    ·
                      refine ⟨3140546271183839604372151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187395028245119472496201 3140546271183839604372151)
                      ·
                        rfl

theorem cell23_6116192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_6116192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116192 prefixEnd_6116192 := by exact prefixLift 6116192
  have htrace : WordTrace (prefixWord ++ tailWord_6116192) baseStart_6116192 baseEnd_6116192 := by
    simpa [prefixWord, tailWord_6116192, baseEnd_6116192] using wordTrace_append hprefix tailTrace_6116192
  have hstable : (prefixWord ++ tailWord_6116192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116192).length < 2 ^ (prefixWord ++ tailWord_6116192).sum := by decide
  have hdescent : baseEnd_6116192 < baseStart_6116192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116199 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_6116199 : Nat := 118140960795 + 6116199 * 2 ^ 59
def prefixEnd_6116199 : Nat := 4983230072969 + 3 ^ 40 * 6116199 * 2
def baseEnd_6116199 : Nat := 3140549865548421076984619

theorem tailTrace_6116199 : CollatzResearch.WordTrace tailWord_6116199 prefixEnd_6116199 3140549865548421076984619 := by
  unfold tailWord_6116199
  simp only [CollatzResearch.WordTrace]
  refine ⟨223076103969063061472351651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148717402646042040981567767 223076103969063061472351651)
  ·
    refine ⟨334614155953594592208527477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223076103969063061472351651 334614155953594592208527477)
    ·
      refine ⟨31370077120649493019549451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334614155953594592208527477 31370077120649493019549451)
      ·
        refine ⟨47055115680974239529324177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31370077120649493019549451 47055115680974239529324177)
        ·
          refine ⟨35291336760730679646993133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47055115680974239529324177 35291336760730679646993133)
          ·
            refine ⟨13234251285274004867622425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35291336760730679646993133 13234251285274004867622425)
            ·
              refine ⟨9925688463955503650716819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13234251285274004867622425 9925688463955503650716819)
              ·
                refine ⟨14888532695933255476075229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925688463955503650716819 14888532695933255476075229)
                ·
                  refine ⟨5583199760974970803528211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14888532695933255476075229 5583199760974970803528211)
                  ·
                    refine ⟨8374799641462456205292317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583199760974970803528211 8374799641462456205292317)
                    ·
                      refine ⟨3140549865548421076984619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374799641462456205292317 3140549865548421076984619)
                      ·
                        rfl

theorem cell23_6116199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_6116199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116199 prefixEnd_6116199 := by exact prefixLift 6116199
  have htrace : WordTrace (prefixWord ++ tailWord_6116199) baseStart_6116199 baseEnd_6116199 := by
    simpa [prefixWord, tailWord_6116199, baseEnd_6116199] using wordTrace_append hprefix tailTrace_6116199
  have hstable : (prefixWord ++ tailWord_6116199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116199).length < 2 ^ (prefixWord ++ tailWord_6116199).sum := by decide
  have hdescent : baseEnd_6116199 < baseStart_6116199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116232 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_6116232 : Nat := 118140960795 + 6116232 * 2 ^ 59
def prefixEnd_6116232 : Nat := 4983230072969 + 3 ^ 40 * 6116232 * 2
def baseEnd_6116232 : Nat := 1046855603470006482623989

theorem tailTrace_6116232 : CollatzResearch.WordTrace tailWord_6116232 prefixEnd_6116232 1046855603470006482623989 := by
  unfold tailWord_6116232
  simp only [CollatzResearch.WordTrace]
  refine ⟨111538653788971754054151475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148718205051962338738868633 111538653788971754054151475)
  ·
    refine ⟨167307980683457631081227213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111538653788971754054151475 167307980683457631081227213)
    ·
      refine ⟨62740492756296611655460205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167307980683457631081227213 62740492756296611655460205)
      ·
        refine ⟨23527684783611229370797577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62740492756296611655460205 23527684783611229370797577)
        ·
          refine ⟨17645763587708422028098183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23527684783611229370797577 17645763587708422028098183)
          ·
            refine ⟨26468645381562633042147275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17645763587708422028098183 26468645381562633042147275)
            ·
              refine ⟨39702968072343949563220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26468645381562633042147275 39702968072343949563220913)
              ·
                refine ⟨29777226054257962172415685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39702968072343949563220913 29777226054257962172415685)
                ·
                  refine ⟨5583229885173367907327941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29777226054257962172415685 5583229885173367907327941)
                  ·
                    refine ⟨1046855603470006482623989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5583229885173367907327941 1046855603470006482623989)
                    ·
                      rfl

theorem cell23_6116232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_6116232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116232 prefixEnd_6116232 := by exact prefixLift 6116232
  have htrace : WordTrace (prefixWord ++ tailWord_6116232) baseStart_6116232 baseEnd_6116232 := by
    simpa [prefixWord, tailWord_6116232, baseEnd_6116232] using wordTrace_append hprefix tailTrace_6116232
  have hstable : (prefixWord ++ tailWord_6116232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116232).length < 2 ^ (prefixWord ++ tailWord_6116232).sum := by decide
  have hdescent : baseEnd_6116232 < baseStart_6116232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116235 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_6116235 : Nat := 118140960795 + 6116235 * 2 ^ 59
def prefixEnd_6116235 : Nat := 4983230072969 + 3 ^ 40 * 6116235 * 2
def baseEnd_6116235 : Nat := 3140568350851982936134453

theorem tailTrace_6116235 : CollatzResearch.WordTrace tailWord_6116235 prefixEnd_6116235 3140568350851982936134453 := by
  unfold tailWord_6116235
  simp only [CollatzResearch.WordTrace]
  refine ⟨223077416996932639620662159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148718277997955093080441439 223077416996932639620662159)
  ·
    refine ⟨334616125495398959430993239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223077416996932639620662159 334616125495398959430993239)
    ·
      refine ⟨501924188243098439146489859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334616125495398959430993239 501924188243098439146489859)
      ·
        refine ⟨752886282364647658719734789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501924188243098439146489859 752886282364647658719734789)
        ·
          refine ⟨141166177943371436009950273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 752886282364647658719734789 141166177943371436009950273)
          ·
            refine ⟨105874633457528577007462705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141166177943371436009950273 105874633457528577007462705)
            ·
              refine ⟨79405975093146432755597029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105874633457528577007462705 79405975093146432755597029)
              ·
                refine ⟨14888620329964956141674443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79405975093146432755597029 14888620329964956141674443)
                ·
                  refine ⟨22332930494947434212511665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14888620329964956141674443 22332930494947434212511665)
                  ·
                    refine ⟨16749697871210575659383749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22332930494947434212511665 16749697871210575659383749)
                    ·
                      refine ⟨3140568350851982936134453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16749697871210575659383749 3140568350851982936134453)
                      ·
                        rfl

theorem cell23_6116235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_6116235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116235 prefixEnd_6116235 := by exact prefixLift 6116235
  have htrace : WordTrace (prefixWord ++ tailWord_6116235) baseStart_6116235 baseEnd_6116235 := by
    simpa [prefixWord, tailWord_6116235, baseEnd_6116235] using wordTrace_append hprefix tailTrace_6116235
  have hstable : (prefixWord ++ tailWord_6116235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116235).length < 2 ^ (prefixWord ++ tailWord_6116235).sum := by decide
  have hdescent : baseEnd_6116235 < baseStart_6116235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116245 : List Nat := [1, 3, 2, 1, 1, 6, 9]
def baseStart_6116245 : Nat := 118140960795 + 6116245 * 2 ^ 59
def prefixEnd_6116245 : Nat := 4983230072969 + 3 ^ 40 * 6116245 * 2
def baseEnd_6116245 : Nat := 38772512168623801197647

theorem tailTrace_6116245 : CollatzResearch.WordTrace tailWord_6116245 prefixEnd_6116245 38772512168623801197647 := by
  unfold tailWord_6116245
  simp only [CollatzResearch.WordTrace]
  refine ⟨223077781726896411328526189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148718521151264274219017459 223077781726896411328526189)
  ·
    refine ⟨83654168147586154248197321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223077781726896411328526189 83654168147586154248197321)
    ·
      refine ⟨62740626110689615686147991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83654168147586154248197321 62740626110689615686147991)
      ·
        refine ⟨94110939166034423529221987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62740626110689615686147991 94110939166034423529221987)
        ·
          refine ⟨141166408749051635293832981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94110939166034423529221987 141166408749051635293832981)
          ·
            refine ⟨6617175410111795404398421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141166408749051635293832981 6617175410111795404398421)
            ·
              refine ⟨38772512168623801197647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6617175410111795404398421 38772512168623801197647)
              ·
                rfl

theorem cell23_6116245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 9].length) (baseStart_6116245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116245 prefixEnd_6116245 := by exact prefixLift 6116245
  have htrace : WordTrace (prefixWord ++ tailWord_6116245) baseStart_6116245 baseEnd_6116245 := by
    simpa [prefixWord, tailWord_6116245, baseEnd_6116245] using wordTrace_append hprefix tailTrace_6116245
  have hstable : (prefixWord ++ tailWord_6116245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116245).length < 2 ^ (prefixWord ++ tailWord_6116245).sum := by decide
  have hdescent : baseEnd_6116245 < baseStart_6116245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116256 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 1, 2, 2]
def baseStart_6116256 : Nat := 118140960795 + 6116256 * 2 ^ 59
def prefixEnd_6116256 : Nat := 4983230072969 + 3 ^ 40 * 6116256 * 2
def baseEnd_6116256 : Nat := 3140579133945727353971857

theorem tailTrace_6116256 : CollatzResearch.WordTrace tailWord_6116256 prefixEnd_6116256 3140579133945727353971857 := by
  unfold tailWord_6116256
  simp only [CollatzResearch.WordTrace]
  refine ⟨111539091464928280103588311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148718788619904373471451081 111539091464928280103588311)
  ·
    refine ⟨167308637197392420155382467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111539091464928280103588311 167308637197392420155382467)
    ·
      refine ⟨250962955796088630233073701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167308637197392420155382467 250962955796088630233073701)
      ·
        refine ⟨47055554211766618168701319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250962955796088630233073701 47055554211766618168701319)
        ·
          refine ⟨70583331317649927253051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47055554211766618168701319 70583331317649927253051979)
          ·
            refine ⟨105874996976474890879577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70583331317649927253051979 105874996976474890879577969)
            ·
              refine ⟨79406247732356168159683477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105874996976474890879577969 79406247732356168159683477)
              ·
                refine ⟨3722167862454195382485163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79406247732356168159683477 3722167862454195382485163)
                ·
                  refine ⟨5583251793681293073727745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722167862454195382485163 5583251793681293073727745)
                  ·
                    refine ⟨4187438845260969805295809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583251793681293073727745 4187438845260969805295809)
                    ·
                      refine ⟨3140579133945727353971857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187438845260969805295809 3140579133945727353971857)
                      ·
                        rfl

theorem cell23_6116256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_6116256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116256 prefixEnd_6116256 := by exact prefixLift 6116256
  have htrace : WordTrace (prefixWord ++ tailWord_6116256) baseStart_6116256 baseEnd_6116256 := by
    simpa [prefixWord, tailWord_6116256, baseEnd_6116256] using wordTrace_append hprefix tailTrace_6116256
  have hstable : (prefixWord ++ tailWord_6116256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116256).length < 2 ^ (prefixWord ++ tailWord_6116256).sum := by decide
  have hdescent : baseEnd_6116256 < baseStart_6116256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116276 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6116276 : Nat := 118140960795 + 6116276 * 2 ^ 59
def prefixEnd_6116276 : Nat := 4983230072969 + 3 ^ 40 * 6116276 * 2
def baseEnd_6116276 : Nat := 3140589403558817275721765

theorem tailTrace_6116276 : CollatzResearch.WordTrace tailWord_6116276 prefixEnd_6116276 3140589403558817275721765 := by
  unfold tailWord_6116276
  simp only [CollatzResearch.WordTrace]
  refine ⟨111539456194892051811452341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148719274926522735748603121 111539456194892051811452341)
  ·
    refine ⟨10456824018271129857323657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111539456194892051811452341 10456824018271129857323657)
    ·
      refine ⟨7842618013703347392992743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10456824018271129857323657 7842618013703347392992743)
      ·
        refine ⟨11763927020555021089489115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7842618013703347392992743 11763927020555021089489115)
        ·
          refine ⟨17645890530832531634233673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11763927020555021089489115 17645890530832531634233673)
          ·
            refine ⟨13234417898124398725675255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17645890530832531634233673 13234417898124398725675255)
            ·
              refine ⟨19851626847186598088512883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13234417898124398725675255 19851626847186598088512883)
              ·
                refine ⟨29777440270779897132769325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19851626847186598088512883 29777440270779897132769325)
                ·
                  refine ⟨11166540101542461424788497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29777440270779897132769325 11166540101542461424788497)
                  ·
                    refine ⟨8374905076156846068591373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11166540101542461424788497 8374905076156846068591373)
                    ·
                      refine ⟨3140589403558817275721765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374905076156846068591373 3140589403558817275721765)
                      ·
                        rfl

theorem cell23_6116276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6116276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116276 prefixEnd_6116276 := by exact prefixLift 6116276
  have htrace : WordTrace (prefixWord ++ tailWord_6116276) baseStart_6116276 baseEnd_6116276 := by
    simpa [prefixWord, tailWord_6116276, baseEnd_6116276] using wordTrace_append hprefix tailTrace_6116276
  have hstable : (prefixWord ++ tailWord_6116276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116276).length < 2 ^ (prefixWord ++ tailWord_6116276).sum := by decide
  have hdescent : baseEnd_6116276 < baseStart_6116276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116301 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6116301 : Nat := 118140960795 + 6116301 * 2 ^ 59
def prefixEnd_6116301 : Nat := 4983230072969 + 3 ^ 40 * 6116301 * 2
def baseEnd_6116301 : Nat := 3140602240575179677909151

theorem tailTrace_6116301 : CollatzResearch.WordTrace tailWord_6116301 prefixEnd_6116301 3140602240575179677909151 := by
  unfold tailWord_6116301
  simp only [CollatzResearch.WordTrace]
  refine ⟨223079824214693532892564757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148719882809795688595043171 223079824214693532892564757)
  ·
    refine ⟨10456866760063759354338973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223079824214693532892564757 10456866760063759354338973)
    ·
      refine ⟨3921325035023909757877115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10456866760063759354338973 3921325035023909757877115)
      ·
        refine ⟨5881987552535864636815673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921325035023909757877115 5881987552535864636815673)
        ·
          refine ⟨4411490664401898477611755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881987552535864636815673 4411490664401898477611755)
          ·
            refine ⟨6617235996602847716417633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411490664401898477611755 6617235996602847716417633)
            ·
              refine ⟨4962926997452135787313225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6617235996602847716417633 4962926997452135787313225)
              ·
                refine ⟨3722195248089101840484919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962926997452135787313225 3722195248089101840484919)
                ·
                  refine ⟨5583292872133652760727379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722195248089101840484919 5583292872133652760727379)
                  ·
                    refine ⟨8374939308200479141091069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583292872133652760727379 8374939308200479141091069)
                    ·
                      refine ⟨3140602240575179677909151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374939308200479141091069 3140602240575179677909151)
                      ·
                        rfl

theorem cell23_6116301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6116301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116301 prefixEnd_6116301 := by exact prefixLift 6116301
  have htrace : WordTrace (prefixWord ++ tailWord_6116301) baseStart_6116301 baseEnd_6116301 := by
    simpa [prefixWord, tailWord_6116301, baseEnd_6116301] using wordTrace_append hprefix tailTrace_6116301
  have hstable : (prefixWord ++ tailWord_6116301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116301).length < 2 ^ (prefixWord ++ tailWord_6116301).sum := by decide
  have hdescent : baseEnd_6116301 < baseStart_6116301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116305 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_6116305 : Nat := 118140960795 + 6116305 * 2 ^ 59
def prefixEnd_6116305 : Nat := 4983230072969 + 3 ^ 40 * 6116305 * 2
def baseEnd_6116305 : Nat := 1046868098165932554086377

theorem tailTrace_6116305 : CollatzResearch.WordTrace tailWord_6116305 prefixEnd_6116305 1046868098165932554086377 := by
  unfold tailWord_6116305
  simp only [CollatzResearch.WordTrace]
  refine ⟨223079970106679041575710369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148719980071119361050473579 223079970106679041575710369)
  ·
    refine ⟨167309977580009281181782777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223079970106679041575710369 167309977580009281181782777)
    ·
      refine ⟨125482483185006960886337083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167309977580009281181782777 125482483185006960886337083)
      ·
        refine ⟨188223724777510441329505625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125482483185006960886337083 188223724777510441329505625)
        ·
          refine ⟨141167793583132830997129219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188223724777510441329505625 141167793583132830997129219)
          ·
            refine ⟨211751690374699246495693829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141167793583132830997129219 211751690374699246495693829)
            ·
              refine ⟨39703441945256108717942593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211751690374699246495693829 39703441945256108717942593)
              ·
                refine ⟨29777581458942081538456945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39703441945256108717942593 29777581458942081538456945)
                ·
                  refine ⟨22333186094206561153842709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29777581458942081538456945 22333186094206561153842709)
                  ·
                    refine ⟨1046868098165932554086377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22333186094206561153842709 1046868098165932554086377)
                    ·
                      rfl

theorem cell23_6116305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_6116305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116305 prefixEnd_6116305 := by exact prefixLift 6116305
  have htrace : WordTrace (prefixWord ++ tailWord_6116305) baseStart_6116305 baseEnd_6116305 := by
    simpa [prefixWord, tailWord_6116305, baseEnd_6116305] using wordTrace_append hprefix tailTrace_6116305
  have hstable : (prefixWord ++ tailWord_6116305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116305).length < 2 ^ (prefixWord ++ tailWord_6116305).sum := by decide
  have hdescent : baseEnd_6116305 < baseStart_6116305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116306 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6116306 : Nat := 118140960795 + 6116306 * 2 ^ 59
def prefixEnd_6116306 : Nat := 4983230072969 + 3 ^ 40 * 6116306 * 2
def baseEnd_6116306 : Nat := 3140604807978452158346627

theorem tailTrace_6116306 : CollatzResearch.WordTrace tailWord_6116306 prefixEnd_6116306 3140604807978452158346627 := by
  unfold tailWord_6116306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55770001644918854686624193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148720004386450279164331181 55770001644918854686624193)
  ·
    refine ⟨41827501233689141014968145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55770001644918854686624193 41827501233689141014968145)
    ·
      refine ⟨31370625925266855761226109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41827501233689141014968145 31370625925266855761226109)
      ·
        refine ⟨11763984721975070910459791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31370625925266855761226109 11763984721975070910459791)
        ·
          refine ⟨17645977082962606365689687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11763984721975070910459791 17645977082962606365689687)
          ·
            refine ⟨26468965624443909548534531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17645977082962606365689687 26468965624443909548534531)
            ·
              refine ⟨39703448436665864322801797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26468965624443909548534531 39703448436665864322801797)
              ·
                refine ⟨7444396581874849560525337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39703448436665864322801797 7444396581874849560525337)
                ·
                  refine ⟨5583297436406137170394003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7444396581874849560525337 5583297436406137170394003)
                  ·
                    refine ⟨8374946154609205755591005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583297436406137170394003 8374946154609205755591005)
                    ·
                      refine ⟨3140604807978452158346627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8374946154609205755591005 3140604807978452158346627)
                      ·
                        rfl

theorem cell23_6116306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6116306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116306 prefixEnd_6116306 := by exact prefixLift 6116306
  have htrace : WordTrace (prefixWord ++ tailWord_6116306) baseStart_6116306 baseEnd_6116306 := by
    simpa [prefixWord, tailWord_6116306, baseEnd_6116306] using wordTrace_append hprefix tailTrace_6116306
  have hstable : (prefixWord ++ tailWord_6116306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116306).length < 2 ^ (prefixWord ++ tailWord_6116306).sum := by decide
  have hdescent : baseEnd_6116306 < baseStart_6116306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116335 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 9]
def baseStart_6116335 : Nat := 118140960795 + 6116335 * 2 ^ 59
def prefixEnd_6116335 : Nat := 4983230072969 + 3 ^ 40 * 6116335 * 2
def baseEnd_6116335 : Nat := 348957744324159171653777

theorem tailTrace_6116335 : CollatzResearch.WordTrace tailWord_6116335 prefixEnd_6116335 348957744324159171653777 := by
  unfold tailWord_6116335
  simp only [CollatzResearch.WordTrace]
  refine ⟨223081064296570356699302459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148720709531046904466201639 223081064296570356699302459)
  ·
    refine ⟨334621596444855535048953689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223081064296570356699302459 334621596444855535048953689)
    ·
      refine ⟨250966197333641651286715267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334621596444855535048953689 250966197333641651286715267)
      ·
        refine ⟨376449296000462476930072901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250966197333641651286715267 376449296000462476930072901)
        ·
          refine ⟨70584243000086714424388669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376449296000462476930072901 70584243000086714424388669)
          ·
            refine ⟨26469091125032517909145751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70584243000086714424388669 26469091125032517909145751)
            ·
              refine ⟨39703636687548776863718627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26469091125032517909145751 39703636687548776863718627)
              ·
                refine ⟨59555455031323165295577941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39703636687548776863718627 59555455031323165295577941)
                ·
                  refine ⟨348957744324159171653777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59555455031323165295577941 348957744324159171653777)
                  ·
                    rfl

theorem cell23_6116335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 9].length) (baseStart_6116335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116335 prefixEnd_6116335 := by exact prefixLift 6116335
  have htrace : WordTrace (prefixWord ++ tailWord_6116335) baseStart_6116335 baseEnd_6116335 := by
    simpa [prefixWord, tailWord_6116335, baseEnd_6116335] using wordTrace_append hprefix tailTrace_6116335
  have hstable : (prefixWord ++ tailWord_6116335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116335).length < 2 ^ (prefixWord ++ tailWord_6116335).sum := by decide
  have hdescent : baseEnd_6116335 < baseStart_6116335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116363 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 2, 2, 2]
def baseStart_6116363 : Nat := 118140960795 + 6116363 * 2 ^ 59
def prefixEnd_6116363 : Nat := 4983230072969 + 3 ^ 40 * 6116363 * 2
def baseEnd_6116363 : Nat := 3140634076375758435333865

theorem tailTrace_6116363 : CollatzResearch.WordTrace tailWord_6116363 prefixEnd_6116363 3140634076375758435333865 := by
  unfold tailWord_6116363
  simp only [CollatzResearch.WordTrace]
  refine ⟨223082085540468917481321743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148721390360312611654214495 223082085540468917481321743)
  ·
    refine ⟨334623128310703376221982615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223082085540468917481321743 334623128310703376221982615)
    ·
      refine ⟨501934692466055064332973923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334623128310703376221982615 501934692466055064332973923)
      ·
        refine ⟨752902038699082596499460885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501934692466055064332973923 752902038699082596499460885)
        ·
          refine ⟨35292283064019496710912229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 752902038699082596499460885 35292283064019496710912229)
          ·
            refine ⟨6617303074503655633296043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35292283064019496710912229 6617303074503655633296043)
            ·
              refine ⟨9925954611755483449944065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617303074503655633296043 9925954611755483449944065)
              ·
                refine ⟨7444465958816612587458049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9925954611755483449944065 7444465958816612587458049)
                ·
                  refine ⟨5583349469112459440593537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7444465958816612587458049 5583349469112459440593537)
                  ·
                    refine ⟨4187512101834344580445153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583349469112459440593537 4187512101834344580445153)
                    ·
                      refine ⟨3140634076375758435333865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187512101834344580445153 3140634076375758435333865)
                      ·
                        rfl

theorem cell23_6116363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2, 2].length) (baseStart_6116363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116363 prefixEnd_6116363 := by exact prefixLift 6116363
  have htrace : WordTrace (prefixWord ++ tailWord_6116363) baseStart_6116363 baseEnd_6116363 := by
    simpa [prefixWord, tailWord_6116363, baseEnd_6116363] using wordTrace_append hprefix tailTrace_6116363
  have hstable : (prefixWord ++ tailWord_6116363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116363).length < 2 ^ (prefixWord ++ tailWord_6116363).sum := by decide
  have hdescent : baseEnd_6116363 < baseStart_6116363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116380 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6116380 : Nat := 118140960795 + 6116380 * 2 ^ 59
def prefixEnd_6116380 : Nat := 4983230072969 + 3 ^ 40 * 6116380 * 2
def baseEnd_6116380 : Nat := 3140642805546884868821287

theorem tailTrace_6116380 : CollatzResearch.WordTrace tailWord_6116380 prefixEnd_6116380 3140642805546884868821287 := by
  unfold tailWord_6116380
  simp only [CollatzResearch.WordTrace]
  refine ⟨111541352790703664692345297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148721803720938219589793729 111541352790703664692345297)
  ·
    refine ⟨83656014593027748519258973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111541352790703664692345297 83656014593027748519258973)
    ·
      refine ⟨31371005472385405694722115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83656014593027748519258973 31371005472385405694722115)
      ·
        refine ⟨47056508208578108542083173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31371005472385405694722115 47056508208578108542083173)
        ·
          refine ⟨8823095289108395351640595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47056508208578108542083173 8823095289108395351640595)
          ·
            refine ⟨13234642933662593027460893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823095289108395351640595 13234642933662593027460893)
            ·
              refine ⟨4962991100123472385297835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13234642933662593027460893 4962991100123472385297835)
              ·
                refine ⟨7444486650185208577946753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962991100123472385297835 7444486650185208577946753)
                ·
                  refine ⟨5583364987638906433460065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7444486650185208577946753 5583364987638906433460065)
                  ·
                    refine ⟨4187523740729179825095049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583364987638906433460065 4187523740729179825095049)
                    ·
                      refine ⟨3140642805546884868821287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187523740729179825095049 3140642805546884868821287)
                      ·
                        rfl

theorem cell23_6116380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6116380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116380 prefixEnd_6116380 := by exact prefixLift 6116380
  have htrace : WordTrace (prefixWord ++ tailWord_6116380) baseStart_6116380 baseEnd_6116380 := by
    simpa [prefixWord, tailWord_6116380, baseEnd_6116380] using wordTrace_append hprefix tailTrace_6116380
  have hstable : (prefixWord ++ tailWord_6116380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116380).length < 2 ^ (prefixWord ++ tailWord_6116380).sum := by decide
  have hdescent : baseEnd_6116380 < baseStart_6116380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116395 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 8]
def baseStart_6116395 : Nat := 118140960795 + 6116395 * 2 ^ 59
def prefixEnd_6116395 : Nat := 4983230072969 + 3 ^ 40 * 6116395 * 2
def baseEnd_6116395 : Nat := 1046883502585567436711239

theorem tailTrace_6116395 : CollatzResearch.WordTrace tailWord_6116395 prefixEnd_6116395 1046883502585567436711239 := by
  unfold tailWord_6116395
  simp only [CollatzResearch.WordTrace]
  refine ⟨223083252676352986946486639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148722168450901991297657759 223083252676352986946486639)
  ·
    refine ⟨334624879014529480419729959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223083252676352986946486639 334624879014529480419729959)
    ·
      refine ⟨501937318521794220629594939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334624879014529480419729959 501937318521794220629594939)
      ·
        refine ⟨752905977782691330944392409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501937318521794220629594939 752905977782691330944392409)
        ·
          refine ⟨564679483337018498208294307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752905977782691330944392409 564679483337018498208294307)
          ·
            refine ⟨847019225005527747312441461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564679483337018498208294307 847019225005527747312441461)
            ·
              refine ⟨79408052344268226310541387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 847019225005527747312441461 79408052344268226310541387)
              ·
                refine ⟨119112078516402339465812081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79408052344268226310541387 119112078516402339465812081)
                ·
                  refine ⟨89334058887301754599359061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119112078516402339465812081 89334058887301754599359061)
                  ·
                    refine ⟨1046883502585567436711239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89334058887301754599359061 1046883502585567436711239)
                    ·
                      rfl

theorem cell23_6116395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_6116395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116395 prefixEnd_6116395 := by exact prefixLift 6116395
  have htrace : WordTrace (prefixWord ++ tailWord_6116395) baseStart_6116395 baseEnd_6116395 := by
    simpa [prefixWord, tailWord_6116395, baseEnd_6116395] using wordTrace_append hprefix tailTrace_6116395
  have hstable : (prefixWord ++ tailWord_6116395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116395).length < 2 ^ (prefixWord ++ tailWord_6116395).sum := by decide
  have hdescent : baseEnd_6116395 < baseStart_6116395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116402 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6116402 : Nat := 118140960795 + 6116402 * 2 ^ 59
def prefixEnd_6116402 : Nat := 4983230072969 + 3 ^ 40 * 6116402 * 2
def baseEnd_6116402 : Nat := 3140654102121283782746185

theorem tailTrace_6116402 : CollatzResearch.WordTrace tailWord_6116402 prefixEnd_6116402 3140654102121283782746185 := by
  unfold tailWord_6116402
  simp only [CollatzResearch.WordTrace]
  refine ⟨55770876996831906785497865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148722338658218418094660973 55770876996831906785497865)
  ·
    refine ⟨41828157747623930089123399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55770876996831906785497865 41828157747623930089123399)
    ·
      refine ⟨62742236621435895133685099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41828157747623930089123399 62742236621435895133685099)
      ·
        refine ⟨94113354932153842700527649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62742236621435895133685099 94113354932153842700527649)
        ·
          refine ⟨70585016199115382025395737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94113354932153842700527649 70585016199115382025395737)
          ·
            refine ⟨52938762149336536519046803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70585016199115382025395737 52938762149336536519046803)
            ·
              refine ⟨79408143224004804778570205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52938762149336536519046803 79408143224004804778570205)
              ·
                refine ⟨29778053709001801791963827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79408143224004804778570205 29778053709001801791963827)
                ·
                  refine ⟨44667080563502702687945741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29778053709001801791963827 44667080563502702687945741)
                  ·
                    refine ⟨16750155211313513507979653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44667080563502702687945741 16750155211313513507979653)
                    ·
                      refine ⟨3140654102121283782746185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16750155211313513507979653 3140654102121283782746185)
                      ·
                        rfl

theorem cell23_6116402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6116402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116402 prefixEnd_6116402 := by exact prefixLift 6116402
  have htrace : WordTrace (prefixWord ++ tailWord_6116402) baseStart_6116402 baseEnd_6116402 := by
    simpa [prefixWord, tailWord_6116402, baseEnd_6116402] using wordTrace_append hprefix tailTrace_6116402
  have hstable : (prefixWord ++ tailWord_6116402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116402).length < 2 ^ (prefixWord ++ tailWord_6116402).sum := by decide
  have hdescent : baseEnd_6116402 < baseStart_6116402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116509 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6116509 : Nat := 118140960795 + 6116509 * 2 ^ 59
def prefixEnd_6116509 : Nat := 4983230072969 + 3 ^ 40 * 6116509 * 2
def baseEnd_6116509 : Nat := 3140709044551314864108193

theorem tailTrace_6116509 : CollatzResearch.WordTrace tailWord_6116509 prefixEnd_6116509 3140709044551314864108193 := by
  unfold tailWord_6116509
  simp only [CollatzResearch.WordTrace]
  refine ⟨223087410597939984416136581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148724940398626656277424387 223087410597939984416136581)
  ·
    refine ⟨41828889487113747078025609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223087410597939984416136581 41828889487113747078025609)
    ·
      refine ⟨31371667115335310308519207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41828889487113747078025609 31371667115335310308519207)
      ·
        refine ⟨47057500673002965462778811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31371667115335310308519207 47057500673002965462778811)
        ·
          refine ⟨70586251009504448194168217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47057500673002965462778811 70586251009504448194168217)
          ·
            refine ⟨52939688257128336145626163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70586251009504448194168217 52939688257128336145626163)
            ·
              refine ⟨79409532385692504218439245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52939688257128336145626163 79409532385692504218439245)
              ·
                refine ⟨29778574644634689081914717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79409532385692504218439245 29778574644634689081914717)
                ·
                  refine ⟨11166965491738008405718019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29778574644634689081914717 11166965491738008405718019)
                  ·
                    refine ⟨16750448237607012608577029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11166965491738008405718019 16750448237607012608577029)
                    ·
                      refine ⟨3140709044551314864108193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16750448237607012608577029 3140709044551314864108193)
                      ·
                        rfl

theorem cell23_6116509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6116509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116509 prefixEnd_6116509 := by exact prefixLift 6116509
  have htrace : WordTrace (prefixWord ++ tailWord_6116509) baseStart_6116509 baseEnd_6116509 := by
    simpa [prefixWord, tailWord_6116509, baseEnd_6116509] using wordTrace_append hprefix tailTrace_6116509
  have hstable : (prefixWord ++ tailWord_6116509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116509).length < 2 ^ (prefixWord ++ tailWord_6116509).sum := by decide
  have hdescent : baseEnd_6116509 < baseStart_6116509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116559 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_6116559 : Nat := 118140960795 + 6116559 * 2 ^ 59
def prefixEnd_6116559 : Nat := 4983230072969 + 3 ^ 40 * 6116559 * 2
def baseEnd_6116559 : Nat := 3140734718584039668482963

theorem tailTrace_6116559 : CollatzResearch.WordTrace tailWord_6116559 prefixEnd_6116559 3140734718584039668482963 := by
  unfold tailWord_6116559
  simp only [CollatzResearch.WordTrace]
  refine ⟨223089234247758842955456731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148726156165172561970304487 223089234247758842955456731)
  ·
    refine ⟨334633851371638264433185097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223089234247758842955456731 334633851371638264433185097)
    ·
      refine ⟨250975388528728698324888823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334633851371638264433185097 250975388528728698324888823)
      ·
        refine ⟨376463082793093047487333235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250975388528728698324888823 376463082793093047487333235)
        ·
          refine ⟨564694624189639571230999853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376463082793093047487333235 564694624189639571230999853)
          ·
            refine ⟨211760484071114839211624945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564694624189639571230999853 211760484071114839211624945)
            ·
              refine ⟨158820363053336129408718709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211760484071114839211624945 158820363053336129408718709)
              ·
                refine ⟨14889409036250262132067379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158820363053336129408718709 14889409036250262132067379)
                ·
                  refine ⟨22334113554375393198101069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14889409036250262132067379 22334113554375393198101069)
                  ·
                    refine ⟨8375292582890772449287901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22334113554375393198101069 8375292582890772449287901)
                    ·
                      refine ⟨3140734718584039668482963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375292582890772449287901 3140734718584039668482963)
                      ·
                        rfl

theorem cell23_6116559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_6116559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116559 prefixEnd_6116559 := by exact prefixLift 6116559
  have htrace : WordTrace (prefixWord ++ tailWord_6116559) baseStart_6116559 baseEnd_6116559 := by
    simpa [prefixWord, tailWord_6116559, baseEnd_6116559] using wordTrace_append hprefix tailTrace_6116559
  have hstable : (prefixWord ++ tailWord_6116559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116559).length < 2 ^ (prefixWord ++ tailWord_6116559).sum := by decide
  have hdescent : baseEnd_6116559 < baseStart_6116559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116576 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_6116576 : Nat := 118140960795 + 6116576 * 2 ^ 59
def prefixEnd_6116576 : Nat := 4983230072969 + 3 ^ 40 * 6116576 * 2
def baseEnd_6116576 : Nat := 3140743447755166101970385

theorem tailTrace_6116576 : CollatzResearch.WordTrace tailWord_6116576 prefixEnd_6116576 3140743447755166101970385 := by
  unfold tailWord_6116576
  simp only [CollatzResearch.WordTrace]
  refine ⟨111544927144348627429412791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148726569525798169905883721 111544927144348627429412791)
  ·
    refine ⟨167317390716522941144119187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111544927144348627429412791 167317390716522941144119187)
    ·
      refine ⟨250976086074784411716178781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167317390716522941144119187 250976086074784411716178781)
      ·
        refine ⟨94116032278044154393567043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250976086074784411716178781 94116032278044154393567043)
        ·
          refine ⟨141174048417066231590350565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94116032278044154393567043 141174048417066231590350565)
          ·
            refine ⟨26470134078199918423190731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141174048417066231590350565 26470134078199918423190731)
            ·
              refine ⟨39705201117299877634786097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26470134078199918423190731 39705201117299877634786097)
              ·
                refine ⟨29778900837974908226089573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39705201117299877634786097 29778900837974908226089573)
                ·
                  refine ⟨5583543907120295292391795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29778900837974908226089573 5583543907120295292391795)
                  ·
                    refine ⟨8375315860680442938587693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583543907120295292391795 8375315860680442938587693)
                    ·
                      refine ⟨3140743447755166101970385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375315860680442938587693 3140743447755166101970385)
                      ·
                        rfl

theorem cell23_6116576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_6116576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116576 prefixEnd_6116576 := by exact prefixLift 6116576
  have htrace : WordTrace (prefixWord ++ tailWord_6116576) baseStart_6116576 baseEnd_6116576 := by
    simpa [prefixWord, tailWord_6116576, baseEnd_6116576] using wordTrace_append hprefix tailTrace_6116576
  have hstable : (prefixWord ++ tailWord_6116576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116576).length < 2 ^ (prefixWord ++ tailWord_6116576).sum := by decide
  have hdescent : baseEnd_6116576 < baseStart_6116576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116577 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_6116577 : Nat := 118140960795 + 6116577 * 2 ^ 59
def prefixEnd_6116577 : Nat := 4983230072969 + 3 ^ 40 * 6116577 * 2
def baseEnd_6116577 : Nat := 3140743961235820598057881

theorem tailTrace_6116577 : CollatzResearch.WordTrace tailWord_6116577 prefixEnd_6116577 3140743961235820598057881 := by
  unfold tailWord_6116577
  simp only [CollatzResearch.WordTrace]
  refine ⟨223089890761693632029611985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148726593841129088019741323 223089890761693632029611985)
  ·
    refine ⟨167317418071270224022208989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223089890761693632029611985 167317418071270224022208989)
    ·
      refine ⟨62744031776726334008328371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167317418071270224022208989 62744031776726334008328371)
      ·
        refine ⟨94116047665089501012492557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62744031776726334008328371 94116047665089501012492557)
        ·
          refine ⟨35293517874408562879684709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94116047665089501012492557 35293517874408562879684709)
          ·
            refine ⟨6617534601451605539940883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35293517874408562879684709 6617534601451605539940883)
            ·
              refine ⟨9926301902177408309911325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617534601451605539940883 9926301902177408309911325)
              ·
                refine ⟨3722363213316528116216747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9926301902177408309911325 3722363213316528116216747)
                ·
                  refine ⟨5583544819974792174325121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722363213316528116216747 5583544819974792174325121)
                  ·
                    refine ⟨4187658614981094130743841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583544819974792174325121 4187658614981094130743841)
                    ·
                      refine ⟨3140743961235820598057881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187658614981094130743841 3140743961235820598057881)
                      ·
                        rfl

theorem cell23_6116577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_6116577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116577 prefixEnd_6116577 := by exact prefixLift 6116577
  have htrace : WordTrace (prefixWord ++ tailWord_6116577) baseStart_6116577 baseEnd_6116577 := by
    simpa [prefixWord, tailWord_6116577, baseEnd_6116577] using wordTrace_append hprefix tailTrace_6116577
  have hstable : (prefixWord ++ tailWord_6116577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116577).length < 2 ^ (prefixWord ++ tailWord_6116577).sum := by decide
  have hdescent : baseEnd_6116577 < baseStart_6116577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116594 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6116594 : Nat := 118140960795 + 6116594 * 2 ^ 59
def prefixEnd_6116594 : Nat := 4983230072969 + 3 ^ 40 * 6116594 * 2
def baseEnd_6116594 : Nat := 3140752690406947031545303

theorem tailTrace_6116594 : CollatzResearch.WordTrace tailWord_6116594 prefixEnd_6116594 3140752690406947031545303 := by
  unfold tailWord_6116594
  simp only [CollatzResearch.WordTrace]
  refine ⟨55772627700658010983245209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148727007201754695955320557 55772627700658010983245209)
  ·
    refine ⟨41829470775493508237433907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55772627700658010983245209 41829470775493508237433907)
    ·
      refine ⟨62744206163240262356150861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41829470775493508237433907 62744206163240262356150861)
      ·
        refine ⟨23529077311215098383556573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62744206163240262356150861 23529077311215098383556573)
        ·
          refine ⟨8823403991705661893833715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23529077311215098383556573 8823403991705661893833715)
          ·
            refine ⟨13235105987558492840750573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823403991705661893833715 13235105987558492840750573)
            ·
              refine ⟨4963164745334434815281465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235105987558492840750573 4963164745334434815281465)
              ·
                refine ⟨3722373559000826111461099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963164745334434815281465 3722373559000826111461099)
                ·
                  refine ⟨5583560338501239167191649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722373559000826111461099 5583560338501239167191649)
                  ·
                    refine ⟨4187670253875929375393737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583560338501239167191649 4187670253875929375393737)
                    ·
                      refine ⟨3140752690406947031545303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187670253875929375393737 3140752690406947031545303)
                      ·
                        rfl

theorem cell23_6116594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6116594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116594 prefixEnd_6116594 := by exact prefixLift 6116594
  have htrace : WordTrace (prefixWord ++ tailWord_6116594) baseStart_6116594 baseEnd_6116594 := by
    simpa [prefixWord, tailWord_6116594, baseEnd_6116594] using wordTrace_append hprefix tailTrace_6116594
  have hstable : (prefixWord ++ tailWord_6116594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116594).length < 2 ^ (prefixWord ++ tailWord_6116594).sum := by decide
  have hdescent : baseEnd_6116594 < baseStart_6116594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116619 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_6116619 : Nat := 118140960795 + 6116619 * 2 ^ 59
def prefixEnd_6116619 : Nat := 4983230072969 + 3 ^ 40 * 6116619 * 2
def baseEnd_6116619 : Nat := 3140765527423309433732687

theorem tailTrace_6116619 : CollatzResearch.WordTrace tailWord_6116619 prefixEnd_6116619 3140765527423309433732687 := by
  unfold tailWord_6116619
  simp only [CollatzResearch.WordTrace]
  refine ⟨223091422627541473202640911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148727615085027648801760607 223091422627541473202640911)
  ·
    refine ⟨334637133941312209803961367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223091422627541473202640911 334637133941312209803961367)
    ·
      refine ⟨501955700911968314705942051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334637133941312209803961367 501955700911968314705942051)
      ·
        refine ⟨752933551367952472058913077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501955700911968314705942051 752933551367952472058913077)
        ·
          refine ⟨70587520440745544255523101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 752933551367952472058913077 70587520440745544255523101)
          ·
            refine ⟨26470320165279579095821163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70587520440745544255523101 26470320165279579095821163)
            ·
              refine ⟨39705480247919368643731745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26470320165279579095821163 39705480247919368643731745)
              ·
                refine ⟨29779110185939526482798809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39705480247919368643731745 29779110185939526482798809)
                ·
                  refine ⟨22334332639454644862099107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29779110185939526482798809 22334332639454644862099107)
                  ·
                    refine ⟨33501498959181967293148661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22334332639454644862099107 33501498959181967293148661)
                    ·
                      refine ⟨3140765527423309433732687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33501498959181967293148661 3140765527423309433732687)
                      ·
                        rfl

theorem cell23_6116619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_6116619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116619 prefixEnd_6116619 := by exact prefixLift 6116619
  have htrace : WordTrace (prefixWord ++ tailWord_6116619) baseStart_6116619 baseEnd_6116619 := by
    simpa [prefixWord, tailWord_6116619, baseEnd_6116619] using wordTrace_append hprefix tailTrace_6116619
  have hstable : (prefixWord ++ tailWord_6116619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116619).length < 2 ^ (prefixWord ++ tailWord_6116619).sum := by decide
  have hdescent : baseEnd_6116619 < baseStart_6116619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116620 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_6116620 : Nat := 118140960795 + 6116620 * 2 ^ 59
def prefixEnd_6116620 : Nat := 4983230072969 + 3 ^ 40 * 6116620 * 2
def baseEnd_6116620 : Nat := 3140766040903963929820183

theorem tailTrace_6116620 : CollatzResearch.WordTrace tailWord_6116620 prefixEnd_6116620 3140766040903963929820183 := by
  unfold tailWord_6116620
  simp only [CollatzResearch.WordTrace]
  refine ⟨111545729550268925186713657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148727639400358566915618209 111545729550268925186713657)
  ·
    refine ⟨83659297162701693890035243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111545729550268925186713657 83659297162701693890035243)
    ·
      refine ⟨125488945744052540835052865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83659297162701693890035243 125488945744052540835052865)
      ·
        refine ⟨94116709308039405626289649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125488945744052540835052865 94116709308039405626289649)
        ·
          refine ⟨70587531981029554219717237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94116709308039405626289649 70587531981029554219717237)
          ·
            refine ⟨6617581123221520708098491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70587531981029554219717237 6617581123221520708098491)
            ·
              refine ⟨9926371684832281062147737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617581123221520708098491 9926371684832281062147737)
              ·
                refine ⟨7444778763624210796610803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9926371684832281062147737 7444778763624210796610803)
                ·
                  refine ⟨11167168145436316194916205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444778763624210796610803 11167168145436316194916205)
                  ·
                    refine ⟨4187688054538618573093577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11167168145436316194916205 4187688054538618573093577)
                    ·
                      refine ⟨3140766040903963929820183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187688054538618573093577 3140766040903963929820183)
                      ·
                        rfl

theorem cell23_6116620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_6116620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116620 prefixEnd_6116620 := by exact prefixLift 6116620
  have htrace : WordTrace (prefixWord ++ tailWord_6116620) baseStart_6116620 baseEnd_6116620 := by
    simpa [prefixWord, tailWord_6116620, baseEnd_6116620] using wordTrace_append hprefix tailTrace_6116620
  have hstable : (prefixWord ++ tailWord_6116620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116620).length < 2 ^ (prefixWord ++ tailWord_6116620).sum := by decide
  have hdescent : baseEnd_6116620 < baseStart_6116620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116629 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_6116629 : Nat := 118140960795 + 6116629 * 2 ^ 59
def prefixEnd_6116629 : Nat := 4983230072969 + 3 ^ 40 * 6116629 * 2
def baseEnd_6116629 : Nat := 3140770662229854394607641

theorem tailTrace_6116629 : CollatzResearch.WordTrace tailWord_6116629 prefixEnd_6116629 3140770662229854394607641 := by
  unfold tailWord_6116629
  simp only [CollatzResearch.WordTrace]
  refine ⟨223091787357505244910504941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148727858238336829940336627 223091787357505244910504941)
  ·
    refine ⟨83659420259064466841439353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223091787357505244910504941 83659420259064466841439353)
    ·
      refine ⟨62744565194298350131079515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83659420259064466841439353 62744565194298350131079515)
      ·
        refine ⟨94116847791447525196619273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62744565194298350131079515 94116847791447525196619273)
        ·
          refine ⟨70587635843585643897464455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94116847791447525196619273 70587635843585643897464455)
          ·
            refine ⟨105881453765378465846196683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70587635843585643897464455 105881453765378465846196683)
            ·
              refine ⟨158822180648067698769295025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105881453765378465846196683 158822180648067698769295025)
              ·
                refine ⟨119116635486050774076971269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158822180648067698769295025 119116635486050774076971269)
                ·
                  refine ⟨22334369153634520139432113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119116635486050774076971269 22334369153634520139432113)
                  ·
                    refine ⟨16750776865225890104574085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22334369153634520139432113 16750776865225890104574085)
                    ·
                      refine ⟨3140770662229854394607641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16750776865225890104574085 3140770662229854394607641)
                      ·
                        rfl

theorem cell23_6116629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_6116629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116629 prefixEnd_6116629 := by exact prefixLift 6116629
  have htrace : WordTrace (prefixWord ++ tailWord_6116629) baseStart_6116629 baseEnd_6116629 := by
    simpa [prefixWord, tailWord_6116629, baseEnd_6116629] using wordTrace_append hprefix tailTrace_6116629
  have hstable : (prefixWord ++ tailWord_6116629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116629).length < 2 ^ (prefixWord ++ tailWord_6116629).sum := by decide
  have hdescent : baseEnd_6116629 < baseStart_6116629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116637 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6116637 : Nat := 118140960795 + 6116637 * 2 ^ 59
def prefixEnd_6116637 : Nat := 4983230072969 + 3 ^ 40 * 6116637 * 2
def baseEnd_6116637 : Nat := 3140774770075090363307605

theorem tailTrace_6116637 : CollatzResearch.WordTrace tailWord_6116637 prefixEnd_6116637 3140774770075090363307605 := by
  unfold tailWord_6116637
  simp only [CollatzResearch.WordTrace]
  refine ⟨223092079141476262276796165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148728052760984174851197443 223092079141476262276796165)
  ·
    refine ⟨41829764839026799176899281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223092079141476262276796165 41829764839026799176899281)
    ·
      refine ⟨31372323629270099382674461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41829764839026799176899281 31372323629270099382674461)
      ·
        refine ⟨11764621360976287268502923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31372323629270099382674461 11764621360976287268502923)
        ·
          refine ⟨17646932041464430902754385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764621360976287268502923 17646932041464430902754385)
          ·
            refine ⟨13235199031098323177065789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17646932041464430902754385 13235199031098323177065789)
            ·
              refine ⟨4963199636661871191399671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235199031098323177065789 4963199636661871191399671)
              ·
                refine ⟨7444799454992806787099507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963199636661871191399671 7444799454992806787099507)
                ·
                  refine ⟨11167199182489210180649261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444799454992806787099507 11167199182489210180649261)
                  ·
                    refine ⟨4187699693433453817743473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11167199182489210180649261 4187699693433453817743473)
                    ·
                      refine ⟨3140774770075090363307605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187699693433453817743473 3140774770075090363307605)
                      ·
                        rfl

theorem cell23_6116637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6116637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116637 prefixEnd_6116637 := by exact prefixLift 6116637
  have htrace : WordTrace (prefixWord ++ tailWord_6116637) baseStart_6116637 baseEnd_6116637 := by
    simpa [prefixWord, tailWord_6116637, baseEnd_6116637] using wordTrace_append hprefix tailTrace_6116637
  have hstable : (prefixWord ++ tailWord_6116637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116637).length < 2 ^ (prefixWord ++ tailWord_6116637).sum := by decide
  have hdescent : baseEnd_6116637 < baseStart_6116637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116653 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6116653 : Nat := 118140960795 + 6116653 * 2 ^ 59
def prefixEnd_6116653 : Nat := 4983230072969 + 3 ^ 40 * 6116653 * 2
def baseEnd_6116653 : Nat := 3140782985765562300707531

theorem tailTrace_6116653 : CollatzResearch.WordTrace tailWord_6116653 prefixEnd_6116653 3140782985765562300707531 := by
  unfold tailWord_6116653
  simp only [CollatzResearch.WordTrace]
  refine ⟨223092662709418297009378613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148728441806278864672919075 223092662709418297009378613)
  ·
    refine ⟨20914937129007965344629245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223092662709418297009378613 20914937129007965344629245)
    ·
      refine ⟨7843101423377987004235967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20914937129007965344629245 7843101423377987004235967)
      ·
        refine ⟨11764652135066980506353951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843101423377987004235967 11764652135066980506353951)
        ·
          refine ⟨17646978202600470759530927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764652135066980506353951 17646978202600470759530927)
          ·
            refine ⟨26470467303900706139296391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17646978202600470759530927 26470467303900706139296391)
            ·
              refine ⟨39705700955851059208944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26470467303900706139296391 39705700955851059208944587)
              ·
                refine ⟨59558551433776588813416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39705700955851059208944587 59558551433776588813416881)
                ·
                  refine ⟨44668913575332441610062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59558551433776588813416881 44668913575332441610062661)
                  ·
                    refine ⟨8375421295374832801886749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44668913575332441610062661 8375421295374832801886749)
                    ·
                      refine ⟨3140782985765562300707531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375421295374832801886749 3140782985765562300707531)
                      ·
                        rfl

theorem cell23_6116653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6116653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116653 prefixEnd_6116653 := by exact prefixLift 6116653
  have htrace : WordTrace (prefixWord ++ tailWord_6116653) baseStart_6116653 baseEnd_6116653 := by
    simpa [prefixWord, tailWord_6116653, baseEnd_6116653] using wordTrace_append hprefix tailTrace_6116653
  have hstable : (prefixWord ++ tailWord_6116653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116653).length < 2 ^ (prefixWord ++ tailWord_6116653).sum := by decide
  have hdescent : baseEnd_6116653 < baseStart_6116653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116656 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 5]
def baseStart_6116656 : Nat := 118140960795 + 6116656 * 2 ^ 59
def prefixEnd_6116656 : Nat := 4983230072969 + 3 ^ 40 * 6116656 * 2
def baseEnd_6116656 : Nat := 348976058467502865441113

theorem tailTrace_6116656 : CollatzResearch.WordTrace tailWord_6116656 prefixEnd_6116656 348976058467502865441113 := by
  unfold tailWord_6116656
  simp only [CollatzResearch.WordTrace]
  refine ⟨111546386064203714260868911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148728514752271619014491881 111546386064203714260868911)
  ·
    refine ⟨167319579096305571391303367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111546386064203714260868911 167319579096305571391303367)
    ·
      refine ⟨250979368644458357086955051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167319579096305571391303367 250979368644458357086955051)
      ·
        refine ⟨376469052966687535630432577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250979368644458357086955051 376469052966687535630432577)
        ·
          refine ⟨282351789725015651722824433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376469052966687535630432577 282351789725015651722824433)
          ·
            refine ⟨211763842293761738792118325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282351789725015651722824433 211763842293761738792118325)
            ·
              refine ⟨19852860215040163011761093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211763842293761738792118325 19852860215040163011761093)
              ·
                refine ⟨3722411290320030564705205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19852860215040163011761093 3722411290320030564705205)
                ·
                  refine ⟨348976058467502865441113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722411290320030564705205 348976058467502865441113)
                  ·
                    rfl

theorem cell23_6116656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 5].length) (baseStart_6116656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116656 prefixEnd_6116656 := by exact prefixLift 6116656
  have htrace : WordTrace (prefixWord ++ tailWord_6116656) baseStart_6116656 baseEnd_6116656 := by
    simpa [prefixWord, tailWord_6116656, baseEnd_6116656] using wordTrace_append hprefix tailTrace_6116656
  have hstable : (prefixWord ++ tailWord_6116656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116656).length < 2 ^ (prefixWord ++ tailWord_6116656).sum := by decide
  have hdescent : baseEnd_6116656 < baseStart_6116656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116666 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_6116666 : Nat := 118140960795 + 6116666 * 2 ^ 59
def prefixEnd_6116666 : Nat := 4983230072969 + 3 ^ 40 * 6116666 * 2
def baseEnd_6116666 : Nat := 3140789661014070749844971

theorem tailTrace_6116666 : CollatzResearch.WordTrace tailWord_6116666 prefixEnd_6116666 3140789661014070749844971 := by
  unfold tailWord_6116666
  simp only [CollatzResearch.WordTrace]
  refine ⟨55773284214592800057400463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148728757905580800153067901 55773284214592800057400463)
  ·
    refine ⟨83659926321889200086100695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55773284214592800057400463 83659926321889200086100695)
    ·
      refine ⟨125489889482833800129151043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83659926321889200086100695 125489889482833800129151043)
      ·
        refine ⟨188234834224250700193726565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125489889482833800129151043 188234834224250700193726565)
        ·
          refine ⟨35294031417047006286323731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188234834224250700193726565 35294031417047006286323731)
          ·
            refine ⟨52941047125570509429485597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35294031417047006286323731 52941047125570509429485597)
            ·
              refine ⟨19852892672088941036057099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52941047125570509429485597 19852892672088941036057099)
              ·
                refine ⟨29779339008133411554085649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19852892672088941036057099 29779339008133411554085649)
                ·
                  refine ⟨22334504256100058665564237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29779339008133411554085649 22334504256100058665564237)
                  ·
                    refine ⟨8375439096037521999586589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22334504256100058665564237 8375439096037521999586589)
                    ·
                      refine ⟨3140789661014070749844971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375439096037521999586589 3140789661014070749844971)
                      ·
                        rfl

theorem cell23_6116666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_6116666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116666 prefixEnd_6116666 := by exact prefixLift 6116666
  have htrace : WordTrace (prefixWord ++ tailWord_6116666) baseStart_6116666 baseEnd_6116666 := by
    simpa [prefixWord, tailWord_6116666, baseEnd_6116666] using wordTrace_append hprefix tailTrace_6116666
  have hstable : (prefixWord ++ tailWord_6116666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116666).length < 2 ^ (prefixWord ++ tailWord_6116666).sum := by decide
  have hdescent : baseEnd_6116666 < baseStart_6116666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116719 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_6116719 : Nat := 118140960795 + 6116719 * 2 ^ 59
def prefixEnd_6116719 : Nat := 4983230072969 + 3 ^ 40 * 6116719 * 2
def baseEnd_6116719 : Nat := 3140816875488759042482227

theorem tailTrace_6116719 : CollatzResearch.WordTrace tailWord_6116719 prefixEnd_6116719 3140816875488759042482227 := by
  unfold tailWord_6116719
  simp only [CollatzResearch.WordTrace]
  refine ⟨223095069927179190281281211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148730046618119460187520807 223095069927179190281281211)
  ·
    refine ⟨334642604890768785421921817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223095069927179190281281211 334642604890768785421921817)
    ·
      refine ⟨250981953668076589066441363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334642604890768785421921817 250981953668076589066441363)
      ·
        refine ⟨376472930502114883599662045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250981953668076589066441363 376472930502114883599662045)
        ·
          refine ⟨141177348938293081349873267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376472930502114883599662045 141177348938293081349873267)
          ·
            refine ⟨211766023407439622024809901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141177348938293081349873267 211766023407439622024809901)
            ·
              refine ⟨79412258777789858259303713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211766023407439622024809901 79412258777789858259303713)
              ·
                refine ⟨59559194083342393694477785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79412258777789858259303713 59559194083342393694477785)
                ·
                  refine ⟨44669395562506795270858339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59559194083342393694477785 44669395562506795270858339)
                  ·
                    refine ⟨67004093343760192906287509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44669395562506795270858339 67004093343760192906287509)
                    ·
                      refine ⟨3140816875488759042482227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67004093343760192906287509 3140816875488759042482227)
                      ·
                        rfl

theorem cell23_6116719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_6116719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116719 prefixEnd_6116719 := by exact prefixLift 6116719
  have htrace : WordTrace (prefixWord ++ tailWord_6116719) baseStart_6116719 baseEnd_6116719 := by
    simpa [prefixWord, tailWord_6116719, baseEnd_6116719] using wordTrace_append hprefix tailTrace_6116719
  have hstable : (prefixWord ++ tailWord_6116719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116719).length < 2 ^ (prefixWord ++ tailWord_6116719).sum := by decide
  have hdescent : baseEnd_6116719 < baseStart_6116719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116760 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6116760 : Nat := 118140960795 + 6116760 * 2 ^ 59
def prefixEnd_6116760 : Nat := 4983230072969 + 3 ^ 40 * 6116760 * 2
def baseEnd_6116760 : Nat := 3140837928195593382069539

theorem tailTrace_6116760 : CollatzResearch.WordTrace tailWord_6116760 prefixEnd_6116760 3140837928195593382069539 := by
  unfold tailWord_6116760
  simp only [CollatzResearch.WordTrace]
  refine ⟨111548282660015327141761867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148731043546687102855682489 111548282660015327141761867)
  ·
    refine ⟨167322423990022990712642801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111548282660015327141761867 167322423990022990712642801)
    ·
      refine ⟨125491817992517243034482101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167322423990022990712642801 125491817992517243034482101)
      ·
        refine ⟨11764857936798491534482697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125491817992517243034482101 11764857936798491534482697)
        ·
          refine ⟨8823643452598868650862023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11764857936798491534482697 8823643452598868650862023)
          ·
            refine ⟨13235465178898302976293035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823643452598868650862023 13235465178898302976293035)
            ·
              refine ⟨19853197768347454464439553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13235465178898302976293035 19853197768347454464439553)
              ·
                refine ⟨14889898326260590848329665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19853197768347454464439553 14889898326260590848329665)
                ·
                  refine ⟨11167423744695443136247249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14889898326260590848329665 11167423744695443136247249)
                  ·
                    refine ⟨8375567808521582352185437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11167423744695443136247249 8375567808521582352185437)
                    ·
                      refine ⟨3140837928195593382069539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375567808521582352185437 3140837928195593382069539)
                      ·
                        rfl

theorem cell23_6116760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6116760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116760 prefixEnd_6116760 := by exact prefixLift 6116760
  have htrace : WordTrace (prefixWord ++ tailWord_6116760) baseStart_6116760 baseEnd_6116760 := by
    simpa [prefixWord, tailWord_6116760, baseEnd_6116760] using wordTrace_append hprefix tailTrace_6116760
  have hstable : (prefixWord ++ tailWord_6116760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116760).length < 2 ^ (prefixWord ++ tailWord_6116760).sum := by decide
  have hdescent : baseEnd_6116760 < baseStart_6116760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116767 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 1, 4]
def baseStart_6116767 : Nat := 118140960795 + 6116767 * 2 ^ 59
def prefixEnd_6116767 : Nat := 4983230072969 + 3 ^ 40 * 6116767 * 2
def baseEnd_6116767 : Nat := 1046947174186724951560669

theorem tailTrace_6116767 : CollatzResearch.WordTrace tailWord_6116767 prefixEnd_6116767 1046947174186724951560669 := by
  unfold tailWord_6116767
  simp only [CollatzResearch.WordTrace]
  refine ⟨223096820631005294479028555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148731213754003529652685703 223096820631005294479028555)
  ·
    refine ⟨334645230946507941718542833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223096820631005294479028555 334645230946507941718542833)
    ·
      refine ⟨250983923209880956288907125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334645230946507941718542833 250983923209880956288907125)
      ·
        refine ⟨23529742800926339652085043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250983923209880956288907125 23529742800926339652085043)
        ·
          refine ⟨35294614201389509478127565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23529742800926339652085043 35294614201389509478127565)
          ·
            refine ⟨13235480325521066054297837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35294614201389509478127565 13235480325521066054297837)
            ·
              refine ⟨4963305122070399770361689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235480325521066054297837 4963305122070399770361689)
              ·
                refine ⟨3722478841552799827771267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963305122070399770361689 3722478841552799827771267)
                ·
                  refine ⟨5583718262329199741656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722478841552799827771267 5583718262329199741656901)
                  ·
                    refine ⟨1046947174186724951560669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5583718262329199741656901 1046947174186724951560669)
                    ·
                      rfl

theorem cell23_6116767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_6116767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116767 prefixEnd_6116767 := by exact prefixLift 6116767
  have htrace : WordTrace (prefixWord ++ tailWord_6116767) baseStart_6116767 baseEnd_6116767 := by
    simpa [prefixWord, tailWord_6116767, baseEnd_6116767] using wordTrace_append hprefix tailTrace_6116767
  have hstable : (prefixWord ++ tailWord_6116767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116767).length < 2 ^ (prefixWord ++ tailWord_6116767).sum := by decide
  have hdescent : baseEnd_6116767 < baseStart_6116767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116773 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_6116773 : Nat := 118140960795 + 6116773 * 2 ^ 59
def prefixEnd_6116773 : Nat := 4983230072969 + 3 ^ 40 * 6116773 * 2
def baseEnd_6116773 : Nat := 3140844603444101831206979

theorem tailTrace_6116773 : CollatzResearch.WordTrace tailWord_6116773 prefixEnd_6116773 3140844603444101831206979 := by
  unfold tailWord_6116773
  simp only [CollatzResearch.WordTrace]
  refine ⟨223097039468983557503746973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148731359645989038335831315 223097039468983557503746973)
  ·
    refine ⟨83661389800868834063905115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223097039468983557503746973 83661389800868834063905115)
    ·
      refine ⟨125492084701303251095857673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83661389800868834063905115 125492084701303251095857673)
      ·
        refine ⟨94119063525977438321893255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125492084701303251095857673 94119063525977438321893255)
        ·
          refine ⟨141178595288966157482839883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94119063525977438321893255 141178595288966157482839883)
          ·
            refine ⟨211767892933449236224259825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141178595288966157482839883 211767892933449236224259825)
            ·
              refine ⟨158825919700086927168194869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211767892933449236224259825 158825919700086927168194869)
              ·
                refine ⟨14889929971883149422018269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158825919700086927168194869 14889929971883149422018269)
                ·
                  refine ⟨5583723739456181033256851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14889929971883149422018269 5583723739456181033256851)
                  ·
                    refine ⟨8375585609184271549885277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583723739456181033256851 8375585609184271549885277)
                    ·
                      refine ⟨3140844603444101831206979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375585609184271549885277 3140844603444101831206979)
                      ·
                        rfl

theorem cell23_6116773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_6116773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116773 prefixEnd_6116773 := by exact prefixLift 6116773
  have htrace : WordTrace (prefixWord ++ tailWord_6116773) baseStart_6116773 baseEnd_6116773 := by
    simpa [prefixWord, tailWord_6116773, baseEnd_6116773] using wordTrace_append hprefix tailTrace_6116773
  have hstable : (prefixWord ++ tailWord_6116773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116773).length < 2 ^ (prefixWord ++ tailWord_6116773).sum := by decide
  have hdescent : baseEnd_6116773 < baseStart_6116773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116793 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_6116793 : Nat := 118140960795 + 6116793 * 2 ^ 59
def prefixEnd_6116793 : Nat := 4983230072969 + 3 ^ 40 * 6116793 * 2
def baseEnd_6116793 : Nat := 1046951624352397250985629

theorem tailTrace_6116793 : CollatzResearch.WordTrace tailWord_6116793 prefixEnd_6116793 1046951624352397250985629 := by
  unfold tailWord_6116793
  simp only [CollatzResearch.WordTrace]
  refine ⟨223097768928911100919475033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148731845952607400612983355 223097768928911100919475033)
  ·
    refine ⟨167323326696683325689606275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223097768928911100919475033 167323326696683325689606275)
    ·
      refine ⟨250984990045024988534409413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167323326696683325689606275 250984990045024988534409413)
      ·
        refine ⟨47059685633442185350201765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250984990045024988534409413 47059685633442185350201765)
        ·
          refine ⟨8823691056270409753162831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47059685633442185350201765 8823691056270409753162831)
          ·
            refine ⟨13235536584405614629744247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823691056270409753162831 13235536584405614629744247)
            ·
              refine ⟨19853304876608421944616371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13235536584405614629744247 19853304876608421944616371)
              ·
                refine ⟨29779957314912632916924557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19853304876608421944616371 29779957314912632916924557)
                ·
                  refine ⟨11167483993092237343846709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29779957314912632916924557 11167483993092237343846709)
                  ·
                    refine ⟨1046951624352397250985629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11167483993092237343846709 1046951624352397250985629)
                    ·
                      rfl

theorem cell23_6116793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_6116793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116793 prefixEnd_6116793 := by exact prefixLift 6116793
  have htrace : WordTrace (prefixWord ++ tailWord_6116793) baseStart_6116793 baseEnd_6116793 := by
    simpa [prefixWord, tailWord_6116793, baseEnd_6116793] using wordTrace_append hprefix tailTrace_6116793
  have hstable : (prefixWord ++ tailWord_6116793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116793).length < 2 ^ (prefixWord ++ tailWord_6116793).sum := by decide
  have hdescent : baseEnd_6116793 < baseStart_6116793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116810 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_6116810 : Nat := 118140960795 + 6116810 * 2 ^ 59
def prefixEnd_6116810 : Nat := 4983230072969 + 3 ^ 40 * 6116810 * 2
def baseEnd_6116810 : Nat := 1046954534076106062148103

theorem tailTrace_6116810 : CollatzResearch.WordTrace tailWord_6116810 prefixEnd_6116810 1046954534076106062148103 := by
  unfold tailWord_6116810
  simp only [CollatzResearch.WordTrace]
  refine ⟨55774597242462378205710971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148732259313233008548562589 55774597242462378205710971)
  ·
    refine ⟨83661895863693567308566457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55774597242462378205710971 83661895863693567308566457)
    ·
      refine ⟨62746421897770175481424843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83661895863693567308566457 62746421897770175481424843)
      ·
        refine ⟨94119632846655263222137265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62746421897770175481424843 94119632846655263222137265)
        ·
          refine ⟨70589724634991447416602949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94119632846655263222137265 70589724634991447416602949)
          ·
            refine ⟨13235573369060896390613053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70589724634991447416602949 13235573369060896390613053)
            ·
              refine ⟨4963340013397836146479895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235573369060896390613053 4963340013397836146479895)
              ·
                refine ⟨7445010020096754219719843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963340013397836146479895 7445010020096754219719843)
                ·
                  refine ⟨11167515030145131329579765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445010020096754219719843 11167515030145131329579765)
                  ·
                    refine ⟨1046954534076106062148103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11167515030145131329579765 1046954534076106062148103)
                    ·
                      rfl

theorem cell23_6116810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_6116810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116810 prefixEnd_6116810 := by exact prefixLift 6116810
  have htrace : WordTrace (prefixWord ++ tailWord_6116810) baseStart_6116810 baseEnd_6116810 := by
    simpa [prefixWord, tailWord_6116810, baseEnd_6116810] using wordTrace_append hprefix tailTrace_6116810
  have hstable : (prefixWord ++ tailWord_6116810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116810).length < 2 ^ (prefixWord ++ tailWord_6116810).sum := by decide
  have hdescent : baseEnd_6116810 < baseStart_6116810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116833 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_6116833 : Nat := 118140960795 + 6116833 * 2 ^ 59
def prefixEnd_6116833 : Nat := 4983230072969 + 3 ^ 40 * 6116833 * 2
def baseEnd_6116833 : Nat := 3140875412283371596456703

theorem tailTrace_6116833 : CollatzResearch.WordTrace tailWord_6116833 prefixEnd_6116833 3140875412283371596456703 := by
  unfold tailWord_6116833
  simp only [CollatzResearch.WordTrace]
  refine ⟨223099227848766187750931153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148732818565844125167287435 223099227848766187750931153)
  ·
    refine ⟨167324420886574640813198365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223099227848766187750931153 167324420886574640813198365)
    ·
      refine ⟨62746657832465490304949387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167324420886574640813198365 62746657832465490304949387)
      ·
        refine ⟨94119986748698235457424081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62746657832465490304949387 94119986748698235457424081)
        ·
          refine ⟨70589990061523676593068061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94119986748698235457424081 70589990061523676593068061)
          ·
            refine ⟨26471246273071378722400523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70589990061523676593068061 26471246273071378722400523)
            ·
              refine ⟨39706869409607068083600785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26471246273071378722400523 39706869409607068083600785)
              ·
                refine ⟨29780152057205301062700589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39706869409607068083600785 29780152057205301062700589)
                ·
                  refine ⟨11167557021451987898512721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29780152057205301062700589 11167557021451987898512721)
                  ·
                    refine ⟨8375667766088990923884541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11167557021451987898512721 8375667766088990923884541)
                    ·
                      refine ⟨3140875412283371596456703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375667766088990923884541 3140875412283371596456703)
                      ·
                        rfl

theorem cell23_6116833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_6116833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116833 prefixEnd_6116833 := by exact prefixLift 6116833
  have htrace : WordTrace (prefixWord ++ tailWord_6116833) baseStart_6116833 baseEnd_6116833 := by
    simpa [prefixWord, tailWord_6116833, baseEnd_6116833] using wordTrace_append hprefix tailTrace_6116833
  have hstable : (prefixWord ++ tailWord_6116833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116833).length < 2 ^ (prefixWord ++ tailWord_6116833).sum := by decide
  have hdescent : baseEnd_6116833 < baseStart_6116833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116850 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6116850 : Nat := 118140960795 + 6116850 * 2 ^ 59
def prefixEnd_6116850 : Nat := 4983230072969 + 3 ^ 40 * 6116850 * 2
def baseEnd_6116850 : Nat := 3140884141454498029944125

theorem tailTrace_6116850 : CollatzResearch.WordTrace tailWord_6116850 prefixEnd_6116850 3140884141454498029944125 := by
  unfold tailWord_6116850
  simp only [CollatzResearch.WordTrace]
  refine ⟨55774961972426149913575001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148733231926469733102866669 55774961972426149913575001)
  ·
    refine ⟨41831221479319612435181251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55774961972426149913575001 41831221479319612435181251)
    ·
      refine ⟨62746832218979418652771877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41831221479319612435181251 62746832218979418652771877)
      ·
        refine ⟨11765031041058640997394727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62746832218979418652771877 11765031041058640997394727)
        ·
          refine ⟨17647546561587961496092091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765031041058640997394727 17647546561587961496092091)
          ·
            refine ⟨26471319842381942244138137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17647546561587961496092091 26471319842381942244138137)
            ·
              refine ⟨19853489881786456683103603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26471319842381942244138137 19853489881786456683103603)
              ·
                refine ⟨29780234822679685024655405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19853489881786456683103603 29780234822679685024655405)
                ·
                  refine ⟨11167588058504881884245777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29780234822679685024655405 11167588058504881884245777)
                  ·
                    refine ⟨8375691043878661413184333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11167588058504881884245777 8375691043878661413184333)
                    ·
                      refine ⟨3140884141454498029944125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375691043878661413184333 3140884141454498029944125)
                      ·
                        rfl

theorem cell23_6116850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6116850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116850 prefixEnd_6116850 := by exact prefixLift 6116850
  have htrace : WordTrace (prefixWord ++ tailWord_6116850) baseStart_6116850 baseEnd_6116850 := by
    simpa [prefixWord, tailWord_6116850, baseEnd_6116850] using wordTrace_append hprefix tailTrace_6116850
  have hstable : (prefixWord ++ tailWord_6116850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116850).length < 2 ^ (prefixWord ++ tailWord_6116850).sum := by decide
  have hdescent : baseEnd_6116850 < baseStart_6116850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116894 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6116894 : Nat := 118140960795 + 6116894 * 2 ^ 59
def prefixEnd_6116894 : Nat := 4983230072969 + 3 ^ 40 * 6116894 * 2
def baseEnd_6116894 : Nat := 3140906734603295857793923

theorem tailTrace_6116894 : CollatzResearch.WordTrace tailWord_6116894 prefixEnd_6116894 3140906734603295857793923 := by
  unfold tailWord_6116894
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887681587693149396112717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148734301801030130112601157 27887681587693149396112717)
  ·
    refine ⟨10457880595384931023542269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27887681587693149396112717 10457880595384931023542269)
    ·
      refine ⟨3921705223269349133828351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10457880595384931023542269 3921705223269349133828351)
      ·
        refine ⟨5882557834904023700742527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921705223269349133828351 5882557834904023700742527)
        ·
          refine ⟨8823836752356035551113791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882557834904023700742527 8823836752356035551113791)
          ·
            refine ⟨13235755128534053326670687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823836752356035551113791 13235755128534053326670687)
            ·
              refine ⟨19853632692801079990006031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13235755128534053326670687 19853632692801079990006031)
              ·
                refine ⟨29780449039201619985009047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19853632692801079990006031 29780449039201619985009047)
                ·
                  refine ⟨44670673558802429977513571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29780449039201619985009047 44670673558802429977513571)
                  ·
                    refine ⟨67006010338203644966270357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44670673558802429977513571 67006010338203644966270357)
                    ·
                      refine ⟨3140906734603295857793923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67006010338203644966270357 3140906734603295857793923)
                      ·
                        rfl

theorem cell23_6116894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6116894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116894 prefixEnd_6116894 := by exact prefixLift 6116894
  have htrace : WordTrace (prefixWord ++ tailWord_6116894) baseStart_6116894 baseEnd_6116894 := by
    simpa [prefixWord, tailWord_6116894, baseEnd_6116894] using wordTrace_append hprefix tailTrace_6116894
  have hstable : (prefixWord ++ tailWord_6116894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116894).length < 2 ^ (prefixWord ++ tailWord_6116894).sum := by decide
  have hdescent : baseEnd_6116894 < baseStart_6116894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6116953 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_6116953 : Nat := 118140960795 + 6116953 * 2 ^ 59
def prefixEnd_6116953 : Nat := 4983230072969 + 3 ^ 40 * 6116953 * 2
def baseEnd_6116953 : Nat := 3140937029961911126956151

theorem tailTrace_6116953 : CollatzResearch.WordTrace tailWord_6116953 prefixEnd_6116953 3140937029961911126956151 := by
  unfold tailWord_6116953
  simp only [CollatzResearch.WordTrace]
  refine ⟨223103604608331448245299513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148735736405554298830199675 223103604608331448245299513)
  ·
    refine ⟨167327703456248586183974635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223103604608331448245299513 167327703456248586183974635)
    ·
      refine ⟨250991555184372879275961953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167327703456248586183974635 250991555184372879275961953)
      ·
        refine ⟨188243666388279659456971465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250991555184372879275961953 188243666388279659456971465)
        ·
          refine ⟨141182749791209744592728599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188243666388279659456971465 141182749791209744592728599)
          ·
            refine ⟨211774124686814616889092899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141182749791209744592728599 211774124686814616889092899)
            ·
              refine ⟨317661187030221925333639349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211774124686814616889092899 317661187030221925333639349)
              ·
                refine ⟨29780736284083305500028689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317661187030221925333639349 29780736284083305500028689)
                ·
                  refine ⟨22335552213062479125021517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29780736284083305500028689 22335552213062479125021517)
                  ·
                    refine ⟨8375832079898429671883069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22335552213062479125021517 8375832079898429671883069)
                    ·
                      refine ⟨3140937029961911126956151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8375832079898429671883069 3140937029961911126956151)
                      ·
                        rfl

theorem cell23_6116953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_6116953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6116953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6116953 prefixEnd_6116953 := by exact prefixLift 6116953
  have htrace : WordTrace (prefixWord ++ tailWord_6116953) baseStart_6116953 baseEnd_6116953 := by
    simpa [prefixWord, tailWord_6116953, baseEnd_6116953] using wordTrace_append hprefix tailTrace_6116953
  have hstable : (prefixWord ++ tailWord_6116953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6116953).length < 2 ^ (prefixWord ++ tailWord_6116953).sum := by decide
  have hdescent : baseEnd_6116953 < baseStart_6116953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6116953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117050 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_6117050 : Nat := 118140960795 + 6117050 * 2 ^ 59
def prefixEnd_6117050 : Nat := 4983230072969 + 3 ^ 40 * 6117050 * 2
def baseEnd_6117050 : Nat := 348998537509488583049245

theorem tailTrace_6117050 : CollatzResearch.WordTrace tailWord_6117050 prefixEnd_6117050 348998537509488583049245 := by
  unfold tailWord_6117050
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776785622245008452895151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148738094992653355874387069 55776785622245008452895151)
  ·
    refine ⟨83665178433367512679342727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55776785622245008452895151 83665178433367512679342727)
    ·
      refine ⟨125497767650051269019014091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83665178433367512679342727 125497767650051269019014091)
      ·
        refine ⟨188246651475076903528521137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125497767650051269019014091 188246651475076903528521137)
        ·
          refine ⟨141184988606307677646390853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188246651475076903528521137 141184988606307677646390853)
          ·
            refine ⟨26472185363682689558698285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141184988606307677646390853 26472185363682689558698285)
            ·
              refine ⟨9927069511381008584511857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26472185363682689558698285 9927069511381008584511857)
              ·
                refine ⟨7445302133535756438383893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927069511381008584511857 7445302133535756438383893)
                ·
                  refine ⟨348998537509488583049245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7445302133535756438383893 348998537509488583049245)
                  ·
                    rfl

theorem cell23_6117050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_6117050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117050 prefixEnd_6117050 := by exact prefixLift 6117050
  have htrace : WordTrace (prefixWord ++ tailWord_6117050) baseStart_6117050 baseEnd_6117050 := by
    simpa [prefixWord, tailWord_6117050, baseEnd_6117050] using wordTrace_append hprefix tailTrace_6117050
  have hstable : (prefixWord ++ tailWord_6117050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117050).length < 2 ^ (prefixWord ++ tailWord_6117050).sum := by decide
  have hdescent : baseEnd_6117050 < baseStart_6117050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117053 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6117053 : Nat := 118140960795 + 6117053 * 2 ^ 59
def prefixEnd_6117053 : Nat := 4983230072969 + 3 ^ 40 * 6117053 * 2
def baseEnd_6117053 : Nat := 3140988378027360735705691

theorem tailTrace_6117053 : CollatzResearch.WordTrace tailWord_6117053 prefixEnd_6117053 3140988378027360735705691 := by
  unfold tailWord_6117053
  simp only [CollatzResearch.WordTrace]
  refine ⟨223107251907969165323939813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148738167938646110215959875 223107251907969165323939813)
  ·
    refine ⟨41832609732744218498238715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223107251907969165323939813 41832609732744218498238715)
    ·
      refine ⟨62748914599116327747358073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41832609732744218498238715 62748914599116327747358073)
      ·
        refine ⟨47061685949337245810518555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62748914599116327747358073 47061685949337245810518555)
        ·
          refine ⟨70592528924005868715777833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47061685949337245810518555 70592528924005868715777833)
          ·
            refine ⟨52944396693004401536833375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70592528924005868715777833 52944396693004401536833375)
            ·
              refine ⟨79416595039506602305250063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52944396693004401536833375 79416595039506602305250063)
              ·
                refine ⟨119124892559259903457875095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79416595039506602305250063 119124892559259903457875095)
                ·
                  refine ⟨178687338838889855186812643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119124892559259903457875095 178687338838889855186812643)
                  ·
                    refine ⟨268031008258334782780218965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178687338838889855186812643 268031008258334782780218965)
                    ·
                      refine ⟨3140988378027360735705691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268031008258334782780218965 3140988378027360735705691)
                      ·
                        rfl

theorem cell23_6117053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6117053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117053 prefixEnd_6117053 := by exact prefixLift 6117053
  have htrace : WordTrace (prefixWord ++ tailWord_6117053) baseStart_6117053 baseEnd_6117053 := by
    simpa [prefixWord, tailWord_6117053, baseEnd_6117053] using wordTrace_append hprefix tailTrace_6117053
  have hstable : (prefixWord ++ tailWord_6117053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117053).length < 2 ^ (prefixWord ++ tailWord_6117053).sum := by decide
  have hdescent : baseEnd_6117053 < baseStart_6117053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117054 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_6117054 : Nat := 118140960795 + 6117054 * 2 ^ 59
def prefixEnd_6117054 : Nat := 4983230072969 + 3 ^ 40 * 6117054 * 2
def baseEnd_6117054 : Nat := 1046996297169338410597729

theorem tailTrace_6117054 : CollatzResearch.WordTrace tailWord_6117054 prefixEnd_6117054 1046996297169338410597729 := by
  unfold tailWord_6117054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888411047620692811840777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148738192253977028329817477 27888411047620692811840777)
  ·
    refine ⟨20916308285715519608880583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27888411047620692811840777 20916308285715519608880583)
    ·
      refine ⟨31374462428573279413320875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20916308285715519608880583 31374462428573279413320875)
      ·
        refine ⟨47061693642859919119981313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31374462428573279413320875 47061693642859919119981313)
        ·
          refine ⟨35296270232144939339985985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47061693642859919119981313 35296270232144939339985985)
          ·
            refine ⟨26472202674108704504989489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35296270232144939339985985 26472202674108704504989489)
            ·
              refine ⟨19854152005581528378742117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26472202674108704504989489 19854152005581528378742117)
              ·
                refine ⟨3722653501046536571014147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19854152005581528378742117 3722653501046536571014147)
                ·
                  refine ⟨5583980251569804856521221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722653501046536571014147 5583980251569804856521221)
                  ·
                    refine ⟨1046996297169338410597729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5583980251569804856521221 1046996297169338410597729)
                    ·
                      rfl

theorem cell23_6117054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_6117054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117054 prefixEnd_6117054 := by exact prefixLift 6117054
  have htrace : WordTrace (prefixWord ++ tailWord_6117054) baseStart_6117054 baseEnd_6117054 := by
    simpa [prefixWord, tailWord_6117054, baseEnd_6117054] using wordTrace_append hprefix tailTrace_6117054
  have hstable : (prefixWord ++ tailWord_6117054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117054).length < 2 ^ (prefixWord ++ tailWord_6117054).sum := by decide
  have hdescent : baseEnd_6117054 < baseStart_6117054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117087 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 2, 3, 2]
def baseStart_6117087 : Nat := 118140960795 + 6117087 * 2 ^ 59
def prefixEnd_6117087 : Nat := 4983230072969 + 3 ^ 40 * 6117087 * 2
def baseEnd_6117087 : Nat := 3141005836369613602680535

theorem tailTrace_6117087 : CollatzResearch.WordTrace tailWord_6117087 prefixEnd_6117087 3141005836369613602680535 := by
  unfold tailWord_6117087
  simp only [CollatzResearch.WordTrace]
  refine ⟨223108491989845989130677515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148738994659897326087118343 223108491989845989130677515)
  ·
    refine ⟨334662737984768983696016273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223108491989845989130677515 334662737984768983696016273)
    ·
      refine ⟨250997053488576737772012205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334662737984768983696016273 250997053488576737772012205)
      ·
        refine ⟨94123895058216276664504577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250997053488576737772012205 94123895058216276664504577)
        ·
          refine ⟨70592921293662207498378433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94123895058216276664504577 70592921293662207498378433)
          ·
            refine ⟨52944690970246655623783825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70592921293662207498378433 52944690970246655623783825)
            ·
              refine ⟨39708518227684991717837869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52944690970246655623783825 39708518227684991717837869)
              ·
                refine ⟨14890694335381871894189201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39708518227684991717837869 14890694335381871894189201)
                ·
                  refine ⟨11168020751536403920641901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14890694335381871894189201 11168020751536403920641901)
                  ·
                    refine ⟨4188007781826151470240713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11168020751536403920641901 4188007781826151470240713)
                    ·
                      refine ⟨3141005836369613602680535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188007781826151470240713 3141005836369613602680535)
                      ·
                        rfl

theorem cell23_6117087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_6117087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117087 prefixEnd_6117087 := by exact prefixLift 6117087
  have htrace : WordTrace (prefixWord ++ tailWord_6117087) baseStart_6117087 baseEnd_6117087 := by
    simpa [prefixWord, tailWord_6117087, baseEnd_6117087] using wordTrace_append hprefix tailTrace_6117087
  have hstable : (prefixWord ++ tailWord_6117087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117087).length < 2 ^ (prefixWord ++ tailWord_6117087).sum := by decide
  have hdescent : baseEnd_6117087 < baseStart_6117087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117120 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_6117120 : Nat := 118140960795 + 6117120 * 2 ^ 59
def prefixEnd_6117120 : Nat := 4983230072969 + 3 ^ 40 * 6117120 * 2
def baseEnd_6117120 : Nat := 3141022781231211973567883

theorem tailTrace_6117120 : CollatzResearch.WordTrace tailWord_6117120 prefixEnd_6117120 3141022781231211973567883 := by
  unfold tailWord_6117120
  simp only [CollatzResearch.WordTrace]
  refine ⟨111554847799363217883314407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148739797065817623844419209 111554847799363217883314407)
  ·
    refine ⟨167332271699044826824971611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111554847799363217883314407 167332271699044826824971611)
    ·
      refine ⟨250998407548567240237457417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167332271699044826824971611 250998407548567240237457417)
      ·
        refine ⟨188248805661425430178093063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250998407548567240237457417 188248805661425430178093063)
        ·
          refine ⟨282373208492138145267139595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188248805661425430178093063 282373208492138145267139595)
          ·
            refine ⟨423559812738207217900709393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282373208492138145267139595 423559812738207217900709393)
            ·
              refine ⟨317669859553655413425532045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423559812738207217900709393 317669859553655413425532045)
              ·
                refine ⟨119126197332620780034574517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317669859553655413425532045 119126197332620780034574517)
                ·
                  refine ⟨11168080999933198128241361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119126197332620780034574517 11168080999933198128241361)
                  ·
                    refine ⟨8376060749949898596181021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11168080999933198128241361 8376060749949898596181021)
                    ·
                      refine ⟨3141022781231211973567883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8376060749949898596181021 3141022781231211973567883)
                      ·
                        rfl

theorem cell23_6117120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_6117120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117120 prefixEnd_6117120 := by exact prefixLift 6117120
  have htrace : WordTrace (prefixWord ++ tailWord_6117120) baseStart_6117120 baseEnd_6117120 := by
    simpa [prefixWord, tailWord_6117120, baseEnd_6117120] using wordTrace_append hprefix tailTrace_6117120
  have hstable : (prefixWord ++ tailWord_6117120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117120).length < 2 ^ (prefixWord ++ tailWord_6117120).sum := by decide
  have hdescent : baseEnd_6117120 < baseStart_6117120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117123 : List Nat := [1, 1, 1, 3, 2, 2, 3, 10]
def baseStart_6117123 : Nat := 118140960795 + 6117123 * 2 ^ 59
def prefixEnd_6117123 : Nat := 4983230072969 + 3 ^ 40 * 6117123 * 2
def baseEnd_6117123 : Nat := 116334234136043535623347

theorem tailTrace_6117123 : CollatzResearch.WordTrace tailWord_6117123 prefixEnd_6117123 116334234136043535623347 := by
  unfold tailWord_6117123
  simp only [CollatzResearch.WordTrace]
  refine ⟨223109805017715567278988023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148739870011810378185992015 223109805017715567278988023)
  ·
    refine ⟨334664707526573350918482035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223109805017715567278988023 334664707526573350918482035)
    ·
      refine ⟨501997061289860026377723053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334664707526573350918482035 501997061289860026377723053)
      ·
        refine ⟨188248897983697509891646145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501997061289860026377723053 188248897983697509891646145)
        ·
          refine ⟨141186673487773132418734609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188248897983697509891646145 141186673487773132418734609)
          ·
            refine ⟨105890005115829849314050957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141186673487773132418734609 105890005115829849314050957)
            ·
              refine ⟨39708751918436193492769109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105890005115829849314050957 39708751918436193492769109)
              ·
                refine ⟨116334234136043535623347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39708751918436193492769109 116334234136043535623347)
                ·
                  rfl

theorem cell23_6117123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 10].length) (baseStart_6117123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117123 prefixEnd_6117123 := by exact prefixLift 6117123
  have htrace : WordTrace (prefixWord ++ tailWord_6117123) baseStart_6117123 baseEnd_6117123 := by
    simpa [prefixWord, tailWord_6117123, baseEnd_6117123] using wordTrace_append hprefix tailTrace_6117123
  have hstable : (prefixWord ++ tailWord_6117123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117123).length < 2 ^ (prefixWord ++ tailWord_6117123).sum := by decide
  have hdescent : baseEnd_6117123 < baseStart_6117123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117130 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6117130 : Nat := 118140960795 + 6117130 * 2 ^ 59
def prefixEnd_6117130 : Nat := 4983230072969 + 3 ^ 40 * 6117130 * 2
def baseEnd_6117130 : Nat := 3141027916037756934442837

theorem tailTrace_6117130 : CollatzResearch.WordTrace tailWord_6117130 prefixEnd_6117130 3141027916037756934442837 := by
  unfold tailWord_6117130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55777515082172551868623211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148740040219126804982995229 55777515082172551868623211)
  ·
    refine ⟨83666272623258827802934817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55777515082172551868623211 83666272623258827802934817)
    ·
      refine ⟨62749704467444120852201113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83666272623258827802934817 62749704467444120852201113)
      ·
        refine ⟨47062278350583090639150835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62749704467444120852201113 47062278350583090639150835)
        ·
          refine ⟨70593417525874635958726253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47062278350583090639150835 70593417525874635958726253)
          ·
            refine ⟨26472531572202988484522345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70593417525874635958726253 26472531572202988484522345)
            ·
              refine ⟨19854398679152241363391759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26472531572202988484522345 19854398679152241363391759)
              ·
                refine ⟨29781598018728362045087639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19854398679152241363391759 29781598018728362045087639)
                ·
                  refine ⟨44672397028092543067631459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29781598018728362045087639 44672397028092543067631459)
                  ·
                    refine ⟨67008595542138814601447189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44672397028092543067631459 67008595542138814601447189)
                    ·
                      refine ⟨3141027916037756934442837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67008595542138814601447189 3141027916037756934442837)
                      ·
                        rfl

theorem cell23_6117130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6117130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117130 prefixEnd_6117130 := by exact prefixLift 6117130
  have htrace : WordTrace (prefixWord ++ tailWord_6117130) baseStart_6117130 baseEnd_6117130 := by
    simpa [prefixWord, tailWord_6117130, baseEnd_6117130] using wordTrace_append hprefix tailTrace_6117130
  have hstable : (prefixWord ++ tailWord_6117130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117130).length < 2 ^ (prefixWord ++ tailWord_6117130).sum := by decide
  have hdescent : baseEnd_6117130 < baseStart_6117130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117134 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6117134 : Nat := 118140960795 + 6117134 * 2 ^ 59
def prefixEnd_6117134 : Nat := 4983230072969 + 3 ^ 40 * 6117134 * 2
def baseEnd_6117134 : Nat := 3141029969960374918792819

theorem tailTrace_6117134 : CollatzResearch.WordTrace tailWord_6117134 prefixEnd_6117134 3141029969960374918792819 := by
  unfold tailWord_6117134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888775777584464519704807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148740137480450477438425637 27888775777584464519704807)
  ·
    refine ⟨41833163666376696779557211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27888775777584464519704807 41833163666376696779557211)
    ·
      refine ⟨62749745499565045169335817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41833163666376696779557211 62749745499565045169335817)
      ·
        refine ⟨47062309124673783877001863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62749745499565045169335817 47062309124673783877001863)
        ·
          refine ⟨70593463687010675815502795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47062309124673783877001863 70593463687010675815502795)
          ·
            refine ⟨105890195530516013723254193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70593463687010675815502795 105890195530516013723254193)
            ·
              refine ⟨79417646647887010292440645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105890195530516013723254193 79417646647887010292440645)
              ·
                refine ⟨14890808746478814429832621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79417646647887010292440645 14890808746478814429832621)
                ·
                  refine ⟨5584053279929555411187233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14890808746478814429832621 5584053279929555411187233)
                  ·
                    refine ⟨4188039959947166558390425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584053279929555411187233 4188039959947166558390425)
                    ·
                      refine ⟨3141029969960374918792819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188039959947166558390425 3141029969960374918792819)
                      ·
                        rfl

theorem cell23_6117134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6117134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117134 prefixEnd_6117134 := by exact prefixLift 6117134
  have htrace : WordTrace (prefixWord ++ tailWord_6117134) baseStart_6117134 baseEnd_6117134 := by
    simpa [prefixWord, tailWord_6117134, baseEnd_6117134] using wordTrace_append hprefix tailTrace_6117134
  have hstable : (prefixWord ++ tailWord_6117134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117134).length < 2 ^ (prefixWord ++ tailWord_6117134).sum := by decide
  have hdescent : baseEnd_6117134 < baseStart_6117134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117151 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 1, 2, 2]
def baseStart_6117151 : Nat := 118140960795 + 6117151 * 2 ^ 59
def prefixEnd_6117151 : Nat := 4983230072969 + 3 ^ 40 * 6117151 * 2
def baseEnd_6117151 : Nat := 3141038699131501352280241

theorem tailTrace_6117151 : CollatzResearch.WordTrace tailWord_6117151 prefixEnd_6117151 3141038699131501352280241 := by
  unfold tailWord_6117151
  simp only [CollatzResearch.WordTrace]
  refine ⟨223110826261614128061007307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148740550841076085374004871 223110826261614128061007307)
  ·
    refine ⟨334666239392421192091510961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223110826261614128061007307 334666239392421192091510961)
    ·
      refine ⟨250999679544315894068633221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334666239392421192091510961 250999679544315894068633221)
      ·
        refine ⟨47062439914559230137868729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250999679544315894068633221 47062439914559230137868729)
        ·
          refine ⟨35296829935919422603401547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47062439914559230137868729 35296829935919422603401547)
          ·
            refine ⟨52945244903879133905102321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35296829935919422603401547 52945244903879133905102321)
            ·
              refine ⟨39708933677909350428826741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52945244903879133905102321 39708933677909350428826741)
              ·
                refine ⟨3722712532304001602702507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39708933677909350428826741 3722712532304001602702507)
                ·
                  refine ⟨5584068798456002404053761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722712532304001602702507 5584068798456002404053761)
                  ·
                    refine ⟨4188051598842001803040321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584068798456002404053761 4188051598842001803040321)
                    ·
                      refine ⟨3141038699131501352280241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188051598842001803040321 3141038699131501352280241)
                      ·
                        rfl

theorem cell23_6117151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_6117151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117151 prefixEnd_6117151 := by exact prefixLift 6117151
  have htrace : WordTrace (prefixWord ++ tailWord_6117151) baseStart_6117151 baseEnd_6117151 := by
    simpa [prefixWord, tailWord_6117151, baseEnd_6117151] using wordTrace_append hprefix tailTrace_6117151
  have hstable : (prefixWord ++ tailWord_6117151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117151).length < 2 ^ (prefixWord ++ tailWord_6117151).sum := by decide
  have hdescent : baseEnd_6117151 < baseStart_6117151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117170 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_6117170 : Nat := 118140960795 + 6117170 * 2 ^ 59
def prefixEnd_6117170 : Nat := 4983230072969 + 3 ^ 40 * 6117170 * 2
def baseEnd_6117170 : Nat := 1047016151754645592647551

theorem tailTrace_6117170 : CollatzResearch.WordTrace tailWord_6117170 prefixEnd_6117170 1047016151754645592647551 := by
  unfold tailWord_6117170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55777879812136323576487241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148741012832363529537299309 55777879812136323576487241)
  ·
    refine ⟨41833409859102242682365431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55777879812136323576487241 41833409859102242682365431)
    ·
      refine ⟨62750114788653364023548147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41833409859102242682365431 62750114788653364023548147)
      ·
        refine ⟨94125172182980046035322221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62750114788653364023548147 94125172182980046035322221)
        ·
          refine ⟨35296939568617517263245833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94125172182980046035322221 35296939568617517263245833)
          ·
            refine ⟨26472704676463137947434375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35296939568617517263245833 26472704676463137947434375)
            ·
              refine ⟨39709057014694706921151563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26472704676463137947434375 39709057014694706921151563)
              ·
                refine ⟨59563585522042060381727345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39709057014694706921151563 59563585522042060381727345)
                ·
                  refine ⟨44672689141531545286295509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59563585522042060381727345 44672689141531545286295509)
                  ·
                    refine ⟨1047016151754645592647551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44672689141531545286295509 1047016151754645592647551)
                    ·
                      rfl

theorem cell23_6117170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_6117170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117170 prefixEnd_6117170 := by exact prefixLift 6117170
  have htrace : WordTrace (prefixWord ++ tailWord_6117170) baseStart_6117170 baseEnd_6117170 := by
    simpa [prefixWord, tailWord_6117170, baseEnd_6117170] using wordTrace_append hprefix tailTrace_6117170
  have hstable : (prefixWord ++ tailWord_6117170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117170).length < 2 ^ (prefixWord ++ tailWord_6117170).sum := by decide
  have hdescent : baseEnd_6117170 < baseStart_6117170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117174 : List Nat := [5, 1, 2, 2, 1, 3, 1, 8]
def baseStart_6117174 : Nat := 118140960795 + 6117174 * 2 ^ 59
def prefixEnd_6117174 : Nat := 4983230072969 + 3 ^ 40 * 6117174 * 2
def baseEnd_6117174 : Nat := 116335204043946472677505

theorem tailTrace_6117174 : CollatzResearch.WordTrace tailWord_6117174 prefixEnd_6117174 116335204043946472677505 := by
  unfold tailWord_6117174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944479071283175186818411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148741110093687201992729717 13944479071283175186818411)
  ·
    refine ⟨20916718606924762780227617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944479071283175186818411 20916718606924762780227617)
    ·
      refine ⟨15687538955193572085170713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20916718606924762780227617 15687538955193572085170713)
      ·
        refine ⟨11765654216395179063878035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15687538955193572085170713 11765654216395179063878035)
        ·
          refine ⟨17648481324592768595817053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765654216395179063878035 17648481324592768595817053)
          ·
            refine ⟨6618180496722288223431395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17648481324592768595817053 6618180496722288223431395)
            ·
              refine ⟨9927270745083432335147093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618180496722288223431395 9927270745083432335147093)
              ·
                refine ⟨116335204043946472677505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9927270745083432335147093 116335204043946472677505)
                ·
                  rfl

theorem cell23_6117174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_6117174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117174 prefixEnd_6117174 := by exact prefixLift 6117174
  have htrace : WordTrace (prefixWord ++ tailWord_6117174) baseStart_6117174 baseEnd_6117174 := by
    simpa [prefixWord, tailWord_6117174, baseEnd_6117174] using wordTrace_append hprefix tailTrace_6117174
  have hstable : (prefixWord ++ tailWord_6117174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117174).length < 2 ^ (prefixWord ++ tailWord_6117174).sum := by decide
  have hdescent : baseEnd_6117174 < baseStart_6117174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117194 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_6117194 : Nat := 118140960795 + 6117194 * 2 ^ 59
def prefixEnd_6117194 : Nat := 4983230072969 + 3 ^ 40 * 6117194 * 2
def baseEnd_6117194 : Nat := 3141060778799644684042543

theorem tailTrace_6117194 : CollatzResearch.WordTrace tailWord_6117194 prefixEnd_6117194 3141060778799644684042543 := by
  unfold tailWord_6117194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778098650114586601205659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148741596400305564269881757 55778098650114586601205659)
  ·
    refine ⟨83667147975171879901808489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55778098650114586601205659 83667147975171879901808489)
    ·
      refine ⟨62750360981378909926356367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83667147975171879901808489 62750360981378909926356367)
      ·
        refine ⟨94125541472068364889534551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62750360981378909926356367 94125541472068364889534551)
        ·
          refine ⟨141188312208102547334301827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94125541472068364889534551 141188312208102547334301827)
          ·
            refine ⟨211782468312153821001452741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141188312208102547334301827 211782468312153821001452741)
            ·
              refine ⟨39709212808528841437772389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211782468312153821001452741 39709212808528841437772389)
              ·
                refine ⟨7445477401599157769582323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39709212808528841437772389 7445477401599157769582323)
                ·
                  refine ⟨11168216102398736654373485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445477401599157769582323 11168216102398736654373485)
                  ·
                    refine ⟨4188081038399526245390057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11168216102398736654373485 4188081038399526245390057)
                    ·
                      refine ⟨3141060778799644684042543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188081038399526245390057 3141060778799644684042543)
                      ·
                        rfl

theorem cell23_6117194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_6117194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117194 prefixEnd_6117194 := by exact prefixLift 6117194
  have htrace : WordTrace (prefixWord ++ tailWord_6117194) baseStart_6117194 baseEnd_6117194 := by
    simpa [prefixWord, tailWord_6117194, baseEnd_6117194] using wordTrace_append hprefix tailTrace_6117194
  have hstable : (prefixWord ++ tailWord_6117194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117194).length < 2 ^ (prefixWord ++ tailWord_6117194).sum := by decide
  have hdescent : baseEnd_6117194 < baseStart_6117194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117210 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_6117210 : Nat := 118140960795 + 6117210 * 2 ^ 59
def prefixEnd_6117210 : Nat := 4983230072969 + 3 ^ 40 * 6117210 * 2
def baseEnd_6117210 : Nat := 3141068994490116621442469

theorem tailTrace_6117210 : CollatzResearch.WordTrace tailWord_6117210 prefixEnd_6117210 3141068994490116621442469 := by
  unfold tailWord_6117210
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778244542100095284351271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148741985445600254091603389 55778244542100095284351271)
  ·
    refine ⟨83667366813150142926526907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55778244542100095284351271 83667366813150142926526907)
    ·
      refine ⟨125501050219725214389790361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83667366813150142926526907 125501050219725214389790361)
      ·
        refine ⟨94125787664793910792342771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125501050219725214389790361 94125787664793910792342771)
        ·
          refine ⟨141188681497190866188514157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94125787664793910792342771 141188681497190866188514157)
          ·
            refine ⟨52945755561446574820692809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141188681497190866188514157 52945755561446574820692809)
            ·
              refine ⟨39709316671084931115519607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52945755561446574820692809 39709316671084931115519607)
              ·
                refine ⟨59563975006627396673279411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39709316671084931115519607 59563975006627396673279411)
                ·
                  refine ⟨89345962509941095009919117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59563975006627396673279411 89345962509941095009919117)
                  ·
                    refine ⟨33504735941227910628719669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89345962509941095009919117 33504735941227910628719669)
                    ·
                      refine ⟨3141068994490116621442469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33504735941227910628719669 3141068994490116621442469)
                      ·
                        rfl

theorem cell23_6117210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_6117210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117210 prefixEnd_6117210 := by exact prefixLift 6117210
  have htrace : WordTrace (prefixWord ++ tailWord_6117210) baseStart_6117210 baseEnd_6117210 := by
    simpa [prefixWord, tailWord_6117210, baseEnd_6117210] using wordTrace_append hprefix tailTrace_6117210
  have hstable : (prefixWord ++ tailWord_6117210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117210).length < 2 ^ (prefixWord ++ tailWord_6117210).sum := by decide
  have hdescent : baseEnd_6117210 < baseStart_6117210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117218 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6117218 : Nat := 118140960795 + 6117218 * 2 ^ 59
def prefixEnd_6117218 : Nat := 4983230072969 + 3 ^ 40 * 6117218 * 2
def baseEnd_6117218 : Nat := 3141073102335352590142433

theorem tailTrace_6117218 : CollatzResearch.WordTrace tailWord_6117218 prefixEnd_6117218 3141073102335352590142433 := by
  unfold tailWord_6117218
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778317488092849625924077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148742179968247599002464205 55778317488092849625924077)
  ·
    refine ⟨20916869058034818609721529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55778317488092849625924077 20916869058034818609721529)
    ·
      refine ⟨15687651793526113957291147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20916869058034818609721529 15687651793526113957291147)
      ·
        refine ⟨23531477690289170935936721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15687651793526113957291147 23531477690289170935936721)
        ·
          refine ⟨17648608267716878201952541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23531477690289170935936721 17648608267716878201952541)
          ·
            refine ⟨6618228100393829325732203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17648608267716878201952541 6618228100393829325732203)
            ·
              refine ⟨9927342150590743988598305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618228100393829325732203 9927342150590743988598305)
              ·
                refine ⟨7445506612943057991448729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927342150590743988598305 7445506612943057991448729)
                ·
                  refine ⟨5584129959707293493586547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445506612943057991448729 5584129959707293493586547)
                  ·
                    refine ⟨8376194939560940240379821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584129959707293493586547 8376194939560940240379821)
                    ·
                      refine ⟨3141073102335352590142433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8376194939560940240379821 3141073102335352590142433)
                      ·
                        rfl

theorem cell23_6117218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6117218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117218 prefixEnd_6117218 := by exact prefixLift 6117218
  have htrace : WordTrace (prefixWord ++ tailWord_6117218) baseStart_6117218 baseEnd_6117218 := by
    simpa [prefixWord, tailWord_6117218, baseEnd_6117218] using wordTrace_append hprefix tailTrace_6117218
  have hstable : (prefixWord ++ tailWord_6117218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117218).length < 2 ^ (prefixWord ++ tailWord_6117218).sum := by decide
  have hdescent : baseEnd_6117218 < baseStart_6117218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117237 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6117237 : Nat := 118140960795 + 6117237 * 2 ^ 59
def prefixEnd_6117237 : Nat := 4983230072969 + 3 ^ 40 * 6117237 * 2
def baseEnd_6117237 : Nat := 3141082858467788015804845

theorem tailTrace_6117237 : CollatzResearch.WordTrace tailWord_6117237 prefixEnd_6117237 3141082858467788015804845 := by
  unfold tailWord_6117237
  simp only [CollatzResearch.WordTrace]
  refine ⟨223113962939302564748637965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148742641959535043165758643 223113962939302564748637965)
  ·
    refine ⟨83667736102238461780739237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223113962939302564748637965 83667736102238461780739237)
    ·
      refine ⟨15687700519169711583888607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83667736102238461780739237 15687700519169711583888607)
      ·
        refine ⟨23531550778754567375832911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15687700519169711583888607 23531550778754567375832911)
        ·
          refine ⟨35297326168131851063749367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23531550778754567375832911 35297326168131851063749367)
          ·
            refine ⟨52945989252197776595624051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35297326168131851063749367 52945989252197776595624051)
            ·
              refine ⟨79418983878296664893436077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52945989252197776595624051 79418983878296664893436077)
              ·
                refine ⟨29782118954361249335038529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79418983878296664893436077 29782118954361249335038529)
                ·
                  refine ⟨22336589215770937001278897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29782118954361249335038529 22336589215770937001278897)
                  ·
                    refine ⟨16752441911828202750959173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22336589215770937001278897 16752441911828202750959173)
                    ·
                      refine ⟨3141082858467788015804845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16752441911828202750959173 3141082858467788015804845)
                      ·
                        rfl

theorem cell23_6117237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6117237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117237 prefixEnd_6117237 := by exact prefixLift 6117237
  have htrace : WordTrace (prefixWord ++ tailWord_6117237) baseStart_6117237 baseEnd_6117237 := by
    simpa [prefixWord, tailWord_6117237, baseEnd_6117237] using wordTrace_append hprefix tailTrace_6117237
  have hstable : (prefixWord ++ tailWord_6117237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117237).length < 2 ^ (prefixWord ++ tailWord_6117237).sum := by decide
  have hdescent : baseEnd_6117237 < baseStart_6117237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117277 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_6117277 : Nat := 118140960795 + 6117277 * 2 ^ 59
def prefixEnd_6117277 : Nat := 4983230072969 + 3 ^ 40 * 6117277 * 2
def baseEnd_6117277 : Nat := 1047034465897989286434887

theorem tailTrace_6117277 : CollatzResearch.WordTrace tailWord_6117277 prefixEnd_6117277 1047034465897989286434887 := by
  unfold tailWord_6117277
  simp only [CollatzResearch.WordTrace]
  refine ⟨223115421859157651580094085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148743614572771767720062723 223115421859157651580094085)
  ·
    refine ⟨41834141598592059671267641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223115421859157651580094085 41834141598592059671267641)
    ·
      refine ⟨31375606198944044753450731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41834141598592059671267641 31375606198944044753450731)
      ·
        refine ⟨47063409298416067130176097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31375606198944044753450731 47063409298416067130176097)
        ·
          refine ⟨35297556973812050347632073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47063409298416067130176097 35297556973812050347632073)
          ·
            refine ⟨26473167730359037760724055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35297556973812050347632073 26473167730359037760724055)
            ·
              refine ⟨39709751595538556641086083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26473167730359037760724055 39709751595538556641086083)
              ·
                refine ⟨59564627393307834961629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39709751595538556641086083 59564627393307834961629125)
                ·
                  refine ⟨11168367636245219055305461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59564627393307834961629125 11168367636245219055305461)
                  ·
                    refine ⟨1047034465897989286434887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11168367636245219055305461 1047034465897989286434887)
                    ·
                      rfl

theorem cell23_6117277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_6117277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117277 prefixEnd_6117277 := by exact prefixLift 6117277
  have htrace : WordTrace (prefixWord ++ tailWord_6117277) baseStart_6117277 baseEnd_6117277 := by
    simpa [prefixWord, tailWord_6117277, baseEnd_6117277] using wordTrace_append hprefix tailTrace_6117277
  have hstable : (prefixWord ++ tailWord_6117277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117277).length < 2 ^ (prefixWord ++ tailWord_6117277).sum := by decide
  have hdescent : baseEnd_6117277 < baseStart_6117277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117281 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 7]
def baseStart_6117281 : Nat := 118140960795 + 6117281 * 2 ^ 59
def prefixEnd_6117281 : Nat := 4983230072969 + 3 ^ 40 * 6117281 * 2
def baseEnd_6117281 : Nat := 349011716846287315961627

theorem tailTrace_6117281 : CollatzResearch.WordTrace tailWord_6117281 prefixEnd_6117281 349011716846287315961627 := by
  unfold tailWord_6117281
  simp only [CollatzResearch.WordTrace]
  refine ⟨223115567751143160263239697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148743711834095440175493131 223115567751143160263239697)
  ·
    refine ⟨167336675813357370197429773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223115567751143160263239697 167336675813357370197429773)
    ·
      refine ⟨62751253430009013824036165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167336675813357370197429773 62751253430009013824036165)
      ·
        refine ⟨11765860018126690092006781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62751253430009013824036165 11765860018126690092006781)
        ·
          refine ⟨4412197506797508784502543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11765860018126690092006781 4412197506797508784502543)
          ·
            refine ⟨6618296260196263176753815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412197506797508784502543 6618296260196263176753815)
            ·
              refine ⟨9927444390294394765130723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618296260196263176753815 9927444390294394765130723)
              ·
                refine ⟨14891166585441592147696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927444390294394765130723 14891166585441592147696085)
                ·
                  refine ⟨349011716846287315961627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14891166585441592147696085 349011716846287315961627)
                  ·
                    rfl

theorem cell23_6117281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_6117281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117281 prefixEnd_6117281 := by exact prefixLift 6117281
  have htrace : WordTrace (prefixWord ++ tailWord_6117281) baseStart_6117281 baseEnd_6117281 := by
    simpa [prefixWord, tailWord_6117281, baseEnd_6117281] using wordTrace_append hprefix tailTrace_6117281
  have hstable : (prefixWord ++ tailWord_6117281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117281).length < 2 ^ (prefixWord ++ tailWord_6117281).sum := by decide
  have hdescent : baseEnd_6117281 < baseStart_6117281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117287 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6117287 : Nat := 118140960795 + 6117287 * 2 ^ 59
def prefixEnd_6117287 : Nat := 4983230072969 + 3 ^ 40 * 6117287 * 2
def baseEnd_6117287 : Nat := 3141108532500512820179615

theorem tailTrace_6117287 : CollatzResearch.WordTrace tailWord_6117287 prefixEnd_6117287 3141108532500512820179615 := by
  unfold tailWord_6117287
  simp only [CollatzResearch.WordTrace]
  refine ⟨223115786589121423287958115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148743857726080948858638743 223115786589121423287958115)
  ·
    refine ⟨334673679883682134931937173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223115786589121423287958115 334673679883682134931937173)
    ·
      refine ⟨15687828744547600074934555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 334673679883682134931937173 15687828744547600074934555)
      ·
        refine ⟨23531743116821400112401833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15687828744547600074934555 23531743116821400112401833)
        ·
          refine ⟨17648807337616050084301375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23531743116821400112401833 17648807337616050084301375)
          ·
            refine ⟨26473211006424075126452063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648807337616050084301375 26473211006424075126452063)
            ·
              refine ⟨39709816509636112689678095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26473211006424075126452063 39709816509636112689678095)
              ·
                refine ⟨59564724764454169034517143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39709816509636112689678095 59564724764454169034517143)
                ·
                  refine ⟨89347087146681253551775715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59564724764454169034517143 89347087146681253551775715)
                  ·
                    refine ⟨134020630720021880327663573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89347087146681253551775715 134020630720021880327663573)
                    ·
                      refine ⟨3141108532500512820179615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134020630720021880327663573 3141108532500512820179615)
                      ·
                        rfl

theorem cell23_6117287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6117287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117287 prefixEnd_6117287 := by exact prefixLift 6117287
  have htrace : WordTrace (prefixWord ++ tailWord_6117287) baseStart_6117287 baseEnd_6117287 := by
    simpa [prefixWord, tailWord_6117287, baseEnd_6117287] using wordTrace_append hprefix tailTrace_6117287
  have hstable : (prefixWord ++ tailWord_6117287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117287).length < 2 ^ (prefixWord ++ tailWord_6117287).sum := by decide
  have hdescent : baseEnd_6117287 < baseStart_6117287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117384 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_6117384 : Nat := 118140960795 + 6117384 * 2 ^ 59
def prefixEnd_6117384 : Nat := 4983230072969 + 3 ^ 40 * 6117384 * 2
def baseEnd_6117384 : Nat := 1047052780041332980222223

theorem tailTrace_6117384 : CollatzResearch.WordTrace tailWord_6117384 prefixEnd_6117384 1047052780041332980222223 := by
  unfold tailWord_6117384
  simp only [CollatzResearch.WordTrace]
  refine ⟨111559662234885004427119603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148746216313180005902826137 111559662234885004427119603)
  ·
    refine ⟨167339493352327506640679405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111559662234885004427119603 167339493352327506640679405)
    ·
      refine ⟨62752310007122814990254777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167339493352327506640679405 62752310007122814990254777)
      ·
        refine ⟨47064232505342111242691083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62752310007122814990254777 47064232505342111242691083)
        ·
          refine ⟨70596348758013166864036625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47064232505342111242691083 70596348758013166864036625)
          ·
            refine ⟨52947261568509875148027469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70596348758013166864036625 52947261568509875148027469)
            ·
              refine ⟨19855223088191203180510301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52947261568509875148027469 19855223088191203180510301)
              ·
                refine ⟨7445708658071701192691363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19855223088191203180510301 7445708658071701192691363)
                ·
                  refine ⟨11168562987107551789037045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445708658071701192691363 11168562987107551789037045)
                  ·
                    refine ⟨1047052780041332980222223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11168562987107551789037045 1047052780041332980222223)
                    ·
                      rfl

theorem cell23_6117384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_6117384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117384 prefixEnd_6117384 := by exact prefixLift 6117384
  have htrace : WordTrace (prefixWord ++ tailWord_6117384) baseStart_6117384 baseEnd_6117384 := by
    simpa [prefixWord, tailWord_6117384, baseEnd_6117384] using wordTrace_append hprefix tailTrace_6117384
  have hstable : (prefixWord ++ tailWord_6117384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117384).length < 2 ^ (prefixWord ++ tailWord_6117384).sum := by decide
  have hdescent : baseEnd_6117384 < baseStart_6117384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117432 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_6117432 : Nat := 118140960795 + 6117432 * 2 ^ 59
def prefixEnd_6117432 : Nat := 4983230072969 + 3 ^ 40 * 6117432 * 2
def baseEnd_6117432 : Nat := 3141182987195414752866449

theorem tailTrace_6117432 : CollatzResearch.WordTrace tailWord_6117432 prefixEnd_6117432 3141182987195414752866449 := by
  unfold tailWord_6117432
  simp only [CollatzResearch.WordTrace]
  refine ⟨111560537586798056525993275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148747383449064075367991033 111560537586798056525993275)
  ·
    refine ⟨167340806380197084788989913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111560537586798056525993275 167340806380197084788989913)
    ·
      refine ⟨125505604785147813591742435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167340806380197084788989913 125505604785147813591742435)
      ·
        refine ⟨188258407177721720387613653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125505604785147813591742435 188258407177721720387613653)
        ·
          refine ⟨4412306418227852821584695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 188258407177721720387613653 4412306418227852821584695)
          ·
            refine ⟨6618459627341779232377043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412306418227852821584695 6618459627341779232377043)
            ·
              refine ⟨9927689441012668848565565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618459627341779232377043 9927689441012668848565565)
              ·
                refine ⟨3722883540379750818212087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9927689441012668848565565 3722883540379750818212087)
                ·
                  refine ⟨5584325310569626227318131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722883540379750818212087 5584325310569626227318131)
                  ·
                    refine ⟨8376487965854439340977197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584325310569626227318131 8376487965854439340977197)
                    ·
                      refine ⟨3141182987195414752866449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8376487965854439340977197 3141182987195414752866449)
                      ·
                        rfl

theorem cell23_6117432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_6117432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117432 prefixEnd_6117432 := by exact prefixLift 6117432
  have htrace : WordTrace (prefixWord ++ tailWord_6117432) baseStart_6117432 baseEnd_6117432 := by
    simpa [prefixWord, tailWord_6117432, baseEnd_6117432] using wordTrace_append hprefix tailTrace_6117432
  have hstable : (prefixWord ++ tailWord_6117432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117432).length < 2 ^ (prefixWord ++ tailWord_6117432).sum := by decide
  have hdescent : baseEnd_6117432 < baseStart_6117432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117441 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6117441 : Nat := 118140960795 + 6117441 * 2 ^ 59
def prefixEnd_6117441 : Nat := 4983230072969 + 3 ^ 40 * 6117441 * 2
def baseEnd_6117441 : Nat := 3141187608521305217653907

theorem tailTrace_6117441 : CollatzResearch.WordTrace tailWord_6117441 prefixEnd_6117441 3141187608521305217653907 := by
  unfold tailWord_6117441
  simp only [CollatzResearch.WordTrace]
  refine ⟨223121403430563507589064177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148747602287042338392709451 223121403430563507589064177)
  ·
    refine ⟨167341052572922630691798133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223121403430563507589064177 167341052572922630691798133)
    ·
      refine ⟨15688223678711496627356075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167341052572922630691798133 15688223678711496627356075)
      ·
        refine ⟨23532335518067244941034113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15688223678711496627356075 23532335518067244941034113)
        ·
          refine ⟨17649251638550433705775585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23532335518067244941034113 17649251638550433705775585)
          ·
            refine ⟨13236938728912825279331689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17649251638550433705775585 13236938728912825279331689)
            ·
              refine ⟨9927704046684618959498767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236938728912825279331689 9927704046684618959498767)
              ·
                refine ⟨14891556070026928439248151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927704046684618959498767 14891556070026928439248151)
                ·
                  refine ⟨22337334105040392658872227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14891556070026928439248151 22337334105040392658872227)
                  ·
                    refine ⟨33506001157560588988308341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22337334105040392658872227 33506001157560588988308341)
                    ·
                      refine ⟨3141187608521305217653907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33506001157560588988308341 3141187608521305217653907)
                      ·
                        rfl

theorem cell23_6117441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6117441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117441 prefixEnd_6117441 := by exact prefixLift 6117441
  have htrace : WordTrace (prefixWord ++ tailWord_6117441) baseStart_6117441 baseEnd_6117441 := by
    simpa [prefixWord, tailWord_6117441, baseEnd_6117441] using wordTrace_append hprefix tailTrace_6117441
  have hstable : (prefixWord ++ tailWord_6117441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117441).length < 2 ^ (prefixWord ++ tailWord_6117441).sum := by decide
  have hdescent : baseEnd_6117441 < baseStart_6117441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117457 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_6117457 : Nat := 118140960795 + 6117457 * 2 ^ 59
def prefixEnd_6117457 : Nat := 4983230072969 + 3 ^ 40 * 6117457 * 2
def baseEnd_6117457 : Nat := 1047065274737259051684611

theorem tailTrace_6117457 : CollatzResearch.WordTrace tailWord_6117457 prefixEnd_6117457 1047065274737259051684611 := by
  unfold tailWord_6117457
  simp only [CollatzResearch.WordTrace]
  refine ⟨223121986998505542321646625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148747991332337028214431083 223121986998505542321646625)
  ·
    refine ⟨167341490248879156741234969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223121986998505542321646625 167341490248879156741234969)
    ·
      refine ⟨125506117686659367555926227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167341490248879156741234969 125506117686659367555926227)
      ·
        refine ⟨188259176529989051333889341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125506117686659367555926227 188259176529989051333889341)
        ·
          refine ⟨70597191198745894250208503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188259176529989051333889341 70597191198745894250208503)
          ·
            refine ⟨105895786798118841375312755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70597191198745894250208503 105895786798118841375312755)
            ·
              refine ⟨158843680197178262062969133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105895786798118841375312755 158843680197178262062969133)
              ·
                refine ⟨59566380073941848273613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158843680197178262062969133 59566380073941848273613425)
                ·
                  refine ⟨44674785055456386205210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59566380073941848273613425 44674785055456386205210069)
                  ·
                    refine ⟨1047065274737259051684611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44674785055456386205210069 1047065274737259051684611)
                    ·
                      rfl

theorem cell23_6117457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_6117457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117457 prefixEnd_6117457 := by exact prefixLift 6117457
  have htrace : WordTrace (prefixWord ++ tailWord_6117457) baseStart_6117457 baseEnd_6117457 := by
    simpa [prefixWord, tailWord_6117457, baseEnd_6117457] using wordTrace_append hprefix tailTrace_6117457
  have hstable : (prefixWord ++ tailWord_6117457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117457).length < 2 ^ (prefixWord ++ tailWord_6117457).sum := by decide
  have hdescent : baseEnd_6117457 < baseStart_6117457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117481 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 3, 3, 2]
def baseStart_6117481 : Nat := 118140960795 + 6117481 * 2 ^ 59
def prefixEnd_6117481 : Nat := 4983230072969 + 3 ^ 40 * 6117481 * 2
def baseEnd_6117481 : Nat := 3141208147747485061153723

theorem tailTrace_6117481 : CollatzResearch.WordTrace tailWord_6117481 prefixEnd_6117481 3141208147747485061153723 := by
  unfold tailWord_6117481
  simp only [CollatzResearch.WordTrace]
  refine ⟨223122862350418594420520297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148748574900279062947013531 223122862350418594420520297)
  ·
    refine ⟨167342146762813945815390223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223122862350418594420520297 167342146762813945815390223)
    ·
      refine ⟨251013220144220918723085335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167342146762813945815390223 251013220144220918723085335)
      ·
        refine ⟨376519830216331378084628003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251013220144220918723085335 376519830216331378084628003)
        ·
          refine ⟨564779745324497067126942005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376519830216331378084628003 564779745324497067126942005)
          ·
            refine ⟨52948101124171600043150813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 564779745324497067126942005 52948101124171600043150813)
            ·
              refine ⟨19855537921564350016181555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52948101124171600043150813 19855537921564350016181555)
              ·
                refine ⟨29783306882346525024272333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19855537921564350016181555 29783306882346525024272333)
                ·
                  refine ⟨11168740080879946884102125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29783306882346525024272333 11168740080879946884102125)
                  ·
                    refine ⟨4188277530329980081538297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11168740080879946884102125 4188277530329980081538297)
                    ·
                      refine ⟨3141208147747485061153723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188277530329980081538297 3141208147747485061153723)
                      ·
                        rfl

theorem cell23_6117481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3, 2].length) (baseStart_6117481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117481 prefixEnd_6117481 := by exact prefixLift 6117481
  have htrace : WordTrace (prefixWord ++ tailWord_6117481) baseStart_6117481 baseEnd_6117481 := by
    simpa [prefixWord, tailWord_6117481, baseEnd_6117481] using wordTrace_append hprefix tailTrace_6117481
  have hstable : (prefixWord ++ tailWord_6117481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117481).length < 2 ^ (prefixWord ++ tailWord_6117481).sum := by decide
  have hdescent : baseEnd_6117481 < baseStart_6117481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117505 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6117505 : Nat := 118140960795 + 6117505 * 2 ^ 59
def prefixEnd_6117505 : Nat := 4983230072969 + 3 ^ 40 * 6117505 * 2
def baseEnd_6117505 : Nat := 3141220471283192967253613

theorem tailTrace_6117505 : CollatzResearch.WordTrace tailWord_6117505 prefixEnd_6117505 3141220471283192967253613 := by
  unfold tailWord_6117505
  simp only [CollatzResearch.WordTrace]
  refine ⟨223123737702331646519393969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148749158468221097679595979 223123737702331646519393969)
  ·
    refine ⟨167342803276748734889545477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223123737702331646519393969 167342803276748734889545477)
    ·
      refine ⟨31376775614390387791789777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167342803276748734889545477 31376775614390387791789777)
      ·
        refine ⟨23532581710792790843842333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31376775614390387791789777 23532581710792790843842333)
        ·
          refine ⟨8824718141547296566440875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23532581710792790843842333 8824718141547296566440875)
          ·
            refine ⟨13237077212320944849661313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824718141547296566440875 13237077212320944849661313)
            ·
              refine ⟨9927807909240708637245985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13237077212320944849661313 9927807909240708637245985)
              ·
                refine ⟨7445855931930531477934489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927807909240708637245985 7445855931930531477934489)
                ·
                  refine ⟨5584391948947898608450867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445855931930531477934489 5584391948947898608450867)
                  ·
                    refine ⟨8376587923421847912676301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584391948947898608450867 8376587923421847912676301)
                    ·
                      refine ⟨3141220471283192967253613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8376587923421847912676301 3141220471283192967253613)
                      ·
                        rfl

theorem cell23_6117505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6117505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117505 prefixEnd_6117505 := by exact prefixLift 6117505
  have htrace : WordTrace (prefixWord ++ tailWord_6117505) baseStart_6117505 baseEnd_6117505 := by
    simpa [prefixWord, tailWord_6117505, baseEnd_6117505] using wordTrace_append hprefix tailTrace_6117505
  have hstable : (prefixWord ++ tailWord_6117505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117505).length < 2 ^ (prefixWord ++ tailWord_6117505).sum := by decide
  have hdescent : baseEnd_6117505 < baseStart_6117505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117556 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6117556 : Nat := 118140960795 + 6117556 * 2 ^ 59
def prefixEnd_6117556 : Nat := 4983230072969 + 3 ^ 40 * 6117556 * 2
def baseEnd_6117556 : Nat := 3141246658796572267715879

theorem tailTrace_6117556 : CollatzResearch.WordTrace tailWord_6117556 prefixEnd_6117556 3141246658796572267715879 := by
  unfold tailWord_6117556
  simp only [CollatzResearch.WordTrace]
  refine ⟨111562798912573441114750261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148750398550097921486333681 111562798912573441114750261)
  ·
    refine ⟨10459012398053760104507837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111562798912573441114750261 10459012398053760104507837)
    ·
      refine ⟨3922129649270160039190439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10459012398053760104507837 3922129649270160039190439)
      ·
        refine ⟨5883194473905240058785659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922129649270160039190439 5883194473905240058785659)
        ·
          refine ⟨8824791710857860088178489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883194473905240058785659 8824791710857860088178489)
          ·
            refine ⟨6618593783143395066133867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824791710857860088178489 6618593783143395066133867)
            ·
              refine ⟨9927890674715092599200801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618593783143395066133867 9927890674715092599200801)
              ·
                refine ⟨7445918006036319449400601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927890674715092599200801 7445918006036319449400601)
                ·
                  refine ⟨5584438504527239587050451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445918006036319449400601 5584438504527239587050451)
                  ·
                    refine ⟨8376657756790859380575677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584438504527239587050451 8376657756790859380575677)
                    ·
                      refine ⟨3141246658796572267715879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8376657756790859380575677 3141246658796572267715879)
                      ·
                        rfl

theorem cell23_6117556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6117556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117556 prefixEnd_6117556 := by exact prefixLift 6117556
  have htrace : WordTrace (prefixWord ++ tailWord_6117556) baseStart_6117556 baseEnd_6117556 := by
    simpa [prefixWord, tailWord_6117556, baseEnd_6117556] using wordTrace_append hprefix tailTrace_6117556
  have hstable : (prefixWord ++ tailWord_6117556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117556).length < 2 ^ (prefixWord ++ tailWord_6117556).sum := by decide
  have hdescent : baseEnd_6117556 < baseStart_6117556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117601 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6117601 : Nat := 118140960795 + 6117601 * 2 ^ 59
def prefixEnd_6117601 : Nat := 4983230072969 + 3 ^ 40 * 6117601 * 2
def baseEnd_6117601 : Nat := 3141269765426024591653171

theorem tailTrace_6117601 : CollatzResearch.WordTrace tailWord_6117601 prefixEnd_6117601 3141269765426024591653171 := by
  unfold tailWord_6117601
  simp only [CollatzResearch.WordTrace]
  refine ⟨223127239109983854914888657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148751492739989236609925771 223127239109983854914888657)
  ·
    refine ⟨167345429332487891186166493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223127239109983854914888657 167345429332487891186166493)
    ·
      refine ⟨62754535999682959194812435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167345429332487891186166493 62754535999682959194812435)
      ·
        refine ⟨94131803999524438792218653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62754535999682959194812435 94131803999524438792218653)
        ·
          refine ⟨35299426499821664547081995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94131803999524438792218653 35299426499821664547081995)
          ·
            refine ⟨52949139749732496820622993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35299426499821664547081995 52949139749732496820622993)
            ·
              refine ⟨39711854812299372615467245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52949139749732496820622993 39711854812299372615467245)
              ·
                refine ⟨14891945554612264730800217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39711854812299372615467245 14891945554612264730800217)
                ·
                  refine ⟨11168959165959198548100163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14891945554612264730800217 11168959165959198548100163)
                  ·
                    refine ⟨16753438748938797822150245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11168959165959198548100163 16753438748938797822150245)
                    ·
                      refine ⟨3141269765426024591653171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16753438748938797822150245 3141269765426024591653171)
                      ·
                        rfl

theorem cell23_6117601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6117601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117601 prefixEnd_6117601 := by exact prefixLift 6117601
  have htrace : WordTrace (prefixWord ++ tailWord_6117601) baseStart_6117601 baseEnd_6117601 := by
    simpa [prefixWord, tailWord_6117601, baseEnd_6117601] using wordTrace_append hprefix tailTrace_6117601
  have hstable : (prefixWord ++ tailWord_6117601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117601).length < 2 ^ (prefixWord ++ tailWord_6117601).sum := by decide
  have hdescent : baseEnd_6117601 < baseStart_6117601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117604 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_6117604 : Nat := 118140960795 + 6117604 * 2 ^ 59
def prefixEnd_6117604 : Nat := 4983230072969 + 3 ^ 40 * 6117604 * 2
def baseEnd_6117604 : Nat := 3141271305867988079915657

theorem tailTrace_6117604 : CollatzResearch.WordTrace tailWord_6117604 prefixEnd_6117604 3141271305867988079915657 := by
  unfold tailWord_6117604
  simp only [CollatzResearch.WordTrace]
  refine ⟨111563674264486493213623933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148751565685981990951498577 111563674264486493213623933)
  ·
    refine ⟨41836377849182434955108975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111563674264486493213623933 41836377849182434955108975)
    ·
      refine ⟨62754566773773652432663463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41836377849182434955108975 62754566773773652432663463)
      ·
        refine ⟨94131850160660478648995195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62754566773773652432663463 94131850160660478648995195)
        ·
          refine ⟨141197775240990717973492793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94131850160660478648995195 141197775240990717973492793)
          ·
            refine ⟨105898331430743038480119595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141197775240990717973492793 105898331430743038480119595)
            ·
              refine ⟨158847497146114557720179393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105898331430743038480119595 158847497146114557720179393)
              ·
                refine ⟨119135622859585918290134545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158847497146114557720179393 119135622859585918290134545)
                ·
                  refine ⟨89351717144689438717600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119135622859585918290134545 89351717144689438717600909)
                  ·
                    refine ⟨33506893929258539519100341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89351717144689438717600909 33506893929258539519100341)
                    ·
                      refine ⟨3141271305867988079915657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33506893929258539519100341 3141271305867988079915657)
                      ·
                        rfl

theorem cell23_6117604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_6117604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117604 prefixEnd_6117604 := by exact prefixLift 6117604
  have htrace : WordTrace (prefixWord ++ tailWord_6117604) baseStart_6117604 baseEnd_6117604 := by
    simpa [prefixWord, tailWord_6117604, baseEnd_6117604] using wordTrace_append hprefix tailTrace_6117604
  have hstable : (prefixWord ++ tailWord_6117604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117604).length < 2 ^ (prefixWord ++ tailWord_6117604).sum := by decide
  have hdescent : baseEnd_6117604 < baseStart_6117604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117618 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6117618 : Nat := 118140960795 + 6117618 * 2 ^ 59
def prefixEnd_6117618 : Nat := 4983230072969 + 3 ^ 40 * 6117618 * 2
def baseEnd_6117618 : Nat := 3141278494597151025140593

theorem tailTrace_6117618 : CollatzResearch.WordTrace tailWord_6117618 prefixEnd_6117618 3141278494597151025140593 := by
  unfold tailWord_6117618
  simp only [CollatzResearch.WordTrace]
  refine ⟨55781964787730566704564377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148751906100614844545505005 55781964787730566704564377)
  ·
    refine ⟨41836473590797925028423283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55781964787730566704564377 41836473590797925028423283)
    ·
      refine ⟨62754710386196887542634925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41836473590797925028423283 62754710386196887542634925)
      ·
        refine ⟨23533016394823832828488097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62754710386196887542634925 23533016394823832828488097)
        ·
          refine ⟨17649762296117874621366073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23533016394823832828488097 17649762296117874621366073)
          ·
            refine ⟨13237321722088405966024555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17649762296117874621366073 13237321722088405966024555)
            ·
              refine ⟨19855982583132608949036833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13237321722088405966024555 19855982583132608949036833)
              ·
                refine ⟨14891986937349456711777625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19855982583132608949036833 14891986937349456711777625)
                ·
                  refine ⟨11168990203012092533833219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14891986937349456711777625 11168990203012092533833219)
                  ·
                    refine ⟨16753485304518138800749829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11168990203012092533833219 16753485304518138800749829)
                    ·
                      refine ⟨3141278494597151025140593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16753485304518138800749829 3141278494597151025140593)
                      ·
                        rfl

theorem cell23_6117618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6117618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117618 prefixEnd_6117618 := by exact prefixLift 6117618
  have htrace : WordTrace (prefixWord ++ tailWord_6117618) baseStart_6117618 baseEnd_6117618 := by
    simpa [prefixWord, tailWord_6117618, baseEnd_6117618] using wordTrace_append hprefix tailTrace_6117618
  have hstable : (prefixWord ++ tailWord_6117618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117618).length < 2 ^ (prefixWord ++ tailWord_6117618).sum := by decide
  have hdescent : baseEnd_6117618 < baseStart_6117618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117628 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_6117628 : Nat := 118140960795 + 6117628 * 2 ^ 59
def prefixEnd_6117628 : Nat := 4983230072969 + 3 ^ 40 * 6117628 * 2
def baseEnd_6117628 : Nat := 1047094543134565328671849

theorem tailTrace_6117628 : CollatzResearch.WordTrace tailWord_6117628 prefixEnd_6117628 1047094543134565328671849 := by
  unfold tailWord_6117628
  simp only [CollatzResearch.WordTrace]
  refine ⟨111564111940443019263060769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148752149253924025684081025 111564111940443019263060769)
  ·
    refine ⟨83673083955332264447295577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111564111940443019263060769 83673083955332264447295577)
    ·
      refine ⟨62754812966499198335471683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83673083955332264447295577 62754812966499198335471683)
      ·
        refine ⟨94132219449748797503207525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62754812966499198335471683 94132219449748797503207525)
        ·
          refine ⟨17649791146827899531851411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94132219449748797503207525 17649791146827899531851411)
          ·
            refine ⟨26474686720241849297777117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17649791146827899531851411 26474686720241849297777117)
            ·
              refine ⟨9928007520090693486666419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26474686720241849297777117 9928007520090693486666419)
              ·
                refine ⟨14892011280136040229999629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928007520090693486666419 14892011280136040229999629)
                ·
                  refine ⟨5584504230051015086249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14892011280136040229999629 5584504230051015086249861)
                  ·
                    refine ⟨1047094543134565328671849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584504230051015086249861 1047094543134565328671849)
                    ·
                      rfl

theorem cell23_6117628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_6117628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117628 prefixEnd_6117628 := by exact prefixLift 6117628
  have htrace : WordTrace (prefixWord ++ tailWord_6117628) baseStart_6117628 baseEnd_6117628 := by
    simpa [prefixWord, tailWord_6117628, baseEnd_6117628] using wordTrace_append hprefix tailTrace_6117628
  have hstable : (prefixWord ++ tailWord_6117628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117628).length < 2 ^ (prefixWord ++ tailWord_6117628).sum := by decide
  have hdescent : baseEnd_6117628 < baseStart_6117628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117641 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 6]
def baseStart_6117641 : Nat := 118140960795 + 6117641 * 2 ^ 59
def prefixEnd_6117641 : Nat := 4983230072969 + 3 ^ 40 * 6117641 * 2
def baseEnd_6117641 : Nat := 349032256072467159461443

theorem tailTrace_6117641 : CollatzResearch.WordTrace tailWord_6117641 prefixEnd_6117641 349032256072467159461443 := by
  unfold tailWord_6117641
  simp only [CollatzResearch.WordTrace]
  refine ⟨223128698029838941746344777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148752465353225961164229851 223128698029838941746344777)
  ·
    refine ⟨167346523522379206309758583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223128698029838941746344777 167346523522379206309758583)
    ·
      refine ⟨251019785283568809464637875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167346523522379206309758583 251019785283568809464637875)
      ·
        refine ⟨376529677925353214196956813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251019785283568809464637875 376529677925353214196956813)
        ·
          refine ⟨141198629222007455323858805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376529677925353214196956813 141198629222007455323858805)
          ·
            refine ⟨13237371489563198936611763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141198629222007455323858805 13237371489563198936611763)
            ·
              refine ⟨19856057234344798404917645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13237371489563198936611763 19856057234344798404917645)
              ·
                refine ⟨7446021462879299401844117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19856057234344798404917645 7446021462879299401844117)
                ·
                  refine ⟨349032256072467159461443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7446021462879299401844117 349032256072467159461443)
                  ·
                    rfl

theorem cell23_6117641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_6117641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117641 prefixEnd_6117641 := by exact prefixLift 6117641
  have htrace : WordTrace (prefixWord ++ tailWord_6117641) baseStart_6117641 baseEnd_6117641 := by
    simpa [prefixWord, tailWord_6117641, baseEnd_6117641] using wordTrace_append hprefix tailTrace_6117641
  have hstable : (prefixWord ++ tailWord_6117641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117641).length < 2 ^ (prefixWord ++ tailWord_6117641).sum := by decide
  have hdescent : baseEnd_6117641 < baseStart_6117641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117701 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_6117701 : Nat := 118140960795 + 6117701 * 2 ^ 59
def prefixEnd_6117701 : Nat := 4983230072969 + 3 ^ 40 * 6117701 * 2
def baseEnd_6117701 : Nat := 1047107037830491400134237

theorem tailTrace_6117701 : CollatzResearch.WordTrace tailWord_6117701 prefixEnd_6117701 1047107037830491400134237 := by
  unfold tailWord_6117701
  simp only [CollatzResearch.WordTrace]
  refine ⟨223130886409621571993528957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148753924273081047995685971 223130886409621571993528957)
  ·
    refine ⟨83674082403608089497573359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223130886409621571993528957 83674082403608089497573359)
    ·
      refine ⟨125511123605412134246360039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83674082403608089497573359 125511123605412134246360039)
      ·
        refine ⟨188266685408118201369540059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125511123605412134246360039 188266685408118201369540059)
        ·
          refine ⟨282400028112177302054310089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188266685408118201369540059 282400028112177302054310089)
          ·
            refine ⟨211800021084132976540732567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282400028112177302054310089 211800021084132976540732567)
            ·
              refine ⟨317700031626199464811098851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211800021084132976540732567 317700031626199464811098851)
              ·
                refine ⟨476550047439299197216648277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317700031626199464811098851 476550047439299197216648277)
                ·
                  refine ⟨5584570868429287467382597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 476550047439299197216648277 5584570868429287467382597)
                  ·
                    refine ⟨1047107037830491400134237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584570868429287467382597 1047107037830491400134237)
                    ·
                      rfl

theorem cell23_6117701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_6117701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117701 prefixEnd_6117701 := by exact prefixLift 6117701
  have htrace : WordTrace (prefixWord ++ tailWord_6117701) baseStart_6117701 baseEnd_6117701 := by
    simpa [prefixWord, tailWord_6117701, baseEnd_6117701] using wordTrace_append hprefix tailTrace_6117701
  have hstable : (prefixWord ++ tailWord_6117701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117701).length < 2 ^ (prefixWord ++ tailWord_6117701).sum := by decide
  have hdescent : baseEnd_6117701 < baseStart_6117701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117708 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6117708 : Nat := 118140960795 + 6117708 * 2 ^ 59
def prefixEnd_6117708 : Nat := 4983230072969 + 3 ^ 40 * 6117708 * 2
def baseEnd_6117708 : Nat := 3141324707856055673015179

theorem tailTrace_6117708 : CollatzResearch.WordTrace tailWord_6117708 prefixEnd_6117708 3141324707856055673015179 := by
  unfold tailWord_6117708
  simp only [CollatzResearch.WordTrace]
  refine ⟨111565570860298106094516889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148754094480397474792689185 111565570860298106094516889)
  ·
    refine ⟨83674178145223579570887667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111565570860298106094516889 83674178145223579570887667)
    ·
      refine ⟨125511267217835369356331501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83674178145223579570887667 125511267217835369356331501)
      ·
        refine ⟨47066725206688263508624313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125511267217835369356331501 47066725206688263508624313)
        ·
          refine ⟨35300043905016197631468235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47066725206688263508624313 35300043905016197631468235)
          ·
            refine ⟨52950065857524296447202353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35300043905016197631468235 52950065857524296447202353)
            ·
              refine ⟨39712549393143222335401765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52950065857524296447202353 39712549393143222335401765)
              ·
                refine ⟨7446103011214354187887831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39712549393143222335401765 7446103011214354187887831)
                ·
                  refine ⟨11169154516821531281831747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446103011214354187887831 11169154516821531281831747)
                  ·
                    refine ⟨16753731775232296922747621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11169154516821531281831747 16753731775232296922747621)
                    ·
                      refine ⟨3141324707856055673015179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16753731775232296922747621 3141324707856055673015179)
                      ·
                        rfl

theorem cell23_6117708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6117708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117708 prefixEnd_6117708 := by exact prefixLift 6117708
  have htrace : WordTrace (prefixWord ++ tailWord_6117708) baseStart_6117708 baseEnd_6117708 := by
    simpa [prefixWord, tailWord_6117708, baseEnd_6117708] using wordTrace_append hprefix tailTrace_6117708
  have hstable : (prefixWord ++ tailWord_6117708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117708).length < 2 ^ (prefixWord ++ tailWord_6117708).sum := by decide
  have hdescent : baseEnd_6117708 < baseStart_6117708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117726 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6117726 : Nat := 118140960795 + 6117726 * 2 ^ 59
def prefixEnd_6117726 : Nat := 4983230072969 + 3 ^ 40 * 6117726 * 2
def baseEnd_6117726 : Nat := 349037105611981844732233

theorem tailTrace_6117726 : CollatzResearch.WordTrace tailWord_6117726 prefixEnd_6117726 349037105611981844732233 := by
  unfold tailWord_6117726
  simp only [CollatzResearch.WordTrace]
  refine ⟨27891474779316375157898629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148754532156354000842126021 27891474779316375157898629)
  ·
    refine ⟨5229651521121820342105993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27891474779316375157898629 5229651521121820342105993)
    ·
      refine ⟨3922238640841365256579495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5229651521121820342105993 3922238640841365256579495)
      ·
        refine ⟨5883357961262047884869243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922238640841365256579495 5883357961262047884869243)
        ·
          refine ⟨8825036941893071827303865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883357961262047884869243 8825036941893071827303865)
          ·
            refine ⟨6618777706419803870477899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8825036941893071827303865 6618777706419803870477899)
            ·
              refine ⟨9928166559629705805716849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618777706419803870477899 9928166559629705805716849)
              ·
                refine ⟨7446124919722279354287637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9928166559629705805716849 7446124919722279354287637)
                ·
                  refine ⟨349037105611981844732233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7446124919722279354287637 349037105611981844732233)
                  ·
                    rfl

theorem cell23_6117726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6117726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117726 prefixEnd_6117726 := by exact prefixLift 6117726
  have htrace : WordTrace (prefixWord ++ tailWord_6117726) baseStart_6117726 baseEnd_6117726 := by
    simpa [prefixWord, tailWord_6117726, baseEnd_6117726] using wordTrace_append hprefix tailTrace_6117726
  have hstable : (prefixWord ++ tailWord_6117726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117726).length < 2 ^ (prefixWord ++ tailWord_6117726).sum := by decide
  have hdescent : baseEnd_6117726 < baseStart_6117726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117735 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 2, 4]
def baseStart_6117735 : Nat := 118140960795 + 6117735 * 2 ^ 59
def prefixEnd_6117735 : Nat := 4983230072969 + 3 ^ 40 * 6117735 * 2
def baseEnd_6117735 : Nat := 1047112857277909022459185

theorem tailTrace_6117735 : CollatzResearch.WordTrace tailWord_6117735 prefixEnd_6117735 1047112857277909022459185 := by
  unfold tailWord_6117735
  simp only [CollatzResearch.WordTrace]
  refine ⟨223132126491498395800266659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148754750994332263866844439 223132126491498395800266659)
  ·
    refine ⟨334698189737247593700399989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223132126491498395800266659 334698189737247593700399989)
    ·
      refine ⟨31377955287866961909412499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334698189737247593700399989 31377955287866961909412499)
      ·
        refine ⟨47066932931800442864118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31377955287866961909412499 47066932931800442864118749)
        ·
          refine ⟨17650099849425166074044531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47066932931800442864118749 17650099849425166074044531)
          ·
            refine ⟨26475149774137749111066797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17650099849425166074044531 26475149774137749111066797)
            ·
              refine ⟨9928181165301655916650049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26475149774137749111066797 9928181165301655916650049)
              ·
                refine ⟨7446135873976241937487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9928181165301655916650049 7446135873976241937487537)
                ·
                  refine ⟨5584601905482181453115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446135873976241937487537 5584601905482181453115653)
                  ·
                    refine ⟨1047112857277909022459185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584601905482181453115653 1047112857277909022459185)
                    ·
                      rfl

theorem cell23_6117735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_6117735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117735 prefixEnd_6117735 := by exact prefixLift 6117735
  have htrace : WordTrace (prefixWord ++ tailWord_6117735) baseStart_6117735 baseEnd_6117735 := by
    simpa [prefixWord, tailWord_6117735, baseEnd_6117735] using wordTrace_append hprefix tailTrace_6117735
  have hstable : (prefixWord ++ tailWord_6117735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117735).length < 2 ^ (prefixWord ++ tailWord_6117735).sum := by decide
  have hdescent : baseEnd_6117735 < baseStart_6117735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117771 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_6117771 : Nat := 118140960795 + 6117771 * 2 ^ 59
def prefixEnd_6117771 : Nat := 4983230072969 + 3 ^ 40 * 6117771 * 2
def baseEnd_6117771 : Nat := 3141357057137288926527389

theorem tailTrace_6117771 : CollatzResearch.WordTrace tailWord_6117771 prefixEnd_6117771 3141357057137288926527389 := by
  unfold tailWord_6117771
  simp only [CollatzResearch.WordTrace]
  refine ⟨223133439519367973948577167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148755626346245315965718111 223133439519367973948577167)
  ·
    refine ⟨334700159279051960922865751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223133439519367973948577167 334700159279051960922865751)
    ·
      refine ⟨502050238918577941384298627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334700159279051960922865751 502050238918577941384298627)
      ·
        refine ⟨753075358377866912076447941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502050238918577941384298627 753075358377866912076447941)
        ·
          refine ⟨141201629695850046014333989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 753075358377866912076447941 141201629695850046014333989)
          ·
            refine ⟨26475305567971883627687623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141201629695850046014333989 26475305567971883627687623)
            ·
              refine ⟨39712958351957825441531435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26475305567971883627687623 39712958351957825441531435)
              ·
                refine ⟨59569437527936738162297153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39712958351957825441531435 59569437527936738162297153)
                ·
                  refine ⟨44677078145952553621722865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59569437527936738162297153 44677078145952553621722865)
                  ·
                    refine ⟨33507808609464415216292149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44677078145952553621722865 33507808609464415216292149)
                    ·
                      refine ⟨3141357057137288926527389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33507808609464415216292149 3141357057137288926527389)
                      ·
                        rfl

theorem cell23_6117771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_6117771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117771 prefixEnd_6117771 := by exact prefixLift 6117771
  have htrace : WordTrace (prefixWord ++ tailWord_6117771) baseStart_6117771 baseEnd_6117771 := by
    simpa [prefixWord, tailWord_6117771, baseEnd_6117771] using wordTrace_append hprefix tailTrace_6117771
  have hstable : (prefixWord ++ tailWord_6117771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117771).length < 2 ^ (prefixWord ++ tailWord_6117771).sum := by decide
  have hdescent : baseEnd_6117771 < baseStart_6117771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117781 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_6117781 : Nat := 118140960795 + 6117781 * 2 ^ 59
def prefixEnd_6117781 : Nat := 4983230072969 + 3 ^ 40 * 6117781 * 2
def baseEnd_6117781 : Nat := 3141362191943833887402343

theorem tailTrace_6117781 : CollatzResearch.WordTrace tailWord_6117781 prefixEnd_6117781 3141362191943833887402343 := by
  unfold tailWord_6117781
  simp only [CollatzResearch.WordTrace]
  refine ⟨223133804249331745656441197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148755869499554497104294131 223133804249331745656441197)
  ·
    refine ⟨83675176593499404621165449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223133804249331745656441197 83675176593499404621165449)
    ·
      refine ⟨62756382445124553465874087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83675176593499404621165449 62756382445124553465874087)
      ·
        refine ⟨94134573667686830198811131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62756382445124553465874087 94134573667686830198811131)
        ·
          refine ⟨141201860501530245298216697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94134573667686830198811131 141201860501530245298216697)
          ·
            refine ⟨105901395376147683973662523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141201860501530245298216697 105901395376147683973662523)
            ·
              refine ⟨158852093064221525960493785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105901395376147683973662523 158852093064221525960493785)
              ·
                refine ⟨119139069798166144470370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158852093064221525960493785 119139069798166144470370339)
                ·
                  refine ⟨178708604697249216705555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119139069798166144470370339 178708604697249216705555509)
                  ·
                    refine ⟨16753931690367114066145829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178708604697249216705555509 16753931690367114066145829)
                    ·
                      refine ⟨3141362191943833887402343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16753931690367114066145829 3141362191943833887402343)
                      ·
                        rfl

theorem cell23_6117781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_6117781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117781 prefixEnd_6117781 := by exact prefixLift 6117781
  have htrace : WordTrace (prefixWord ++ tailWord_6117781) baseStart_6117781 baseEnd_6117781 := by
    simpa [prefixWord, tailWord_6117781, baseEnd_6117781] using wordTrace_append hprefix tailTrace_6117781
  have hstable : (prefixWord ++ tailWord_6117781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117781).length < 2 ^ (prefixWord ++ tailWord_6117781).sum := by decide
  have hdescent : baseEnd_6117781 < baseStart_6117781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117785 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 1, 3, 2]
def baseStart_6117785 : Nat := 118140960795 + 6117785 * 2 ^ 59
def prefixEnd_6117785 : Nat := 4983230072969 + 3 ^ 40 * 6117785 * 2
def baseEnd_6117785 : Nat := 3141364245866451871752325

theorem tailTrace_6117785 : CollatzResearch.WordTrace tailWord_6117785 prefixEnd_6117785 3141364245866451871752325 := by
  unfold tailWord_6117785
  simp only [CollatzResearch.WordTrace]
  refine ⟨223133950141317254339586809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148755966760878169559724539 223133950141317254339586809)
  ·
    refine ⟨167350462605987940754690107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223133950141317254339586809 167350462605987940754690107)
    ·
      refine ⟨251025693908981911132035161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167350462605987940754690107 251025693908981911132035161)
      ·
        refine ⟨188269270431736433349026371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251025693908981911132035161 188269270431736433349026371)
        ·
          refine ⟨282403905647604650023539557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188269270431736433349026371 282403905647604650023539557)
          ·
            refine ⟨52950732308925871879413667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282403905647604650023539557 52950732308925871879413667)
            ·
              refine ⟨79426098463388807819120501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52950732308925871879413667 79426098463388807819120501)
              ·
                refine ⟨7446196730942700733042547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79426098463388807819120501 7446196730942700733042547)
                ·
                  refine ⟨11169295096414051099563821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446196730942700733042547 11169295096414051099563821)
                  ·
                    refine ⟨4188485661155269162336433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11169295096414051099563821 4188485661155269162336433)
                    ·
                      refine ⟨3141364245866451871752325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188485661155269162336433 3141364245866451871752325)
                      ·
                        rfl

theorem cell23_6117785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_6117785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117785 prefixEnd_6117785 := by exact prefixLift 6117785
  have htrace : WordTrace (prefixWord ++ tailWord_6117785) baseStart_6117785 baseEnd_6117785 := by
    simpa [prefixWord, tailWord_6117785, baseEnd_6117785] using wordTrace_append hprefix tailTrace_6117785
  have hstable : (prefixWord ++ tailWord_6117785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117785).length < 2 ^ (prefixWord ++ tailWord_6117785).sum := by decide
  have hdescent : baseEnd_6117785 < baseStart_6117785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117793 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6117793 : Nat := 118140960795 + 6117793 * 2 ^ 59
def prefixEnd_6117793 : Nat := 4983230072969 + 3 ^ 40 * 6117793 * 2
def baseEnd_6117793 : Nat := 3141368353711687840452289

theorem tailTrace_6117793 : CollatzResearch.WordTrace tailWord_6117793 prefixEnd_6117793 3141368353711687840452289 := by
  unfold tailWord_6117793
  simp only [CollatzResearch.WordTrace]
  refine ⟨223134241925288271705878033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148756161283525514470585355 223134241925288271705878033)
  ·
    refine ⟨167350681443966203779408525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223134241925288271705878033 167350681443966203779408525)
    ·
      refine ⟨62756505541487326417278197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167350681443966203779408525 62756505541487326417278197)
      ·
        refine ⟨5883422394514436851619831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62756505541487326417278197 5883422394514436851619831)
        ·
          refine ⟨8825133591771655277429747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883422394514436851619831 8825133591771655277429747)
          ·
            refine ⟨13237700387657482916144621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8825133591771655277429747 13237700387657482916144621)
            ·
              refine ⟨4964137645371556093554233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13237700387657482916144621 4964137645371556093554233)
              ·
                refine ⟨3723103234028667070165675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964137645371556093554233 3723103234028667070165675)
                ·
                  refine ⟨5584654851043000605248513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723103234028667070165675 5584654851043000605248513)
                  ·
                    refine ⟨4188491138282250453936385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584654851043000605248513 4188491138282250453936385)
                    ·
                      refine ⟨3141368353711687840452289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188491138282250453936385 3141368353711687840452289)
                      ·
                        rfl

theorem cell23_6117793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6117793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117793 prefixEnd_6117793 := by exact prefixLift 6117793
  have htrace : WordTrace (prefixWord ++ tailWord_6117793) baseStart_6117793 baseEnd_6117793 := by
    simpa [prefixWord, tailWord_6117793, baseEnd_6117793] using wordTrace_append hprefix tailTrace_6117793
  have hstable : (prefixWord ++ tailWord_6117793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117793).length < 2 ^ (prefixWord ++ tailWord_6117793).sum := by decide
  have hdescent : baseEnd_6117793 < baseStart_6117793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117809 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6117809 : Nat := 118140960795 + 6117809 * 2 ^ 59
def prefixEnd_6117809 : Nat := 4983230072969 + 3 ^ 40 * 6117809 * 2
def baseEnd_6117809 : Nat := 3141376569402159777852215

theorem tailTrace_6117809 : CollatzResearch.WordTrace tailWord_6117809 prefixEnd_6117809 3141376569402159777852215 := by
  unfold tailWord_6117809
  simp only [CollatzResearch.WordTrace]
  refine ⟨223134825493230306438460481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148756550328820204292306987 223134825493230306438460481)
  ·
    refine ⟨167351119119922729828845361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223134825493230306438460481 167351119119922729828845361)
    ·
      refine ⟨125513339339942047371634021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167351119119922729828845361 125513339339942047371634021)
      ·
        refine ⟨23533751126239133882181379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125513339339942047371634021 23533751126239133882181379)
        ·
          refine ⟨35300626689358700823272069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23533751126239133882181379 35300626689358700823272069)
          ·
            refine ⟨6618867504254756404363513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35300626689358700823272069 6618867504254756404363513)
            ·
              refine ⟨4964150628191067303272635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618867504254756404363513 4964150628191067303272635)
              ·
                refine ⟨7446225942286600954908953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964150628191067303272635 7446225942286600954908953)
                ·
                  refine ⟨5584669456714950716181715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446225942286600954908953 5584669456714950716181715)
                  ·
                    refine ⟨8377004185072426074272573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584669456714950716181715 8377004185072426074272573)
                    ·
                      refine ⟨3141376569402159777852215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377004185072426074272573 3141376569402159777852215)
                      ·
                        rfl

theorem cell23_6117809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6117809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117809 prefixEnd_6117809 := by exact prefixLift 6117809
  have htrace : WordTrace (prefixWord ++ tailWord_6117809) baseStart_6117809 baseEnd_6117809 := by
    simpa [prefixWord, tailWord_6117809, baseEnd_6117809] using wordTrace_append hprefix tailTrace_6117809
  have hstable : (prefixWord ++ tailWord_6117809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117809).length < 2 ^ (prefixWord ++ tailWord_6117809).sum := by decide
  have hdescent : baseEnd_6117809 < baseStart_6117809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117848 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_6117848 : Nat := 118140960795 + 6117848 * 2 ^ 59
def prefixEnd_6117848 : Nat := 4983230072969 + 3 ^ 40 * 6117848 * 2
def baseEnd_6117848 : Nat := 3141396595147685125264535

theorem tailTrace_6117848 : CollatzResearch.WordTrace tailWord_6117848 prefixEnd_6117848 3141396595147685125264535 := by
  unfold tailWord_6117848
  simp only [CollatzResearch.WordTrace]
  refine ⟨111568123970044508049565099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148757498626726010732753465 111568123970044508049565099)
  ·
    refine ⟨167352185955066762074347649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111568123970044508049565099 167352185955066762074347649)
    ·
      refine ⟨125514139466300071555760737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167352185955066762074347649 125514139466300071555760737)
      ·
        refine ⟨94135604599725053666820553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125514139466300071555760737 94135604599725053666820553)
        ·
          refine ⟨70601703449793790250115415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94135604599725053666820553 70601703449793790250115415)
          ·
            refine ⟨105902555174690685375173123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70601703449793790250115415 105902555174690685375173123)
            ·
              refine ⟨158853832762036028062759685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105902555174690685375173123 158853832762036028062759685)
              ·
                refine ⟨29785093642881755261767441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158853832762036028062759685 29785093642881755261767441)
                ·
                  refine ⟨22338820232161316446325581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29785093642881755261767441 22338820232161316446325581)
                  ·
                    refine ⟨8377057587060493667372093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22338820232161316446325581 8377057587060493667372093)
                    ·
                      refine ⟨3141396595147685125264535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377057587060493667372093 3141396595147685125264535)
                      ·
                        rfl

theorem cell23_6117848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_6117848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117848 prefixEnd_6117848 := by exact prefixLift 6117848
  have htrace : WordTrace (prefixWord ++ tailWord_6117848) baseStart_6117848 baseEnd_6117848 := by
    simpa [prefixWord, tailWord_6117848, baseEnd_6117848] using wordTrace_append hprefix tailTrace_6117848
  have hstable : (prefixWord ++ tailWord_6117848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117848).length < 2 ^ (prefixWord ++ tailWord_6117848).sum := by decide
  have hdescent : baseEnd_6117848 < baseStart_6117848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117855 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 5]
def baseStart_6117855 : Nat := 118140960795 + 6117855 * 2 ^ 59
def prefixEnd_6117855 : Nat := 4983230072969 + 3 ^ 40 * 6117855 * 2
def baseEnd_6117855 : Nat := 349044465501362955319667

theorem tailTrace_6117855 : CollatzResearch.WordTrace tailWord_6117855 prefixEnd_6117855 349044465501362955319667 := by
  unfold tailWord_6117855
  simp only [CollatzResearch.WordTrace]
  refine ⟨223136503251063656294635019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148757668834042437529756679 223136503251063656294635019)
  ·
    refine ⟨334704754876595484441952529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223136503251063656294635019 334704754876595484441952529)
    ·
      refine ⟨251028566157446613331464397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334704754876595484441952529 251028566157446613331464397)
      ·
        refine ⟨94135712309042479999299149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251028566157446613331464397 94135712309042479999299149)
        ·
          refine ⟨35300892115890929999737181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94135712309042479999299149 35300892115890929999737181)
          ·
            refine ⟨13237834543459098749901443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35300892115890929999737181 13237834543459098749901443)
            ·
              refine ⟨19856751815188648124852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13237834543459098749901443 19856751815188648124852165)
              ·
                refine ⟨3723140965347871523409781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19856751815188648124852165 3723140965347871523409781)
                ·
                  refine ⟨349044465501362955319667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3723140965347871523409781 349044465501362955319667)
                  ·
                    rfl

theorem cell23_6117855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 5].length) (baseStart_6117855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117855 prefixEnd_6117855 := by exact prefixLift 6117855
  have htrace : WordTrace (prefixWord ++ tailWord_6117855) baseStart_6117855 baseEnd_6117855 := by
    simpa [prefixWord, tailWord_6117855, baseEnd_6117855] using wordTrace_append hprefix tailTrace_6117855
  have hstable : (prefixWord ++ tailWord_6117855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117855).length < 2 ^ (prefixWord ++ tailWord_6117855).sum := by decide
  have hdescent : baseEnd_6117855 < baseStart_6117855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117942 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6117942 : Nat := 118140960795 + 6117942 * 2 ^ 59
def prefixEnd_6117942 : Nat := 4983230072969 + 3 ^ 40 * 6117942 * 2
def baseEnd_6117942 : Nat := 3141444862329207757489103

theorem tailTrace_6117942 : CollatzResearch.WordTrace tailWord_6117942 prefixEnd_6117942 3141444862329207757489103 := by
  unfold tailWord_6117942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13946229775109279384565755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148759784267832313435368053 13946229775109279384565755)
  ·
    refine ⟨20919344662663919076848633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13946229775109279384565755 20919344662663919076848633)
    ·
      refine ⟨15689508496997939307636475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20919344662663919076848633 15689508496997939307636475)
      ·
        refine ⟨23534262745496908961454713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689508496997939307636475 23534262745496908961454713)
        ·
          refine ⟨17650697059122681721091035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23534262745496908961454713 17650697059122681721091035)
          ·
            refine ⟨26476045588684022581636553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17650697059122681721091035 26476045588684022581636553)
            ·
              refine ⟨19857034191513016936227415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26476045588684022581636553 19857034191513016936227415)
              ·
                refine ⟨29785551287269525404341123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19857034191513016936227415 29785551287269525404341123)
                ·
                  refine ⟨44678326930904288106511685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29785551287269525404341123 44678326930904288106511685)
                  ·
                    refine ⟨8377186299544554019970941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44678326930904288106511685 8377186299544554019970941)
                    ·
                      refine ⟨3141444862329207757489103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377186299544554019970941 3141444862329207757489103)
                      ·
                        rfl

theorem cell23_6117942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6117942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117942 prefixEnd_6117942 := by exact prefixLift 6117942
  have htrace : WordTrace (prefixWord ++ tailWord_6117942) baseStart_6117942 baseEnd_6117942 := by
    simpa [prefixWord, tailWord_6117942, baseEnd_6117942] using wordTrace_append hprefix tailTrace_6117942
  have hstable : (prefixWord ++ tailWord_6117942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117942).length < 2 ^ (prefixWord ++ tailWord_6117942).sum := by decide
  have hdescent : baseEnd_6117942 < baseStart_6117942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117949 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_6117949 : Nat := 118140960795 + 6117949 * 2 ^ 59
def prefixEnd_6117949 : Nat := 4983230072969 + 3 ^ 40 * 6117949 * 2
def baseEnd_6117949 : Nat := 1047149485564596410033857

theorem tailTrace_6117949 : CollatzResearch.WordTrace tailWord_6117949 prefixEnd_6117949 1047149485564596410033857 := by
  unfold tailWord_6117949
  simp only [CollatzResearch.WordTrace]
  refine ⟨223139931712723110348556901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148759954475148740232371267 223139931712723110348556901)
  ·
    refine ⟨41838737196135583190354419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223139931712723110348556901 41838737196135583190354419)
    ·
      refine ⟨62758105794203374785531629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41838737196135583190354419 62758105794203374785531629)
      ·
        refine ⟨23534289672826265544574361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62758105794203374785531629 23534289672826265544574361)
        ·
          refine ⟨17650717254619699158430771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23534289672826265544574361 17650717254619699158430771)
          ·
            refine ⟨26476075881929548737646157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17650717254619699158430771 26476075881929548737646157)
            ·
              refine ⟨9928528455723580776617309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26476075881929548737646157 9928528455723580776617309)
              ·
                refine ⟨3723198170896342791231491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9928528455723580776617309 3723198170896342791231491)
                ·
                  refine ⟨5584797256344514186847237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723198170896342791231491 5584797256344514186847237)
                  ·
                    refine ⟨1047149485564596410033857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5584797256344514186847237 1047149485564596410033857)
                    ·
                      rfl

theorem cell23_6117949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_6117949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117949 prefixEnd_6117949 := by exact prefixLift 6117949
  have htrace : WordTrace (prefixWord ++ tailWord_6117949) baseStart_6117949 baseEnd_6117949 := by
    simpa [prefixWord, tailWord_6117949, baseEnd_6117949] using wordTrace_append hprefix tailTrace_6117949
  have hstable : (prefixWord ++ tailWord_6117949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117949).length < 2 ^ (prefixWord ++ tailWord_6117949).sum := by decide
  have hdescent : baseEnd_6117949 < baseStart_6117949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117955 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 3]
def baseStart_6117955 : Nat := 118140960795 + 6117955 * 2 ^ 59
def prefixEnd_6117955 : Nat := 4983230072969 + 3 ^ 40 * 6117955 * 2
def baseEnd_6117955 : Nat := 3141451537577716206626543

theorem tailTrace_6117955 : CollatzResearch.WordTrace tailWord_6117955 prefixEnd_6117955 3141451537577716206626543 := by
  unfold tailWord_6117955
  simp only [CollatzResearch.WordTrace]
  refine ⟨223140150550701373373275319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148760100367134248915516879 223140150550701373373275319)
  ·
    refine ⟨334710225826052060059912979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223140150550701373373275319 334710225826052060059912979)
    ·
      refine ⟨502065338739078090089869469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334710225826052060059912979 502065338739078090089869469)
      ·
        refine ⟨188274502027154283783701051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502065338739078090089869469 188274502027154283783701051)
        ·
          refine ⟨282411753040731425675551577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188274502027154283783701051 282411753040731425675551577)
          ·
            refine ⟨211808814780548569256663683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282411753040731425675551577 211808814780548569256663683)
            ·
              refine ⟨317713222170822853884995525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211808814780548569256663683 317713222170822853884995525)
              ·
                refine ⟨59571229157029285103436661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317713222170822853884995525 59571229157029285103436661)
                ·
                  refine ⟨5584802733471495478447187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59571229157029285103436661 5584802733471495478447187)
                  ·
                    refine ⟨8377204100207243217670781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584802733471495478447187 8377204100207243217670781)
                    ·
                      refine ⟨3141451537577716206626543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377204100207243217670781 3141451537577716206626543)
                      ·
                        rfl

theorem cell23_6117955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_6117955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117955 prefixEnd_6117955 := by exact prefixLift 6117955
  have htrace : WordTrace (prefixWord ++ tailWord_6117955) baseStart_6117955 baseEnd_6117955 := by
    simpa [prefixWord, tailWord_6117955, baseEnd_6117955] using wordTrace_append hprefix tailTrace_6117955
  have hstable : (prefixWord ++ tailWord_6117955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117955).length < 2 ^ (prefixWord ++ tailWord_6117955).sum := by decide
  have hdescent : baseEnd_6117955 < baseStart_6117955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117956 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6117956 : Nat := 118140960795 + 6117956 * 2 ^ 59
def prefixEnd_6117956 : Nat := 4983230072969 + 3 ^ 40 * 6117956 * 2
def baseEnd_6117956 : Nat := 3141452051058370702714039

theorem tailTrace_6117956 : CollatzResearch.WordTrace tailWord_6117956 prefixEnd_6117956 3141452051058370702714039 := by
  unfold tailWord_6117956
  simp only [CollatzResearch.WordTrace]
  refine ⟨111570093511848875272030861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148760124682465167029374481 111570093511848875272030861)
  ·
    refine ⟨41838785066943328227011573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111570093511848875272030861 41838785066943328227011573)
    ·
      refine ⟨3922386100025937021282335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41838785066943328227011573 3922386100025937021282335)
      ·
        refine ⟨5883579150038905531923503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922386100025937021282335 5883579150038905531923503)
        ·
          refine ⟨8825368725058358297885255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883579150038905531923503 8825368725058358297885255)
          ·
            refine ⟨13238053087587537446827883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8825368725058358297885255 13238053087587537446827883)
            ·
              refine ⟨19857079631381306170241825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13238053087587537446827883 19857079631381306170241825)
              ·
                refine ⟨14892809723535979627681369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19857079631381306170241825 14892809723535979627681369)
                ·
                  refine ⟨11169607292651984720761027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14892809723535979627681369 11169607292651984720761027)
                  ·
                    refine ⟨16754410938977977081141541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11169607292651984720761027 16754410938977977081141541)
                    ·
                      refine ⟨3141452051058370702714039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16754410938977977081141541 3141452051058370702714039)
                      ·
                        rfl

theorem cell23_6117956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6117956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117956 prefixEnd_6117956 := by exact prefixLift 6117956
  have htrace : WordTrace (prefixWord ++ tailWord_6117956) baseStart_6117956 baseEnd_6117956 := by
    simpa [prefixWord, tailWord_6117956, baseEnd_6117956] using wordTrace_append hprefix tailTrace_6117956
  have hstable : (prefixWord ++ tailWord_6117956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117956).length < 2 ^ (prefixWord ++ tailWord_6117956).sum := by decide
  have hdescent : baseEnd_6117956 < baseStart_6117956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117978 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_6117978 : Nat := 118140960795 + 6117978 * 2 ^ 59
def prefixEnd_6117978 : Nat := 4983230072969 + 3 ^ 40 * 6117978 * 2
def baseEnd_6117978 : Nat := 3141463347632769616638937

theorem tailTrace_6117978 : CollatzResearch.WordTrace tailWord_6117978 prefixEnd_6117978 3141463347632769616638937 := by
  unfold tailWord_6117978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55785247357404512075340647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148760659619745365534241725 55785247357404512075340647)
  ·
    refine ⟨83677871036106768113010971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55785247357404512075340647 83677871036106768113010971)
    ·
      refine ⟨125516806554160152169516457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83677871036106768113010971 125516806554160152169516457)
      ·
        refine ⟨94137604915620114127137343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125516806554160152169516457 94137604915620114127137343)
        ·
          refine ⟨141206407373430171190706015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94137604915620114127137343 141206407373430171190706015)
          ·
            refine ⟨211809611060145256786059023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141206407373430171190706015 211809611060145256786059023)
            ·
              refine ⟨317714416590217885179088535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211809611060145256786059023 317714416590217885179088535)
              ·
                refine ⟨476571624885326827768632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317714416590217885179088535 476571624885326827768632803)
                ·
                  refine ⟨714857437327990241652949205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476571624885326827768632803 714857437327990241652949205)
                  ·
                    refine ⟨16754471187374771288740997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 714857437327990241652949205 16754471187374771288740997)
                    ·
                      refine ⟨3141463347632769616638937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16754471187374771288740997 3141463347632769616638937)
                      ·
                        rfl

theorem cell23_6117978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_6117978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117978 prefixEnd_6117978 := by exact prefixLift 6117978
  have htrace : WordTrace (prefixWord ++ tailWord_6117978) baseStart_6117978 baseEnd_6117978 := by
    simpa [prefixWord, tailWord_6117978, baseEnd_6117978] using wordTrace_append hprefix tailTrace_6117978
  have hstable : (prefixWord ++ tailWord_6117978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117978).length < 2 ^ (prefixWord ++ tailWord_6117978).sum := by decide
  have hdescent : baseEnd_6117978 < baseStart_6117978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117992 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6117992 : Nat := 118140960795 + 6117992 * 2 ^ 59
def prefixEnd_6117992 : Nat := 4983230072969 + 3 ^ 40 * 6117992 * 2
def baseEnd_6117992 : Nat := 1047156845453977520621291

theorem tailTrace_6117992 : CollatzResearch.WordTrace tailWord_6117992 prefixEnd_6117992 1047156845453977520621291 := by
  unfold tailWord_6117992
  simp only [CollatzResearch.WordTrace]
  refine ⟨111570750025783664346186115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148761000034378219128248153 111570750025783664346186115)
  ·
    refine ⟨167356125038675496519279173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111570750025783664346186115 167356125038675496519279173)
    ·
      refine ⟨31379273444751655597364845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167356125038675496519279173 31379273444751655597364845)
      ·
        refine ⟨11767227541781870849011817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31379273444751655597364845 11767227541781870849011817)
        ·
          refine ⟨8825420656336403136758863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11767227541781870849011817 8825420656336403136758863)
          ·
            refine ⟨13238130984504604705138295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8825420656336403136758863 13238130984504604705138295)
            ·
              refine ⟨19857196476756907057707443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13238130984504604705138295 19857196476756907057707443)
              ·
                refine ⟨29785794715135360586561165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19857196476756907057707443 29785794715135360586561165)
                ·
                  refine ⟨11169673018175760219960437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29785794715135360586561165 11169673018175760219960437)
                  ·
                    refine ⟨1047156845453977520621291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11169673018175760219960437 1047156845453977520621291)
                    ·
                      rfl

theorem cell23_6117992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6117992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117992 prefixEnd_6117992 := by exact prefixLift 6117992
  have htrace : WordTrace (prefixWord ++ tailWord_6117992) baseStart_6117992 baseEnd_6117992 := by
    simpa [prefixWord, tailWord_6117992, baseEnd_6117992] using wordTrace_append hprefix tailTrace_6117992
  have hstable : (prefixWord ++ tailWord_6117992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117992).length < 2 ^ (prefixWord ++ tailWord_6117992).sum := by decide
  have hdescent : baseEnd_6117992 < baseStart_6117992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6117995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 4]
def baseStart_6117995 : Nat := 118140960795 + 6117995 * 2 ^ 59
def prefixEnd_6117995 : Nat := 4983230072969 + 3 ^ 40 * 6117995 * 2
def baseEnd_6117995 : Nat := 3141472076803896050126359

theorem tailTrace_6117995 : CollatzResearch.WordTrace tailWord_6117995 prefixEnd_6117995 3141472076803896050126359 := by
  unfold tailWord_6117995
  simp only [CollatzResearch.WordTrace]
  refine ⟨223141609470556460204731439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148761072980370973469820959 223141609470556460204731439)
  ·
    refine ⟨334712414205834690307097159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223141609470556460204731439 334712414205834690307097159)
    ·
      refine ⟨502068621308752035460645739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334712414205834690307097159 502068621308752035460645739)
      ·
        refine ⟨753102931963128053190968609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502068621308752035460645739 753102931963128053190968609)
        ·
          refine ⟨564827198972346039893226457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753102931963128053190968609 564827198972346039893226457)
          ·
            refine ⟨423620399229259529919919843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564827198972346039893226457 423620399229259529919919843)
            ·
              refine ⟨635430598843889294879879765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423620399229259529919919843 635430598843889294879879765)
              ·
                refine ⟨7446452330201827674373591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 635430598843889294879879765 7446452330201827674373591)
                ·
                  refine ⟨11169678495302741511560387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446452330201827674373591 11169678495302741511560387)
                  ·
                    refine ⟨16754517742954112267340581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11169678495302741511560387 16754517742954112267340581)
                    ·
                      refine ⟨3141472076803896050126359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16754517742954112267340581 3141472076803896050126359)
                      ·
                        rfl

theorem cell23_6117995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 4].length) (baseStart_6117995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6117995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6117995 prefixEnd_6117995 := by exact prefixLift 6117995
  have htrace : WordTrace (prefixWord ++ tailWord_6117995) baseStart_6117995 baseEnd_6117995 := by
    simpa [prefixWord, tailWord_6117995, baseEnd_6117995] using wordTrace_append hprefix tailTrace_6117995
  have hstable : (prefixWord ++ tailWord_6117995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6117995).length < 2 ^ (prefixWord ++ tailWord_6117995).sum := by decide
  have hdescent : baseEnd_6117995 < baseStart_6117995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6117995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6118028 : Nat := 118140960795 + 6118028 * 2 ^ 59
def prefixEnd_6118028 : Nat := 4983230072969 + 3 ^ 40 * 6118028 * 2
def baseEnd_6118028 : Nat := 3141489021665494421013707

theorem tailTrace_6118028 : CollatzResearch.WordTrace tailWord_6118028 prefixEnd_6118028 3141489021665494421013707 := by
  unfold tailWord_6118028
  simp only [CollatzResearch.WordTrace]
  refine ⟨111571406539718453420341369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148761875386291271227121825 111571406539718453420341369)
  ·
    refine ⟨83678554904788840065256027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111571406539718453420341369 83678554904788840065256027)
    ·
      refine ⟨125517832357183260097884041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83678554904788840065256027 125517832357183260097884041)
      ·
        refine ⟨94138374267887445073413031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125517832357183260097884041 94138374267887445073413031)
        ·
          refine ⟨141207561401831167610119547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94138374267887445073413031 141207561401831167610119547)
          ·
            refine ⟨211811342102746751415179321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141207561401831167610119547 211811342102746751415179321)
            ·
              refine ⟨158858506577060063561384491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211811342102746751415179321 158858506577060063561384491)
              ·
                refine ⟨238287759865590095342076737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158858506577060063561384491 238287759865590095342076737)
                ·
                  refine ⟨178715819899192571506557553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238287759865590095342076737 178715819899192571506557553)
                  ·
                    refine ⟨134036864924394428629918165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178715819899192571506557553 134036864924394428629918165)
                    ·
                      refine ⟨3141489021665494421013707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134036864924394428629918165 3141489021665494421013707)
                      ·
                        rfl

theorem cell23_6118028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6118028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118028 prefixEnd_6118028 := by exact prefixLift 6118028
  have htrace : WordTrace (prefixWord ++ tailWord_6118028) baseStart_6118028 baseEnd_6118028 := by
    simpa [prefixWord, tailWord_6118028, baseEnd_6118028] using wordTrace_append hprefix tailTrace_6118028
  have hstable : (prefixWord ++ tailWord_6118028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118028).length < 2 ^ (prefixWord ++ tailWord_6118028).sum := by decide
  have hdescent : baseEnd_6118028 < baseStart_6118028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118046 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6118046 : Nat := 118140960795 + 6118046 * 2 ^ 59
def prefixEnd_6118046 : Nat := 4983230072969 + 3 ^ 40 * 6118046 * 2
def baseEnd_6118046 : Nat := 3141498264317275350588625

theorem tailTrace_6118046 : CollatzResearch.WordTrace tailWord_6118046 prefixEnd_6118046 3141498264317275350588625 := by
  unfold tailWord_6118046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892933699171461989354749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148762313062247797276558661 27892933699171461989354749)
  ·
    refine ⟨10459850137189298246008031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27892933699171461989354749 10459850137189298246008031)
    ·
      refine ⟨15689775205783947369012047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459850137189298246008031 15689775205783947369012047)
      ·
        refine ⟨23534662808675921053518071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689775205783947369012047 23534662808675921053518071)
        ·
          refine ⟨35301994213013881580277107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23534662808675921053518071 35301994213013881580277107)
          ·
            refine ⟨52952991319520822370415661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35301994213013881580277107 52952991319520822370415661)
            ·
              refine ⟨19857371744820308388905873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52952991319520822370415661 19857371744820308388905873)
              ·
                refine ⟨14893028808615231291679405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19857371744820308388905873 14893028808615231291679405)
                ·
                  refine ⟨5584885803230711734379777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14893028808615231291679405 5584885803230711734379777)
                  ·
                    refine ⟨4188664352423033800784833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584885803230711734379777 4188664352423033800784833)
                    ·
                      refine ⟨3141498264317275350588625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188664352423033800784833 3141498264317275350588625)
                      ·
                        rfl

theorem cell23_6118046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6118046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118046 prefixEnd_6118046 := by exact prefixLift 6118046
  have htrace : WordTrace (prefixWord ++ tailWord_6118046) baseStart_6118046 baseEnd_6118046 := by
    simpa [prefixWord, tailWord_6118046, baseEnd_6118046] using wordTrace_append hprefix tailTrace_6118046
  have hstable : (prefixWord ++ tailWord_6118046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118046).length < 2 ^ (prefixWord ++ tailWord_6118046).sum := by decide
  have hdescent : baseEnd_6118046 < baseStart_6118046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118079 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_6118079 : Nat := 118140960795 + 6118079 * 2 ^ 59
def prefixEnd_6118079 : Nat := 4983230072969 + 3 ^ 40 * 6118079 * 2
def baseEnd_6118079 : Nat := 3141515209178873721475973

theorem tailTrace_6118079 : CollatzResearch.WordTrace tailWord_6118079 prefixEnd_6118079 3141515209178873721475973 := by
  unfold tailWord_6118079
  simp only [CollatzResearch.WordTrace]
  refine ⟨223144673202252142550789291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148763115468168095033859527 223144673202252142550789291)
  ·
    refine ⟨334717009803378213826183937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223144673202252142550789291 334717009803378213826183937)
    ·
      refine ⟨251037757352533660369637953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334717009803378213826183937 251037757352533660369637953)
      ·
        refine ⟨188278318014400245277228465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251037757352533660369637953 188278318014400245277228465)
        ·
          refine ⟨141208738510800183957921349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188278318014400245277228465 141208738510800183957921349)
          ·
            refine ⟨26476638470775034492110253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141208738510800183957921349 26476638470775034492110253)
            ·
              refine ⟨9928739426540637934541345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26476638470775034492110253 9928739426540637934541345)
              ·
                refine ⟨7446554569905478450906009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9928739426540637934541345 7446554569905478450906009)
                ·
                  refine ⟨5584915927429108838179507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446554569905478450906009 5584915927429108838179507)
                  ·
                    refine ⟨8377373891143663257269261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5584915927429108838179507 8377373891143663257269261)
                    ·
                      refine ⟨3141515209178873721475973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377373891143663257269261 3141515209178873721475973)
                      ·
                        rfl

theorem cell23_6118079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_6118079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118079 prefixEnd_6118079 := by exact prefixLift 6118079
  have htrace : WordTrace (prefixWord ++ tailWord_6118079) baseStart_6118079 baseEnd_6118079 := by
    simpa [prefixWord, tailWord_6118079, baseEnd_6118079] using wordTrace_append hprefix tailTrace_6118079
  have hstable : (prefixWord ++ tailWord_6118079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118079).length < 2 ^ (prefixWord ++ tailWord_6118079).sum := by decide
  have hdescent : baseEnd_6118079 < baseStart_6118079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118093 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6118093 : Nat := 118140960795 + 6118093 * 2 ^ 59
def prefixEnd_6118093 : Nat := 4983230072969 + 3 ^ 40 * 6118093 * 2
def baseEnd_6118093 : Nat := 3141522397908036666700909

theorem tailTrace_6118093 : CollatzResearch.WordTrace tailWord_6118093 prefixEnd_6118093 3141522397908036666700909 := by
  unfold tailWord_6118093
  simp only [CollatzResearch.WordTrace]
  refine ⟨223145183824201422941798933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148763455882800948627865955 223145183824201422941798933)
  ·
    refine ⟨10459930491759441700396825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223145183824201422941798933 10459930491759441700396825)
    ·
      refine ⟨7844947868819581275297619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10459930491759441700396825 7844947868819581275297619)
      ·
        refine ⟨11767421803229371912946429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7844947868819581275297619 11767421803229371912946429)
        ·
          refine ⟨4412783176211014467354911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11767421803229371912946429 4412783176211014467354911)
          ·
            refine ⟨6619174764316521701032367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412783176211014467354911 6619174764316521701032367)
            ·
              refine ⟨9928762146474782551548551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619174764316521701032367 9928762146474782551548551)
              ·
                refine ⟨14893143219712173827322827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928762146474782551548551 14893143219712173827322827)
                ·
                  refine ⟨22339714829568260740984241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14893143219712173827322827 22339714829568260740984241)
                  ·
                    refine ⟨16754786122176195555738181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22339714829568260740984241 16754786122176195555738181)
                    ·
                      refine ⟨3141522397908036666700909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16754786122176195555738181 3141522397908036666700909)
                      ·
                        rfl

theorem cell23_6118093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6118093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118093 prefixEnd_6118093 := by exact prefixLift 6118093
  have htrace : WordTrace (prefixWord ++ tailWord_6118093) baseStart_6118093 baseEnd_6118093 := by
    simpa [prefixWord, tailWord_6118093, baseEnd_6118093] using wordTrace_append hprefix tailTrace_6118093
  have hstable : (prefixWord ++ tailWord_6118093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118093).length < 2 ^ (prefixWord ++ tailWord_6118093).sum := by decide
  have hdescent : baseEnd_6118093 < baseStart_6118093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118105 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_6118105 : Nat := 118140960795 + 6118105 * 2 ^ 59
def prefixEnd_6118105 : Nat := 4983230072969 + 3 ^ 40 * 6118105 * 2
def baseEnd_6118105 : Nat := 3141528559675890619750853

theorem tailTrace_6118105 : CollatzResearch.WordTrace tailWord_6118105 prefixEnd_6118105 3141528559675890619750853 := by
  unfold tailWord_6118105
  simp only [CollatzResearch.WordTrace]
  refine ⟨223145621500157948991235769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148763747666771965994157179 223145621500157948991235769)
  ·
    refine ⟨167359216125118461743426827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223145621500157948991235769 167359216125118461743426827)
    ·
      refine ⟨251038824187677692615140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167359216125118461743426827 251038824187677692615140241)
      ·
        refine ⟨188279118140758269461355181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251038824187677692615140241 188279118140758269461355181)
        ·
          refine ⟨70604669302784351048008193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188279118140758269461355181 70604669302784351048008193)
          ·
            refine ⟨52953501977088263286006145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70604669302784351048008193 52953501977088263286006145)
            ·
              refine ⟨39715126482816197464504609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52953501977088263286006145 39715126482816197464504609)
              ·
                refine ⟨29786344862112148098378457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39715126482816197464504609 29786344862112148098378457)
                ·
                  refine ⟨22339758646584111073783843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29786344862112148098378457 22339758646584111073783843)
                  ·
                    refine ⟨33509637969876166610675765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22339758646584111073783843 33509637969876166610675765)
                    ·
                      refine ⟨3141528559675890619750853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33509637969876166610675765 3141528559675890619750853)
                      ·
                        rfl

theorem cell23_6118105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_6118105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118105 prefixEnd_6118105 := by exact prefixLift 6118105
  have htrace : WordTrace (prefixWord ++ tailWord_6118105) baseStart_6118105 baseEnd_6118105 := by
    simpa [prefixWord, tailWord_6118105, baseEnd_6118105] using wordTrace_append hprefix tailTrace_6118105
  have hstable : (prefixWord ++ tailWord_6118105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118105).length < 2 ^ (prefixWord ++ tailWord_6118105).sum := by decide
  have hdescent : baseEnd_6118105 < baseStart_6118105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118155 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 6, 5]
def baseStart_6118155 : Nat := 118140960795 + 6118155 * 2 ^ 59
def prefixEnd_6118155 : Nat := 4983230072969 + 3 ^ 40 * 6118155 * 2
def baseEnd_6118155 : Nat := 1047184744569538474708541

theorem tailTrace_6118155 : CollatzResearch.WordTrace tailWord_6118155 prefixEnd_6118155 1047184744569538474708541 := by
  unfold tailWord_6118155
  simp only [CollatzResearch.WordTrace]
  refine ⟨223147445149976807530555919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148764963433317871687037279 223147445149976807530555919)
  ·
    refine ⟨334721167724965211295833879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223147445149976807530555919 334721167724965211295833879)
    ·
      refine ⟨502081751587447816943750819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334721167724965211295833879 502081751587447816943750819)
      ·
        refine ⟨753122627381171725415626229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502081751587447816943750819 753122627381171725415626229)
        ·
          refine ⟨70605246316984849257714959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 753122627381171725415626229 70605246316984849257714959)
          ·
            refine ⟨105907869475477273886572439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70605246316984849257714959 105907869475477273886572439)
            ·
              refine ⟨158861804213215910829858659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105907869475477273886572439 158861804213215910829858659)
              ·
                refine ⟨238292706319823866244787989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158861804213215910829858659 238292706319823866244787989)
                ·
                  refine ⟨11169970608741743730224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 238292706319823866244787989 11169970608741743730224437)
                  ·
                    refine ⟨1047184744569538474708541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11169970608741743730224437 1047184744569538474708541)
                    ·
                      rfl

theorem cell23_6118155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].length) (baseStart_6118155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118155 prefixEnd_6118155 := by exact prefixLift 6118155
  have htrace : WordTrace (prefixWord ++ tailWord_6118155) baseStart_6118155 baseEnd_6118155 := by
    simpa [prefixWord, tailWord_6118155, baseEnd_6118155] using wordTrace_append hprefix tailTrace_6118155
  have hstable : (prefixWord ++ tailWord_6118155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118155).length < 2 ^ (prefixWord ++ tailWord_6118155).sum := by decide
  have hdescent : baseEnd_6118155 < baseStart_6118155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118165 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_6118165 : Nat := 118140960795 + 6118165 * 2 ^ 59
def prefixEnd_6118165 : Nat := 4983230072969 + 3 ^ 40 * 6118165 * 2
def baseEnd_6118165 : Nat := 3141559368515160385000577

theorem tailTrace_6118165 : CollatzResearch.WordTrace tailWord_6118165 prefixEnd_6118165 3141559368515160385000577 := by
  unfold tailWord_6118165
  simp only [CollatzResearch.WordTrace]
  refine ⟨223147809879940579238419949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148765206586627052825613299 223147809879940579238419949)
  ·
    refine ⟨83680428704977717214407481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223147809879940579238419949 83680428704977717214407481)
    ·
      refine ⟨62760321528733287910805611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83680428704977717214407481 62760321528733287910805611)
      ·
        refine ⟨94140482293099931866208417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62760321528733287910805611 94140482293099931866208417)
        ·
          refine ⟨70605361719824948899656313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94140482293099931866208417 70605361719824948899656313)
          ·
            refine ⟨52954021289868711674742235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70605361719824948899656313 52954021289868711674742235)
            ·
              refine ⟨79431031934803067512113353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52954021289868711674742235 79431031934803067512113353)
              ·
                refine ⟨59573273951102300634085015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79431031934803067512113353 59573273951102300634085015)
                ·
                  refine ⟨89359910926653450951127523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59573273951102300634085015 89359910926653450951127523)
                  ·
                    refine ⟨134039866389980176426691285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89359910926653450951127523 134039866389980176426691285)
                    ·
                      refine ⟨3141559368515160385000577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134039866389980176426691285 3141559368515160385000577)
                      ·
                        rfl

theorem cell23_6118165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_6118165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118165 prefixEnd_6118165 := by exact prefixLift 6118165
  have htrace : WordTrace (prefixWord ++ tailWord_6118165) baseStart_6118165 baseEnd_6118165 := by
    simpa [prefixWord, tailWord_6118165, baseEnd_6118165] using wordTrace_append hprefix tailTrace_6118165
  have hstable : (prefixWord ++ tailWord_6118165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118165).length < 2 ^ (prefixWord ++ tailWord_6118165).sum := by decide
  have hdescent : baseEnd_6118165 < baseStart_6118165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118172 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_6118172 : Nat := 118140960795 + 6118172 * 2 ^ 59
def prefixEnd_6118172 : Nat := 4983230072969 + 3 ^ 40 * 6118172 * 2
def baseEnd_6118172 : Nat := 1047187654293247285871015

theorem tailTrace_6118172 : CollatzResearch.WordTrace tailWord_6118172 prefixEnd_6118172 1047187654293247285871015 := by
  unfold tailWord_6118172
  simp only [CollatzResearch.WordTrace]
  refine ⟨111574032595457609716962385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148765376793943479622616513 111574032595457609716962385)
  ·
    refine ⟨83680524446593207287721789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111574032595457609716962385 83680524446593207287721789)
    ·
      refine ⟨31380196667472452732895671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83680524446593207287721789 31380196667472452732895671)
      ·
        refine ⟨47070295001208679099343507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31380196667472452732895671 47070295001208679099343507)
        ·
          refine ⟨70605442501813018649015261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47070295001208679099343507 70605442501813018649015261)
          ·
            refine ⟨26477040938179881993380723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70605442501813018649015261 26477040938179881993380723)
            ·
              refine ⟨39715561407269822990071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26477040938179881993380723 39715561407269822990071085)
              ·
                refine ⟨14893335527726183621276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39715561407269822990071085 14893335527726183621276657)
                ·
                  refine ⟨11170001645794637715957493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14893335527726183621276657 11170001645794637715957493)
                  ·
                    refine ⟨1047187654293247285871015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11170001645794637715957493 1047187654293247285871015)
                    ·
                      rfl

theorem cell23_6118172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_6118172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118172 prefixEnd_6118172 := by exact prefixLift 6118172
  have htrace : WordTrace (prefixWord ++ tailWord_6118172) baseStart_6118172 baseEnd_6118172 := by
    simpa [prefixWord, tailWord_6118172, baseEnd_6118172] using wordTrace_append hprefix tailTrace_6118172
  have hstable : (prefixWord ++ tailWord_6118172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118172).length < 2 ^ (prefixWord ++ tailWord_6118172).sum := by decide
  have hdescent : baseEnd_6118172 < baseStart_6118172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118192 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2]
def baseStart_6118192 : Nat := 118140960795 + 6118192 * 2 ^ 59
def prefixEnd_6118192 : Nat := 4983230072969 + 3 ^ 40 * 6118192 * 2
def baseEnd_6118192 : Nat := 3141573232492831779362953

theorem tailTrace_6118192 : CollatzResearch.WordTrace tailWord_6118192 prefixEnd_6118192 3141573232492831779362953 := by
  unfold tailWord_6118192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111574397325421381424826415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148765863100561841899768553 111574397325421381424826415)
  ·
    refine ⟨167361595988132072137239623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111574397325421381424826415 167361595988132072137239623)
    ·
      refine ⟨251042393982198108205859435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167361595988132072137239623 251042393982198108205859435)
      ·
        refine ⟨376563590973297162308789153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251042393982198108205859435 376563590973297162308789153)
        ·
          refine ⟨282422693229972871731591865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376563590973297162308789153 282422693229972871731591865)
          ·
            refine ⟨211817019922479653798693899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282422693229972871731591865 211817019922479653798693899)
            ·
              refine ⟨317725529883719480698040849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211817019922479653798693899 317725529883719480698040849)
              ·
                refine ⟨238294147412789610523530637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317725529883719480698040849 238294147412789610523530637)
                ·
                  refine ⟨89360305279796103946323989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238294147412789610523530637 89360305279796103946323989)
                  ·
                    refine ⟨4188764309990442372483937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89360305279796103946323989 4188764309990442372483937)
                    ·
                      refine ⟨3141573232492831779362953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188764309990442372483937 3141573232492831779362953)
                      ·
                        rfl

theorem cell23_6118192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2].length) (baseStart_6118192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118192 prefixEnd_6118192 := by exact prefixLift 6118192
  have htrace : WordTrace (prefixWord ++ tailWord_6118192) baseStart_6118192 baseEnd_6118192 := by
    simpa [prefixWord, tailWord_6118192, baseEnd_6118192] using wordTrace_append hprefix tailTrace_6118192
  have hstable : (prefixWord ++ tailWord_6118192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118192).length < 2 ^ (prefixWord ++ tailWord_6118192).sum := by decide
  have hdescent : baseEnd_6118192 < baseStart_6118192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118215 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 10]
def baseStart_6118215 : Nat := 118140960795 + 6118215 * 2 ^ 59
def prefixEnd_6118215 : Nat := 4983230072969 + 3 ^ 40 * 6118215 * 2
def baseEnd_6118215 : Nat := 349065004727542798819483

theorem tailTrace_6118215 : CollatzResearch.WordTrace tailWord_6118215 prefixEnd_6118215 349065004727542798819483 := by
  unfold tailWord_6118215
  simp only [CollatzResearch.WordTrace]
  refine ⟨223149633529759437777740099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148766422353172958518493399 223149633529759437777740099)
  ·
    refine ⟨334724450294639156666610149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223149633529759437777740099 334724450294639156666610149)
    ·
      refine ⟨62760834430244841874989403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334724450294639156666610149 62760834430244841874989403)
      ·
        refine ⟨94141251645367262812484105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62760834430244841874989403 94141251645367262812484105)
        ·
          refine ⟨70605938734025447109363079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94141251645367262812484105 70605938734025447109363079)
          ·
            refine ⟨105908908101038170664044619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70605938734025447109363079 105908908101038170664044619)
            ·
              refine ⟨158863362151557255996066929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105908908101038170664044619 158863362151557255996066929)
              ·
                refine ⟨119147521613667941997050197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158863362151557255996066929 119147521613667941997050197)
                ·
                  refine ⟨349065004727542798819483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119147521613667941997050197 349065004727542798819483)
                  ·
                    rfl

theorem cell23_6118215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 10].length) (baseStart_6118215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118215 prefixEnd_6118215 := by exact prefixLift 6118215
  have htrace : WordTrace (prefixWord ++ tailWord_6118215) baseStart_6118215 baseEnd_6118215 := by
    simpa [prefixWord, tailWord_6118215, baseEnd_6118215] using wordTrace_append hprefix tailTrace_6118215
  have hstable : (prefixWord ++ tailWord_6118215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118215).length < 2 ^ (prefixWord ++ tailWord_6118215).sum := by decide
  have hdescent : baseEnd_6118215 < baseStart_6118215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118259 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 3]
def baseStart_6118259 : Nat := 118140960795 + 6118259 * 2 ^ 59
def prefixEnd_6118259 : Nat := 4983230072969 + 3 ^ 40 * 6118259 * 2
def baseEnd_6118259 : Nat := 3141607635696683017225145

theorem tailTrace_6118259 : CollatzResearch.WordTrace tailWord_6118259 prefixEnd_6118259 3141607635696683017225145 := by
  unfold tailWord_6118259
  simp only [CollatzResearch.WordTrace]
  refine ⟨223151238341600033292341831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148767492227733355528227887 223151238341600033292341831)
  ·
    refine ⟨334726857512400049938512747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223151238341600033292341831 334726857512400049938512747)
    ·
      refine ⟨502090286268600074907769121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334726857512400049938512747 502090286268600074907769121)
      ·
        refine ⟨376567714701450056180826841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502090286268600074907769121 376567714701450056180826841)
        ·
          refine ⟨282425786026087542135620131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376567714701450056180826841 282425786026087542135620131)
          ·
            refine ⟨423638679039131313203430197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282425786026087542135620131 423638679039131313203430197)
            ·
              refine ⟨39716126159918560612821581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 423638679039131313203430197 39716126159918560612821581)
              ·
                refine ⟨14893547309969460229808093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39716126159918560612821581 14893547309969460229808093)
                ·
                  refine ⟨5585080241238547586178035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14893547309969460229808093 5585080241238547586178035)
                  ·
                    refine ⟨8377620361857821379267053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585080241238547586178035 8377620361857821379267053)
                    ·
                      refine ⟨3141607635696683017225145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377620361857821379267053 3141607635696683017225145)
                      ·
                        rfl

theorem cell23_6118259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_6118259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118259 prefixEnd_6118259 := by exact prefixLift 6118259
  have htrace : WordTrace (prefixWord ++ tailWord_6118259) baseStart_6118259 baseEnd_6118259 := by
    simpa [prefixWord, tailWord_6118259, baseEnd_6118259] using wordTrace_append hprefix tailTrace_6118259
  have hstable : (prefixWord ++ tailWord_6118259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118259).length < 2 ^ (prefixWord ++ tailWord_6118259).sum := by decide
  have hdescent : baseEnd_6118259 < baseStart_6118259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118269 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_6118269 : Nat := 118140960795 + 6118269 * 2 ^ 59
def prefixEnd_6118269 : Nat := 4983230072969 + 3 ^ 40 * 6118269 * 2
def baseEnd_6118269 : Nat := 3141612770503227978100099

theorem tailTrace_6118269 : CollatzResearch.WordTrace tailWord_6118269 prefixEnd_6118269 3141612770503227978100099 := by
  unfold tailWord_6118269
  simp only [CollatzResearch.WordTrace]
  refine ⟨223151603071563805000205861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148767735381042536666803907 223151603071563805000205861)
  ·
    refine ⟨41840925575918213437538599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223151603071563805000205861 41840925575918213437538599)
    ·
      refine ⟨62761388363877320156307899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41840925575918213437538599 62761388363877320156307899)
      ·
        refine ⟨94142082545815980234461849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62761388363877320156307899 94142082545815980234461849)
        ·
          refine ⟨70606561909361985175846387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94142082545815980234461849 70606561909361985175846387)
          ·
            refine ⟨105909842864042977763769581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70606561909361985175846387 105909842864042977763769581)
            ·
              refine ⟨39716191074016116661413593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105909842864042977763769581 39716191074016116661413593)
              ·
                refine ⟨29787143305512087496060195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39716191074016116661413593 29787143305512087496060195)
                ·
                  refine ⟨44680714958268131244090293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29787143305512087496060195 44680714958268131244090293)
                  ·
                    refine ⟨4188817027337637304133465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44680714958268131244090293 4188817027337637304133465)
                    ·
                      refine ⟨3141612770503227978100099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188817027337637304133465 3141612770503227978100099)
                      ·
                        rfl

theorem cell23_6118269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_6118269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118269 prefixEnd_6118269 := by exact prefixLift 6118269
  have htrace : WordTrace (prefixWord ++ tailWord_6118269) baseStart_6118269 baseEnd_6118269 := by
    simpa [prefixWord, tailWord_6118269, baseEnd_6118269] using wordTrace_append hprefix tailTrace_6118269
  have hstable : (prefixWord ++ tailWord_6118269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118269).length < 2 ^ (prefixWord ++ tailWord_6118269).sum := by decide
  have hdescent : baseEnd_6118269 < baseStart_6118269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118279 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 1, 5]
def baseStart_6118279 : Nat := 118140960795 + 6118279 * 2 ^ 59
def prefixEnd_6118279 : Nat := 4983230072969 + 3 ^ 40 * 6118279 * 2
def baseEnd_6118279 : Nat := 1047205968436590979658351

theorem tailTrace_6118279 : CollatzResearch.WordTrace tailWord_6118279 prefixEnd_6118279 1047205968436590979658351 := by
  unfold tailWord_6118279
  simp only [CollatzResearch.WordTrace]
  refine ⟨223151967801527576708069891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148767978534351717805379927 223151967801527576708069891)
  ·
    refine ⟨334727951702291365062104837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223151967801527576708069891 334727951702291365062104837)
    ·
      refine ⟨62761490944179630949144657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334727951702291365062104837 62761490944179630949144657)
      ·
        refine ⟨47071118208134723211858493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62761490944179630949144657 47071118208134723211858493)
        ·
          refine ⟨17651669328050521204446935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47071118208134723211858493 17651669328050521204446935)
          ·
            refine ⟨26477503992075781806670403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17651669328050521204446935 26477503992075781806670403)
            ·
              refine ⟨39716255988113672710005605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26477503992075781806670403 39716255988113672710005605)
              ·
                refine ⟨7446797997771313633126051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39716255988113672710005605 7446797997771313633126051)
                ·
                  refine ⟨11170196996656970449689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446797997771313633126051 11170196996656970449689077)
                  ·
                    refine ⟨1047205968436590979658351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11170196996656970449689077 1047205968436590979658351)
                    ·
                      rfl

theorem cell23_6118279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_6118279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118279 prefixEnd_6118279 := by exact prefixLift 6118279
  have htrace : WordTrace (prefixWord ++ tailWord_6118279) baseStart_6118279 baseEnd_6118279 := by
    simpa [prefixWord, tailWord_6118279, baseEnd_6118279] using wordTrace_append hprefix tailTrace_6118279
  have hstable : (prefixWord ++ tailWord_6118279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118279).length < 2 ^ (prefixWord ++ tailWord_6118279).sum := by decide
  have hdescent : baseEnd_6118279 < baseStart_6118279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118293 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_6118293 : Nat := 118140960795 + 6118293 * 2 ^ 59
def prefixEnd_6118293 : Nat := 4983230072969 + 3 ^ 40 * 6118293 * 2
def baseEnd_6118293 : Nat := 3141625094038935884199989

theorem tailTrace_6118293 : CollatzResearch.WordTrace tailWord_6118293 prefixEnd_6118293 3141625094038935884199989 := by
  unfold tailWord_6118293
  simp only [CollatzResearch.WordTrace]
  refine ⟨223152478423476857099079533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148768318948984571399386355 223152478423476857099079533)
  ·
    refine ⟨83682179408803821412154825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223152478423476857099079533 83682179408803821412154825)
    ·
      refine ⟨62761634556602866059116119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83682179408803821412154825 62761634556602866059116119)
      ·
        refine ⟨94142451834904299088674179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62761634556602866059116119 94142451834904299088674179)
        ·
          refine ⟨141213677752356448633011269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94142451834904299088674179 141213677752356448633011269)
          ·
            refine ⟨26477564578566834118689613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141213677752356448633011269 26477564578566834118689613)
            ·
              refine ⟨9929086716962562794508605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26477564578566834118689613 9929086716962562794508605)
              ·
                refine ⟨3723407518860961047940727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929086716962562794508605 3723407518860961047940727)
                ·
                  refine ⟨5585111278291441571911091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723407518860961047940727 5585111278291441571911091)
                  ·
                    refine ⟨8377666917437162357866637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585111278291441571911091 8377666917437162357866637)
                    ·
                      refine ⟨3141625094038935884199989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377666917437162357866637 3141625094038935884199989)
                      ·
                        rfl

theorem cell23_6118293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_6118293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118293 prefixEnd_6118293 := by exact prefixLift 6118293
  have htrace : WordTrace (prefixWord ++ tailWord_6118293) baseStart_6118293 baseEnd_6118293 := by
    simpa [prefixWord, tailWord_6118293, baseEnd_6118293] using wordTrace_append hprefix tailTrace_6118293
  have hstable : (prefixWord ++ tailWord_6118293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118293).length < 2 ^ (prefixWord ++ tailWord_6118293).sum := by decide
  have hdescent : baseEnd_6118293 < baseStart_6118293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118333 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_6118333 : Nat := 118140960795 + 6118333 * 2 ^ 59
def prefixEnd_6118333 : Nat := 4983230072969 + 3 ^ 40 * 6118333 * 2
def baseEnd_6118333 : Nat := 3141645633265115727699805

theorem tailTrace_6118333 : CollatzResearch.WordTrace tailWord_6118333 prefixEnd_6118333 3141645633265115727699805 := by
  unfold tailWord_6118333
  simp only [CollatzResearch.WordTrace]
  refine ⟨223153937343331943930535653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148769291562221295953690435 223153937343331943930535653)
  ·
    refine ⟨41841363251874739486975435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223153937343331943930535653 41841363251874739486975435)
    ·
      refine ⟨62762044877812109230463153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41841363251874739486975435 62762044877812109230463153)
      ·
        refine ⟨47071533658359081922847365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62762044877812109230463153 47071533658359081922847365)
        ·
          refine ⟨8825912560942327860533881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47071533658359081922847365 8825912560942327860533881)
          ·
            refine ⟨6619434420706745895400411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8825912560942327860533881 6619434420706745895400411)
            ·
              refine ⟨9929151631060118843100617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619434420706745895400411 9929151631060118843100617)
              ·
                refine ⟨7446863723295089132325463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9929151631060118843100617 7446863723295089132325463)
                ·
                  refine ⟨11170295584942633698488195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446863723295089132325463 11170295584942633698488195)
                  ·
                    refine ⟨16755443377413950547732293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11170295584942633698488195 16755443377413950547732293)
                    ·
                      refine ⟨3141645633265115727699805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16755443377413950547732293 3141645633265115727699805)
                      ·
                        rfl

theorem cell23_6118333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_6118333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118333 prefixEnd_6118333 := by exact prefixLift 6118333
  have htrace : WordTrace (prefixWord ++ tailWord_6118333) baseStart_6118333 baseEnd_6118333 := by
    simpa [prefixWord, tailWord_6118333, baseEnd_6118333] using wordTrace_append hprefix tailTrace_6118333
  have hstable : (prefixWord ++ tailWord_6118333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118333).length < 2 ^ (prefixWord ++ tailWord_6118333).sum := by decide
  have hdescent : baseEnd_6118333 < baseStart_6118333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118336 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_6118336 : Nat := 118140960795 + 6118336 * 2 ^ 59
def prefixEnd_6118336 : Nat := 4983230072969 + 3 ^ 40 * 6118336 * 2
def baseEnd_6118336 : Nat := 3141647173707079215962291

theorem tailTrace_6118336 : CollatzResearch.WordTrace tailWord_6118336 prefixEnd_6118336 3141647173707079215962291 := by
  unfold tailWord_6118336
  simp only [CollatzResearch.WordTrace]
  refine ⟨111577023381160537721447431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148769364508214050295263241 111577023381160537721447431)
  ·
    refine ⟨167365535071740806582171147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111577023381160537721447431 167365535071740806582171147)
    ·
      refine ⟨251048302607611209873256721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167365535071740806582171147 251048302607611209873256721)
      ·
        refine ⟨188286226955708407404942541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251048302607611209873256721 188286226955708407404942541)
        ·
          refine ⟨70607335108390652776853453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188286226955708407404942541 70607335108390652776853453)
          ·
            refine ⟨26477750665646494791320045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70607335108390652776853453 26477750665646494791320045)
            ·
              refine ⟨9929156499617435546745017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26477750665646494791320045 9929156499617435546745017)
              ·
                refine ⟨7446867374713076660058763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9929156499617435546745017 7446867374713076660058763)
                ·
                  refine ⟨11170301062069614990088145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446867374713076660058763 11170301062069614990088145)
                  ·
                    refine ⟨8377725796552211242566109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11170301062069614990088145 8377725796552211242566109)
                    ·
                      refine ⟨3141647173707079215962291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8377725796552211242566109 3141647173707079215962291)
                      ·
                        rfl

theorem cell23_6118336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_6118336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118336 prefixEnd_6118336 := by exact prefixLift 6118336
  have htrace : WordTrace (prefixWord ++ tailWord_6118336) baseStart_6118336 baseEnd_6118336 := by
    simpa [prefixWord, tailWord_6118336, baseEnd_6118336] using wordTrace_append hprefix tailTrace_6118336
  have hstable : (prefixWord ++ tailWord_6118336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118336).length < 2 ^ (prefixWord ++ tailWord_6118336).sum := by decide
  have hdescent : baseEnd_6118336 < baseStart_6118336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118373 : List Nat := [1, 3, 1, 6, 2, 1, 1, 8]
def baseStart_6118373 : Nat := 118140960795 + 6118373 * 2 ^ 59
def prefixEnd_6118373 : Nat := 4983230072969 + 3 ^ 40 * 6118373 * 2
def baseEnd_6118373 : Nat := 116358006388566502637023

theorem tailTrace_6118373 : CollatzResearch.WordTrace tailWord_6118373 prefixEnd_6118373 116358006388566502637023 := by
  unfold tailWord_6118373
  simp only [CollatzResearch.WordTrace]
  refine ⟨223155396263187030761991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148770264175458020507994515 223155396263187030761991773)
  ·
    refine ⟨83683273598695136535746915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223155396263187030761991773 83683273598695136535746915)
    ·
      refine ⟨125524910398042704803620373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83683273598695136535746915 125524910398042704803620373)
      ·
        refine ⟨5883980174908251787669705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125524910398042704803620373 5883980174908251787669705)
        ·
          refine ⟨4412985131181188840752279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5883980174908251787669705 4412985131181188840752279)
          ·
            refine ⟨6619477696771783261128419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412985131181188840752279 6619477696771783261128419)
            ·
              refine ⟨9929216545157674891692629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619477696771783261128419 9929216545157674891692629)
              ·
                refine ⟨116358006388566502637023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9929216545157674891692629 116358006388566502637023)
                ·
                  rfl

theorem cell23_6118373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 8].length) (baseStart_6118373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118373 prefixEnd_6118373 := by exact prefixLift 6118373
  have htrace : WordTrace (prefixWord ++ tailWord_6118373) baseStart_6118373 baseEnd_6118373 := by
    simpa [prefixWord, tailWord_6118373, baseEnd_6118373] using wordTrace_append hprefix tailTrace_6118373
  have hstable : (prefixWord ++ tailWord_6118373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118373).length < 2 ^ (prefixWord ++ tailWord_6118373).sum := by decide
  have hdescent : baseEnd_6118373 < baseStart_6118373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118376 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6118376 : Nat := 118140960795 + 6118376 * 2 ^ 59
def prefixEnd_6118376 : Nat := 4983230072969 + 3 ^ 40 * 6118376 * 2
def baseEnd_6118376 : Nat := 3141667712933259059462107

theorem tailTrace_6118376 : CollatzResearch.WordTrace tailWord_6118376 prefixEnd_6118376 3141667712933259059462107 := by
  unfold tailWord_6118376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111577752841088081137175491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148770337121450774849567321 111577752841088081137175491)
  ·
    refine ⟨167366629261632121705763237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111577752841088081137175491 167366629261632121705763237)
    ·
      refine ⟨31381242986556022819830607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167366629261632121705763237 31381242986556022819830607)
      ·
        refine ⟨47071864479834034229745911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31381242986556022819830607 47071864479834034229745911)
        ·
          refine ⟨70607796719751051344618867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47071864479834034229745911 70607796719751051344618867)
          ·
            refine ⟨105911695079626577016928301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70607796719751051344618867 105911695079626577016928301)
            ·
              refine ⟨39716885654859966381348113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105911695079626577016928301 39716885654859966381348113)
              ·
                refine ⟨29787664241144974786011085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39716885654859966381348113 29787664241144974786011085)
                ·
                  refine ⟨11170374090429365544754157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29787664241144974786011085 11170374090429365544754157)
                  ·
                    refine ⟨4188890283911012079282809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11170374090429365544754157 4188890283911012079282809)
                    ·
                      refine ⟨3141667712933259059462107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188890283911012079282809 3141667712933259059462107)
                      ·
                        rfl

theorem cell23_6118376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6118376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118376 prefixEnd_6118376 := by exact prefixLift 6118376
  have htrace : WordTrace (prefixWord ++ tailWord_6118376) baseStart_6118376 baseEnd_6118376 := by
    simpa [prefixWord, tailWord_6118376, baseEnd_6118376] using wordTrace_append hprefix tailTrace_6118376
  have hstable : (prefixWord ++ tailWord_6118376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118376).length < 2 ^ (prefixWord ++ tailWord_6118376).sum := by decide
  have hdescent : baseEnd_6118376 < baseStart_6118376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118410 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_6118410 : Nat := 118140960795 + 6118410 * 2 ^ 59
def prefixEnd_6118410 : Nat := 4983230072969 + 3 ^ 40 * 6118410 * 2
def baseEnd_6118410 : Nat := 3141685171275511926436951

theorem tailTrace_6118410 : CollatzResearch.WordTrace tailWord_6118410 prefixEnd_6118410 3141685171275511926436951 := by
  unfold tailWord_6118410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55789186441013246520272171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148771163842701990720725789 55789186441013246520272171)
  ·
    refine ⟨83683779661519869780408257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55789186441013246520272171 83683779661519869780408257)
    ·
      refine ⟨62762834746139902335306193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83683779661519869780408257 62762834746139902335306193)
      ·
        refine ⟨47072126059604926751479645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62762834746139902335306193 47072126059604926751479645)
        ·
          refine ⟨17652047272351847531804867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47072126059604926751479645 17652047272351847531804867)
          ·
            refine ⟨26478070908527771297707301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652047272351847531804867 26478070908527771297707301)
            ·
              refine ⟨4964638295348957118320119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26478070908527771297707301 4964638295348957118320119)
              ·
                refine ⟨7446957443023435677480179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964638295348957118320119 7446957443023435677480179)
                ·
                  refine ⟨11170436164535153516220269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446957443023435677480179 11170436164535153516220269)
                  ·
                    refine ⟨4188913561700682568582601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11170436164535153516220269 4188913561700682568582601)
                    ·
                      refine ⟨3141685171275511926436951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188913561700682568582601 3141685171275511926436951)
                      ·
                        rfl

theorem cell23_6118410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_6118410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118410 prefixEnd_6118410 := by exact prefixLift 6118410
  have htrace : WordTrace (prefixWord ++ tailWord_6118410) baseStart_6118410 baseEnd_6118410 := by
    simpa [prefixWord, tailWord_6118410, baseEnd_6118410] using wordTrace_append hprefix tailTrace_6118410
  have hstable : (prefixWord ++ tailWord_6118410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118410).length < 2 ^ (prefixWord ++ tailWord_6118410).sum := by decide
  have hdescent : baseEnd_6118410 < baseStart_6118410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118436 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6118436 : Nat := 118140960795 + 6118436 * 2 ^ 59
def prefixEnd_6118436 : Nat := 4983230072969 + 3 ^ 40 * 6118436 * 2
def baseEnd_6118436 : Nat := 3141698521772528824711831

theorem tailTrace_6118436 : CollatzResearch.WordTrace tailWord_6118436 prefixEnd_6118436 3141698521772528824711831 := by
  unfold tailWord_6118436
  simp only [CollatzResearch.WordTrace]
  refine ⟨111578847030979396260767581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148771796041305861681023441 111578847030979396260767581)
  ·
    refine ⟨41842067636617273597787843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111578847030979396260767581 41842067636617273597787843)
    ·
      refine ⟨62763101454925910396681765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41842067636617273597787843 62763101454925910396681765)
      ·
        refine ⟨11768081522798608199377831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62763101454925910396681765 11768081522798608199377831)
        ·
          refine ⟨17652122284197912299066747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768081522798608199377831 17652122284197912299066747)
          ·
            refine ⟨26478183426296868448600121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652122284197912299066747 26478183426296868448600121)
            ·
              refine ⟨19858637569722651336450091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26478183426296868448600121 19858637569722651336450091)
              ·
                refine ⟨29787956354583977004675137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19858637569722651336450091 29787956354583977004675137)
                ·
                  refine ⟨22340967265937982753506353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29787956354583977004675137 22340967265937982753506353)
                  ·
                    refine ⟨16755725449453487065129765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22340967265937982753506353 16755725449453487065129765)
                    ·
                      refine ⟨3141698521772528824711831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16755725449453487065129765 3141698521772528824711831)
                      ·
                        rfl

theorem cell23_6118436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6118436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118436 prefixEnd_6118436 := by exact prefixLift 6118436
  have htrace : WordTrace (prefixWord ++ tailWord_6118436) baseStart_6118436 baseEnd_6118436 := by
    simpa [prefixWord, tailWord_6118436, baseEnd_6118436] using wordTrace_append hprefix tailTrace_6118436
  have hstable : (prefixWord ++ tailWord_6118436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118436).length < 2 ^ (prefixWord ++ tailWord_6118436).sum := by decide
  have hdescent : baseEnd_6118436 < baseStart_6118436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118496 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2]
def baseStart_6118496 : Nat := 118140960795 + 6118496 * 2 ^ 59
def prefixEnd_6118496 : Nat := 4983230072969 + 3 ^ 40 * 6118496 * 2
def baseEnd_6118496 : Nat := 3141729330611798589961555

theorem tailTrace_6118496 : CollatzResearch.WordTrace tailWord_6118496 prefixEnd_6118496 3141729330611798589961555 := by
  unfold tailWord_6118496
  simp only [CollatzResearch.WordTrace]
  refine ⟨111579941220870711384359671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148773254961160948512479561 111579941220870711384359671)
  ·
    refine ⟨167369911831306067076539507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111579941220870711384359671 167369911831306067076539507)
    ·
      refine ⟨251054867746959100614809261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167369911831306067076539507 251054867746959100614809261)
      ·
        refine ⟨94145575405109662730553473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251054867746959100614809261 94145575405109662730553473)
        ·
          refine ⟨70609181553832247047915105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94145575405109662730553473 70609181553832247047915105)
          ·
            refine ⟨52956886165374185285936329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70609181553832247047915105 52956886165374185285936329)
            ·
              refine ⟨39717664624030638964452247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52956886165374185285936329 39717664624030638964452247)
              ·
                refine ⟨59576496936045958446678371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39717664624030638964452247 59576496936045958446678371)
                ·
                  refine ⟨89364745404068937670017557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59576496936045958446678371 89364745404068937670017557)
                  ·
                    refine ⟨4188972440815731453282073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89364745404068937670017557 4188972440815731453282073)
                    ·
                      refine ⟨3141729330611798589961555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4188972440815731453282073 3141729330611798589961555)
                      ·
                        rfl

theorem cell23_6118496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_6118496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118496 prefixEnd_6118496 := by exact prefixLift 6118496
  have htrace : WordTrace (prefixWord ++ tailWord_6118496) baseStart_6118496 baseEnd_6118496 := by
    simpa [prefixWord, tailWord_6118496, baseEnd_6118496] using wordTrace_append hprefix tailTrace_6118496
  have hstable : (prefixWord ++ tailWord_6118496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118496).length < 2 ^ (prefixWord ++ tailWord_6118496).sum := by decide
  have hdescent : baseEnd_6118496 < baseStart_6118496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118569 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_6118569 : Nat := 118140960795 + 6118569 * 2 ^ 59
def prefixEnd_6118569 : Nat := 4983230072969 + 3 ^ 40 * 6118569 * 2
def baseEnd_6118569 : Nat := 3141766814699576804348719

theorem tailTrace_6118569 : CollatzResearch.WordTrace tailWord_6118569 prefixEnd_6118569 3141766814699576804348719 := by
  unfold tailWord_6118569
  simp only [CollatzResearch.WordTrace]
  refine ⟨223162544970476956236126761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148775029980317970824084507 223162544970476956236126761)
  ·
    refine ⟨167371908727857717177095071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223162544970476956236126761 167371908727857717177095071)
    ·
      refine ⟨251057863091786575765642607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167371908727857717177095071 251057863091786575765642607)
      ·
        refine ⟨376586794637679863648463911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251057863091786575765642607 376586794637679863648463911)
        ·
          refine ⟨564880191956519795472695867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376586794637679863648463911 564880191956519795472695867)
          ·
            refine ⟨847320287934779693209043801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564880191956519795472695867 847320287934779693209043801)
            ·
              refine ⟨635490215951084769906782851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847320287934779693209043801 635490215951084769906782851)
              ·
                refine ⟨953235323926627154860174277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635490215951084769906782851 953235323926627154860174277)
                ·
                  refine ⟨178731623236242591536282677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953235323926627154860174277 178731623236242591536282677)
                  ·
                    refine ⟨16756089678397742956526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178731623236242591536282677 16756089678397742956526501)
                    ·
                      refine ⟨3141766814699576804348719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16756089678397742956526501 3141766814699576804348719)
                      ·
                        rfl

theorem cell23_6118569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_6118569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118569 prefixEnd_6118569 := by exact prefixLift 6118569
  have htrace : WordTrace (prefixWord ++ tailWord_6118569) baseStart_6118569 baseEnd_6118569 := by
    simpa [prefixWord, tailWord_6118569, baseEnd_6118569] using wordTrace_append hprefix tailTrace_6118569
  have hstable : (prefixWord ++ tailWord_6118569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118569).length < 2 ^ (prefixWord ++ tailWord_6118569).sum := by decide
  have hdescent : baseEnd_6118569 < baseStart_6118569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118609 : List Nat := [1, 2, 2, 1, 2, 2, 1, 12]
def baseStart_6118609 : Nat := 118140960795 + 6118609 * 2 ^ 59
def prefixEnd_6118609 : Nat := 4983230072969 + 3 ^ 40 * 6118609 * 2
def baseEnd_6118609 : Nat := 116362494589842838809205

theorem tailTrace_6118609 : CollatzResearch.WordTrace tailWord_6118609 prefixEnd_6118609 116362494589842838809205 := by
  unfold tailWord_6118609
  simp only [CollatzResearch.WordTrace]
  refine ⟨223164003890332043067582881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148776002593554695378388587 223164003890332043067582881)
  ·
    refine ⟨167373002917749032300687161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223164003890332043067582881 167373002917749032300687161)
    ·
      refine ⟨125529752188311774225515371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167373002917749032300687161 125529752188311774225515371)
      ·
        refine ⟨188294628282467661338273057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125529752188311774225515371 188294628282467661338273057)
        ·
          refine ⟨141220971211850746003704793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188294628282467661338273057 141220971211850746003704793)
          ·
            refine ⟨105915728408888059502778595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141220971211850746003704793 105915728408888059502778595)
            ·
              refine ⟨158873592613332089254167893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105915728408888059502778595 158873592613332089254167893)
              ·
                refine ⟨116362494589842838809205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 158873592613332089254167893 116362494589842838809205)
                ·
                  rfl

theorem cell23_6118609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 12].length) (baseStart_6118609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118609 prefixEnd_6118609 := by exact prefixLift 6118609
  have htrace : WordTrace (prefixWord ++ tailWord_6118609) baseStart_6118609 baseEnd_6118609 := by
    simpa [prefixWord, tailWord_6118609, baseEnd_6118609] using wordTrace_append hprefix tailTrace_6118609
  have hstable : (prefixWord ++ tailWord_6118609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118609).length < 2 ^ (prefixWord ++ tailWord_6118609).sum := by decide
  have hdescent : baseEnd_6118609 < baseStart_6118609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118613 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_6118613 : Nat := 118140960795 + 6118613 * 2 ^ 59
def prefixEnd_6118613 : Nat := 4983230072969 + 3 ^ 40 * 6118613 * 2
def baseEnd_6118613 : Nat := 1047263135949458210732839

theorem tailTrace_6118613 : CollatzResearch.WordTrace tailWord_6118613 prefixEnd_6118613 1047263135949458210732839 := by
  unfold tailWord_6118613
  simp only [CollatzResearch.WordTrace]
  refine ⟨223164149782317551750728493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148776099854878367833818995 223164149782317551750728493)
  ·
    refine ⟨83686556168369081906523185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223164149782317551750728493 83686556168369081906523185)
    ·
      refine ⟨62764917126276811429892389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83686556168369081906523185 62764917126276811429892389)
      ·
        refine ⟨11768421961176902143104823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62764917126276811429892389 11768421961176902143104823)
        ·
          refine ⟨17652632941765353214657235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768421961176902143104823 17652632941765353214657235)
          ·
            refine ⟨26478949412648029821985853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652632941765353214657235 26478949412648029821985853)
            ·
              refine ⟨9929606029743011183244695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26478949412648029821985853 9929606029743011183244695)
              ·
                refine ⟨14894409044614516774867043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9929606029743011183244695 14894409044614516774867043)
                ·
                  refine ⟨22341613566921775162300565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14894409044614516774867043 22341613566921775162300565)
                  ·
                    refine ⟨1047263135949458210732839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22341613566921775162300565 1047263135949458210732839)
                    ·
                      rfl

theorem cell23_6118613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_6118613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118613 prefixEnd_6118613 := by exact prefixLift 6118613
  have htrace : WordTrace (prefixWord ++ tailWord_6118613) baseStart_6118613 baseEnd_6118613 := by
    simpa [prefixWord, tailWord_6118613, baseEnd_6118613] using wordTrace_append hprefix tailTrace_6118613
  have hstable : (prefixWord ++ tailWord_6118613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118613).length < 2 ^ (prefixWord ++ tailWord_6118613).sum := by decide
  have hdescent : baseEnd_6118613 < baseStart_6118613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118623 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_6118623 : Nat := 118140960795 + 6118623 * 2 ^ 59
def prefixEnd_6118623 : Nat := 4983230072969 + 3 ^ 40 * 6118623 * 2
def baseEnd_6118623 : Nat := 3141794542654919593073471

theorem tailTrace_6118623 : CollatzResearch.WordTrace tailWord_6118623 prefixEnd_6118623 3141794542654919593073471 := by
  unfold tailWord_6118623
  simp only [CollatzResearch.WordTrace]
  refine ⟨223164514512281323458592523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148776343008187548972395015 223164514512281323458592523)
  ·
    refine ⟨334746771768421985187888785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223164514512281323458592523 334746771768421985187888785)
    ·
      refine ⟨251060078826316488890916589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334746771768421985187888785 251060078826316488890916589)
      ·
        refine ⟨94147529559868683334093721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251060078826316488890916589 94147529559868683334093721)
        ·
          refine ⟨70610647169901512500570291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94147529559868683334093721 70610647169901512500570291)
          ·
            refine ⟨105915970754852268750855437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70610647169901512500570291 105915970754852268750855437)
            ·
              refine ⟨39718489033069600781570789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105915970754852268750855437 39718489033069600781570789)
              ·
                refine ⟨7447216693700550146544523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39718489033069600781570789 7447216693700550146544523)
                ·
                  refine ⟨11170825040550825219816785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7447216693700550146544523 11170825040550825219816785)
                  ·
                    refine ⟨8378118780413118914862589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11170825040550825219816785 8378118780413118914862589)
                    ·
                      refine ⟨3141794542654919593073471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378118780413118914862589 3141794542654919593073471)
                      ·
                        rfl

theorem cell23_6118623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_6118623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118623 prefixEnd_6118623 := by exact prefixLift 6118623
  have htrace : WordTrace (prefixWord ++ tailWord_6118623) baseStart_6118623 baseEnd_6118623 := by
    simpa [prefixWord, tailWord_6118623, baseEnd_6118623] using wordTrace_append hprefix tailTrace_6118623
  have hstable : (prefixWord ++ tailWord_6118623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118623).length < 2 ^ (prefixWord ++ tailWord_6118623).sum := by decide
  have hdescent : baseEnd_6118623 < baseStart_6118623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118631 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6118631 : Nat := 118140960795 + 6118631 * 2 ^ 59
def prefixEnd_6118631 : Nat := 4983230072969 + 3 ^ 40 * 6118631 * 2
def baseEnd_6118631 : Nat := 3141798650500155561773435

theorem tailTrace_6118631 : CollatzResearch.WordTrace tailWord_6118631 prefixEnd_6118631 3141798650500155561773435 := by
  unfold tailWord_6118631
  simp only [CollatzResearch.WordTrace]
  refine ⟨223164806296252340824883747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148776537530834893883255831 223164806296252340824883747)
  ·
    refine ⟨334747209444378511237325621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223164806296252340824883747 334747209444378511237325621)
    ·
      refine ⟨31382550885410485428499277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334747209444378511237325621 31382550885410485428499277)
      ·
        refine ⟨11768456582028932035687229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31382550885410485428499277 11768456582028932035687229)
        ·
          refine ⟨4413171218260849513382711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11768456582028932035687229 4413171218260849513382711)
          ·
            refine ⟨6619756827391274270074067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413171218260849513382711 6619756827391274270074067)
            ·
              refine ⟨9929635241086911405111101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619756827391274270074067 9929635241086911405111101)
              ·
                refine ⟨3723613215407591776916663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929635241086911405111101 3723613215407591776916663)
                ·
                  refine ⟨5585419823111387665374995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723613215407591776916663 5585419823111387665374995)
                  ·
                    refine ⟨8378129734667081498062493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585419823111387665374995 8378129734667081498062493)
                    ·
                      refine ⟨3141798650500155561773435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378129734667081498062493 3141798650500155561773435)
                      ·
                        rfl

theorem cell23_6118631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6118631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118631 prefixEnd_6118631 := by exact prefixLift 6118631
  have htrace : WordTrace (prefixWord ++ tailWord_6118631) baseStart_6118631 baseEnd_6118631 := by
    simpa [prefixWord, tailWord_6118631, baseEnd_6118631] using wordTrace_append hprefix tailTrace_6118631
  have hstable : (prefixWord ++ tailWord_6118631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118631).length < 2 ^ (prefixWord ++ tailWord_6118631).sum := by decide
  have hdescent : baseEnd_6118631 < baseStart_6118631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118654 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_6118654 : Nat := 118140960795 + 6118654 * 2 ^ 59
def prefixEnd_6118654 : Nat := 4983230072969 + 3 ^ 40 * 6118654 * 2
def baseEnd_6118654 : Nat := 3141810460555208971785829

theorem tailTrace_6118654 : CollatzResearch.WordTrace tailWord_6118654 prefixEnd_6118654 3141810460555208971785829 := by
  unfold tailWord_6118654
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895705646896126969121377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148777096783446010501980677 27895705646896126969121377)
  ·
    refine ⟨20921779235172095226841033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27895705646896126969121377 20921779235172095226841033)
    ·
      refine ⟨15691334426379071420130775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20921779235172095226841033 15691334426379071420130775)
      ·
        refine ⟨23537001639568607130196163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15691334426379071420130775 23537001639568607130196163)
        ·
          refine ⟨35305502459352910695294245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23537001639568607130196163 35305502459352910695294245)
          ·
            refine ⟨6619781711128670755367671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35305502459352910695294245 6619781711128670755367671)
            ·
              refine ⟨9929672566693006133051507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619781711128670755367671 9929672566693006133051507)
              ·
                refine ⟨14894508850039509199577261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9929672566693006133051507 14894508850039509199577261)
                ·
                  refine ⟨5585440818764815949841473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14894508850039509199577261 5585440818764815949841473)
                  ·
                    refine ⟨4189080614073611962381105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585440818764815949841473 4189080614073611962381105)
                    ·
                      refine ⟨3141810460555208971785829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189080614073611962381105 3141810460555208971785829)
                      ·
                        rfl

theorem cell23_6118654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_6118654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118654 prefixEnd_6118654 := by exact prefixLift 6118654
  have htrace : WordTrace (prefixWord ++ tailWord_6118654) baseStart_6118654 baseEnd_6118654 := by
    simpa [prefixWord, tailWord_6118654, baseEnd_6118654] using wordTrace_append hprefix tailTrace_6118654
  have hstable : (prefixWord ++ tailWord_6118654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118654).length < 2 ^ (prefixWord ++ tailWord_6118654).sum := by decide
  have hdescent : baseEnd_6118654 < baseStart_6118654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118664 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_6118664 : Nat := 118140960795 + 6118664 * 2 ^ 59
def prefixEnd_6118664 : Nat := 4983230072969 + 3 ^ 40 * 6118664 * 2
def baseEnd_6118664 : Nat := 1047271865120584644220261

theorem tailTrace_6118664 : CollatzResearch.WordTrace tailWord_6118664 prefixEnd_6118664 1047271865120584644220261 := by
  unfold tailWord_6118664
  simp only [CollatzResearch.WordTrace]
  refine ⟨111583004952566393730417523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148777339936755191640556697 111583004952566393730417523)
  ·
    refine ⟨167374507428849590595626285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111583004952566393730417523 167374507428849590595626285)
    ·
      refine ⟨62765440285818596473359857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167374507428849590595626285 62765440285818596473359857)
      ·
        refine ⟨47074080214363947355019893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62765440285818596473359857 47074080214363947355019893)
        ·
          refine ⟨4413195020096620064533115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47074080214363947355019893 4413195020096620064533115)
          ·
            refine ⟨6619792530144930096799673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413195020096620064533115 6619792530144930096799673)
            ·
              refine ⟨4964844397608697572599755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6619792530144930096799673 4964844397608697572599755)
              ·
                refine ⟨7447266596413046358899633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964844397608697572599755 7447266596413046358899633)
                ·
                  refine ⟨5585449947309784769174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7447266596413046358899633 5585449947309784769174725)
                  ·
                    refine ⟨1047271865120584644220261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585449947309784769174725 1047271865120584644220261)
                    ·
                      rfl

theorem cell23_6118664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_6118664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118664 prefixEnd_6118664 := by exact prefixLift 6118664
  have htrace : WordTrace (prefixWord ++ tailWord_6118664) baseStart_6118664 baseEnd_6118664 := by
    simpa [prefixWord, tailWord_6118664, baseEnd_6118664] using wordTrace_append hprefix tailTrace_6118664
  have hstable : (prefixWord ++ tailWord_6118664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118664).length < 2 ^ (prefixWord ++ tailWord_6118664).sum := by decide
  have hdescent : baseEnd_6118664 < baseStart_6118664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118680 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6118680 : Nat := 118140960795 + 6118680 * 2 ^ 59
def prefixEnd_6118680 : Nat := 4983230072969 + 3 ^ 40 * 6118680 * 2
def baseEnd_6118680 : Nat := 3141823811052225870060709

theorem tailTrace_6118680 : CollatzResearch.WordTrace tailWord_6118680 prefixEnd_6118680 3141823811052225870060709 := by
  unfold tailWord_6118680
  simp only [CollatzResearch.WordTrace]
  refine ⟨111583296736537411096708747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148777728982049881462278329 111583296736537411096708747)
  ·
    refine ⟨167374945104806116645063121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111583296736537411096708747 167374945104806116645063121)
    ·
      refine ⟨125531208828604587483797341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167374945104806116645063121 125531208828604587483797341)
      ·
        refine ⟨47074203310726720306424003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125531208828604587483797341 47074203310726720306424003)
        ·
          refine ⟨70611304966090080459636005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47074203310726720306424003 70611304966090080459636005)
          ·
            refine ⟨13239619681141890086181751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70611304966090080459636005 13239619681141890086181751)
            ·
              refine ⟨19859429521712835129272627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13239619681141890086181751 19859429521712835129272627)
              ·
                refine ⟨29789144282569252693908941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19859429521712835129272627 29789144282569252693908941)
                ·
                  refine ⟨11170929105963469760215853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29789144282569252693908941 11170929105963469760215853)
                  ·
                    refine ⟨4189098414736301160080945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11170929105963469760215853 4189098414736301160080945)
                    ·
                      refine ⟨3141823811052225870060709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189098414736301160080945 3141823811052225870060709)
                      ·
                        rfl

theorem cell23_6118680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6118680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118680 prefixEnd_6118680 := by exact prefixLift 6118680
  have htrace : WordTrace (prefixWord ++ tailWord_6118680) baseStart_6118680 baseEnd_6118680 := by
    simpa [prefixWord, tailWord_6118680, baseEnd_6118680] using wordTrace_append hprefix tailTrace_6118680
  have hstable : (prefixWord ++ tailWord_6118680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118680).length < 2 ^ (prefixWord ++ tailWord_6118680).sum := by decide
  have hdescent : baseEnd_6118680 < baseStart_6118680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118727 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_6118727 : Nat := 118140960795 + 6118727 * 2 ^ 59
def prefixEnd_6118727 : Nat := 4983230072969 + 3 ^ 40 * 6118727 * 2
def baseEnd_6118727 : Nat := 3141847944642987186172993

theorem tailTrace_6118727 : CollatzResearch.WordTrace tailWord_6118727 prefixEnd_6118727 3141847944642987186172993 := by
  unfold tailWord_6118727
  simp only [CollatzResearch.WordTrace]
  refine ⟨223168307703904549220378435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148778871802603032813585623 223168307703904549220378435)
  ·
    refine ⟨334752461555856823830567653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223168307703904549220378435 334752461555856823830567653)
    ·
      refine ⟨62766086541723154468231435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334752461555856823830567653 62766086541723154468231435)
      ·
        refine ⟨94149129812584731702347153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62766086541723154468231435 94149129812584731702347153)
        ·
          refine ⟨70611847359438548776760365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94149129812584731702347153 70611847359438548776760365)
          ·
            refine ⟨26479442759789455791285137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70611847359438548776760365 26479442759789455791285137)
            ·
              refine ⟨19859582069842091843463853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26479442759789455791285137 19859582069842091843463853)
              ·
                refine ⟨7447343276190784441298945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19859582069842091843463853 7447343276190784441298945)
                ·
                  refine ⟨5585507457143088330974209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7447343276190784441298945 5585507457143088330974209)
                  ·
                    refine ⟨4189130592857316248230657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585507457143088330974209 4189130592857316248230657)
                    ·
                      refine ⟨3141847944642987186172993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189130592857316248230657 3141847944642987186172993)
                      ·
                        rfl

theorem cell23_6118727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_6118727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118727 prefixEnd_6118727 := by exact prefixLift 6118727
  have htrace : WordTrace (prefixWord ++ tailWord_6118727) baseStart_6118727 baseEnd_6118727 := by
    simpa [prefixWord, tailWord_6118727, baseEnd_6118727] using wordTrace_append hprefix tailTrace_6118727
  have hstable : (prefixWord ++ tailWord_6118727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118727).length < 2 ^ (prefixWord ++ tailWord_6118727).sum := by decide
  have hdescent : baseEnd_6118727 < baseStart_6118727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118803 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3]
def baseStart_6118803 : Nat := 118140960795 + 6118803 * 2 ^ 59
def prefixEnd_6118803 : Nat := 4983230072969 + 3 ^ 40 * 6118803 * 2
def baseEnd_6118803 : Nat := 3141886969172728888822643

theorem tailTrace_6118803 : CollatzResearch.WordTrace tailWord_6118803 prefixEnd_6118803 3141886969172728888822643 := by
  unfold tailWord_6118803
  simp only [CollatzResearch.WordTrace]
  refine ⟨223171079651629214200145063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148780719767752809466763375 223171079651629214200145063)
  ·
    refine ⟨334756619477443821300217595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223171079651629214200145063 334756619477443821300217595)
    ·
      refine ⟨502134929216165731950326393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334756619477443821300217595 502134929216165731950326393)
      ·
        refine ⟨376601196912124298962744795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502134929216165731950326393 376601196912124298962744795)
        ·
          refine ⟨564901795368186448444117193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376601196912124298962744795 564901795368186448444117193)
          ·
            refine ⟨423676346526139836333087895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564901795368186448444117193 423676346526139836333087895)
            ·
              refine ⟨635514519789209754499631843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423676346526139836333087895 635514519789209754499631843)
              ·
                refine ⟨953271779683814631749447765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635514519789209754499631843 953271779683814631749447765)
                ·
                  refine ⟨11171153668169702715813841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 953271779683814631749447765 11171153668169702715813841)
                  ·
                    refine ⟨8378365251127277036860381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11171153668169702715813841 8378365251127277036860381)
                    ·
                      refine ⟨3141886969172728888822643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378365251127277036860381 3141886969172728888822643)
                      ·
                        rfl

theorem cell23_6118803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_6118803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118803 prefixEnd_6118803 := by exact prefixLift 6118803
  have htrace : WordTrace (prefixWord ++ tailWord_6118803) baseStart_6118803 baseEnd_6118803 := by
    simpa [prefixWord, tailWord_6118803, baseEnd_6118803] using wordTrace_append hprefix tailTrace_6118803
  have hstable : (prefixWord ++ tailWord_6118803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118803).length < 2 ^ (prefixWord ++ tailWord_6118803).sum := by decide
  have hdescent : baseEnd_6118803 < baseStart_6118803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118823 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 8]
def baseStart_6118823 : Nat := 118140960795 + 6118823 * 2 ^ 59
def prefixEnd_6118823 : Nat := 4983230072969 + 3 ^ 40 * 6118823 * 2
def baseEnd_6118823 : Nat := 349099693198424312285839

theorem tailTrace_6118823 : CollatzResearch.WordTrace tailWord_6118823 prefixEnd_6118823 349099693198424312285839 := by
  unfold tailWord_6118823
  simp only [CollatzResearch.WordTrace]
  refine ⟨223171809111556757615873123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148781206074371171743915415 223171809111556757615873123)
  ·
    refine ⟨334757713667335136423809685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223171809111556757615873123 334757713667335136423809685)
    ·
      refine ⟨15691767828156334519866079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 334757713667335136423809685 15691767828156334519866079)
      ·
        refine ⟨23537651742234501779799119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15691767828156334519866079 23537651742234501779799119)
        ·
          refine ⟨35306477613351752669698679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23537651742234501779799119 35306477613351752669698679)
          ·
            refine ⟨52959716420027629004548019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35306477613351752669698679 52959716420027629004548019)
            ·
              refine ⟨79439574630041443506822029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52959716420027629004548019 79439574630041443506822029)
              ·
                refine ⟨29789840486265541315058261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79439574630041443506822029 29789840486265541315058261)
                ·
                  refine ⟨349099693198424312285839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29789840486265541315058261 349099693198424312285839)
                  ·
                    rfl

theorem cell23_6118823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 8].length) (baseStart_6118823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118823 prefixEnd_6118823 := by exact prefixLift 6118823
  have htrace : WordTrace (prefixWord ++ tailWord_6118823) baseStart_6118823 baseEnd_6118823 := by
    simpa [prefixWord, tailWord_6118823, baseEnd_6118823] using wordTrace_append hprefix tailTrace_6118823
  have hstable : (prefixWord ++ tailWord_6118823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118823).length < 2 ^ (prefixWord ++ tailWord_6118823).sum := by decide
  have hdescent : baseEnd_6118823 < baseStart_6118823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118840 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 6]
def baseStart_6118840 : Nat := 118140960795 + 6118840 * 2 ^ 59
def prefixEnd_6118840 : Nat := 4983230072969 + 3 ^ 40 * 6118840 * 2
def baseEnd_6118840 : Nat := 349100663106327249339997

theorem tailTrace_6118840 : CollatzResearch.WordTrace tailWord_6118840 prefixEnd_6118840 349100663106327249339997 := by
  unfold tailWord_6118840
  simp only [CollatzResearch.WordTrace]
  refine ⟨111586214576247584759620987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148781619434996779679494649 111586214576247584759620987)
  ·
    refine ⟨167379321864371377139431481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111586214576247584759620987 167379321864371377139431481)
    ·
      refine ⟨125534491398278532854573611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167379321864371377139431481 125534491398278532854573611)
      ·
        refine ⟨188301737097417799281860417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125534491398278532854573611 188301737097417799281860417)
        ·
          refine ⟨141226302823063349461395313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188301737097417799281860417 141226302823063349461395313)
          ·
            refine ⟨105919727117297512096046485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141226302823063349461395313 105919727117297512096046485)
            ·
              refine ⟨4964987208623320879502179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105919727117297512096046485 4964987208623320879502179)
              ·
                refine ⟨7447480812934981319253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964987208623320879502179 7447480812934981319253269)
                ·
                  refine ⟨349100663106327249339997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7447480812934981319253269 349100663106327249339997)
                  ·
                    rfl

theorem cell23_6118840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_6118840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118840 prefixEnd_6118840 := by exact prefixLift 6118840
  have htrace : WordTrace (prefixWord ++ tailWord_6118840) baseStart_6118840 baseEnd_6118840 := by
    simpa [prefixWord, tailWord_6118840, baseEnd_6118840] using wordTrace_append hprefix tailTrace_6118840
  have hstable : (prefixWord ++ tailWord_6118840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118840).length < 2 ^ (prefixWord ++ tailWord_6118840).sum := by decide
  have hdescent : baseEnd_6118840 < baseStart_6118840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118907 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 3, 2, 2]
def baseStart_6118907 : Nat := 118140960795 + 6118907 * 2 ^ 59
def prefixEnd_6118907 : Nat := 4983230072969 + 3 ^ 40 * 6118907 * 2
def baseEnd_6118907 : Nat := 3141940371160796481922165

theorem tailTrace_6118907 : CollatzResearch.WordTrace tailWord_6118907 prefixEnd_6118907 3141940371160796481922165 := by
  unfold tailWord_6118907
  simp only [CollatzResearch.WordTrace]
  refine ⟨223174872843252439961930975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148783248562168293307953983 223174872843252439961930975)
  ·
    refine ⟨334762309264878659942896463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223174872843252439961930975 334762309264878659942896463)
    ·
      refine ⟨502143463897317989914344695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334762309264878659942896463 502143463897317989914344695)
      ·
        refine ⟨753215195845976984871517043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502143463897317989914344695 753215195845976984871517043)
        ·
          refine ⟨1129822793768965477307275565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753215195845976984871517043 1129822793768965477307275565)
          ·
            refine ⟨423683547663362053990228337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1129822793768965477307275565 423683547663362053990228337)
            ·
              refine ⟨317762660747521540492671253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423683547663362053990228337 317762660747521540492671253)
              ·
                refine ⟨14895124722540072210593965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317762660747521540492671253 14895124722540072210593965)
                ·
                  refine ⟨5585671770952527078972737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14895124722540072210593965 5585671770952527078972737)
                  ·
                    refine ⟨4189253828214395309229553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585671770952527078972737 4189253828214395309229553)
                    ·
                      refine ⟨3141940371160796481922165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189253828214395309229553 3141940371160796481922165)
                      ·
                        rfl

theorem cell23_6118907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2, 2].length) (baseStart_6118907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118907 prefixEnd_6118907 := by exact prefixLift 6118907
  have htrace : WordTrace (prefixWord ++ tailWord_6118907) baseStart_6118907 baseEnd_6118907 := by
    simpa [prefixWord, tailWord_6118907, baseEnd_6118907] using wordTrace_append hprefix tailTrace_6118907
  have hstable : (prefixWord ++ tailWord_6118907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118907).length < 2 ^ (prefixWord ++ tailWord_6118907).sum := by decide
  have hdescent : baseEnd_6118907 < baseStart_6118907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118920 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6118920 : Nat := 118140960795 + 6118920 * 2 ^ 59
def prefixEnd_6118920 : Nat := 4983230072969 + 3 ^ 40 * 6118920 * 2
def baseEnd_6118920 : Nat := 3141947046409304931059605

theorem tailTrace_6118920 : CollatzResearch.WordTrace tailWord_6118920 prefixEnd_6118920 3141947046409304931059605 := by
  unfold tailWord_6118920
  simp only [CollatzResearch.WordTrace]
  refine ⟨111587673496102671591077107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148783564661470228788102809 111587673496102671591077107)
  ·
    refine ⟨167381510244154007386615661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111587673496102671591077107 167381510244154007386615661)
    ·
      refine ⟨62768066341557752769980873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167381510244154007386615661 62768066341557752769980873)
      ·
        refine ⟨47076049756168314577485655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62768066341557752769980873 47076049756168314577485655)
        ·
          refine ⟨70614074634252471866228483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47076049756168314577485655 70614074634252471866228483)
          ·
            refine ⟨105921111951378707799342725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70614074634252471866228483 105921111951378707799342725)
            ·
              refine ⟨19860208490883507712376761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105921111951378707799342725 19860208490883507712376761)
              ·
                refine ⟨14895156368162630784282571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19860208490883507712376761 14895156368162630784282571)
                ·
                  refine ⟨22342734552243946176423857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14895156368162630784282571 22342734552243946176423857)
                  ·
                    refine ⟨16757050914182959632317893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22342734552243946176423857 16757050914182959632317893)
                    ·
                      refine ⟨3141947046409304931059605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16757050914182959632317893 3141947046409304931059605)
                      ·
                        rfl

theorem cell23_6118920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6118920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118920 prefixEnd_6118920 := by exact prefixLift 6118920
  have htrace : WordTrace (prefixWord ++ tailWord_6118920) baseStart_6118920 baseEnd_6118920 := by
    simpa [prefixWord, tailWord_6118920, baseEnd_6118920] using wordTrace_append hprefix tailTrace_6118920
  have hstable : (prefixWord ++ tailWord_6118920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118920).length < 2 ^ (prefixWord ++ tailWord_6118920).sum := by decide
  have hdescent : baseEnd_6118920 < baseStart_6118920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118941 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6118941 : Nat := 118140960795 + 6118941 * 2 ^ 59
def prefixEnd_6118941 : Nat := 4983230072969 + 3 ^ 40 * 6118941 * 2
def baseEnd_6118941 : Nat := 3141957829503049348897009

theorem tailTrace_6118941 : CollatzResearch.WordTrace tailWord_6118941 prefixEnd_6118941 3141957829503049348897009 := by
  unfold tailWord_6118941
  simp only [CollatzResearch.WordTrace]
  refine ⟨223176112925129263768668677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148784075283419509179112451 223176112925129263768668677)
  ·
    refine ⟨41845521173461736956625377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223176112925129263768668677 41845521173461736956625377)
    ·
      refine ⟨31384140880096302717469033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41845521173461736956625377 31384140880096302717469033)
      ·
        refine ⟨23538105660072227038101775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31384140880096302717469033 23538105660072227038101775)
        ·
          refine ⟨35307158490108340557152663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23538105660072227038101775 35307158490108340557152663)
          ·
            refine ⟨52960737735162510835728995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35307158490108340557152663 52960737735162510835728995)
            ·
              refine ⟨79441106602743766253593493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52960737735162510835728995 79441106602743766253593493)
              ·
                refine ⟨3723801872003614043137195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79441106602743766253593493 3723801872003614043137195)
                ·
                  refine ⟨5585702808005421064705793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723801872003614043137195 5585702808005421064705793)
                  ·
                    refine ⟨4189277106004065798529345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585702808005421064705793 4189277106004065798529345)
                    ·
                      refine ⟨3141957829503049348897009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189277106004065798529345 3141957829503049348897009)
                      ·
                        rfl

theorem cell23_6118941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6118941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118941 prefixEnd_6118941 := by exact prefixLift 6118941
  have htrace : WordTrace (prefixWord ++ tailWord_6118941) baseStart_6118941 baseEnd_6118941 := by
    simpa [prefixWord, tailWord_6118941, baseEnd_6118941] using wordTrace_append hprefix tailTrace_6118941
  have hstable : (prefixWord ++ tailWord_6118941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118941).length < 2 ^ (prefixWord ++ tailWord_6118941).sum := by decide
  have hdescent : baseEnd_6118941 < baseStart_6118941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6118943 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 9]
def baseStart_6118943 : Nat := 118140960795 + 6118943 * 2 ^ 59
def prefixEnd_6118943 : Nat := 4983230072969 + 3 ^ 40 * 6118943 * 2
def baseEnd_6118943 : Nat := 1047319618821452780357333

theorem tailTrace_6118943 : CollatzResearch.WordTrace tailWord_6118943 prefixEnd_6118943 1047319618821452780357333 := by
  unfold tailWord_6118943
  simp only [CollatzResearch.WordTrace]
  refine ⟨223176185871122018110241483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148784123914081345406827655 223176185871122018110241483)
  ·
    refine ⟨334764278806683027165362225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223176185871122018110241483 334764278806683027165362225)
    ·
      refine ⟨251073209105012270374021669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334764278806683027165362225 251073209105012270374021669)
      ·
        refine ⟨47076226707189800695129063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251073209105012270374021669 47076226707189800695129063)
        ·
          refine ⟨70614340060784701042693595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47076226707189800695129063 70614340060784701042693595)
          ·
            refine ⟨105921510091177051564040393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70614340060784701042693595 105921510091177051564040393)
            ·
              refine ⟨79441132568382788673030295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105921510091177051564040393 79441132568382788673030295)
              ·
                refine ⟨119161698852574183009545443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79441132568382788673030295 119161698852574183009545443)
                ·
                  refine ⟨178742548278861274514318165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119161698852574183009545443 178742548278861274514318165)
                  ·
                    refine ⟨1047319618821452780357333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178742548278861274514318165 1047319618821452780357333)
                    ·
                      rfl

theorem cell23_6118943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_6118943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6118943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6118943 prefixEnd_6118943 := by exact prefixLift 6118943
  have htrace : WordTrace (prefixWord ++ tailWord_6118943) baseStart_6118943 baseEnd_6118943 := by
    simpa [prefixWord, tailWord_6118943, baseEnd_6118943] using wordTrace_append hprefix tailTrace_6118943
  have hstable : (prefixWord ++ tailWord_6118943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6118943).length < 2 ^ (prefixWord ++ tailWord_6118943).sum := by decide
  have hdescent : baseEnd_6118943 < baseStart_6118943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6118943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119000 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_6119000 : Nat := 118140960795 + 6119000 * 2 ^ 59
def prefixEnd_6119000 : Nat := 4983230072969 + 3 ^ 40 * 6119000 * 2
def baseEnd_6119000 : Nat := 3141988124861664618059237

theorem tailTrace_6119000 : CollatzResearch.WordTrace tailWord_6119000 prefixEnd_6119000 3141988124861664618059237 := by
  unfold tailWord_6119000
  simp only [CollatzResearch.WordTrace]
  refine ⟨111589132415957758422533227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148785509887943677896710969 111589132415957758422533227)
  ·
    refine ⟨167383698623936637633799841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111589132415957758422533227 167383698623936637633799841)
    ·
      refine ⟨125537773967952478225349881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167383698623936637633799841 125537773967952478225349881)
      ·
        refine ⟨94153330475964358669012411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125537773967952478225349881 94153330475964358669012411)
        ·
          refine ⟨141229995713946538003518617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94153330475964358669012411 141229995713946538003518617)
          ·
            refine ⟨105922496785459903502638963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141229995713946538003518617 105922496785459903502638963)
            ·
              refine ⟨158883745178189855253958445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105922496785459903502638963 158883745178189855253958445)
              ·
                refine ⟨59581404441821195720234417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158883745178189855253958445 59581404441821195720234417)
                ·
                  refine ⟨44686053331365896790175813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59581404441821195720234417 44686053331365896790175813)
                  ·
                    refine ⟨8378634999631105648157965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44686053331365896790175813 8378634999631105648157965)
                    ·
                      refine ⟨3141988124861664618059237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378634999631105648157965 3141988124861664618059237)
                      ·
                        rfl

theorem cell23_6119000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_6119000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119000 prefixEnd_6119000 := by exact prefixLift 6119000
  have htrace : WordTrace (prefixWord ++ tailWord_6119000) baseStart_6119000 baseEnd_6119000 := by
    simpa [prefixWord, tailWord_6119000, baseEnd_6119000] using wordTrace_append hprefix tailTrace_6119000
  have hstable : (prefixWord ++ tailWord_6119000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119000).length < 2 ^ (prefixWord ++ tailWord_6119000).sum := by decide
  have hdescent : baseEnd_6119000 < baseStart_6119000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119054 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_6119054 : Nat := 118140960795 + 6119054 * 2 ^ 59
def prefixEnd_6119054 : Nat := 4983230072969 + 3 ^ 40 * 6119054 * 2
def baseEnd_6119054 : Nat := 349112872535223045198221

theorem tailTrace_6119054 : CollatzResearch.WordTrace tailWord_6119054 prefixEnd_6119054 349112872535223045198221 := by
  unfold tailWord_6119054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897529296714985508441527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148786822915813256045021477 27897529296714985508441527)
  ·
    refine ⟨41846293945072478262662291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27897529296714985508441527 41846293945072478262662291)
    ·
      refine ⟨62769440917608717393993437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41846293945072478262662291 62769440917608717393993437)
      ·
        refine ⟨23538540344103269022747539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62769440917608717393993437 23538540344103269022747539)
        ·
          refine ⟨35307810516154903534121309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23538540344103269022747539 35307810516154903534121309)
          ·
            refine ⟨13240428943558088825295491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35307810516154903534121309 13240428943558088825295491)
            ·
              refine ⟨19860643415337133237943237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240428943558088825295491 19860643415337133237943237)
              ·
                refine ⟨3723870640375712482114357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19860643415337133237943237 3723870640375712482114357)
                ·
                  refine ⟨349112872535223045198221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3723870640375712482114357 349112872535223045198221)
                  ·
                    rfl

theorem cell23_6119054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_6119054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119054 prefixEnd_6119054 := by exact prefixLift 6119054
  have htrace : WordTrace (prefixWord ++ tailWord_6119054) baseStart_6119054 baseEnd_6119054 := by
    simpa [prefixWord, tailWord_6119054, baseEnd_6119054] using wordTrace_append hprefix tailTrace_6119054
  have hstable : (prefixWord ++ tailWord_6119054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119054).length < 2 ^ (prefixWord ++ tailWord_6119054).sum := by decide
  have hdescent : baseEnd_6119054 < baseStart_6119054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119087 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 6, 2]
def baseStart_6119087 : Nat := 118140960795 + 6119087 * 2 ^ 59
def prefixEnd_6119087 : Nat := 4983230072969 + 3 ^ 40 * 6119087 * 2
def baseEnd_6119087 : Nat := 3142032797678605777671337

theorem tailTrace_6119087 : CollatzResearch.WordTrace tailWord_6119087 prefixEnd_6119087 3142032797678605777671337 := by
  unfold tailWord_6119087
  simp only [CollatzResearch.WordTrace]
  refine ⟨223181437982600330703483515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148787625321733553802322343 223181437982600330703483515)
  ·
    refine ⟨334772156973900496055225273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223181437982600330703483515 334772156973900496055225273)
    ·
      refine ⟨251079117730425372041418955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334772156973900496055225273 251079117730425372041418955)
      ·
        refine ⟨376618676595638058062128433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251079117730425372041418955 376618676595638058062128433)
        ·
          refine ⟨282464007446728543546596325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376618676595638058062128433 282464007446728543546596325)
          ·
            refine ⟨52962001396261601914986811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282464007446728543546596325 52962001396261601914986811)
            ·
              refine ⟨79443002094392402872480217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52962001396261601914986811 79443002094392402872480217)
              ·
                refine ⟨59582251570794302154360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79443002094392402872480217 59582251570794302154360163)
                ·
                  refine ⟨89373377356191453231540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59582251570794302154360163 89373377356191453231540245)
                  ·
                    refine ⟨4189377063571474370228449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89373377356191453231540245 4189377063571474370228449)
                    ·
                      refine ⟨3142032797678605777671337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189377063571474370228449 3142032797678605777671337)
                      ·
                        rfl

theorem cell23_6119087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6, 2].length) (baseStart_6119087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119087 prefixEnd_6119087 := by exact prefixLift 6119087
  have htrace : WordTrace (prefixWord ++ tailWord_6119087) baseStart_6119087 baseEnd_6119087 := by
    simpa [prefixWord, tailWord_6119087, baseEnd_6119087] using wordTrace_append hprefix tailTrace_6119087
  have hstable : (prefixWord ++ tailWord_6119087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119087).length < 2 ^ (prefixWord ++ tailWord_6119087).sum := by decide
  have hdescent : baseEnd_6119087 < baseStart_6119087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119124 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6119124 : Nat := 118140960795 + 6119124 * 2 ^ 59
def prefixEnd_6119124 : Nat := 4983230072969 + 3 ^ 40 * 6119124 * 2
def baseEnd_6119124 : Nat := 3142051796462822132908667

theorem tailTrace_6119124 : CollatzResearch.WordTrace tailWord_6119124 prefixEnd_6119124 3142051796462822132908667 := by
  unfold tailWord_6119124
  simp only [CollatzResearch.WordTrace]
  refine ⟨111591393741733143011290213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148788524988977524015053617 111591393741733143011290213)
  ·
    refine ⟨20923386326574964314616915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111591393741733143011290213 20923386326574964314616915)
    ·
      refine ⟨31385079489862446471925373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20923386326574964314616915 31385079489862446471925373)
      ·
        refine ⟨11769404808698417426972015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31385079489862446471925373 11769404808698417426972015)
        ·
          refine ⟨17654107213047626140458023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769404808698417426972015 17654107213047626140458023)
          ·
            refine ⟨26481160819571439210687035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17654107213047626140458023 26481160819571439210687035)
            ·
              refine ⟨39721741229357158816030553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26481160819571439210687035 39721741229357158816030553)
              ·
                refine ⟨29791305922017869112022915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39721741229357158816030553 29791305922017869112022915)
                ·
                  refine ⟨44686958883026803668034373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29791305922017869112022915 44686958883026803668034373)
                  ·
                    refine ⟨8378804790567525687756445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44686958883026803668034373 8378804790567525687756445)
                    ·
                      refine ⟨3142051796462822132908667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378804790567525687756445 3142051796462822132908667)
                      ·
                        rfl

theorem cell23_6119124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6119124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119124 prefixEnd_6119124 := by exact prefixLift 6119124
  have htrace : WordTrace (prefixWord ++ tailWord_6119124) baseStart_6119124 baseEnd_6119124 := by
    simpa [prefixWord, tailWord_6119124, baseEnd_6119124] using wordTrace_append hprefix tailTrace_6119124
  have hstable : (prefixWord ++ tailWord_6119124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119124).length < 2 ^ (prefixWord ++ tailWord_6119124).sum := by decide
  have hdescent : baseEnd_6119124 < baseStart_6119124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119171 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 1, 1, 3]
def baseStart_6119171 : Nat := 118140960795 + 6119171 * 2 ^ 59
def prefixEnd_6119171 : Nat := 4983230072969 + 3 ^ 40 * 6119171 * 2
def baseEnd_6119171 : Nat := 3142075930053583449020951

theorem tailTrace_6119171 : CollatzResearch.WordTrace tailWord_6119171 prefixEnd_6119171 3142075930053583449020951 := by
  unfold tailWord_6119171
  simp only [CollatzResearch.WordTrace]
  refine ⟨223184501714296013049541367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148789667809530675366360911 223184501714296013049541367)
  ·
    refine ⟨334776752571444019574312051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223184501714296013049541367 334776752571444019574312051)
    ·
      refine ⟨502165128857166029361468077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334776752571444019574312051 502165128857166029361468077)
      ·
        refine ⟨188311923321437261010550529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502165128857166029361468077 188311923321437261010550529)
        ·
          refine ⟨141233942491077945757912897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188311923321437261010550529 141233942491077945757912897)
          ·
            refine ⟨105925456868308459318434673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141233942491077945757912897 105925456868308459318434673)
            ·
              refine ⟨79444092651231344488826005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105925456868308459318434673 79444092651231344488826005)
              ·
                refine ⟨3723941843026469272913719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79444092651231344488826005 3723941843026469272913719)
                ·
                  refine ⟨5585912764539703909370579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723941843026469272913719 5585912764539703909370579)
                  ·
                    refine ⟨8378869146809555864055869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585912764539703909370579 8378869146809555864055869)
                    ·
                      refine ⟨3142075930053583449020951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378869146809555864055869 3142075930053583449020951)
                      ·
                        rfl

theorem cell23_6119171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_6119171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119171 prefixEnd_6119171 := by exact prefixLift 6119171
  have htrace : WordTrace (prefixWord ++ tailWord_6119171) baseStart_6119171 baseEnd_6119171 := by
    simpa [prefixWord, tailWord_6119171, baseEnd_6119171] using wordTrace_append hprefix tailTrace_6119171
  have hstable : (prefixWord ++ tailWord_6119171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119171).length < 2 ^ (prefixWord ++ tailWord_6119171).sum := by decide
  have hdescent : baseEnd_6119171 < baseStart_6119171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119177 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_6119177 : Nat := 118140960795 + 6119177 * 2 ^ 59
def prefixEnd_6119177 : Nat := 4983230072969 + 3 ^ 40 * 6119177 * 2
def baseEnd_6119177 : Nat := 3142079010937510425545923

theorem tailTrace_6119177 : CollatzResearch.WordTrace tailWord_6119177 prefixEnd_6119177 3142079010937510425545923 := by
  unfold tailWord_6119177
  simp only [CollatzResearch.WordTrace]
  refine ⟨223184720552274276074259785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148789813701516184049506523 223184720552274276074259785)
  ·
    refine ⟨167388540414205707055694839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223184720552274276074259785 167388540414205707055694839)
    ·
      refine ⟨251082810621308560583542259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167388540414205707055694839 251082810621308560583542259)
      ·
        refine ⟨376624215931962840875313389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251082810621308560583542259 376624215931962840875313389)
        ·
          refine ⟨141234080974486065328242521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376624215931962840875313389 141234080974486065328242521)
          ·
            refine ⟨105925560730864548996181891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141234080974486065328242521 105925560730864548996181891)
            ·
              refine ⟨158888341096296823494272837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105925560730864548996181891 158888341096296823494272837)
              ·
                refine ⟨29791563955555654405176157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158888341096296823494272837 29791563955555654405176157)
                ·
                  refine ⟨11171836483333370401941059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29791563955555654405176157 11171836483333370401941059)
                  ·
                    refine ⟨16757754725000055602911589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11171836483333370401941059 16757754725000055602911589)
                    ·
                      refine ⟨3142079010937510425545923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16757754725000055602911589 3142079010937510425545923)
                      ·
                        rfl

theorem cell23_6119177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_6119177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119177 prefixEnd_6119177 := by exact prefixLift 6119177
  have htrace : WordTrace (prefixWord ++ tailWord_6119177) baseStart_6119177 baseEnd_6119177 := by
    simpa [prefixWord, tailWord_6119177, baseEnd_6119177] using wordTrace_append hprefix tailTrace_6119177
  have hstable : (prefixWord ++ tailWord_6119177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119177).length < 2 ^ (prefixWord ++ tailWord_6119177).sum := by decide
  have hdescent : baseEnd_6119177 < baseStart_6119177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119187 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 6, 4]
def baseStart_6119187 : Nat := 118140960795 + 6119187 * 2 ^ 59
def prefixEnd_6119187 : Nat := 4983230072969 + 3 ^ 40 * 6119187 * 2
def baseEnd_6119187 : Nat := 1047361381914685128806959

theorem tailTrace_6119187 : CollatzResearch.WordTrace tailWord_6119187 prefixEnd_6119187 1047361381914685128806959 := by
  unfold tailWord_6119187
  simp only [CollatzResearch.WordTrace]
  refine ⟨223185085282238047782123815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148790056854825365188082543 223185085282238047782123815)
  ·
    refine ⟨334777627923357071673185723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223185085282238047782123815 334777627923357071673185723)
    ·
      refine ⟨502166441885035607509778585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334777627923357071673185723 502166441885035607509778585)
      ·
        refine ⟨376624831413776705632333939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502166441885035607509778585 376624831413776705632333939)
        ·
          refine ⟨564937247120665058448500909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376624831413776705632333939 564937247120665058448500909)
          ·
            refine ⟨211851467670249396918187841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564937247120665058448500909 211851467670249396918187841)
            ·
              refine ⟨158888600752687047688640881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211851467670249396918187841 158888600752687047688640881)
              ·
                refine ⟨119166450564515285766480661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158888600752687047688640881 119166450564515285766480661)
                ·
                  refine ⟨5585927370211654020303781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119166450564515285766480661 5585927370211654020303781)
                  ·
                    refine ⟨1047361381914685128806959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585927370211654020303781 1047361381914685128806959)
                    ·
                      rfl

theorem cell23_6119187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 4].length) (baseStart_6119187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119187 prefixEnd_6119187 := by exact prefixLift 6119187
  have htrace : WordTrace (prefixWord ++ tailWord_6119187) baseStart_6119187 baseEnd_6119187 := by
    simpa [prefixWord, tailWord_6119187, baseEnd_6119187] using wordTrace_append hprefix tailTrace_6119187
  have hstable : (prefixWord ++ tailWord_6119187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119187).length < 2 ^ (prefixWord ++ tailWord_6119187).sum := by decide
  have hdescent : baseEnd_6119187 < baseStart_6119187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119191 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 1, 5]
def baseStart_6119191 : Nat := 118140960795 + 6119191 * 2 ^ 59
def prefixEnd_6119191 : Nat := 4983230072969 + 3 ^ 40 * 6119191 * 2
def baseEnd_6119191 : Nat := 1047362066555557790256953

theorem tailTrace_6119191 : CollatzResearch.WordTrace tailWord_6119191 prefixEnd_6119191 1047362066555557790256953 := by
  unfold tailWord_6119191
  simp only [CollatzResearch.WordTrace]
  refine ⟨223185231174223556465269427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148790154116149037643512951 223185231174223556465269427)
  ·
    refine ⟨334777846761335334697904141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223185231174223556465269427 334777846761335334697904141)
    ·
      refine ⟨125541692535500750511714053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334777846761335334697904141 125541692535500750511714053)
      ·
        refine ⟨23539067350406390720946385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125541692535500750511714053 23539067350406390720946385)
        ·
          refine ⟨17654300512804793040709789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23539067350406390720946385 17654300512804793040709789)
          ·
            refine ⟨6620362692301797390266171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17654300512804793040709789 6620362692301797390266171)
            ·
              refine ⟨9930544038452696085399257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620362692301797390266171 9930544038452696085399257)
              ·
                refine ⟨7447908028839522064049443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9930544038452696085399257 7447908028839522064049443)
                ·
                  refine ⟨11171862043259283096074165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7447908028839522064049443 11171862043259283096074165)
                  ·
                    refine ⟨1047362066555557790256953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11171862043259283096074165 1047362066555557790256953)
                    ·
                      rfl

theorem cell23_6119191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_6119191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119191 prefixEnd_6119191 := by exact prefixLift 6119191
  have htrace : WordTrace (prefixWord ++ tailWord_6119191) baseStart_6119191 baseEnd_6119191 := by
    simpa [prefixWord, tailWord_6119191, baseEnd_6119191] using wordTrace_append hprefix tailTrace_6119191
  have hstable : (prefixWord ++ tailWord_6119191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119191).length < 2 ^ (prefixWord ++ tailWord_6119191).sum := by decide
  have hdescent : baseEnd_6119191 < baseStart_6119191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119194 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_6119194 : Nat := 118140960795 + 6119194 * 2 ^ 59
def prefixEnd_6119194 : Nat := 4983230072969 + 3 ^ 40 * 6119194 * 2
def baseEnd_6119194 : Nat := 3142087740108636859033345

theorem tailTrace_6119194 : CollatzResearch.WordTrace tailWord_6119194 prefixEnd_6119194 3142087740108636859033345 := by
  unfold tailWord_6119194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55796335148303171994407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148790227062141791985085757 55796335148303171994407159)
  ·
    refine ⟨83694502722454757991610739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55796335148303171994407159 83694502722454757991610739)
    ·
      refine ⟨125541754083682136987416109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83694502722454757991610739 125541754083682136987416109)
      ·
        refine ⟨47078157781380801370281041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125541754083682136987416109 47078157781380801370281041)
        ·
          refine ⟨35308618336035601027710781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47078157781380801370281041 35308618336035601027710781)
          ·
            refine ⟨13240731876013350385391543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35308618336035601027710781 13240731876013350385391543)
            ·
              refine ⟨19861097814020025578087315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240731876013350385391543 19861097814020025578087315)
              ·
                refine ⟨29791646721030038367130973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19861097814020025578087315 29791646721030038367130973)
                ·
                  refine ⟨11171867520386264387674115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29791646721030038367130973 11171867520386264387674115)
                  ·
                    refine ⟨16757801280579396581511173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11171867520386264387674115 16757801280579396581511173)
                    ·
                      refine ⟨3142087740108636859033345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16757801280579396581511173 3142087740108636859033345)
                      ·
                        rfl

theorem cell23_6119194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_6119194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119194 prefixEnd_6119194 := by exact prefixLift 6119194
  have htrace : WordTrace (prefixWord ++ tailWord_6119194) baseStart_6119194 baseEnd_6119194 := by
    simpa [prefixWord, tailWord_6119194, baseEnd_6119194] using wordTrace_append hprefix tailTrace_6119194
  have hstable : (prefixWord ++ tailWord_6119194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119194).length < 2 ^ (prefixWord ++ tailWord_6119194).sum := by decide
  have hdescent : baseEnd_6119194 < baseStart_6119194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119204 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_6119204 : Nat := 118140960795 + 6119204 * 2 ^ 59
def prefixEnd_6119204 : Nat := 4983230072969 + 3 ^ 40 * 6119204 * 2
def baseEnd_6119204 : Nat := 1047364291638393939969433

theorem tailTrace_6119204 : CollatzResearch.WordTrace tailWord_6119204 prefixEnd_6119204 1047364291638393939969433 := by
  unfold tailWord_6119204
  simp only [CollatzResearch.WordTrace]
  refine ⟨111592852661588229842746333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148790470215450973123661777 111592852661588229842746333)
  ·
    refine ⟨41847319748095586191029875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111592852661588229842746333 41847319748095586191029875)
    ·
      refine ⟨62770979622143379286544813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41847319748095586191029875 62770979622143379286544813)
      ·
        refine ⟨23539117358303767232454305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62770979622143379286544813 23539117358303767232454305)
        ·
          refine ⟨17654338018727825424340729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23539117358303767232454305 17654338018727825424340729)
          ·
            refine ⟨13240753514045869068255547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17654338018727825424340729 13240753514045869068255547)
            ·
              refine ⟨19861130271068803602383321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240753514045869068255547 19861130271068803602383321)
              ·
                refine ⟨14895847703301602701787491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19861130271068803602383321 14895847703301602701787491)
                ·
                  refine ⟨22343771554952404052681237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14895847703301602701787491 22343771554952404052681237)
                  ·
                    refine ⟨1047364291638393939969433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22343771554952404052681237 1047364291638393939969433)
                    ·
                      rfl

theorem cell23_6119204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_6119204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119204 prefixEnd_6119204 := by exact prefixLift 6119204
  have htrace : WordTrace (prefixWord ++ tailWord_6119204) baseStart_6119204 baseEnd_6119204 := by
    simpa [prefixWord, tailWord_6119204, baseEnd_6119204] using wordTrace_append hprefix tailTrace_6119204
  have hstable : (prefixWord ++ tailWord_6119204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119204).length < 2 ^ (prefixWord ++ tailWord_6119204).sum := by decide
  have hdescent : baseEnd_6119204 < baseStart_6119204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119222 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6119222 : Nat := 118140960795 + 6119222 * 2 ^ 59
def prefixEnd_6119222 : Nat := 4983230072969 + 3 ^ 40 * 6119222 * 2
def baseEnd_6119222 : Nat := 3142102117566962749483217

theorem tailTrace_6119222 : CollatzResearch.WordTrace tailWord_6119222 prefixEnd_6119222 3142102117566962749483217 := by
  unfold tailWord_6119222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13949147614819453047477995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148790907891407499173098613 13949147614819453047477995)
  ·
    refine ⟨20923721422229179571216993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13949147614819453047477995 20923721422229179571216993)
    ·
      refine ⟨15692791066671884678412745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20923721422229179571216993 15692791066671884678412745)
      ·
        refine ⟨11769593300003913508809559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15692791066671884678412745 11769593300003913508809559)
        ·
          refine ⟨17654389950005870263214339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769593300003913508809559 17654389950005870263214339)
          ·
            refine ⟨26481584925008805394821509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17654389950005870263214339 26481584925008805394821509)
            ·
              refine ⟨4965297173439151011529033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26481584925008805394821509 4965297173439151011529033)
              ·
                refine ⟨3723972880079363258646775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965297173439151011529033 3723972880079363258646775)
                ·
                  refine ⟨5585959320119044887970163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723972880079363258646775 5585959320119044887970163)
                  ·
                    refine ⟨8378938980178567331955245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585959320119044887970163 8378938980178567331955245)
                    ·
                      refine ⟨3142102117566962749483217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8378938980178567331955245 3142102117566962749483217)
                      ·
                        rfl

theorem cell23_6119222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6119222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119222 prefixEnd_6119222 := by exact prefixLift 6119222
  have htrace : WordTrace (prefixWord ++ tailWord_6119222) baseStart_6119222 baseEnd_6119222 := by
    simpa [prefixWord, tailWord_6119222, baseEnd_6119222] using wordTrace_append hprefix tailTrace_6119222
  have hstable : (prefixWord ++ tailWord_6119222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119222).length < 2 ^ (prefixWord ++ tailWord_6119222).sum := by decide
  have hdescent : baseEnd_6119222 < baseStart_6119222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119238 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_6119238 : Nat := 118140960795 + 6119238 * 2 ^ 59
def prefixEnd_6119238 : Nat := 4983230072969 + 3 ^ 40 * 6119238 * 2
def baseEnd_6119238 : Nat := 1047370111085811562294381

theorem tailTrace_6119238 : CollatzResearch.WordTrace tailWord_6119238 prefixEnd_6119238 1047370111085811562294381 := by
  unfold tailWord_6119238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974592043907915109132199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148791296936702188994820245 6974592043907915109132199)
  ·
    refine ⟨10461888065861872663698299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974592043907915109132199 10461888065861872663698299)
    ·
      refine ⟨15692832098792808995547449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10461888065861872663698299 15692832098792808995547449)
      ·
        refine ⟨11769624074094606746660587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15692832098792808995547449 11769624074094606746660587)
        ·
          refine ⟨17654436111141910119990881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769624074094606746660587 17654436111141910119990881)
          ·
            refine ⟨13240827083356432589993161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17654436111141910119990881 13240827083356432589993161)
            ·
              refine ⟨9930620312517324442494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13240827083356432589993161 9930620312517324442494871)
              ·
                refine ⟨14895930468775986663742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9930620312517324442494871 14895930468775986663742307)
                ·
                  refine ⟨22343895703163979995613461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14895930468775986663742307 22343895703163979995613461)
                  ·
                    refine ⟨1047370111085811562294381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22343895703163979995613461 1047370111085811562294381)
                    ·
                      rfl

theorem cell23_6119238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_6119238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119238 prefixEnd_6119238 := by exact prefixLift 6119238
  have htrace : WordTrace (prefixWord ++ tailWord_6119238) baseStart_6119238 baseEnd_6119238 := by
    simpa [prefixWord, tailWord_6119238, baseEnd_6119238] using wordTrace_append hprefix tailTrace_6119238
  have hstable : (prefixWord ++ tailWord_6119238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119238).length < 2 ^ (prefixWord ++ tailWord_6119238).sum := by decide
  have hdescent : baseEnd_6119238 < baseStart_6119238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119245 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6119245 : Nat := 118140960795 + 6119245 * 2 ^ 59
def prefixEnd_6119245 : Nat := 4983230072969 + 3 ^ 40 * 6119245 * 2
def baseEnd_6119245 : Nat := 3142113927622016159495611

theorem tailTrace_6119245 : CollatzResearch.WordTrace tailWord_6119245 prefixEnd_6119245 3142113927622016159495611 := by
  unfold tailWord_6119245
  simp only [CollatzResearch.WordTrace]
  refine ⟨223187200716027923687735189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148791467144018615791823459 223187200716027923687735189)
  ·
    refine ⟨10461900033563808922862587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223187200716027923687735189 10461900033563808922862587)
    ·
      refine ⟨15692850050345713384293881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10461900033563808922862587 15692850050345713384293881)
      ·
        refine ⟨11769637537759285038220411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15692850050345713384293881 11769637537759285038220411)
        ·
          refine ⟨17654456306638927557330617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769637537759285038220411 17654456306638927557330617)
          ·
            refine ⟨13240842229979195667997963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17654456306638927557330617 13240842229979195667997963)
            ·
              refine ⟨19861263344968793501996945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240842229979195667997963 19861263344968793501996945)
              ·
                refine ⟨14895947508726595126497709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19861263344968793501996945 14895947508726595126497709)
                ·
                  refine ⟨5585980315772473172436641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14895947508726595126497709 5585980315772473172436641)
                  ·
                    refine ⟨4189485236829354879327481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585980315772473172436641 4189485236829354879327481)
                    ·
                      refine ⟨3142113927622016159495611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189485236829354879327481 3142113927622016159495611)
                      ·
                        rfl

theorem cell23_6119245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6119245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119245 prefixEnd_6119245 := by exact prefixLift 6119245
  have htrace : WordTrace (prefixWord ++ tailWord_6119245) baseStart_6119245 baseEnd_6119245 := by
    simpa [prefixWord, tailWord_6119245, baseEnd_6119245] using wordTrace_append hprefix tailTrace_6119245
  have hstable : (prefixWord ++ tailWord_6119245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119245).length < 2 ^ (prefixWord ++ tailWord_6119245).sum := by decide
  have hdescent : baseEnd_6119245 < baseStart_6119245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119257 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_6119257 : Nat := 118140960795 + 6119257 * 2 ^ 59
def prefixEnd_6119257 : Nat := 4983230072969 + 3 ^ 40 * 6119257 * 2
def baseEnd_6119257 : Nat := 3142120089389870112545555

theorem tailTrace_6119257 : CollatzResearch.WordTrace tailWord_6119257 prefixEnd_6119257 3142120089389870112545555 := by
  unfold tailWord_6119257
  simp only [CollatzResearch.WordTrace]
  refine ⟨223187638391984449737172025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148791758927989633158114683 223187638391984449737172025)
  ·
    refine ⟨167390728793988337302879019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223187638391984449737172025 167390728793988337302879019)
    ·
      refine ⟨251086093190982505954318529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167390728793988337302879019 251086093190982505954318529)
      ·
        refine ⟨188314569893236879465738897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251086093190982505954318529 188314569893236879465738897)
        ·
          refine ⟨141235927419927659599304173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188314569893236879465738897 141235927419927659599304173)
          ·
            refine ⟨52963472782472872349739065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141235927419927659599304173 52963472782472872349739065)
            ·
              refine ⟨39722604586854654262304299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52963472782472872349739065 39722604586854654262304299)
              ·
                refine ⟨59583906880281981393456449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39722604586854654262304299 59583906880281981393456449)
                ·
                  refine ⟨44687930160211486045092337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59583906880281981393456449 44687930160211486045092337)
                  ·
                    refine ⟨33515947620158614533819253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44687930160211486045092337 33515947620158614533819253)
                    ·
                      refine ⟨3142120089389870112545555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33515947620158614533819253 3142120089389870112545555)
                      ·
                        rfl

theorem cell23_6119257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_6119257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119257 prefixEnd_6119257 := by exact prefixLift 6119257
  have htrace : WordTrace (prefixWord ++ tailWord_6119257) baseStart_6119257 baseEnd_6119257 := by
    simpa [prefixWord, tailWord_6119257, baseEnd_6119257] using wordTrace_append hprefix tailTrace_6119257
  have hstable : (prefixWord ++ tailWord_6119257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119257).length < 2 ^ (prefixWord ++ tailWord_6119257).sum := by decide
  have hdescent : baseEnd_6119257 < baseStart_6119257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119278 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6119278 : Nat := 118140960795 + 6119278 * 2 ^ 59
def prefixEnd_6119278 : Nat := 4983230072969 + 3 ^ 40 * 6119278 * 2
def baseEnd_6119278 : Nat := 3142130872483614530382959

theorem tailTrace_6119278 : CollatzResearch.WordTrace tailWord_6119278 prefixEnd_6119278 3142130872483614530382959 := by
  unfold tailWord_6119278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898550540613546290460811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148792269549938913549124325 27898550540613546290460811)
  ·
    refine ⟨41847825810920319435691217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27898550540613546290460811 41847825810920319435691217)
    ·
      refine ⟨31385869358190239576768413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41847825810920319435691217 31385869358190239576768413)
      ·
        refine ⟨11769701009321339841288155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31385869358190239576768413 11769701009321339841288155)
        ·
          refine ⟨17654551513982009761932233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769701009321339841288155 17654551513982009761932233)
          ·
            refine ⟨13240913635486507321449175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17654551513982009761932233 13240913635486507321449175)
            ·
              refine ⟨19861370453229760982173763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240913635486507321449175 19861370453229760982173763)
              ·
                refine ⟨29792055679844641473260645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19861370453229760982173763 29792055679844641473260645)
                ·
                  refine ⟨5586010439970870276236371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29792055679844641473260645 5586010439970870276236371)
                  ·
                    refine ⟨8379015659956305414354557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5586010439970870276236371 8379015659956305414354557)
                    ·
                      refine ⟨3142130872483614530382959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379015659956305414354557 3142130872483614530382959)
                      ·
                        rfl

theorem cell23_6119278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6119278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119278 prefixEnd_6119278 := by exact prefixLift 6119278
  have htrace : WordTrace (prefixWord ++ tailWord_6119278) baseStart_6119278 baseEnd_6119278 := by
    simpa [prefixWord, tailWord_6119278, baseEnd_6119278] using wordTrace_append hprefix tailTrace_6119278
  have hstable : (prefixWord ++ tailWord_6119278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119278).length < 2 ^ (prefixWord ++ tailWord_6119278).sum := by decide
  have hdescent : baseEnd_6119278 < baseStart_6119278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119287 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_6119287 : Nat := 118140960795 + 6119287 * 2 ^ 59
def prefixEnd_6119287 : Nat := 4983230072969 + 3 ^ 40 * 6119287 * 2
def baseEnd_6119287 : Nat := 3142135493809504995170417

theorem tailTrace_6119287 : CollatzResearch.WordTrace tailWord_6119287 prefixEnd_6119287 3142135493809504995170417 := by
  unfold tailWord_6119287
  simp only [CollatzResearch.WordTrace]
  refine ⟨223188732581875764860764115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148792488387917176573842743 223188732581875764860764115)
  ·
    refine ⟨334783098872813647291146173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223188732581875764860764115 334783098872813647291146173)
    ·
      refine ⟨125543662077305117734179815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334783098872813647291146173 125543662077305117734179815)
      ·
        refine ⟨188315493115957676601269723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125543662077305117734179815 188315493115957676601269723)
        ·
          refine ⟨282473239673936514901904585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188315493115957676601269723 282473239673936514901904585)
          ·
            refine ⟨211854929755452386176428439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282473239673936514901904585 211854929755452386176428439)
            ·
              refine ⟨317782394633178579264642659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211854929755452386176428439 317782394633178579264642659)
              ·
                refine ⟨476673591949767868896963989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317782394633178579264642659 476673591949767868896963989)
                ·
                  refine ⟨22344074622645368854545187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 476673591949767868896963989 22344074622645368854545187)
                  ·
                    refine ⟨33516111933968053281817781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22344074622645368854545187 33516111933968053281817781)
                    ·
                      refine ⟨3142135493809504995170417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33516111933968053281817781 3142135493809504995170417)
                      ·
                        rfl

theorem cell23_6119287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_6119287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119287 prefixEnd_6119287 := by exact prefixLift 6119287
  have htrace : WordTrace (prefixWord ++ tailWord_6119287) baseStart_6119287 baseEnd_6119287 := by
    simpa [prefixWord, tailWord_6119287, baseEnd_6119287] using wordTrace_append hprefix tailTrace_6119287
  have hstable : (prefixWord ++ tailWord_6119287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119287).length < 2 ^ (prefixWord ++ tailWord_6119287).sum := by decide
  have hdescent : baseEnd_6119287 < baseStart_6119287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119337 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_6119337 : Nat := 118140960795 + 6119337 * 2 ^ 59
def prefixEnd_6119337 : Nat := 4983230072969 + 3 ^ 40 * 6119337 * 2
def baseEnd_6119337 : Nat := 1047387055947409933181729

theorem tailTrace_6119337 : CollatzResearch.WordTrace tailWord_6119337 prefixEnd_6119337 1047387055947409933181729 := by
  unfold tailWord_6119337
  simp only [CollatzResearch.WordTrace]
  refine ⟨223190556231694623400084265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148793704154463082266722843 223190556231694623400084265)
  ·
    refine ⟨167392917173770967550063199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223190556231694623400084265 167392917173770967550063199)
    ·
      refine ⟨251089375760656451325094799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167392917173770967550063199 251089375760656451325094799)
      ·
        refine ⟨376634063640984676987642199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251089375760656451325094799 376634063640984676987642199)
        ·
          refine ⟨564951095461477015481463299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376634063640984676987642199 564951095461477015481463299)
          ·
            refine ⟨847426643192215523222194949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564951095461477015481463299 847426643192215523222194949)
            ·
              refine ⟨158892495598540410604161553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 847426643192215523222194949 158892495598540410604161553)
              ·
                refine ⟨119169371698905307953121165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158892495598540410604161553 119169371698905307953121165)
                ·
                  refine ⟨44688514387089490482420437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119169371698905307953121165 44688514387089490482420437)
                  ·
                    refine ⟨1047387055947409933181729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44688514387089490482420437 1047387055947409933181729)
                    ·
                      rfl

theorem cell23_6119337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_6119337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119337 prefixEnd_6119337 := by exact prefixLift 6119337
  have htrace : WordTrace (prefixWord ++ tailWord_6119337) baseStart_6119337 baseEnd_6119337 := by
    simpa [prefixWord, tailWord_6119337, baseEnd_6119337] using wordTrace_append hprefix tailTrace_6119337
  have hstable : (prefixWord ++ tailWord_6119337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119337).length < 2 ^ (prefixWord ++ tailWord_6119337).sum := by decide
  have hdescent : baseEnd_6119337 < baseStart_6119337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119391 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_6119391 : Nat := 118140960795 + 6119391 * 2 ^ 59
def prefixEnd_6119391 : Nat := 4983230072969 + 3 ^ 40 * 6119391 * 2
def baseEnd_6119391 : Nat := 3142188895797572588269939

theorem tailTrace_6119391 : CollatzResearch.WordTrace tailWord_6119391 prefixEnd_6119391 3142188895797572588269939 := by
  unfold tailWord_6119391
  simp only [CollatzResearch.WordTrace]
  refine ⟨223192525773498990622550027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148795017182332660415033351 223192525773498990622550027)
  ·
    refine ⟨334788788660248485933825041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223192525773498990622550027 334788788660248485933825041)
    ·
      refine ⟨251091591495186364450368781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334788788660248485933825041 251091591495186364450368781)
      ·
        refine ⟨94159346810694886668888293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251091591495186364450368781 94159346810694886668888293)
        ·
          refine ⟨17654877527005291250416555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94159346810694886668888293 17654877527005291250416555)
          ·
            refine ⟨26482316290507936875624833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17654877527005291250416555 26482316290507936875624833)
            ·
              refine ⟨19861737217880952656718625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26482316290507936875624833 19861737217880952656718625)
              ·
                refine ⟨14896302913410714492538969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19861737217880952656718625 14896302913410714492538969)
                ·
                  refine ⟨11172227185058035869404227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14896302913410714492538969 11172227185058035869404227)
                  ·
                    refine ⟨16758340777587053804106341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11172227185058035869404227 16758340777587053804106341)
                    ·
                      refine ⟨3142188895797572588269939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16758340777587053804106341 3142188895797572588269939)
                      ·
                        rfl

theorem cell23_6119391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_6119391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119391 prefixEnd_6119391 := by exact prefixLift 6119391
  have htrace : WordTrace (prefixWord ++ tailWord_6119391) baseStart_6119391 baseEnd_6119391 := by
    simpa [prefixWord, tailWord_6119391, baseEnd_6119391] using wordTrace_append hprefix tailTrace_6119391
  have hstable : (prefixWord ++ tailWord_6119391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119391).length < 2 ^ (prefixWord ++ tailWord_6119391).sum := by decide
  have hdescent : baseEnd_6119391 < baseStart_6119391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119424 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_6119424 : Nat := 118140960795 + 6119424 * 2 ^ 59
def prefixEnd_6119424 : Nat := 4983230072969 + 3 ^ 40 * 6119424 * 2
def baseEnd_6119424 : Nat := 3142205840659170959157287

theorem tailTrace_6119424 : CollatzResearch.WordTrace tailWord_6119424 prefixEnd_6119424 3142205840659170959157287 := by
  unfold tailWord_6119424
  simp only [CollatzResearch.WordTrace]
  refine ⟨111596864691189718629250663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148795819588252958172334217 111596864691189718629250663)
  ·
    refine ⟨167395297036784577943875995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111596864691189718629250663 167395297036784577943875995)
    ·
      refine ⟨251092945555176866915813993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167395297036784577943875995 251092945555176866915813993)
      ·
        refine ⟨188319709166382650186860495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251092945555176866915813993 188319709166382650186860495)
        ·
          refine ⟨282479563749573975280290743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188319709166382650186860495 282479563749573975280290743)
          ·
            refine ⟨423719345624360962920436115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282479563749573975280290743 423719345624360962920436115)
            ·
              refine ⟨635579018436541444380654173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423719345624360962920436115 635579018436541444380654173)
              ·
                refine ⟨238342131913703041642745315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635579018436541444380654173 238342131913703041642745315)
                ·
                  refine ⟨357513197870554562464117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238342131913703041642745315 357513197870554562464117973)
                  ·
                    refine ⟨8379215575091122557752765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 357513197870554562464117973 8379215575091122557752765)
                    ·
                      refine ⟨3142205840659170959157287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379215575091122557752765 3142205840659170959157287)
                      ·
                        rfl

theorem cell23_6119424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_6119424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119424 prefixEnd_6119424 := by exact prefixLift 6119424
  have htrace : WordTrace (prefixWord ++ tailWord_6119424) baseStart_6119424 baseEnd_6119424 := by
    simpa [prefixWord, tailWord_6119424, baseEnd_6119424] using wordTrace_append hprefix tailTrace_6119424
  have hstable : (prefixWord ++ tailWord_6119424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119424).length < 2 ^ (prefixWord ++ tailWord_6119424).sum := by decide
  have hdescent : baseEnd_6119424 < baseStart_6119424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119508 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6119508 : Nat := 118140960795 + 6119508 * 2 ^ 59
def prefixEnd_6119508 : Nat := 4983230072969 + 3 ^ 40 * 6119508 * 2
def baseEnd_6119508 : Nat := 1047416324344716210168967

theorem tailTrace_6119508 : CollatzResearch.WordTrace tailWord_6119508 prefixEnd_6119508 1047416324344716210168967 := by
  unfold tailWord_6119508
  simp only [CollatzResearch.WordTrace]
  refine ⟨111598396557037559802279589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148797862076050079736372785 111598396557037559802279589)
  ·
    refine ⟨20924699354444542462927423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111598396557037559802279589 20924699354444542462927423)
    ·
      refine ⟨31387049031666813694391135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20924699354444542462927423 31387049031666813694391135)
      ·
        refine ⟨47080573547500220541586703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31387049031666813694391135 47080573547500220541586703)
        ·
          refine ⟨70620860321250330812380055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47080573547500220541586703 70620860321250330812380055)
          ·
            refine ⟨105931290481875496218570083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70620860321250330812380055 105931290481875496218570083)
            ·
              refine ⟨158896935722813244327855125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105931290481875496218570083 158896935722813244327855125)
              ·
                refine ⟨7448293862006870827868209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158896935722813244327855125 7448293862006870827868209)
                ·
                  refine ⟨5586220396505153120901157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448293862006870827868209 5586220396505153120901157)
                  ·
                    refine ⟨1047416324344716210168967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586220396505153120901157 1047416324344716210168967)
                    ·
                      rfl

theorem cell23_6119508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6119508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119508 prefixEnd_6119508 := by exact prefixLift 6119508
  have htrace : WordTrace (prefixWord ++ tailWord_6119508) baseStart_6119508 baseEnd_6119508 := by
    simpa [prefixWord, tailWord_6119508, baseEnd_6119508] using wordTrace_append hprefix tailTrace_6119508
  have hstable : (prefixWord ++ tailWord_6119508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119508).length < 2 ^ (prefixWord ++ tailWord_6119508).sum := by decide
  have hdescent : baseEnd_6119508 < baseStart_6119508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119525 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_6119525 : Nat := 118140960795 + 6119525 * 2 ^ 59
def prefixEnd_6119525 : Nat := 4983230072969 + 3 ^ 40 * 6119525 * 2
def baseEnd_6119525 : Nat := 1047419234068425021331441

theorem tailTrace_6119525 : CollatzResearch.WordTrace tailWord_6119525 prefixEnd_6119525 1047419234068425021331441 := by
  unfold tailWord_6119525
  simp only [CollatzResearch.WordTrace]
  refine ⟨223197413155013531507928029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148798275436675687671952019 223197413155013531507928029)
  ·
    refine ⟨83699029933130074315473011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223197413155013531507928029 83699029933130074315473011)
    ·
      refine ⟨125548544899695111473209517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83699029933130074315473011 125548544899695111473209517)
      ·
        refine ⟨47080704337385666802453569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125548544899695111473209517 47080704337385666802453569)
        ·
          refine ⟨35310528253039250101840177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47080704337385666802453569 35310528253039250101840177)
          ·
            refine ⟨26482896189779437576380133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35310528253039250101840177 26482896189779437576380133)
            ·
              refine ⟨4965543035583644545571275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26482896189779437576380133 4965543035583644545571275)
              ·
                refine ⟨7448314553375466818356913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965543035583644545571275 7448314553375466818356913)
                ·
                  refine ⟨5586235915031600113767685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448314553375466818356913 5586235915031600113767685)
                  ·
                    refine ⟨1047419234068425021331441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586235915031600113767685 1047419234068425021331441)
                    ·
                      rfl

theorem cell23_6119525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_6119525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119525 prefixEnd_6119525 := by exact prefixLift 6119525
  have htrace : WordTrace (prefixWord ++ tailWord_6119525) baseStart_6119525 baseEnd_6119525 := by
    simpa [prefixWord, tailWord_6119525, baseEnd_6119525] using wordTrace_append hprefix tailTrace_6119525
  have hstable : (prefixWord ++ tailWord_6119525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119525).length < 2 ^ (prefixWord ++ tailWord_6119525).sum := by decide
  have hdescent : baseEnd_6119525 < baseStart_6119525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119535 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_6119535 : Nat := 118140960795 + 6119535 * 2 ^ 59
def prefixEnd_6119535 : Nat := 4983230072969 + 3 ^ 40 * 6119535 * 2
def baseEnd_6119535 : Nat := 3142262837011820024869277

theorem tailTrace_6119535 : CollatzResearch.WordTrace tailWord_6119535 prefixEnd_6119535 3142262837011820024869277 := by
  unfold tailWord_6119535
  simp only [CollatzResearch.WordTrace]
  refine ⟨223197777884977303215792059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148798518589984868810528039 223197777884977303215792059)
  ·
    refine ⟨334796666827465954823688089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223197777884977303215792059 334796666827465954823688089)
    ·
      refine ⟨251097500120599466117766067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334796666827465954823688089 251097500120599466117766067)
      ·
        refine ⟨376646250180899199176649101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251097500120599466117766067 376646250180899199176649101)
        ·
          refine ⟨141242343817837199691243413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376646250180899199176649101 141242343817837199691243413)
          ·
            refine ⟨6620734866461118735527035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141242343817837199691243413 6620734866461118735527035)
            ·
              refine ⟨9931102299691678103290553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620734866461118735527035 9931102299691678103290553)
              ·
                refine ⟨7448326724768758577467915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9931102299691678103290553 7448326724768758577467915)
                ·
                  refine ⟨11172490087153137866201873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7448326724768758577467915 11172490087153137866201873)
                  ·
                    refine ⟨8379367565364853399651405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11172490087153137866201873 8379367565364853399651405)
                    ·
                      refine ⟨3142262837011820024869277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379367565364853399651405 3142262837011820024869277)
                      ·
                        rfl

theorem cell23_6119535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_6119535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119535 prefixEnd_6119535 := by exact prefixLift 6119535
  have htrace : WordTrace (prefixWord ++ tailWord_6119535) baseStart_6119535 baseEnd_6119535 := by
    simpa [prefixWord, tailWord_6119535, baseEnd_6119535] using wordTrace_append hprefix tailTrace_6119535
  have hstable : (prefixWord ++ tailWord_6119535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119535).length < 2 ^ (prefixWord ++ tailWord_6119535).sum := by decide
  have hdescent : baseEnd_6119535 < baseStart_6119535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119548 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_6119548 : Nat := 118140960795 + 6119548 * 2 ^ 59
def prefixEnd_6119548 : Nat := 4983230072969 + 3 ^ 40 * 6119548 * 2
def baseEnd_6119548 : Nat := 3142269512260328474006717

theorem tailTrace_6119548 : CollatzResearch.WordTrace tailWord_6119548 prefixEnd_6119548 3142269512260328474006717 := by
  unfold tailWord_6119548
  simp only [CollatzResearch.WordTrace]
  refine ⟨111599126016965103218007649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148798834689286804290676865 111599126016965103218007649)
  ·
    refine ⟨83699344512723827413505737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111599126016965103218007649 83699344512723827413505737)
    ·
      refine ⟨62774508384542870560129303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83699344512723827413505737 62774508384542870560129303)
      ·
        refine ⟨94161762576814305840193955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62774508384542870560129303 94161762576814305840193955)
        ·
          refine ⟨141242643865221458760290933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94161762576814305840193955 141242643865221458760290933)
          ·
            refine ⟨13241497862364511758777275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141242643865221458760290933 13241497862364511758777275)
            ·
              refine ⟨19862246793546767638165913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13241497862364511758777275 19862246793546767638165913)
              ·
                refine ⟨14896685095160075728624435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19862246793546767638165913 14896685095160075728624435)
                ·
                  refine ⟨22345027642740113592936653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896685095160075728624435 22345027642740113592936653)
                  ·
                    refine ⟨8379385366027542597351245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22345027642740113592936653 8379385366027542597351245)
                    ·
                      refine ⟨3142269512260328474006717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379385366027542597351245 3142269512260328474006717)
                      ·
                        rfl

theorem cell23_6119548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_6119548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119548 prefixEnd_6119548 := by exact prefixLift 6119548
  have htrace : WordTrace (prefixWord ++ tailWord_6119548) baseStart_6119548 baseEnd_6119548 := by
    simpa [prefixWord, tailWord_6119548, baseEnd_6119548] using wordTrace_append hprefix tailTrace_6119548
  have hstable : (prefixWord ++ tailWord_6119548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119548).length < 2 ^ (prefixWord ++ tailWord_6119548).sum := by decide
  have hdescent : baseEnd_6119548 < baseStart_6119548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119572 : List Nat := [2, 4, 2, 3, 2, 1, 1, 8]
def baseStart_6119572 : Nat := 118140960795 + 6119572 * 2 ^ 59
def prefixEnd_6119572 : Nat := 4983230072969 + 3 ^ 40 * 6119572 * 2
def baseEnd_6119572 : Nat := 116380808733186532596541

theorem tailTrace_6119572 : CollatzResearch.WordTrace tailWord_6119572 prefixEnd_6119572 116380808733186532596541 := by
  unfold tailWord_6119572
  simp only [CollatzResearch.WordTrace]
  refine ⟨111599563692921629267444485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148799418257228839023259313 111599563692921629267444485)
  ·
    refine ⟨20924918192422805487645841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111599563692921629267444485 20924918192422805487645841)
    ·
      refine ⟨15693688644317104115734381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20924918192422805487645841 15693688644317104115734381)
      ·
        refine ⟨5885133241618914043400393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15693688644317104115734381 5885133241618914043400393)
        ·
          refine ⟨4413849931214185532550295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885133241618914043400393 4413849931214185532550295)
          ·
            refine ⟨6620774896821278298825443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413849931214185532550295 6620774896821278298825443)
            ·
              refine ⟨9931162345231917448238165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620774896821278298825443 9931162345231917448238165)
              ·
                refine ⟨116380808733186532596541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9931162345231917448238165 116380808733186532596541)
                ·
                  rfl

theorem cell23_6119572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 8].length) (baseStart_6119572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119572 prefixEnd_6119572 := by exact prefixLift 6119572
  have htrace : WordTrace (prefixWord ++ tailWord_6119572) baseStart_6119572 baseEnd_6119572 := by
    simpa [prefixWord, tailWord_6119572, baseEnd_6119572] using wordTrace_append hprefix tailTrace_6119572
  have hstable : (prefixWord ++ tailWord_6119572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119572).length < 2 ^ (prefixWord ++ tailWord_6119572).sum := by decide
  have hdescent : baseEnd_6119572 < baseStart_6119572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119581 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_6119581 : Nat := 118140960795 + 6119581 * 2 ^ 59
def prefixEnd_6119581 : Nat := 4983230072969 + 3 ^ 40 * 6119581 * 2
def baseEnd_6119581 : Nat := 1047428819040642281631355

theorem tailTrace_6119581 : CollatzResearch.WordTrace tailWord_6119581 prefixEnd_6119581 1047428819040642281631355 := by
  unfold tailWord_6119581
  simp only [CollatzResearch.WordTrace]
  refine ⟨223199455642810653071966597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148799637095207102047977731 223199455642810653071966597)
  ·
    refine ⟨41849897933026997450993737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223199455642810653071966597 41849897933026997450993737)
    ·
      refine ⟨31387423449770248088245303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41849897933026997450993737 31387423449770248088245303)
      ·
        refine ⟨47081135174655372132367955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31387423449770248088245303 47081135174655372132367955)
        ·
          refine ⟨70621702761983058198551933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47081135174655372132367955 70621702761983058198551933)
          ·
            refine ⟨26483138535743646824456975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70621702761983058198551933 26483138535743646824456975)
            ·
              refine ⟨39724707803615470236685463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26483138535743646824456975 39724707803615470236685463)
              ·
                refine ⟨59587061705423205355028195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39724707803615470236685463 59587061705423205355028195)
                ·
                  refine ⟨89380592558134808032542293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59587061705423205355028195 89380592558134808032542293)
                  ·
                    refine ⟨1047428819040642281631355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89380592558134808032542293 1047428819040642281631355)
                    ·
                      rfl

theorem cell23_6119581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_6119581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119581 prefixEnd_6119581 := by exact prefixLift 6119581
  have htrace : WordTrace (prefixWord ++ tailWord_6119581) baseStart_6119581 baseEnd_6119581 := by
    simpa [prefixWord, tailWord_6119581, baseEnd_6119581] using wordTrace_append hprefix tailTrace_6119581
  have hstable : (prefixWord ++ tailWord_6119581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119581).length < 2 ^ (prefixWord ++ tailWord_6119581).sum := by decide
  have hdescent : baseEnd_6119581 < baseStart_6119581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119582 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6119582 : Nat := 118140960795 + 6119582 * 2 ^ 59
def prefixEnd_6119582 : Nat := 4983230072969 + 3 ^ 40 * 6119582 * 2
def baseEnd_6119582 : Nat := 3142286970602581340981561

theorem tailTrace_6119582 : CollatzResearch.WordTrace tailWord_6119582 prefixEnd_6119582 3142286970602581340981561 := by
  unfold tailWord_6119582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27899936514475878780344125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148799661410538020161835333 27899936514475878780344125)
  ·
    refine ⟨10462476192928454542629047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27899936514475878780344125 10462476192928454542629047)
    ·
      refine ⟨15693714289392681813943571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462476192928454542629047 15693714289392681813943571)
      ·
        refine ⟨23540571434089022720915357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693714289392681813943571 23540571434089022720915357)
        ·
          refine ⟨8827714287783383520343259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23540571434089022720915357 8827714287783383520343259)
          ·
            refine ⟨13241571431675075280514889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827714287783383520343259 13241571431675075280514889)
            ·
              refine ⟨9931178573756306460386167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13241571431675075280514889 9931178573756306460386167)
              ·
                refine ⟨14896767860634459690579251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931178573756306460386167 14896767860634459690579251)
                ·
                  refine ⟨22345151790951689535868877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896767860634459690579251 22345151790951689535868877)
                  ·
                    refine ⟨8379431921606883575950829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22345151790951689535868877 8379431921606883575950829)
                    ·
                      refine ⟨3142286970602581340981561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379431921606883575950829 3142286970602581340981561)
                      ·
                        rfl

theorem cell23_6119582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6119582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119582 prefixEnd_6119582 := by exact prefixLift 6119582
  have htrace : WordTrace (prefixWord ++ tailWord_6119582) baseStart_6119582 baseEnd_6119582 := by
    simpa [prefixWord, tailWord_6119582, baseEnd_6119582] using wordTrace_append hprefix tailTrace_6119582
  have hstable : (prefixWord ++ tailWord_6119582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119582).length < 2 ^ (prefixWord ++ tailWord_6119582).sum := by decide
  have hdescent : baseEnd_6119582 < baseStart_6119582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119641 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_6119641 : Nat := 118140960795 + 6119641 * 2 ^ 59
def prefixEnd_6119641 : Nat := 4983230072969 + 3 ^ 40 * 6119641 * 2
def baseEnd_6119641 : Nat := 1047439088653732203381263

theorem tailTrace_6119641 : CollatzResearch.WordTrace tailWord_6119641 prefixEnd_6119641 1047439088653732203381263 := by
  unfold tailWord_6119641
  simp only [CollatzResearch.WordTrace]
  refine ⟨223201644022593283319150777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148801096015062188879433851 223201644022593283319150777)
  ·
    refine ⟨167401233016944962489363083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223201644022593283319150777 167401233016944962489363083)
    ·
      refine ⟨251101849525417443734044625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167401233016944962489363083 251101849525417443734044625)
      ·
        refine ⟨188326387144063082800533469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251101849525417443734044625 188326387144063082800533469)
        ·
          refine ⟨70622395179023656050200051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188326387144063082800533469 70622395179023656050200051)
          ·
            refine ⟨105933592768535484075300077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70622395179023656050200051 105933592768535484075300077)
            ·
              refine ⟨39725097288200806528237529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105933592768535484075300077 39725097288200806528237529)
              ·
                refine ⟨29793822966150604896178147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39725097288200806528237529 29793822966150604896178147)
                ·
                  refine ⟨44690734449225907344267221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29793822966150604896178147 44690734449225907344267221)
                  ·
                    refine ⟨1047439088653732203381263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44690734449225907344267221 1047439088653732203381263)
                    ·
                      rfl

theorem cell23_6119641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_6119641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119641 prefixEnd_6119641 := by exact prefixLift 6119641
  have htrace : WordTrace (prefixWord ++ tailWord_6119641) baseStart_6119641 baseEnd_6119641 := by
    simpa [prefixWord, tailWord_6119641, baseEnd_6119641] using wordTrace_append hprefix tailTrace_6119641
  have hstable : (prefixWord ++ tailWord_6119641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119641).length < 2 ^ (prefixWord ++ tailWord_6119641).sum := by decide
  have hdescent : baseEnd_6119641 < baseStart_6119641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119658 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_6119658 : Nat := 118140960795 + 6119658 * 2 ^ 59
def prefixEnd_6119658 : Nat := 4983230072969 + 3 ^ 40 * 6119658 * 2
def baseEnd_6119658 : Nat := 1047441998377441014543737

theorem tailTrace_6119658 : CollatzResearch.WordTrace tailWord_6119658 prefixEnd_6119658 1047441998377441014543737 := by
  unfold tailWord_6119658
  simp only [CollatzResearch.WordTrace]
  refine ⟨55800566015882923805629907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148801509375687796815013085 55800566015882923805629907)
  ·
    refine ⟨83700849023824385708444861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55800566015882923805629907 83700849023824385708444861)
    ·
      refine ⟨31387818383934144640666823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83700849023824385708444861 31387818383934144640666823)
      ·
        refine ⟨47081727575901216961000235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31387818383934144640666823 47081727575901216961000235)
        ·
          refine ⟨70622591363851825441500353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47081727575901216961000235 70622591363851825441500353)
          ·
            refine ⟨52966943522888869081125265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70622591363851825441500353 52966943522888869081125265)
            ·
              refine ⟨39725207642166651810843949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52966943522888869081125265 39725207642166651810843949)
              ·
                refine ⟨14896952865812494429066481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39725207642166651810843949 14896952865812494429066481)
                ·
                  refine ⟨11172714649359370821799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14896952865812494429066481 11172714649359370821799861)
                  ·
                    refine ⟨1047441998377441014543737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11172714649359370821799861 1047441998377441014543737)
                    ·
                      rfl

theorem cell23_6119658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_6119658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119658 prefixEnd_6119658 := by exact prefixLift 6119658
  have htrace : WordTrace (prefixWord ++ tailWord_6119658) baseStart_6119658 baseEnd_6119658 := by
    simpa [prefixWord, tailWord_6119658, baseEnd_6119658] using wordTrace_append hprefix tailTrace_6119658
  have hstable : (prefixWord ++ tailWord_6119658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119658).length < 2 ^ (prefixWord ++ tailWord_6119658).sum := by decide
  have hdescent : baseEnd_6119658 < baseStart_6119658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119715 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3]
def baseStart_6119715 : Nat := 118140960795 + 6119715 * 2 ^ 59
def prefixEnd_6119715 : Nat := 4983230072969 + 3 ^ 40 * 6119715 * 2
def baseEnd_6119715 : Nat := 3142355263529629320618449

theorem tailTrace_6119715 : CollatzResearch.WordTrace tailWord_6119715 prefixEnd_6119715 3142355263529629320618449 := by
  unfold tailWord_6119715
  simp only [CollatzResearch.WordTrace]
  refine ⟨223204343024325193957344599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148802895349550129304896399 223204343024325193957344599)
  ·
    refine ⟨334806514536487790936016899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223204343024325193957344599 334806514536487790936016899)
    ·
      refine ⟨502209771804731686404025349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334806514536487790936016899 502209771804731686404025349)
      ·
        refine ⟨94164332213387191200754753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502209771804731686404025349 94164332213387191200754753)
        ·
          refine ⟨70623249160040393400566065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94164332213387191200754753 70623249160040393400566065)
          ·
            refine ⟨52967436870030295050424549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70623249160040393400566065 52967436870030295050424549)
            ·
              refine ⟨9931394413130680321954603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52967436870030295050424549 9931394413130680321954603)
              ·
                refine ⟨14897091619696020482931905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931394413130680321954603 14897091619696020482931905)
                ·
                  refine ⟨11172818714772015362198929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14897091619696020482931905 11172818714772015362198929)
                  ·
                    refine ⟨8379614036079011521649197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11172818714772015362198929 8379614036079011521649197)
                    ·
                      refine ⟨3142355263529629320618449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379614036079011521649197 3142355263529629320618449)
                      ·
                        rfl

theorem cell23_6119715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_6119715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119715 prefixEnd_6119715 := by exact prefixLift 6119715
  have htrace : WordTrace (prefixWord ++ tailWord_6119715) baseStart_6119715 baseEnd_6119715 := by
    simpa [prefixWord, tailWord_6119715, baseEnd_6119715] using wordTrace_append hprefix tailTrace_6119715
  have hstable : (prefixWord ++ tailWord_6119715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119715).length < 2 ^ (prefixWord ++ tailWord_6119715).sum := by decide
  have hdescent : baseEnd_6119715 < baseStart_6119715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119732 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6119732 : Nat := 118140960795 + 6119732 * 2 ^ 59
def prefixEnd_6119732 : Nat := 4983230072969 + 3 ^ 40 * 6119732 * 2
def baseEnd_6119732 : Nat := 3142363992700755754105871

theorem tailTrace_6119732 : CollatzResearch.WordTrace tailWord_6119732 prefixEnd_6119732 3142363992700755754105871 := by
  unfold tailWord_6119732
  simp only [CollatzResearch.WordTrace]
  refine ⟨111602481532631802930356725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148803308710175737240475633 111602481532631802930356725)
  ·
    refine ⟨10462732643684231524720943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111602481532631802930356725 10462732643684231524720943)
    ·
      refine ⟨15694098965526347287081415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462732643684231524720943 15694098965526347287081415)
      ·
        refine ⟨23541148448289520930622123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15694098965526347287081415 23541148448289520930622123)
        ·
          refine ⟨35311722672434281395933185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23541148448289520930622123 35311722672434281395933185)
          ·
            refine ⟨26483792004325711046949889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35311722672434281395933185 26483792004325711046949889)
            ·
              refine ⟨19862844003244283285212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26483792004325711046949889 19862844003244283285212417)
              ·
                refine ⟨14897133002433212463909313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19862844003244283285212417 14897133002433212463909313)
                ·
                  refine ⟨11172849751824909347931985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14897133002433212463909313 11172849751824909347931985)
                  ·
                    refine ⟨8379637313868682010948989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11172849751824909347931985 8379637313868682010948989)
                    ·
                      refine ⟨3142363992700755754105871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379637313868682010948989 3142363992700755754105871)
                      ·
                        rfl

theorem cell23_6119732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6119732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119732 prefixEnd_6119732 := by exact prefixLift 6119732
  have htrace : WordTrace (prefixWord ++ tailWord_6119732) baseStart_6119732 baseEnd_6119732 := by
    simpa [prefixWord, tailWord_6119732, baseEnd_6119732] using wordTrace_append hprefix tailTrace_6119732
  have hstable : (prefixWord ++ tailWord_6119732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119732).length < 2 ^ (prefixWord ++ tailWord_6119732).sum := by decide
  have hdescent : baseEnd_6119732 < baseStart_6119732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119779 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 1, 1, 3]
def baseStart_6119779 : Nat := 118140960795 + 6119779 * 2 ^ 59
def prefixEnd_6119779 : Nat := 4983230072969 + 3 ^ 40 * 6119779 * 2
def baseEnd_6119779 : Nat := 3142388126291517070218155

theorem tailTrace_6119779 : CollatzResearch.WordTrace tailWord_6119779 prefixEnd_6119779 3142388126291517070218155 := by
  unfold tailWord_6119779
  simp only [CollatzResearch.WordTrace]
  refine ⟨223206677296093332887674391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148804451530728888591782927 223206677296093332887674391)
  ·
    refine ⟨334810015944139999331511587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223206677296093332887674391 334810015944139999331511587)
    ·
      refine ⟨502215023916209998997267381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334810015944139999331511587 502215023916209998997267381)
      ·
        refine ⟨47082658492144687405993817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 502215023916209998997267381 47082658492144687405993817)
        ·
          refine ⟨35311993869108515554495363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47082658492144687405993817 35311993869108515554495363)
          ·
            refine ⟨52967990803662773331743045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35311993869108515554495363 52967990803662773331743045)
            ·
              refine ⟨9931498275686769999701821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52967990803662773331743045 9931498275686769999701821)
              ·
                refine ⟨3724311853382538749888183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9931498275686769999701821 3724311853382538749888183)
                ·
                  refine ⟨5586467780073808124832275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724311853382538749888183 5586467780073808124832275)
                  ·
                    refine ⟨8379701670110712187248413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5586467780073808124832275 8379701670110712187248413)
                    ·
                      refine ⟨3142388126291517070218155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379701670110712187248413 3142388126291517070218155)
                      ·
                        rfl

theorem cell23_6119779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_6119779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119779 prefixEnd_6119779 := by exact prefixLift 6119779
  have htrace : WordTrace (prefixWord ++ tailWord_6119779) baseStart_6119779 baseEnd_6119779 := by
    simpa [prefixWord, tailWord_6119779, baseEnd_6119779] using wordTrace_append hprefix tailTrace_6119779
  have hstable : (prefixWord ++ tailWord_6119779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119779).length < 2 ^ (prefixWord ++ tailWord_6119779).sum := by decide
  have hdescent : baseEnd_6119779 < baseStart_6119779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119785 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_6119785 : Nat := 118140960795 + 6119785 * 2 ^ 59
def prefixEnd_6119785 : Nat := 4983230072969 + 3 ^ 40 * 6119785 * 2
def baseEnd_6119785 : Nat := 3142391207175444046743127

theorem tailTrace_6119785 : CollatzResearch.WordTrace tailWord_6119785 prefixEnd_6119785 3142391207175444046743127 := by
  unfold tailWord_6119785
  simp only [CollatzResearch.WordTrace]
  refine ⟨223206896134071595912392809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148804597422714397274928539 223206896134071595912392809)
  ·
    refine ⟨167405172100553696934294607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223206896134071595912392809 167405172100553696934294607)
    ·
      refine ⟨251107758150830545401441911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167405172100553696934294607 251107758150830545401441911)
      ·
        refine ⟨376661637226245818102162867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251107758150830545401441911 376661637226245818102162867)
        ·
          refine ⟨564992455839368727153244301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376661637226245818102162867 564992455839368727153244301)
          ·
            refine ⟨211872170939763272682466613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564992455839368727153244301 211872170939763272682466613)
            ·
              refine ⟨19863016025602806813981245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211872170939763272682466613 19863016025602806813981245)
              ·
                refine ⟨7448631009601052555242967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19863016025602806813981245 7448631009601052555242967)
                ·
                  refine ⟨11172946514401578832864451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7448631009601052555242967 11172946514401578832864451)
                  ·
                    refine ⟨16759419771602368249296677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11172946514401578832864451 16759419771602368249296677)
                    ·
                      refine ⟨3142391207175444046743127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16759419771602368249296677 3142391207175444046743127)
                      ·
                        rfl

theorem cell23_6119785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_6119785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119785 prefixEnd_6119785 := by exact prefixLift 6119785
  have htrace : WordTrace (prefixWord ++ tailWord_6119785) baseStart_6119785 baseEnd_6119785 := by
    simpa [prefixWord, tailWord_6119785, baseEnd_6119785] using wordTrace_append hprefix tailTrace_6119785
  have hstable : (prefixWord ++ tailWord_6119785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119785).length < 2 ^ (prefixWord ++ tailWord_6119785).sum := by decide
  have hdescent : baseEnd_6119785 < baseStart_6119785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119805 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_6119805 : Nat := 118140960795 + 6119805 * 2 ^ 59
def prefixEnd_6119805 : Nat := 4983230072969 + 3 ^ 40 * 6119805 * 2
def baseEnd_6119805 : Nat := 3142401476788533968493035

theorem tailTrace_6119805 : CollatzResearch.WordTrace tailWord_6119805 prefixEnd_6119805 3142401476788533968493035 := by
  unfold tailWord_6119805
  simp only [CollatzResearch.WordTrace]
  refine ⟨223207625593999139328120869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148805083729332759552080579 223207625593999139328120869)
  ·
    refine ⟨41851429798874838624022663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223207625593999139328120869 41851429798874838624022663)
    ·
      refine ⟨62777144698312257936033995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41851429798874838624022663 62777144698312257936033995)
      ·
        refine ⟨94165717047468386904050993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62777144698312257936033995 94165717047468386904050993)
        ·
          refine ⟨70624287785601290178038245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94165717047468386904050993 70624287785601290178038245)
          ·
            refine ⟨13242053959800241908382171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70624287785601290178038245 13242053959800241908382171)
            ·
              refine ⟨19863080939700362862573257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13242053959800241908382171 19863080939700362862573257)
              ·
                refine ⟨14897310704775272146929943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19863080939700362862573257 14897310704775272146929943)
                ·
                  refine ⟨22345966057162908220394915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14897310704775272146929943 22345966057162908220394915)
                  ·
                    refine ⟨33518949085744362330592373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22345966057162908220394915 33518949085744362330592373)
                    ·
                      refine ⟨3142401476788533968493035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33518949085744362330592373 3142401476788533968493035)
                      ·
                        rfl

theorem cell23_6119805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_6119805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119805 prefixEnd_6119805 := by exact prefixLift 6119805
  have htrace : WordTrace (prefixWord ++ tailWord_6119805) baseStart_6119805 baseEnd_6119805 := by
    simpa [prefixWord, tailWord_6119805, baseEnd_6119805] using wordTrace_append hprefix tailTrace_6119805
  have hstable : (prefixWord ++ tailWord_6119805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119805).length < 2 ^ (prefixWord ++ tailWord_6119805).sum := by decide
  have hdescent : baseEnd_6119805 < baseStart_6119805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119852 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_6119852 : Nat := 118140960795 + 6119852 * 2 ^ 59
def prefixEnd_6119852 : Nat := 4983230072969 + 3 ^ 40 * 6119852 * 2
def baseEnd_6119852 : Nat := 3142425610379295284605319

theorem tailTrace_6119852 : CollatzResearch.WordTrace tailWord_6119852 prefixEnd_6119852 3142425610379295284605319 := by
  unfold tailWord_6119852
  simp only [CollatzResearch.WordTrace]
  refine ⟨111604669912414433177540905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148806226549885910903387873 111604669912414433177540905)
  ·
    refine ⟨83703502434310824883155679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111604669912414433177540905 83703502434310824883155679)
    ·
      refine ⟨125555253651466237324733519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83703502434310824883155679 125555253651466237324733519)
      ·
        refine ⟨188332880477199355987100279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125555253651466237324733519 188332880477199355987100279)
        ·
          refine ⟨282499320715799033980650419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188332880477199355987100279 282499320715799033980650419)
          ·
            refine ⟨423748981073698550970975629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282499320715799033980650419 423748981073698550970975629)
            ·
              refine ⟨158905867902636956614115861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423748981073698550970975629 158905867902636956614115861)
              ·
                refine ⟨7448712557936107341286681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158905867902636956614115861 7448712557936107341286681)
                ·
                  refine ⟨5586534418452080505965011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448712557936107341286681 5586534418452080505965011)
                  ·
                    refine ⟨8379801627678120758947517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5586534418452080505965011 8379801627678120758947517)
                    ·
                      refine ⟨3142425610379295284605319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379801627678120758947517 3142425610379295284605319)
                      ·
                        rfl

theorem cell23_6119852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_6119852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119852 prefixEnd_6119852 := by exact prefixLift 6119852
  have htrace : WordTrace (prefixWord ++ tailWord_6119852) baseStart_6119852 baseEnd_6119852 := by
    simpa [prefixWord, tailWord_6119852, baseEnd_6119852] using wordTrace_append hprefix tailTrace_6119852
  have hstable : (prefixWord ++ tailWord_6119852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119852).length < 2 ^ (prefixWord ++ tailWord_6119852).sum := by decide
  have hdescent : baseEnd_6119852 < baseStart_6119852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119853 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6119853 : Nat := 118140960795 + 6119853 * 2 ^ 59
def prefixEnd_6119853 : Nat := 4983230072969 + 3 ^ 40 * 6119853 * 2
def baseEnd_6119853 : Nat := 3142426123859949780692815

theorem tailTrace_6119853 : CollatzResearch.WordTrace tailWord_6119853 prefixEnd_6119853 3142426123859949780692815 := by
  unfold tailWord_6119853
  simp only [CollatzResearch.WordTrace]
  refine ⟨223209376297825243525868213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148806250865216829017245475 223209376297825243525868213)
  ·
    refine ⟨20925879027921116580550145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223209376297825243525868213 20925879027921116580550145)
    ·
      refine ⟨15694409270940837435412609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20925879027921116580550145 15694409270940837435412609)
      ·
        refine ⟨11770806953205628076559457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15694409270940837435412609 11770806953205628076559457)
        ·
          refine ⟨8828105214904221057419593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11770806953205628076559457 8828105214904221057419593)
          ·
            refine ⟨6621078911178165793064695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828105214904221057419593 6621078911178165793064695)
            ·
              refine ⟨9931618366767248689597043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621078911178165793064695 9931618366767248689597043)
              ·
                refine ⟨14897427550150873034395565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931618366767248689597043 14897427550150873034395565)
                ·
                  refine ⟨5586535331306577387898337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14897427550150873034395565 5586535331306577387898337)
                  ·
                    refine ⟨4189901498479933040923753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586535331306577387898337 4189901498479933040923753)
                    ·
                      refine ⟨3142426123859949780692815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189901498479933040923753 3142426123859949780692815)
                      ·
                        rfl

theorem cell23_6119853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6119853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119853 prefixEnd_6119853 := by exact prefixLift 6119853
  have htrace : WordTrace (prefixWord ++ tailWord_6119853) baseStart_6119853 baseEnd_6119853 := by
    simpa [prefixWord, tailWord_6119853, baseEnd_6119853] using wordTrace_append hprefix tailTrace_6119853
  have hstable : (prefixWord ++ tailWord_6119853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119853).length < 2 ^ (prefixWord ++ tailWord_6119853).sum := by decide
  have hdescent : baseEnd_6119853 < baseStart_6119853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119869 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_6119869 : Nat := 118140960795 + 6119869 * 2 ^ 59
def prefixEnd_6119869 : Nat := 4983230072969 + 3 ^ 40 * 6119869 * 2
def baseEnd_6119869 : Nat := 3142434339550421718092741

theorem tailTrace_6119869 : CollatzResearch.WordTrace tailWord_6119869 prefixEnd_6119869 3142434339550421718092741 := by
  unfold tailWord_6119869
  simp only [CollatzResearch.WordTrace]
  refine ⟨223209959865767278258450661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148806639910511518838967107 223209959865767278258450661)
  ·
    refine ⟨41851867474831364673459499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223209959865767278258450661 41851867474831364673459499)
    ·
      refine ⟨62777801212247047010189249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41851867474831364673459499 62777801212247047010189249)
      ·
        refine ⟨47083350909185285257641937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62777801212247047010189249 47083350909185285257641937)
        ·
          refine ⟨35312513181888963943231453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47083350909185285257641937 35312513181888963943231453)
          ·
            refine ⟨13242192443208361478711795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35312513181888963943231453 13242192443208361478711795)
            ·
              refine ⟨19863288664812542218067693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13242192443208361478711795 19863288664812542218067693)
              ·
                refine ⟨7448733249304703331775385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19863288664812542218067693 7448733249304703331775385)
                ·
                  refine ⟨5586549936978527498831539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448733249304703331775385 5586549936978527498831539)
                  ·
                    refine ⟨8379824905467791248247309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5586549936978527498831539 8379824905467791248247309)
                    ·
                      refine ⟨3142434339550421718092741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8379824905467791248247309 3142434339550421718092741)
                      ·
                        rfl

theorem cell23_6119869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_6119869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119869 prefixEnd_6119869 := by exact prefixLift 6119869
  have htrace : WordTrace (prefixWord ++ tailWord_6119869) baseStart_6119869 baseEnd_6119869 := by
    simpa [prefixWord, tailWord_6119869, baseEnd_6119869] using wordTrace_append hprefix tailTrace_6119869
  have hstable : (prefixWord ++ tailWord_6119869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119869).length < 2 ^ (prefixWord ++ tailWord_6119869).sum := by decide
  have hdescent : baseEnd_6119869 < baseStart_6119869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119879 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_6119879 : Nat := 118140960795 + 6119879 * 2 ^ 59
def prefixEnd_6119879 : Nat := 4983230072969 + 3 ^ 40 * 6119879 * 2
def baseEnd_6119879 : Nat := 3142439474356966678967695

theorem tailTrace_6119879 : CollatzResearch.WordTrace tailWord_6119879 prefixEnd_6119879 3142439474356966678967695 := by
  unfold tailWord_6119879
  simp only [CollatzResearch.WordTrace]
  refine ⟨223210324595731049966314691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148806883063820699977543127 223210324595731049966314691)
  ·
    refine ⟨334815486893596574949472037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223210324595731049966314691 334815486893596574949472037)
    ·
      refine ⟨62777903792549357803026007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334815486893596574949472037 62777903792549357803026007)
      ·
        refine ⟨94166855688824036704539011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62777903792549357803026007 94166855688824036704539011)
        ·
          refine ⟨141250283533236055056808517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94166855688824036704539011 141250283533236055056808517)
          ·
            refine ⟨26484428162481760323151597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141250283533236055056808517 26484428162481760323151597)
            ·
              refine ⟨9931660560930660121181849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26484428162481760323151597 9931660560930660121181849)
              ·
                refine ⟨7448745420697995090886387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9931660560930660121181849 7448745420697995090886387)
                ·
                  refine ⟨11173118131046992636329581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7448745420697995090886387 11173118131046992636329581)
                  ·
                    refine ⟨4189919299142622238623593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11173118131046992636329581 4189919299142622238623593)
                    ·
                      refine ⟨3142439474356966678967695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189919299142622238623593 3142439474356966678967695)
                      ·
                        rfl

theorem cell23_6119879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_6119879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119879 prefixEnd_6119879 := by exact prefixLift 6119879
  have htrace : WordTrace (prefixWord ++ tailWord_6119879) baseStart_6119879 baseEnd_6119879 := by
    simpa [prefixWord, tailWord_6119879, baseEnd_6119879] using wordTrace_append hprefix tailTrace_6119879
  have hstable : (prefixWord ++ tailWord_6119879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119879).length < 2 ^ (prefixWord ++ tailWord_6119879).sum := by decide
  have hdescent : baseEnd_6119879 < baseStart_6119879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119905 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6119905 : Nat := 118140960795 + 6119905 * 2 ^ 59
def prefixEnd_6119905 : Nat := 4983230072969 + 3 ^ 40 * 6119905 * 2
def baseEnd_6119905 : Nat := 3142452824853983577242575

theorem tailTrace_6119905 : CollatzResearch.WordTrace tailWord_6119905 prefixEnd_6119905 3142452824853983577242575 := by
  unfold tailWord_6119905
  simp only [CollatzResearch.WordTrace]
  refine ⟨223211272893636856406761169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148807515262424570937840779 223211272893636856406761169)
  ·
    refine ⟨167408454670227642305070877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223211272893636856406761169 167408454670227642305070877)
    ·
      refine ⟨62778170501335365864401579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167408454670227642305070877 62778170501335365864401579)
      ·
        refine ⟨94167255752003048796602369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62778170501335365864401579 94167255752003048796602369)
        ·
          refine ⟨70625441814002286597451777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94167255752003048796602369 70625441814002286597451777)
          ·
            refine ⟨52969081360501714948088833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70625441814002286597451777 52969081360501714948088833)
            ·
              refine ⟨39726811020376286211066625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52969081360501714948088833 39726811020376286211066625)
              ·
                refine ⟨29795108265282214658299969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39726811020376286211066625 29795108265282214658299969)
                ·
                  refine ⟨22346331198961660993724977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29795108265282214658299969 22346331198961660993724977)
                  ·
                    refine ⟨16759748399221245745293733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22346331198961660993724977 16759748399221245745293733)
                    ·
                      refine ⟨3142452824853983577242575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16759748399221245745293733 3142452824853983577242575)
                      ·
                        rfl

theorem cell23_6119905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6119905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119905 prefixEnd_6119905 := by exact prefixLift 6119905
  have htrace : WordTrace (prefixWord ++ tailWord_6119905) baseStart_6119905 baseEnd_6119905 := by
    simpa [prefixWord, tailWord_6119905, baseEnd_6119905] using wordTrace_append hprefix tailTrace_6119905
  have hstable : (prefixWord ++ tailWord_6119905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119905).length < 2 ^ (prefixWord ++ tailWord_6119905).sum := by decide
  have hdescent : baseEnd_6119905 < baseStart_6119905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119926 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6119926 : Nat := 118140960795 + 6119926 * 2 ^ 59
def prefixEnd_6119926 : Nat := 4983230072969 + 3 ^ 40 * 6119926 * 2
def baseEnd_6119926 : Nat := 3142463607947727995079979

theorem tailTrace_6119926 : CollatzResearch.WordTrace tailWord_6119926 prefixEnd_6119926 3142463607947727995079979 := by
  unfold tailWord_6119926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950752426660048562079727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148808025884373851328850421 13950752426660048562079727)
  ·
    refine ⟨20926128639990072843119591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13950752426660048562079727 20926128639990072843119591)
    ·
      refine ⟨31389192959985109264679387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20926128639990072843119591 31389192959985109264679387)
      ·
        refine ⟨47083789439977663897019081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31389192959985109264679387 47083789439977663897019081)
        ·
          refine ⟨35312842079983247922764311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47083789439977663897019081 35312842079983247922764311)
          ·
            refine ⟨52969263119974871884146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35312842079983247922764311 52969263119974871884146467)
            ·
              refine ⟨79453894679962307826219701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52969263119974871884146467 79453894679962307826219701)
              ·
                refine ⟨7448802626246466358708097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79453894679962307826219701 7448802626246466358708097)
                ·
                  refine ⟨5586601969684849769031073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448802626246466358708097 5586601969684849769031073)
                  ·
                    refine ⟨4189951477263637326773305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586601969684849769031073 4189951477263637326773305)
                    ·
                      refine ⟨3142463607947727995079979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4189951477263637326773305 3142463607947727995079979)
                      ·
                        rfl

theorem cell23_6119926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6119926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119926 prefixEnd_6119926 := by exact prefixLift 6119926
  have htrace : WordTrace (prefixWord ++ tailWord_6119926) baseStart_6119926 baseEnd_6119926 := by
    simpa [prefixWord, tailWord_6119926, baseEnd_6119926] using wordTrace_append hprefix tailTrace_6119926
  have hstable : (prefixWord ++ tailWord_6119926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119926).length < 2 ^ (prefixWord ++ tailWord_6119926).sum := by decide
  have hdescent : baseEnd_6119926 < baseStart_6119926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119945 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_6119945 : Nat := 118140960795 + 6119945 * 2 ^ 59
def prefixEnd_6119945 : Nat := 4983230072969 + 3 ^ 40 * 6119945 * 2
def baseEnd_6119945 : Nat := 1047491121360054473580797

theorem tailTrace_6119945 : CollatzResearch.WordTrace tailWord_6119945 prefixEnd_6119945 1047491121360054473580797 := by
  unfold tailWord_6119945
  simp only [CollatzResearch.WordTrace]
  refine ⟨223212731813491943238217289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148808487875661295492144859 223212731813491943238217289)
  ·
    refine ⟨167409548860118957428662967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223212731813491943238217289 167409548860118957428662967)
    ·
      refine ⟨251114323290178436142994451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167409548860118957428662967 251114323290178436142994451)
      ·
        refine ⟨376671484935267654214491677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251114323290178436142994451 376671484935267654214491677)
        ·
          refine ⟨141251806850725370330434379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376671484935267654214491677 141251806850725370330434379)
          ·
            refine ⟨211877710276088055495651569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141251806850725370330434379 211877710276088055495651569)
            ·
              refine ⟨158908282707066041621738677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211877710276088055495651569 158908282707066041621738677)
              ·
                refine ⟨14897651503787441402038001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158908282707066041621738677 14897651503787441402038001)
                ·
                  refine ⟨11173238627840581051528501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14897651503787441402038001 11173238627840581051528501)
                  ·
                    refine ⟨1047491121360054473580797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11173238627840581051528501 1047491121360054473580797)
                    ·
                      rfl

theorem cell23_6119945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_6119945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119945 prefixEnd_6119945 := by exact prefixLift 6119945
  have htrace : WordTrace (prefixWord ++ tailWord_6119945) baseStart_6119945 baseEnd_6119945 := by
    simpa [prefixWord, tailWord_6119945, baseEnd_6119945] using wordTrace_append hprefix tailTrace_6119945
  have hstable : (prefixWord ++ tailWord_6119945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119945).length < 2 ^ (prefixWord ++ tailWord_6119945).sum := by decide
  have hdescent : baseEnd_6119945 < baseStart_6119945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6119992 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_6119992 : Nat := 118140960795 + 6119992 * 2 ^ 59
def prefixEnd_6119992 : Nat := 4983230072969 + 3 ^ 40 * 6119992 * 2
def baseEnd_6119992 : Nat := 1047499165890308245618225

theorem tailTrace_6119992 : CollatzResearch.WordTrace tailWord_6119992 prefixEnd_6119992 1047499165890308245618225 := by
  unfold tailWord_6119992
  simp only [CollatzResearch.WordTrace]
  refine ⟨111607223022160835132589115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148809630696214446843452153 111607223022160835132589115)
  ·
    refine ⟨167410834533241252698883673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111607223022160835132589115 167410834533241252698883673)
    ·
      refine ⟨125558125899930939524162755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167410834533241252698883673 125558125899930939524162755)
      ·
        refine ⟨188337188849896409286244133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125558125899930939524162755 188337188849896409286244133)
        ·
          refine ⟨35313222909355576741170775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188337188849896409286244133 35313222909355576741170775)
          ·
            refine ⟨52969834364033365111756163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35313222909355576741170775 52969834364033365111756163)
            ·
              refine ⟨79454751546050047667634245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52969834364033365111756163 79454751546050047667634245)
              ·
                refine ⟨14897765914884383937681421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79454751546050047667634245 14897765914884383937681421)
                ·
                  refine ⟨5586662218081643976630533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14897765914884383937681421 5586662218081643976630533)
                  ·
                    refine ⟨1047499165890308245618225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586662218081643976630533 1047499165890308245618225)
                    ·
                      rfl

theorem cell23_6119992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_6119992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6119992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6119992 prefixEnd_6119992 := by exact prefixLift 6119992
  have htrace : WordTrace (prefixWord ++ tailWord_6119992) baseStart_6119992 baseEnd_6119992 := by
    simpa [prefixWord, tailWord_6119992, baseEnd_6119992] using wordTrace_append hprefix tailTrace_6119992
  have hstable : (prefixWord ++ tailWord_6119992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6119992).length < 2 ^ (prefixWord ++ tailWord_6119992).sum := by decide
  have hdescent : baseEnd_6119992 < baseStart_6119992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6119992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120005 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 8]
def baseStart_6120005 : Nat := 118140960795 + 6120005 * 2 ^ 59
def prefixEnd_6120005 : Nat := 4983230072969 + 3 ^ 40 * 6120005 * 2
def baseEnd_6120005 : Nat := 349167130324381465110235

theorem tailTrace_6120005 : CollatzResearch.WordTrace tailWord_6120005 prefixEnd_6120005 349167130324381465110235 := by
  unfold tailWord_6120005
  simp only [CollatzResearch.WordTrace]
  refine ⟨223214920193274573485401469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148809946795516382323600979 223214920193274573485401469)
  ·
    refine ⟨83705595072477965057025551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223214920193274573485401469 83705595072477965057025551)
    ·
      refine ⟨125558392608716947585538327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83705595072477965057025551 125558392608716947585538327)
      ·
        refine ⟨188337588913075421378307491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125558392608716947585538327 188337588913075421378307491)
        ·
          refine ⟨282506383369613132067461237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188337588913075421378307491 282506383369613132067461237)
          ·
            refine ⟨26484973440901231131324491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282506383369613132067461237 26484973440901231131324491)
            ·
              refine ⟨39727460161351846696986737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26484973440901231131324491 39727460161351846696986737)
              ·
                refine ⟨29795595121013885022740053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39727460161351846696986737 29795595121013885022740053)
                ·
                  refine ⟨349167130324381465110235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29795595121013885022740053 349167130324381465110235)
                  ·
                    rfl

theorem cell23_6120005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_6120005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120005 prefixEnd_6120005 := by exact prefixLift 6120005
  have htrace : WordTrace (prefixWord ++ tailWord_6120005) baseStart_6120005 baseEnd_6120005 := by
    simpa [prefixWord, tailWord_6120005, baseEnd_6120005] using wordTrace_append hprefix tailTrace_6120005
  have hstable : (prefixWord ++ tailWord_6120005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120005).length < 2 ^ (prefixWord ++ tailWord_6120005).sum := by decide
  have hdescent : baseEnd_6120005 < baseStart_6120005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120110 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6120110 : Nat := 118140960795 + 6120110 * 2 ^ 59
def prefixEnd_6120110 : Nat := 4983230072969 + 3 ^ 40 * 6120110 * 2
def baseEnd_6120110 : Nat := 3142558088388155275179133

theorem tailTrace_6120110 : CollatzResearch.WordTrace tailWord_6120110 prefixEnd_6120110 3142558088388155275179133 := by
  unfold tailWord_6120110
  simp only [CollatzResearch.WordTrace]
  refine ⟨27902343732236772052246723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148812499905262784278649189 27902343732236772052246723)
  ·
    refine ⟨41853515598355158078370085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27902343732236772052246723 41853515598355158078370085)
    ·
      refine ⟨7847534174691592139694391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41853515598355158078370085 7847534174691592139694391)
      ·
        refine ⟨11771301262037388209541587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847534174691592139694391 11771301262037388209541587)
        ·
          refine ⟨17656951893056082314312381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771301262037388209541587 17656951893056082314312381)
          ·
            refine ⟨6621356959896030867867143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17656951893056082314312381 6621356959896030867867143)
            ·
              refine ⟨9932035439844046301800715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621356959896030867867143 9932035439844046301800715)
              ·
                refine ⟨14898053159766069452701073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932035439844046301800715 14898053159766069452701073)
                ·
                  refine ⟨11173539869824552089525805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14898053159766069452701073 11173539869824552089525805)
                  ·
                    refine ⟨4190077451184207033572177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11173539869824552089525805 4190077451184207033572177)
                    ·
                      refine ⟨3142558088388155275179133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190077451184207033572177 3142558088388155275179133)
                      ·
                        rfl

theorem cell23_6120110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6120110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120110 prefixEnd_6120110 := by exact prefixLift 6120110
  have htrace : WordTrace (prefixWord ++ tailWord_6120110) baseStart_6120110 baseEnd_6120110 := by
    simpa [prefixWord, tailWord_6120110, baseEnd_6120110] using wordTrace_append hprefix tailTrace_6120110
  have hstable : (prefixWord ++ tailWord_6120110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120110).length < 2 ^ (prefixWord ++ tailWord_6120110).sum := by decide
  have hdescent : baseEnd_6120110 < baseStart_6120110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120126 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_6120126 : Nat := 118140960795 + 6120126 * 2 ^ 59
def prefixEnd_6120126 : Nat := 4983230072969 + 3 ^ 40 * 6120126 * 2
def baseEnd_6120126 : Nat := 3142566304078627212579059

theorem tailTrace_6120126 : CollatzResearch.WordTrace tailWord_6120126 prefixEnd_6120126 3142566304078627212579059 := by
  unfold tailWord_6120126
  simp only [CollatzResearch.WordTrace]
  refine ⟨27902416678229526393819529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148812888950557474100370821 27902416678229526393819529)
  ·
    refine ⟨20926812508672144795364647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27902416678229526393819529 20926812508672144795364647)
    ·
      refine ⟨31390218763008217193046971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20926812508672144795364647 31390218763008217193046971)
      ·
        refine ⟨47085328144512325789570457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31390218763008217193046971 47085328144512325789570457)
        ·
          refine ⟨35313996108384244342177843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47085328144512325789570457 35313996108384244342177843)
          ·
            refine ⟨52970994162576366513266765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35313996108384244342177843 52970994162576366513266765)
            ·
              refine ⟨19864122810966137442475037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52970994162576366513266765 19864122810966137442475037)
              ·
                refine ⟨7449046054112301540928139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19864122810966137442475037 7449046054112301540928139)
                ·
                  refine ⟨11173569081168452311392209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449046054112301540928139 11173569081168452311392209)
                  ·
                    refine ⟨8380176810876339233544157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11173569081168452311392209 8380176810876339233544157)
                    ·
                      refine ⟨3142566304078627212579059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8380176810876339233544157 3142566304078627212579059)
                      ·
                        rfl

theorem cell23_6120126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_6120126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120126 prefixEnd_6120126 := by exact prefixLift 6120126
  have htrace : WordTrace (prefixWord ++ tailWord_6120126) baseStart_6120126 baseEnd_6120126 := by
    simpa [prefixWord, tailWord_6120126, baseEnd_6120126] using wordTrace_append hprefix tailTrace_6120126
  have hstable : (prefixWord ++ tailWord_6120126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120126).length < 2 ^ (prefixWord ++ tailWord_6120126).sum := by decide
  have hdescent : baseEnd_6120126 < baseStart_6120126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120140 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6120140 : Nat := 118140960795 + 6120140 * 2 ^ 59
def prefixEnd_6120140 : Nat := 4983230072969 + 3 ^ 40 * 6120140 * 2
def baseEnd_6120140 : Nat := 3142573492807790157803995

theorem tailTrace_6120140 : CollatzResearch.WordTrace tailWord_6120140 prefixEnd_6120140 3142573492807790157803995 := by
  unfold tailWord_6120140
  simp only [CollatzResearch.WordTrace]
  refine ⟨111609922023892745770782937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148813229365190327694377249 111609922023892745770782937)
  ·
    refine ⟨83707441517919559328087203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111609922023892745770782937 83707441517919559328087203)
    ·
      refine ⟨125561162276879338992130805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83707441517919559328087203 125561162276879338992130805)
      ·
        refine ⟨11771358963457438030512263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125561162276879338992130805 11771358963457438030512263)
        ·
          refine ⟨17657038445186157045768395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771358963457438030512263 17657038445186157045768395)
          ·
            refine ⟨26485557667779235568652593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17657038445186157045768395 26485557667779235568652593)
            ·
              refine ⟨19864168250834426676489445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26485557667779235568652593 19864168250834426676489445)
              ·
                refine ⟨3724531547031455001841771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19864168250834426676489445 3724531547031455001841771)
                ·
                  refine ⟨5586797320547182502762657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724531547031455001841771 5586797320547182502762657)
                  ·
                    refine ⟨4190097990410386877071993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586797320547182502762657 4190097990410386877071993)
                    ·
                      refine ⟨3142573492807790157803995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190097990410386877071993 3142573492807790157803995)
                      ·
                        rfl

theorem cell23_6120140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6120140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120140 prefixEnd_6120140 := by exact prefixLift 6120140
  have htrace : WordTrace (prefixWord ++ tailWord_6120140) baseStart_6120140 baseEnd_6120140 := by
    simpa [prefixWord, tailWord_6120140, baseEnd_6120140] using wordTrace_append hprefix tailTrace_6120140
  have hstable : (prefixWord ++ tailWord_6120140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120140).length < 2 ^ (prefixWord ++ tailWord_6120140).sum := by decide
  have hdescent : baseEnd_6120140 < baseStart_6120140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120179 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 4, 2]
def baseStart_6120179 : Nat := 118140960795 + 6120179 * 2 ^ 59
def prefixEnd_6120179 : Nat := 4983230072969 + 3 ^ 40 * 6120179 * 2
def baseEnd_6120179 : Nat := 3142593518553315505216315

theorem tailTrace_6120179 : CollatzResearch.WordTrace tailWord_6120179 prefixEnd_6120179 3142593518553315505216315 := by
  unfold tailWord_6120179
  simp only [CollatzResearch.WordTrace]
  refine ⟨223221266494644201202235591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148814177663096134134823727 223221266494644201202235591)
  ·
    refine ⟨334831899741966301803353387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223221266494644201202235591 334831899741966301803353387)
    ·
      refine ⟨502247849612949452705030081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334831899741966301803353387 502247849612949452705030081)
      ·
        refine ⟨376685887209712089528772561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502247849612949452705030081 376685887209712089528772561)
        ·
          refine ⟨282514415407284067146579421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376685887209712089528772561 282514415407284067146579421)
          ·
            refine ⟨105942905777731525179967283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282514415407284067146579421 105942905777731525179967283)
            ·
              refine ⟨158914358666597287769950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105942905777731525179967283 158914358666597287769950925)
              ·
                refine ⟨59592884499973982913731597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158914358666597287769950925 59592884499973982913731597)
                ·
                  refine ⟨22347331687490243592649349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59592884499973982913731597 22347331687490243592649349)
                  ·
                    refine ⟨4190124691404420673621753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22347331687490243592649349 4190124691404420673621753)
                    ·
                      refine ⟨3142593518553315505216315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190124691404420673621753 3142593518553315505216315)
                      ·
                        rfl

theorem cell23_6120179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4, 2].length) (baseStart_6120179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120179 prefixEnd_6120179 := by exact prefixLift 6120179
  have htrace : WordTrace (prefixWord ++ tailWord_6120179) baseStart_6120179 baseEnd_6120179 := by
    simpa [prefixWord, tailWord_6120179, baseEnd_6120179] using wordTrace_append hprefix tailTrace_6120179
  have hstable : (prefixWord ++ tailWord_6120179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120179).length < 2 ^ (prefixWord ++ tailWord_6120179).sum := by decide
  have hdescent : baseEnd_6120179 < baseStart_6120179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120213 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_6120213 : Nat := 118140960795 + 6120213 * 2 ^ 59
def prefixEnd_6120213 : Nat := 4983230072969 + 3 ^ 40 * 6120213 * 2
def baseEnd_6120213 : Nat := 3142610976895568372191159

theorem tailTrace_6120213 : CollatzResearch.WordTrace tailWord_6120213 prefixEnd_6120213 3142610976895568372191159 := by
  unfold tailWord_6120213
  simp only [CollatzResearch.WordTrace]
  refine ⟨223222506576521025008973293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148815004384347350005982195 223222506576521025008973293)
  ·
    refine ⟨83708439966195384378364985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223222506576521025008973293 83708439966195384378364985)
    ·
      refine ⟨62781329974646538283773739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83708439966195384378364985 62781329974646538283773739)
      ·
        refine ⟨94171994961969807425660609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62781329974646538283773739 94171994961969807425660609)
        ·
          refine ⟨70628996221477355569245457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94171994961969807425660609 70628996221477355569245457)
          ·
            refine ⟨52971747166108016676934093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70628996221477355569245457 52971747166108016676934093)
            ·
              refine ⟨19864405187290506253850285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52971747166108016676934093 19864405187290506253850285)
              ·
                refine ⟨7449151945233939845193857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19864405187290506253850285 7449151945233939845193857)
                ·
                  refine ⟨5586863958925454883895393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449151945233939845193857 5586863958925454883895393)
                  ·
                    refine ⟨4190147969194091162921545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586863958925454883895393 4190147969194091162921545)
                    ·
                      refine ⟨3142610976895568372191159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190147969194091162921545 3142610976895568372191159)
                      ·
                        rfl

theorem cell23_6120213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_6120213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120213 prefixEnd_6120213 := by exact prefixLift 6120213
  have htrace : WordTrace (prefixWord ++ tailWord_6120213) baseStart_6120213 baseEnd_6120213 := by
    simpa [prefixWord, tailWord_6120213, baseEnd_6120213] using wordTrace_append hprefix tailTrace_6120213
  have hstable : (prefixWord ++ tailWord_6120213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120213).length < 2 ^ (prefixWord ++ tailWord_6120213).sum := by decide
  have hdescent : baseEnd_6120213 < baseStart_6120213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120239 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 7, 2]
def baseStart_6120239 : Nat := 118140960795 + 6120239 * 2 ^ 59
def prefixEnd_6120239 : Nat := 4983230072969 + 3 ^ 40 * 6120239 * 2
def baseEnd_6120239 : Nat := 3142624327392585270466039

theorem tailTrace_6120239 : CollatzResearch.WordTrace tailWord_6120239 prefixEnd_6120239 3142624327392585270466039 := by
  unfold tailWord_6120239
  simp only [CollatzResearch.WordTrace]
  refine ⟨223223454874426831449419771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148815636582951220966279847 223223454874426831449419771)
  ·
    refine ⟨334835182311640247174129657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223223454874426831449419771 334835182311640247174129657)
    ·
      refine ⟨251126386733730185380597243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334835182311640247174129657 251126386733730185380597243)
      ·
        refine ⟨376689580100595278070895865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251126386733730185380597243 376689580100595278070895865)
        ·
          refine ⟨282517185075446458553171899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376689580100595278070895865 282517185075446458553171899)
          ·
            refine ⟨423775777613169687829757849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282517185075446458553171899 423775777613169687829757849)
            ·
              refine ⟨317831833209877265872318387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423775777613169687829757849 317831833209877265872318387)
              ·
                refine ⟨476747749814815898808477581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317831833209877265872318387 476747749814815898808477581)
                ·
                  refine ⟨178780406180555962053179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476747749814815898808477581 178780406180555962053179093)
                  ·
                    refine ⟨4190165769856780360621385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178780406180555962053179093 4190165769856780360621385)
                    ·
                      refine ⟨3142624327392585270466039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190165769856780360621385 3142624327392585270466039)
                      ·
                        rfl

theorem cell23_6120239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7, 2].length) (baseStart_6120239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120239 prefixEnd_6120239 := by exact prefixLift 6120239
  have htrace : WordTrace (prefixWord ++ tailWord_6120239) baseStart_6120239 baseEnd_6120239 := by
    simpa [prefixWord, tailWord_6120239, baseEnd_6120239] using wordTrace_append hprefix tailTrace_6120239
  have hstable : (prefixWord ++ tailWord_6120239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120239).length < 2 ^ (prefixWord ++ tailWord_6120239).sum := by decide
  have hdescent : baseEnd_6120239 < baseStart_6120239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120253 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 5]
def baseStart_6120253 : Nat := 118140960795 + 6120253 * 2 ^ 59
def prefixEnd_6120253 : Nat := 4983230072969 + 3 ^ 40 * 6120253 * 2
def baseEnd_6120253 : Nat := 349181279569083135076775

theorem tailTrace_6120253 : CollatzResearch.WordTrace tailWord_6120253 prefixEnd_6120253 349181279569083135076775 := by
  unfold tailWord_6120253
  simp only [CollatzResearch.WordTrace]
  refine ⟨223223965496376111840429413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148815976997584074560286275 223223965496376111840429413)
  ·
    refine ⟨41854493530570520970080515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223223965496376111840429413 41854493530570520970080515)
    ·
      refine ⟨62781740295855781455120773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41854493530570520970080515 62781740295855781455120773)
      ·
        refine ⟨11771576305472959022835145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62781740295855781455120773 11771576305472959022835145)
        ·
          refine ⟨8828682229104719267126359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11771576305472959022835145 8828682229104719267126359)
          ·
            refine ⟨13243023343657078900689539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828682229104719267126359 13243023343657078900689539)
            ·
              refine ⟨19864535015485618351034309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243023343657078900689539 19864535015485618351034309)
              ·
                refine ⟨3724600315403553440818933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19864535015485618351034309 3724600315403553440818933)
                ·
                  refine ⟨349181279569083135076775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3724600315403553440818933 349181279569083135076775)
                  ·
                    rfl

theorem cell23_6120253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_6120253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120253 prefixEnd_6120253 := by exact prefixLift 6120253
  have htrace : WordTrace (prefixWord ++ tailWord_6120253) baseStart_6120253 baseEnd_6120253 := by
    simpa [prefixWord, tailWord_6120253, baseEnd_6120253] using wordTrace_append hprefix tailTrace_6120253
  have hstable : (prefixWord ++ tailWord_6120253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120253).length < 2 ^ (prefixWord ++ tailWord_6120253).sum := by decide
  have hdescent : baseEnd_6120253 < baseStart_6120253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120306 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6120306 : Nat := 118140960795 + 6120306 * 2 ^ 59
def prefixEnd_6120306 : Nat := 4983230072969 + 3 ^ 40 * 6120306 * 2
def baseEnd_6120306 : Nat := 3142658730596436508328231

theorem tailTrace_6120306 : CollatzResearch.WordTrace tailWord_6120306 prefixEnd_6120306 3142658730596436508328231 := by
  unfold tailWord_6120306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806474641296025473027193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148817265710122734594739181 55806474641296025473027193)
  ·
    refine ⟨41854855980972019104770395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55806474641296025473027193 41854855980972019104770395)
    ·
      refine ⟨62782283971458028657155593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41854855980972019104770395 62782283971458028657155593)
      ·
        refine ⟨47086712978593521492866695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62782283971458028657155593 47086712978593521492866695)
        ·
          refine ⟨70630069467890282239300043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47086712978593521492866695 70630069467890282239300043)
          ·
            refine ⟨105945104201835423358950065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70630069467890282239300043 105945104201835423358950065)
            ·
              refine ⟨79458828151376567519212549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105945104201835423358950065 79458828151376567519212549)
              ·
                refine ⟨14898530278383106409852353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79458828151376567519212549 14898530278383106409852353)
                ·
                  refine ⟨11173897708787329807389265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14898530278383106409852353 11173897708787329807389265)
                  ·
                    refine ⟨8380423281590497355541949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11173897708787329807389265 8380423281590497355541949)
                    ·
                      refine ⟨3142658730596436508328231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8380423281590497355541949 3142658730596436508328231)
                      ·
                        rfl

theorem cell23_6120306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6120306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120306 prefixEnd_6120306 := by exact prefixLift 6120306
  have htrace : WordTrace (prefixWord ++ tailWord_6120306) baseStart_6120306 baseEnd_6120306 := by
    simpa [prefixWord, tailWord_6120306, baseEnd_6120306] using wordTrace_append hprefix tailTrace_6120306
  have hstable : (prefixWord ++ tailWord_6120306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120306).length < 2 ^ (prefixWord ++ tailWord_6120306).sum := by decide
  have hdescent : baseEnd_6120306 < baseStart_6120306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120313 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 1, 4]
def baseStart_6120313 : Nat := 118140960795 + 6120313 * 2 ^ 59
def prefixEnd_6120313 : Nat := 4983230072969 + 3 ^ 40 * 6120313 * 2
def baseEnd_6120313 : Nat := 1047554108320339326980233

theorem tailTrace_6120313 : CollatzResearch.WordTrace tailWord_6120313 prefixEnd_6120313 1047554108320339326980233 := by
  unfold tailWord_6120313
  simp only [CollatzResearch.WordTrace]
  refine ⟨223226153876158742087613593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148817435917439161391742395 223226153876158742087613593)
  ·
    refine ⟨167419615407119056565710195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223226153876158742087613593 167419615407119056565710195)
    ·
      refine ⟨251129423110678584848565293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167419615407119056565710195 251129423110678584848565293)
      ·
        refine ⟨94173533666504469318211985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251129423110678584848565293 94173533666504469318211985)
        ·
          refine ⟨70630150249878351988658989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94173533666504469318211985 70630150249878351988658989)
          ·
            refine ⟨26486306343704381995747121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70630150249878351988658989 26486306343704381995747121)
            ·
              refine ⟨19864729757778286496810341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26486306343704381995747121 19864729757778286496810341)
              ·
                refine ⟨3724636829583428718151939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19864729757778286496810341 3724636829583428718151939)
                ·
                  refine ⟨5586955244375143077227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724636829583428718151939 5586955244375143077227909)
                  ·
                    refine ⟨1047554108320339326980233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586955244375143077227909 1047554108320339326980233)
                    ·
                      rfl

theorem cell23_6120313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_6120313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120313 prefixEnd_6120313 := by exact prefixLift 6120313
  have htrace : WordTrace (prefixWord ++ tailWord_6120313) baseStart_6120313 baseEnd_6120313 := by
    simpa [prefixWord, tailWord_6120313, baseEnd_6120313] using wordTrace_append hprefix tailTrace_6120313
  have hstable : (prefixWord ++ tailWord_6120313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120313).length < 2 ^ (prefixWord ++ tailWord_6120313).sum := by decide
  have hdescent : baseEnd_6120313 < baseStart_6120313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120356 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_6120356 : Nat := 118140960795 + 6120356 * 2 ^ 59
def prefixEnd_6120356 : Nat := 4983230072969 + 3 ^ 40 * 6120356 * 2
def baseEnd_6120356 : Nat := 1047561468209720437567667

theorem tailTrace_6120356 : CollatzResearch.WordTrace tailWord_6120356 prefixEnd_6120356 1047561468209720437567667 := by
  unfold tailWord_6120356
  simp only [CollatzResearch.WordTrace]
  refine ⟨111613861107501480215714461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148818481476668640287619281 111613861107501480215714461)
  ·
    refine ⟨41855197915313055080892923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111613861107501480215714461 41855197915313055080892923)
    ·
      refine ⟨62782796872969582621339385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41855197915313055080892923 62782796872969582621339385)
      ·
        refine ⟨47087097654727186966004539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62782796872969582621339385 47087097654727186966004539)
        ·
          refine ⟨70630646482090780449006809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47087097654727186966004539 70630646482090780449006809)
          ·
            refine ⟨52972984861568085336755107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70630646482090780449006809 52972984861568085336755107)
            ·
              refine ⟨79459477292352128005132661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52972984861568085336755107 79459477292352128005132661)
              ·
                refine ⟨7449325996158012000481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79459477292352128005132661 7449325996158012000481187)
                ·
                  refine ⟨11173988994237018000721781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449325996158012000481187 11173988994237018000721781)
                  ·
                    refine ⟨1047561468209720437567667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11173988994237018000721781 1047561468209720437567667)
                    ·
                      rfl

theorem cell23_6120356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_6120356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120356 prefixEnd_6120356 := by exact prefixLift 6120356
  have htrace : WordTrace (prefixWord ++ tailWord_6120356) baseStart_6120356 baseEnd_6120356 := by
    simpa [prefixWord, tailWord_6120356, baseEnd_6120356] using wordTrace_append hprefix tailTrace_6120356
  have hstable : (prefixWord ++ tailWord_6120356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120356).length < 2 ^ (prefixWord ++ tailWord_6120356).sum := by decide
  have hdescent : baseEnd_6120356 < baseStart_6120356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120399 : List Nat := [1, 1, 2, 1, 1, 6, 2, 9]
def baseStart_6120399 : Nat := 118140960795 + 6120399 * 2 ^ 59
def prefixEnd_6120399 : Nat := 4983230072969 + 3 ^ 40 * 6120399 * 2
def baseEnd_6120399 : Nat := 116396536455455727572789

theorem tailTrace_6120399 : CollatzResearch.WordTrace tailWord_6120399 prefixEnd_6120399 116396536455455727572789 := by
  unfold tailWord_6120399
  simp only [CollatzResearch.WordTrace]
  refine ⟨223229290553847178775244251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148819527035898119183496167 223229290553847178775244251)
  ·
    refine ⟨334843935830770768162866377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223229290553847178775244251 334843935830770768162866377)
    ·
      refine ⟨251132951873078076122149783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334843935830770768162866377 251132951873078076122149783)
      ·
        refine ⟨376699427809617114183224675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251132951873078076122149783 376699427809617114183224675)
        ·
          refine ⟨565049141714425671274837013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376699427809617114183224675 565049141714425671274837013)
          ·
            refine ⟨26486678517863703341007985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 565049141714425671274837013 26486678517863703341007985)
            ·
              refine ⟨19865008888397777505755989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26486678517863703341007985 19865008888397777505755989)
              ·
                refine ⟨116396536455455727572789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19865008888397777505755989 116396536455455727572789)
                ·
                  rfl

theorem cell23_6120399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 9].length) (baseStart_6120399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120399 prefixEnd_6120399 := by exact prefixLift 6120399
  have htrace : WordTrace (prefixWord ++ tailWord_6120399) baseStart_6120399 baseEnd_6120399 := by
    simpa [prefixWord, tailWord_6120399, baseEnd_6120399] using wordTrace_append hprefix tailTrace_6120399
  have hstable : (prefixWord ++ tailWord_6120399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120399).length < 2 ^ (prefixWord ++ tailWord_6120399).sum := by decide
  have hdescent : baseEnd_6120399 < baseStart_6120399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120410 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_6120410 : Nat := 118140960795 + 6120410 * 2 ^ 59
def prefixEnd_6120410 : Nat := 4983230072969 + 3 ^ 40 * 6120410 * 2
def baseEnd_6120410 : Nat := 3142712132584504101427753

theorem tailTrace_6120410 : CollatzResearch.WordTrace tailWord_6120410 prefixEnd_6120410 3142712132584504101427753 := by
  unfold tailWord_6120410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55807422939201831913473671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148819794504538218435929789 55807422939201831913473671)
  ·
    refine ⟨83711134408802747870210507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55807422939201831913473671 83711134408802747870210507)
    ·
      refine ⟨125566701613204121805315761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83711134408802747870210507 125566701613204121805315761)
      ·
        refine ⟨94175026209903091353986821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125566701613204121805315761 94175026209903091353986821)
        ·
          refine ⟨17657817414356829628872529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94175026209903091353986821 17657817414356829628872529)
          ·
            refine ⟨13243363060767622221654397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17657817414356829628872529 13243363060767622221654397)
            ·
              refine ⟨4966261147787858333120399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13243363060767622221654397 4966261147787858333120399)
              ·
                refine ⟨7449391721681787499680599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966261147787858333120399 7449391721681787499680599)
                ·
                  refine ⟨11174087582522681249520899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449391721681787499680599 11174087582522681249520899)
                  ·
                    refine ⟨16761131373784021874281349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11174087582522681249520899 16761131373784021874281349)
                    ·
                      refine ⟨3142712132584504101427753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16761131373784021874281349 3142712132584504101427753)
                      ·
                        rfl

theorem cell23_6120410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_6120410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120410 prefixEnd_6120410 := by exact prefixLift 6120410
  have htrace : WordTrace (prefixWord ++ tailWord_6120410) baseStart_6120410 baseEnd_6120410 := by
    simpa [prefixWord, tailWord_6120410, baseEnd_6120410] using wordTrace_append hprefix tailTrace_6120410
  have hstable : (prefixWord ++ tailWord_6120410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120410).length < 2 ^ (prefixWord ++ tailWord_6120410).sum := by decide
  have hdescent : baseEnd_6120410 < baseStart_6120410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120413 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_6120413 : Nat := 118140960795 + 6120413 * 2 ^ 59
def prefixEnd_6120413 : Nat := 4983230072969 + 3 ^ 40 * 6120413 * 2
def baseEnd_6120413 : Nat := 3142713673026467589690239

theorem tailTrace_6120413 : CollatzResearch.WordTrace tailWord_6120413 prefixEnd_6120413 3142713673026467589690239 := by
  unfold tailWord_6120413
  simp only [CollatzResearch.WordTrace]
  refine ⟨223229801175796459166253893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148819867450530972777502595 223229801175796459166253893)
  ·
    refine ⟨41855587720461836093672605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223229801175796459166253893 41855587720461836093672605)
    ·
      refine ⟨15695845395173188535127227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41855587720461836093672605 15695845395173188535127227)
      ·
        refine ⟨23543768092759782802690841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15695845395173188535127227 23543768092759782802690841)
        ·
          refine ⟨17657826069569837102018131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23543768092759782802690841 17657826069569837102018131)
          ·
            refine ⟨26486739104354755653027197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17657826069569837102018131 26486739104354755653027197)
            ·
              refine ⟨9932527164133033369885199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26486739104354755653027197 9932527164133033369885199)
              ·
                refine ⟨14898790746199550054827799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932527164133033369885199 14898790746199550054827799)
                ·
                  refine ⟨22348186119299325082241699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14898790746199550054827799 22348186119299325082241699)
                  ·
                    refine ⟨33522279178948987623362549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22348186119299325082241699 33522279178948987623362549)
                    ·
                      refine ⟨3142713673026467589690239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33522279178948987623362549 3142713673026467589690239)
                      ·
                        rfl

theorem cell23_6120413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_6120413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120413 prefixEnd_6120413 := by exact prefixLift 6120413
  have htrace : WordTrace (prefixWord ++ tailWord_6120413) baseStart_6120413 baseEnd_6120413 := by
    simpa [prefixWord, tailWord_6120413, baseEnd_6120413] using wordTrace_append hprefix tailTrace_6120413
  have hstable : (prefixWord ++ tailWord_6120413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120413).length < 2 ^ (prefixWord ++ tailWord_6120413).sum := by decide
  have hdescent : baseEnd_6120413 < baseStart_6120413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120421 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6120421 : Nat := 118140960795 + 6120421 * 2 ^ 59
def prefixEnd_6120421 : Nat := 4983230072969 + 3 ^ 40 * 6120421 * 2
def baseEnd_6120421 : Nat := 3142717780871703558390203

theorem tailTrace_6120421 : CollatzResearch.WordTrace tailWord_6120421 prefixEnd_6120421 3142717780871703558390203 := by
  unfold tailWord_6120421
  simp only [CollatzResearch.WordTrace]
  refine ⟨223230092959767476532545117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148820061973178317688363411 223230092959767476532545117)
  ·
    refine ⟨83711284859912803699704419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223230092959767476532545117 83711284859912803699704419)
    ·
      refine ⟨125566927289869205549556629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83711284859912803699704419 125566927289869205549556629)
      ·
        refine ⟨5885949716712619010135467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125566927289869205549556629 5885949716712619010135467)
        ·
          refine ⟨8828924575068928515203201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885949716712619010135467 8828924575068928515203201)
          ·
            refine ⟨6621693431301696386402401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828924575068928515203201 6621693431301696386402401)
            ·
              refine ⟨4966270073476272289801801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621693431301696386402401 4966270073476272289801801)
              ·
                refine ⟨3724702555107204217351351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966270073476272289801801 3724702555107204217351351)
                ·
                  refine ⟨5587053832660806326027027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724702555107204217351351 5587053832660806326027027)
                  ·
                    refine ⟨8380580748991209489040541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5587053832660806326027027 8380580748991209489040541)
                    ·
                      refine ⟨3142717780871703558390203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8380580748991209489040541 3142717780871703558390203)
                      ·
                        rfl

theorem cell23_6120421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6120421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120421 prefixEnd_6120421 := by exact prefixLift 6120421
  have htrace : WordTrace (prefixWord ++ tailWord_6120421) baseStart_6120421 baseEnd_6120421 := by
    simpa [prefixWord, tailWord_6120421, baseEnd_6120421] using wordTrace_append hprefix tailTrace_6120421
  have hstable : (prefixWord ++ tailWord_6120421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120421).length < 2 ^ (prefixWord ++ tailWord_6120421).sum := by decide
  have hdescent : baseEnd_6120421 < baseStart_6120421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120453 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_6120453 : Nat := 118140960795 + 6120453 * 2 ^ 59
def prefixEnd_6120453 : Nat := 4983230072969 + 3 ^ 40 * 6120453 * 2
def baseEnd_6120453 : Nat := 3142734212252647433190055

theorem tailTrace_6120453 : CollatzResearch.WordTrace tailWord_6120453 prefixEnd_6120453 3142734212252647433190055 := by
  unfold tailWord_6120453
  simp only [CollatzResearch.WordTrace]
  refine ⟨223231260095651545997710013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148820840063767697331806675 223231260095651545997710013)
  ·
    refine ⟨83711722535869329749141255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223231260095651545997710013 83711722535869329749141255)
    ·
      refine ⟨125567583803803994623711883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83711722535869329749141255 125567583803803994623711883)
      ·
        refine ⟨188351375705705991935567825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125567583803803994623711883 188351375705705991935567825)
        ·
          refine ⟨141263531779279493951675869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188351375705705991935567825 141263531779279493951675869)
          ·
            refine ⟨52973824417229810231878451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141263531779279493951675869 52973824417229810231878451)
            ·
              refine ⟨79460736625844715347817677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52973824417229810231878451 79460736625844715347817677)
              ·
                refine ⟨29797776234691768255431629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79460736625844715347817677 29797776234691768255431629)
                ·
                  refine ⟨11174166088009413095786861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29797776234691768255431629 11174166088009413095786861)
                  ·
                    refine ⟨4190312283003529910920073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11174166088009413095786861 4190312283003529910920073)
                    ·
                      refine ⟨3142734212252647433190055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190312283003529910920073 3142734212252647433190055)
                      ·
                        rfl

theorem cell23_6120453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_6120453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120453 prefixEnd_6120453 := by exact prefixLift 6120453
  have htrace : WordTrace (prefixWord ++ tailWord_6120453) baseStart_6120453 baseEnd_6120453 := by
    simpa [prefixWord, tailWord_6120453, baseEnd_6120453] using wordTrace_append hprefix tailTrace_6120453
  have hstable : (prefixWord ++ tailWord_6120453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120453).length < 2 ^ (prefixWord ++ tailWord_6120453).sum := by decide
  have hdescent : baseEnd_6120453 < baseStart_6120453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120496 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_6120496 : Nat := 118140960795 + 6120496 * 2 ^ 59
def prefixEnd_6120496 : Nat := 4983230072969 + 3 ^ 40 * 6120496 * 2
def baseEnd_6120496 : Nat := 3142756291920790764952357

theorem tailTrace_6120496 : CollatzResearch.WordTrace tailWord_6120496 prefixEnd_6120496 3142756291920790764952357 := by
  unfold tailWord_6120496
  simp only [CollatzResearch.WordTrace]
  refine ⟨111616414217247882170762671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148821885622997176227683561 111616414217247882170762671)
  ·
    refine ⟨167424621325871823256144007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111616414217247882170762671 167424621325871823256144007)
    ·
      refine ⟨251136931988807734884216011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167424621325871823256144007 251136931988807734884216011)
      ·
        refine ⟨376705397983211602326324017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251136931988807734884216011 376705397983211602326324017)
        ·
          refine ⟨282529048487408701744743013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376705397983211602326324017 282529048487408701744743013)
          ·
            refine ⟨52974196591389131577139315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282529048487408701744743013 52974196591389131577139315)
            ·
              refine ⟨79461294887083697365708973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52974196591389131577139315 79461294887083697365708973)
              ·
                refine ⟨29797985582656386512140865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79461294887083697365708973 29797985582656386512140865)
                ·
                  refine ⟨22348489186992289884105649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29797985582656386512140865 22348489186992289884105649)
                  ·
                    refine ⟨16761366890244217413079237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22348489186992289884105649 16761366890244217413079237)
                    ·
                      refine ⟨3142756291920790764952357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16761366890244217413079237 3142756291920790764952357)
                      ·
                        rfl

theorem cell23_6120496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_6120496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120496 prefixEnd_6120496 := by exact prefixLift 6120496
  have htrace : WordTrace (prefixWord ++ tailWord_6120496) baseStart_6120496 baseEnd_6120496 := by
    simpa [prefixWord, tailWord_6120496, baseEnd_6120496] using wordTrace_append hprefix tailTrace_6120496
  have hstable : (prefixWord ++ tailWord_6120496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120496).length < 2 ^ (prefixWord ++ tailWord_6120496).sum := by decide
  have hdescent : baseEnd_6120496 < baseStart_6120496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120506 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_6120506 : Nat := 118140960795 + 6120506 * 2 ^ 59
def prefixEnd_6120506 : Nat := 4983230072969 + 3 ^ 40 * 6120506 * 2
def baseEnd_6120506 : Nat := 349195714080815080647479

theorem tailTrace_6120506 : CollatzResearch.WordTrace tailWord_6120506 prefixEnd_6120506 349195714080815080647479 := by
  unfold tailWord_6120506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808298291114884012347343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148822128776306357366259581 55808298291114884012347343)
  ·
    refine ⟨83712447436672326018521015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55808298291114884012347343 83712447436672326018521015)
    ·
      refine ⟨125568671155008489027781523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83712447436672326018521015 125568671155008489027781523)
      ·
        refine ⟨188353006732512733541672285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125568671155008489027781523 188353006732512733541672285)
        ·
          refine ⟨70632377524692275078127107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188353006732512733541672285 70632377524692275078127107)
          ·
            refine ⟨105948566287038412617190661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70632377524692275078127107 105948566287038412617190661)
            ·
              refine ⟨19865356178819702365723249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105948566287038412617190661 19865356178819702365723249)
              ·
                refine ⟨14899017134114776774292437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19865356178819702365723249 14899017134114776774292437)
                ·
                  refine ⟨349195714080815080647479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14899017134114776774292437 349195714080815080647479)
                  ·
                    rfl

theorem cell23_6120506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_6120506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120506 prefixEnd_6120506 := by exact prefixLift 6120506
  have htrace : WordTrace (prefixWord ++ tailWord_6120506) baseStart_6120506 baseEnd_6120506 := by
    simpa [prefixWord, tailWord_6120506, baseEnd_6120506] using wordTrace_append hprefix tailTrace_6120506
  have hstable : (prefixWord ++ tailWord_6120506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120506).length < 2 ^ (prefixWord ++ tailWord_6120506).sum := by decide
  have hdescent : baseEnd_6120506 < baseStart_6120506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120543 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 5, 2]
def baseStart_6120543 : Nat := 118140960795 + 6120543 * 2 ^ 59
def prefixEnd_6120543 : Nat := 4983230072969 + 3 ^ 40 * 6120543 * 2
def baseEnd_6120543 : Nat := 3142780425511552081064641

theorem tailTrace_6120543 : CollatzResearch.WordTrace tailWord_6120543 prefixEnd_6120543 3142780425511552081064641 := by
  unfold tailWord_6120543
  simp only [CollatzResearch.WordTrace]
  refine ⟨223234542665325491368486283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148823028443550327578990855 223234542665325491368486283)
  ·
    refine ⟨334851813997988237052729425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223234542665325491368486283 334851813997988237052729425)
    ·
      refine ⟨251138860498491177789547069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334851813997988237052729425 251138860498491177789547069)
      ·
        refine ⟨94177072686934191671080151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251138860498491177789547069 94177072686934191671080151)
        ·
          refine ⟨141265609030401287506620227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94177072686934191671080151 141265609030401287506620227)
          ·
            refine ⟨211898413545601931259930341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141265609030401287506620227 211898413545601931259930341)
            ·
              refine ⟨39730952539800362111236939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211898413545601931259930341 39730952539800362111236939)
              ·
                refine ⟨59596428809700543166855409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39730952539800362111236939 59596428809700543166855409)
                ·
                  refine ⟨44697321607275407375141557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59596428809700543166855409 44697321607275407375141557)
                  ·
                    refine ⟨4190373900682069441419521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44697321607275407375141557 4190373900682069441419521)
                    ·
                      refine ⟨3142780425511552081064641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190373900682069441419521 3142780425511552081064641)
                      ·
                        rfl

theorem cell23_6120543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_6120543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120543 prefixEnd_6120543 := by exact prefixLift 6120543
  have htrace : WordTrace (prefixWord ++ tailWord_6120543) baseStart_6120543 baseEnd_6120543 := by
    simpa [prefixWord, tailWord_6120543, baseEnd_6120543] using wordTrace_append hprefix tailTrace_6120543
  have hstable : (prefixWord ++ tailWord_6120543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120543).length < 2 ^ (prefixWord ++ tailWord_6120543).sum := by decide
  have hdescent : baseEnd_6120543 < baseStart_6120543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120590 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6120590 : Nat := 118140960795 + 6120590 * 2 ^ 59
def prefixEnd_6120590 : Nat := 4983230072969 + 3 ^ 40 * 6120590 * 2
def baseEnd_6120590 : Nat := 3142804559102313397176925

theorem tailTrace_6120590 : CollatzResearch.WordTrace tailWord_6120590 prefixEnd_6120590 3142804559102313397176925 := by
  unfold tailWord_6120590
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904532112019402299430903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148824171264103478930298149 27904532112019402299430903)
  ·
    refine ⟨41856798168029103449146355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904532112019402299430903 41856798168029103449146355)
    ·
      refine ⟨62785197252043655173719533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41856798168029103449146355 62785197252043655173719533)
      ·
        refine ⟨23544448969516370690144825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62785197252043655173719533 23544448969516370690144825)
        ·
          refine ⟨17658336727137278017608619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23544448969516370690144825 17658336727137278017608619)
          ·
            refine ⟨26487505090705917026412929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17658336727137278017608619 26487505090705917026412929)
            ·
              refine ⟨19865628818029437769809697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26487505090705917026412929 19865628818029437769809697)
              ·
                refine ⟨14899221613522078327357273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19865628818029437769809697 14899221613522078327357273)
                ·
                  refine ⟨11174416210141558745517955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14899221613522078327357273 11174416210141558745517955)
                  ·
                    refine ⟨16761624315212338118276933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11174416210141558745517955 16761624315212338118276933)
                    ·
                      refine ⟨3142804559102313397176925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16761624315212338118276933 3142804559102313397176925)
                      ·
                        rfl

theorem cell23_6120590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6120590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120590 prefixEnd_6120590 := by exact prefixLift 6120590
  have htrace : WordTrace (prefixWord ++ tailWord_6120590) baseStart_6120590 baseEnd_6120590 := by
    simpa [prefixWord, tailWord_6120590, baseEnd_6120590] using wordTrace_append hprefix tailTrace_6120590
  have hstable : (prefixWord ++ tailWord_6120590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120590).length < 2 ^ (prefixWord ++ tailWord_6120590).sum := by decide
  have hdescent : baseEnd_6120590 < baseStart_6120590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120607 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6120607 : Nat := 118140960795 + 6120607 * 2 ^ 59
def prefixEnd_6120607 : Nat := 4983230072969 + 3 ^ 40 * 6120607 * 2
def baseEnd_6120607 : Nat := 3142813288273439830664347

theorem tailTrace_6120607 : CollatzResearch.WordTrace tailWord_6120607 prefixEnd_6120607 3142813288273439830664347 := by
  unfold tailWord_6120607
  simp only [CollatzResearch.WordTrace]
  refine ⟨223236876937093630298816075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148824584624729086865877383 223236876937093630298816075)
  ·
    refine ⟨334855315405640445448224113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223236876937093630298816075 334855315405640445448224113)
    ·
      refine ⟨251141486554230334086168085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334855315405640445448224113 251141486554230334086168085)
      ·
        refine ⟨11772257182229546910289129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251141486554230334086168085 11772257182229546910289129)
        ·
          refine ⟨8829192886672160182716847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11772257182229546910289129 8829192886672160182716847)
          ·
            refine ⟨13243789330008240274075271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829192886672160182716847 13243789330008240274075271)
            ·
              refine ⟨19865683995012360411112907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243789330008240274075271 19865683995012360411112907)
              ·
                refine ⟨29798525992518540616669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19865683995012360411112907 29798525992518540616669361)
                ·
                  refine ⟨22348894494388905462502021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29798525992518540616669361 22348894494388905462502021)
                  ·
                    refine ⟨4190417717697919774219129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22348894494388905462502021 4190417717697919774219129)
                    ·
                      refine ⟨3142813288273439830664347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190417717697919774219129 3142813288273439830664347)
                      ·
                        rfl

theorem cell23_6120607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6120607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120607 prefixEnd_6120607 := by exact prefixLift 6120607
  have htrace : WordTrace (prefixWord ++ tailWord_6120607) baseStart_6120607 baseEnd_6120607 := by
    simpa [prefixWord, tailWord_6120607, baseEnd_6120607] using wordTrace_append hprefix tailTrace_6120607
  have hstable : (prefixWord ++ tailWord_6120607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120607).length < 2 ^ (prefixWord ++ tailWord_6120607).sum := by decide
  have hdescent : baseEnd_6120607 < baseStart_6120607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120613 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 6]
def baseStart_6120613 : Nat := 118140960795 + 6120613 * 2 ^ 59
def prefixEnd_6120613 : Nat := 4983230072969 + 3 ^ 40 * 6120613 * 2
def baseEnd_6120613 : Nat := 349201818795262978576591

theorem tailTrace_6120613 : CollatzResearch.WordTrace tailWord_6120613 prefixEnd_6120613 349201818795262978576591 := by
  unfold tailWord_6120613
  simp only [CollatzResearch.WordTrace]
  refine ⟨223237095775071893323534493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148824730516714595549022995 223237095775071893323534493)
  ·
    refine ⟨83713910915651959996325435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223237095775071893323534493 83713910915651959996325435)
    ·
      refine ⟨125570866373477939994488153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83713910915651959996325435 125570866373477939994488153)
      ·
        refine ⟨94178149780108454995866115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125570866373477939994488153 94178149780108454995866115)
        ·
          refine ⟨141267224670162682493799173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94178149780108454995866115 141267224670162682493799173)
          ·
            refine ⟨26487604625655502967587345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141267224670162682493799173 26487604625655502967587345)
            ·
              refine ⟨19865703469241627225690509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26487604625655502967587345 19865703469241627225690509)
              ·
                refine ⟨7449638800965610209633941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19865703469241627225690509 7449638800965610209633941)
                ·
                  refine ⟨349201818795262978576591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7449638800965610209633941 349201818795262978576591)
                  ·
                    rfl

theorem cell23_6120613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_6120613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120613 prefixEnd_6120613 := by exact prefixLift 6120613
  have htrace : WordTrace (prefixWord ++ tailWord_6120613) baseStart_6120613 baseEnd_6120613 := by
    simpa [prefixWord, tailWord_6120613, baseEnd_6120613] using wordTrace_append hprefix tailTrace_6120613
  have hstable : (prefixWord ++ tailWord_6120613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120613).length < 2 ^ (prefixWord ++ tailWord_6120613).sum := by decide
  have hdescent : baseEnd_6120613 < baseStart_6120613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_6120656 : Nat := 118140960795 + 6120656 * 2 ^ 59
def prefixEnd_6120656 : Nat := 4983230072969 + 3 ^ 40 * 6120656 * 2
def baseEnd_6120656 : Nat := 1047612816275170046317207

theorem tailTrace_6120656 : CollatzResearch.WordTrace tailWord_6120656 prefixEnd_6120656 1047612816275170046317207 := by
  unfold tailWord_6120656
  simp only [CollatzResearch.WordTrace]
  refine ⟨111619332056958055833674911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148825776075944074444899881 111619332056958055833674911)
  ·
    refine ⟨167428998085437083750512367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111619332056958055833674911 167428998085437083750512367)
    ·
      refine ⟨251143497128155625625768551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167428998085437083750512367 251143497128155625625768551)
      ·
        refine ⟨376715245692233438438652827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251143497128155625625768551 376715245692233438438652827)
        ·
          refine ⟨565072868538350157657979241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376715245692233438438652827 565072868538350157657979241)
          ·
            refine ⟨423804651403762618243484431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565072868538350157657979241 423804651403762618243484431)
            ·
              refine ⟨635706977105643927365226647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423804651403762618243484431 635706977105643927365226647)
              ·
                refine ⟨953560465658465891047839971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635706977105643927365226647 953560465658465891047839971)
                ·
                  refine ⟨1430340698487698836571759957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953560465658465891047839971 1430340698487698836571759957)
                  ·
                    refine ⟨1047612816275170046317207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1430340698487698836571759957 1047612816275170046317207)
                    ·
                      rfl

theorem cell23_6120656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_6120656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120656 prefixEnd_6120656 := by exact prefixLift 6120656
  have htrace : WordTrace (prefixWord ++ tailWord_6120656) baseStart_6120656 baseEnd_6120656 := by
    simpa [prefixWord, tailWord_6120656, baseEnd_6120656] using wordTrace_append hprefix tailTrace_6120656
  have hstable : (prefixWord ++ tailWord_6120656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120656).length < 2 ^ (prefixWord ++ tailWord_6120656).sum := by decide
  have hdescent : baseEnd_6120656 < baseStart_6120656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120663 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_6120663 : Nat := 118140960795 + 6120663 * 2 ^ 59
def prefixEnd_6120663 : Nat := 4983230072969 + 3 ^ 40 * 6120663 * 2
def baseEnd_6120663 : Nat := 3142842043190091611564089

theorem tailTrace_6120663 : CollatzResearch.WordTrace tailWord_6120663 prefixEnd_6120663 3142842043190091611564089 := by
  unfold tailWord_6120663
  simp only [CollatzResearch.WordTrace]
  refine ⟨223238919424890751862854643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148825946283260501241903095 223238919424890751862854643)
  ·
    refine ⟨334858379137336127794281965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223238919424890751862854643 334858379137336127794281965)
    ·
      refine ⟨125571892176501047922855737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334858379137336127794281965 125571892176501047922855737)
      ·
        refine ⟨94178919132375785942141803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125571892176501047922855737 94178919132375785942141803)
        ·
          refine ⟨141268378698563678913212705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94178919132375785942141803 141268378698563678913212705)
          ·
            refine ⟨105951284023922759184909529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141268378698563678913212705 105951284023922759184909529)
            ·
              refine ⟨79463463017942069388682147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105951284023922759184909529 79463463017942069388682147)
              ·
                refine ⟨119195194526913104083023221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79463463017942069388682147 119195194526913104083023221)
                ·
                  refine ⟨11174549486898103507783427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119195194526913104083023221 11174549486898103507783427)
                  ·
                    refine ⟨16761824230347155261675141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11174549486898103507783427 16761824230347155261675141)
                    ·
                      refine ⟨3142842043190091611564089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16761824230347155261675141 3142842043190091611564089)
                      ·
                        rfl

theorem cell23_6120663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_6120663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120663 prefixEnd_6120663 := by exact prefixLift 6120663
  have htrace : WordTrace (prefixWord ++ tailWord_6120663) baseStart_6120663 baseEnd_6120663 := by
    simpa [prefixWord, tailWord_6120663, baseEnd_6120663] using wordTrace_append hprefix tailTrace_6120663
  have hstable : (prefixWord ++ tailWord_6120663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120663).length < 2 ^ (prefixWord ++ tailWord_6120663).sum := by decide
  have hdescent : baseEnd_6120663 < baseStart_6120663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120677 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_6120677 : Nat := 118140960795 + 6120677 * 2 ^ 59
def prefixEnd_6120677 : Nat := 4983230072969 + 3 ^ 40 * 6120677 * 2
def baseEnd_6120677 : Nat := 1047616410639751518929675

theorem tailTrace_6120677 : CollatzResearch.WordTrace tailWord_6120677 prefixEnd_6120677 1047616410639751518929675 := by
  unfold tailWord_6120677
  simp only [CollatzResearch.WordTrace]
  refine ⟨223239430046840032253864285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148826286697893354835909523 223239430046840032253864285)
  ·
    refine ⟨83714786267565012095199107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223239430046840032253864285 83714786267565012095199107)
    ·
      refine ⟨125572179401347518142798661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83714786267565012095199107 125572179401347518142798661)
      ·
        refine ⟨23544783637752659651774749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125572179401347518142798661 23544783637752659651774749)
        ·
          refine ⟨8829293864157247369415531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23544783637752659651774749 8829293864157247369415531)
          ·
            refine ⟨13243940796235871054123297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829293864157247369415531 13243940796235871054123297)
            ·
              refine ⟨9932955597176903290592473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13243940796235871054123297 9932955597176903290592473)
              ·
                refine ⟨7449716697882677467944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9932955597176903290592473 7449716697882677467944355)
                ·
                  refine ⟨11174575046824016201916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449716697882677467944355 11174575046824016201916533)
                  ·
                    refine ⟨1047616410639751518929675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11174575046824016201916533 1047616410639751518929675)
                    ·
                      rfl

theorem cell23_6120677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_6120677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120677 prefixEnd_6120677 := by exact prefixLift 6120677
  have htrace : WordTrace (prefixWord ++ tailWord_6120677) baseStart_6120677 baseEnd_6120677 := by
    simpa [prefixWord, tailWord_6120677, baseEnd_6120677] using wordTrace_append hprefix tailTrace_6120677
  have hstable : (prefixWord ++ tailWord_6120677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120677).length < 2 ^ (prefixWord ++ tailWord_6120677).sum := by decide
  have hdescent : baseEnd_6120677 < baseStart_6120677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120680 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6120680 : Nat := 118140960795 + 6120680 * 2 ^ 59
def prefixEnd_6120680 : Nat := 4983230072969 + 3 ^ 40 * 6120680 * 2
def baseEnd_6120680 : Nat := 3142850772361218045051511

theorem tailTrace_6120680 : CollatzResearch.WordTrace tailWord_6120680 prefixEnd_6120680 3142850772361218045051511 := by
  unfold tailWord_6120680
  simp only [CollatzResearch.WordTrace]
  refine ⟨111619769732914581883111747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148826359643886109177482329 111619769732914581883111747)
  ·
    refine ⟨167429654599371872824667621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111619769732914581883111747 167429654599371872824667621)
    ·
      refine ⟨31393060237382226154625179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167429654599371872824667621 31393060237382226154625179)
      ·
        refine ⟨47089590356073339231937769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31393060237382226154625179 47089590356073339231937769)
        ·
          refine ⟨35317192767055004423953327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47089590356073339231937769 35317192767055004423953327)
          ·
            refine ⟨52975789150582506635929991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35317192767055004423953327 52975789150582506635929991)
            ·
              refine ⟨79463683725873759953894987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52975789150582506635929991 79463683725873759953894987)
              ·
                refine ⟨119195525588810639930842481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79463683725873759953894987 119195525588810639930842481)
                ·
                  refine ⟨89396644191607979948131861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119195525588810639930842481 89396644191607979948131861)
                  ·
                    refine ⟨4190467696481624060068681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89396644191607979948131861 4190467696481624060068681)
                    ·
                      refine ⟨3142850772361218045051511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190467696481624060068681 3142850772361218045051511)
                      ·
                        rfl

theorem cell23_6120680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6120680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120680 prefixEnd_6120680 := by exact prefixLift 6120680
  have htrace : WordTrace (prefixWord ++ tailWord_6120680) baseStart_6120680 baseEnd_6120680 := by
    simpa [prefixWord, tailWord_6120680, baseEnd_6120680] using wordTrace_append hprefix tailTrace_6120680
  have hstable : (prefixWord ++ tailWord_6120680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120680).length < 2 ^ (prefixWord ++ tailWord_6120680).sum := by decide
  have hdescent : baseEnd_6120680 < baseStart_6120680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120703 : List Nat := [1, 1, 2, 2, 1, 7, 9]
def baseStart_6120703 : Nat := 118140960795 + 6120703 * 2 ^ 59
def prefixEnd_6120703 : Nat := 4983230072969 + 3 ^ 40 * 6120703 * 2
def baseEnd_6120703 : Nat := 38800772622423104383505

theorem tailTrace_6120703 : CollatzResearch.WordTrace tailWord_6120703 prefixEnd_6120703 38800772622423104383505 := by
  unfold tailWord_6120703
  simp only [CollatzResearch.WordTrace]
  refine ⟨223240378344745838694310763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148826918896497225796207175 223240378344745838694310763)
  ·
    refine ⟨334860567517118758041466145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223240378344745838694310763 334860567517118758041466145)
    ·
      refine ⟨251145425637839068531099609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334860567517118758041466145 251145425637839068531099609)
      ·
        refine ⟨188359069228379301398324707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251145425637839068531099609 188359069228379301398324707)
        ·
          refine ⟨282538603842568952097487061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188359069228379301398324707 282538603842568952097487061)
          ·
            refine ⟨6621998527560209814784853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 282538603842568952097487061 6621998527560209814784853)
            ·
              refine ⟨38800772622423104383505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6621998527560209814784853 38800772622423104383505)
              ·
                rfl

theorem cell23_6120703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 9].length) (baseStart_6120703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120703 prefixEnd_6120703 := by exact prefixLift 6120703
  have htrace : WordTrace (prefixWord ++ tailWord_6120703) baseStart_6120703 baseEnd_6120703 := by
    simpa [prefixWord, tailWord_6120703, baseEnd_6120703] using wordTrace_append hprefix tailTrace_6120703
  have hstable : (prefixWord ++ tailWord_6120703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120703).length < 2 ^ (prefixWord ++ tailWord_6120703).sum := by decide
  have hdescent : baseEnd_6120703 < baseStart_6120703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120764 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_6120764 : Nat := 118140960795 + 6120764 * 2 ^ 59
def prefixEnd_6120764 : Nat := 4983230072969 + 3 ^ 40 * 6120764 * 2
def baseEnd_6120764 : Nat := 3142893904736195716401125

theorem tailTrace_6120764 : CollatzResearch.WordTrace tailWord_6120764 prefixEnd_6120764 3142893904736195716401125 := by
  unfold tailWord_6120764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111621301598762423056140673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148828402131683230741520897 111621301598762423056140673)
  ·
    refine ⟨83715976199071817292105505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111621301598762423056140673 83715976199071817292105505)
    ·
      refine ⟨62786982149303862969079129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83715976199071817292105505 62786982149303862969079129)
      ·
        refine ⟨47090236611977897226809347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62786982149303862969079129 47090236611977897226809347)
        ·
          refine ⟨70635354917966845840214021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47090236611977897226809347 70635354917966845840214021)
          ·
            refine ⟨13244129047118783595040129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70635354917966845840214021 13244129047118783595040129)
            ·
              refine ⟨9933096785339087696280097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13244129047118783595040129 9933096785339087696280097)
              ·
                refine ⟨7449822589004315772210073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9933096785339087696280097 7449822589004315772210073)
                ·
                  refine ⟨5587366941753236829157555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449822589004315772210073 5587366941753236829157555)
                  ·
                    refine ⟨8381050412629855243736333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5587366941753236829157555 8381050412629855243736333)
                    ·
                      refine ⟨3142893904736195716401125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381050412629855243736333 3142893904736195716401125)
                      ·
                        rfl

theorem cell23_6120764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_6120764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120764 prefixEnd_6120764 := by exact prefixLift 6120764
  have htrace : WordTrace (prefixWord ++ tailWord_6120764) baseStart_6120764 baseEnd_6120764 := by
    simpa [prefixWord, tailWord_6120764, baseEnd_6120764] using wordTrace_append hprefix tailTrace_6120764
  have hstable : (prefixWord ++ tailWord_6120764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120764).length < 2 ^ (prefixWord ++ tailWord_6120764).sum := by decide
  have hdescent : baseEnd_6120764 < baseStart_6120764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120773 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_6120773 : Nat := 118140960795 + 6120773 * 2 ^ 59
def prefixEnd_6120773 : Nat := 4983230072969 + 3 ^ 40 * 6120773 * 2
def baseEnd_6120773 : Nat := 3142898526062086181188583

theorem tailTrace_6120773 : CollatzResearch.WordTrace tailWord_6120773 prefixEnd_6120773 3142898526062086181188583 := by
  unfold tailWord_6120773
  simp only [CollatzResearch.WordTrace]
  refine ⟨223242931454492240649358973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148828620969661493766239315 223242931454492240649358973)
  ·
    refine ⟨83716099295434590243509615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223242931454492240649358973 83716099295434590243509615)
    ·
      refine ⟨125574148943151885365264423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83716099295434590243509615 125574148943151885365264423)
      ·
        refine ⟨188361223414727828047896635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125574148943151885365264423 188361223414727828047896635)
        ·
          refine ⟨282541835122091742071844953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188361223414727828047896635 282541835122091742071844953)
          ·
            refine ⟨211906376341568806553883715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282541835122091742071844953 211906376341568806553883715)
            ·
              refine ⟨317859564512353209830825573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211906376341568806553883715 317859564512353209830825573)
              ·
                refine ⟨59598668346066226843279795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317859564512353209830825573 59598668346066226843279795)
                ·
                  refine ⟨89398002519099340264919693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59598668346066226843279795 89398002519099340264919693)
                  ·
                    refine ⟨33524250944662252599344885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89398002519099340264919693 33524250944662252599344885)
                    ·
                      refine ⟨3142898526062086181188583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33524250944662252599344885 3142898526062086181188583)
                      ·
                        rfl

theorem cell23_6120773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_6120773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120773 prefixEnd_6120773 := by exact prefixLift 6120773
  have htrace : WordTrace (prefixWord ++ tailWord_6120773) baseStart_6120773 baseEnd_6120773 := by
    simpa [prefixWord, tailWord_6120773, baseEnd_6120773] using wordTrace_append hprefix tailTrace_6120773
  have hstable : (prefixWord ++ tailWord_6120773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120773).length < 2 ^ (prefixWord ++ tailWord_6120773).sum := by decide
  have hdescent : baseEnd_6120773 < baseStart_6120773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120780 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_6120780 : Nat := 118140960795 + 6120780 * 2 ^ 59
def prefixEnd_6120780 : Nat := 4983230072969 + 3 ^ 40 * 6120780 * 2
def baseEnd_6120780 : Nat := 1047634040142222551267017

theorem tailTrace_6120780 : CollatzResearch.WordTrace tailWord_6120780 prefixEnd_6120780 1047634040142222551267017 := by
  unfold tailWord_6120780
  simp only [CollatzResearch.WordTrace]
  refine ⟨111621593382733440422431897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148828791176977920563242529 111621593382733440422431897)
  ·
    refine ⟨83716195037050080316823923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111621593382733440422431897 83716195037050080316823923)
    ·
      refine ⟨125574292555575120475235885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83716195037050080316823923 125574292555575120475235885)
      ·
        refine ⟨47090359708340670178213457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125574292555575120475235885 47090359708340670178213457)
        ·
          refine ⟨35317769781255502633660093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47090359708340670178213457 35317769781255502633660093)
          ·
            refine ⟨13244163667970813487622535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35317769781255502633660093 13244163667970813487622535)
            ·
              refine ⟨19866245501956220231433803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244163667970813487622535 19866245501956220231433803)
              ·
                refine ⟨29799368252934330347150705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866245501956220231433803 29799368252934330347150705)
                ·
                  refine ⟨22349526189700747760363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29799368252934330347150705 22349526189700747760363029)
                  ·
                    refine ⟨1047634040142222551267017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22349526189700747760363029 1047634040142222551267017)
                    ·
                      rfl

theorem cell23_6120780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_6120780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120780 prefixEnd_6120780 := by exact prefixLift 6120780
  have htrace : WordTrace (prefixWord ++ tailWord_6120780) baseStart_6120780 baseEnd_6120780 := by
    simpa [prefixWord, tailWord_6120780, baseEnd_6120780] using wordTrace_append hprefix tailTrace_6120780
  have hstable : (prefixWord ++ tailWord_6120780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120780).length < 2 ^ (prefixWord ++ tailWord_6120780).sum := by decide
  have hdescent : baseEnd_6120780 < baseStart_6120780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120781 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6120781 : Nat := 118140960795 + 6120781 * 2 ^ 59
def prefixEnd_6120781 : Nat := 4983230072969 + 3 ^ 40 * 6120781 * 2
def baseEnd_6120781 : Nat := 3142902633907322149888547

theorem tailTrace_6120781 : CollatzResearch.WordTrace tailWord_6120781 prefixEnd_6120781 3142902633907322149888547 := by
  unfold tailWord_6120781
  simp only [CollatzResearch.WordTrace]
  refine ⟨223243223238463258015650197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148828815492308838677100131 223243223238463258015650197)
  ·
    refine ⟨10464526089302965219483603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223243223238463258015650197 10464526089302965219483603)
    ·
      refine ⟨15696789133954447829225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10464526089302965219483603 15696789133954447829225405)
      ·
        refine ⟨5886295925232917935959527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15696789133954447829225405 5886295925232917935959527)
        ·
          refine ⟨8829443887849376903939291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886295925232917935959527 8829443887849376903939291)
          ·
            refine ⟨13244165831774065355908937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829443887849376903939291 13244165831774065355908937)
            ·
              refine ⟨9933124373830549016931703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13244165831774065355908937 9933124373830549016931703)
              ·
                refine ⟨14899686560745823525397555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9933124373830549016931703 14899686560745823525397555)
                ·
                  refine ⟨22349529841118735288096333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14899686560745823525397555 22349529841118735288096333)
                  ·
                    refine ⟨8381073690419525733036125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22349529841118735288096333 8381073690419525733036125)
                    ·
                      refine ⟨3142902633907322149888547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381073690419525733036125 3142902633907322149888547)
                      ·
                        rfl

theorem cell23_6120781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6120781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120781 prefixEnd_6120781 := by exact prefixLift 6120781
  have htrace : WordTrace (prefixWord ++ tailWord_6120781) baseStart_6120781 baseEnd_6120781 := by
    simpa [prefixWord, tailWord_6120781, baseEnd_6120781] using wordTrace_append hprefix tailTrace_6120781
  have hstable : (prefixWord ++ tailWord_6120781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120781).length < 2 ^ (prefixWord ++ tailWord_6120781).sum := by decide
  have hdescent : baseEnd_6120781 < baseStart_6120781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120787 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 4, 2]
def baseStart_6120787 : Nat := 118140960795 + 6120787 * 2 ^ 59
def prefixEnd_6120787 : Nat := 4983230072969 + 3 ^ 40 * 6120787 * 2
def baseEnd_6120787 : Nat := 3142905714791249126413519

theorem tailTrace_6120787 : CollatzResearch.WordTrace tailWord_6120787 prefixEnd_6120787 3142905714791249126413519 := by
  unfold tailWord_6120787
  simp only [CollatzResearch.WordTrace]
  refine ⟨223243442076441521040368615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148828961384294347360245743 223243442076441521040368615)
  ·
    refine ⟨334865163114662281560552923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223243442076441521040368615 334865163114662281560552923)
    ·
      refine ⟨502297744671993422340829385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334865163114662281560552923 502297744671993422340829385)
      ·
        refine ⟨376723308503995066755622039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502297744671993422340829385 376723308503995066755622039)
        ·
          refine ⟨565084962755992600133433059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376723308503995066755622039 565084962755992600133433059)
          ·
            refine ⟨847627444133988900200149589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565084962755992600133433059 847627444133988900200149589)
            ·
              refine ⟨9933134110945182424220503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 847627444133988900200149589 9933134110945182424220503)
              ·
                refine ⟨14899701166417773636330755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9933134110945182424220503 14899701166417773636330755)
                ·
                  refine ⟨22349551749626660454496133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14899701166417773636330755 22349551749626660454496133)
                  ·
                    refine ⟨4190540953054998835218025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22349551749626660454496133 4190540953054998835218025)
                    ·
                      refine ⟨3142905714791249126413519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190540953054998835218025 3142905714791249126413519)
                      ·
                        rfl

theorem cell23_6120787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4, 2].length) (baseStart_6120787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120787 prefixEnd_6120787 := by exact prefixLift 6120787
  have htrace : WordTrace (prefixWord ++ tailWord_6120787) baseStart_6120787 baseEnd_6120787 := by
    simpa [prefixWord, tailWord_6120787, baseEnd_6120787] using wordTrace_append hprefix tailTrace_6120787
  have hstable : (prefixWord ++ tailWord_6120787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120787).length < 2 ^ (prefixWord ++ tailWord_6120787).sum := by decide
  have hdescent : baseEnd_6120787 < baseStart_6120787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120793 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 9]
def baseStart_6120793 : Nat := 118140960795 + 6120793 * 2 ^ 59
def prefixEnd_6120793 : Nat := 4983230072969 + 3 ^ 40 * 6120793 * 2
def baseEnd_6120793 : Nat := 349212088408352900326499

theorem tailTrace_6120793 : CollatzResearch.WordTrace tailWord_6120793 prefixEnd_6120793 349212088408352900326499 := by
  unfold tailWord_6120793
  simp only [CollatzResearch.WordTrace]
  refine ⟨223243660914419784065087033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148829107276279856043391355 223243660914419784065087033)
  ·
    refine ⟨167432745685814838048815275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223243660914419784065087033 167432745685814838048815275)
    ·
      refine ⟨251149118528722257073222913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167432745685814838048815275 251149118528722257073222913)
      ·
        refine ⟨188361838896541692804917185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251149118528722257073222913 188361838896541692804917185)
        ·
          refine ⟨141271379172406269603687889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188361838896541692804917185 141271379172406269603687889)
          ·
            refine ⟨105953534379304702202765917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141271379172406269603687889 105953534379304702202765917)
            ·
              refine ⟨39732575392239263326037219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105953534379304702202765917 39732575392239263326037219)
              ·
                refine ⟨59598863088358894989055829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39732575392239263326037219 59598863088358894989055829)
                ·
                  refine ⟨349212088408352900326499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59598863088358894989055829 349212088408352900326499)
                  ·
                    rfl

theorem cell23_6120793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_6120793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120793 prefixEnd_6120793 := by exact prefixLift 6120793
  have htrace : WordTrace (prefixWord ++ tailWord_6120793) baseStart_6120793 baseEnd_6120793 := by
    simpa [prefixWord, tailWord_6120793, baseEnd_6120793] using wordTrace_append hprefix tailTrace_6120793
  have hstable : (prefixWord ++ tailWord_6120793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120793).length < 2 ^ (prefixWord ++ tailWord_6120793).sum := by decide
  have hdescent : baseEnd_6120793 < baseStart_6120793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120808 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6120808 : Nat := 118140960795 + 6120808 * 2 ^ 59
def prefixEnd_6120808 : Nat := 4983230072969 + 3 ^ 40 * 6120808 * 2
def baseEnd_6120808 : Nat := 3142916497884993544250923

theorem tailTrace_6120808 : CollatzResearch.WordTrace tailWord_6120808 prefixEnd_6120808 3142916497884993544250923 := by
  unfold tailWord_6120808
  simp only [CollatzResearch.WordTrace]
  refine ⟨111622104004682720813441539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148829472006243627751255385 111622104004682720813441539)
  ·
    refine ⟨167433156007024081220162309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111622104004682720813441539 167433156007024081220162309)
    ·
      refine ⟨31393716751317015228780433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167433156007024081220162309 31393716751317015228780433)
      ·
        refine ⟨23545287563487761421585325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31393716751317015228780433 23545287563487761421585325)
        ·
          refine ⟨8829482836307910533094497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23545287563487761421585325 8829482836307910533094497)
          ·
            refine ⟨6622112127230932899820873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8829482836307910533094497 6622112127230932899820873)
            ·
              refine ⟨4966584095423199674865655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6622112127230932899820873 4966584095423199674865655)
              ·
                refine ⟨7449876143134799512298483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966584095423199674865655 7449876143134799512298483)
                ·
                  refine ⟨11174814214702199268447725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449876143134799512298483 11174814214702199268447725)
                  ·
                    refine ⟨4190555330513324725667897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11174814214702199268447725 4190555330513324725667897)
                    ·
                      refine ⟨3142916497884993544250923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190555330513324725667897 3142916497884993544250923)
                      ·
                        rfl

theorem cell23_6120808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6120808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120808 prefixEnd_6120808 := by exact prefixLift 6120808
  have htrace : WordTrace (prefixWord ++ tailWord_6120808) baseStart_6120808 baseEnd_6120808 := by
    simpa [prefixWord, tailWord_6120808, baseEnd_6120808] using wordTrace_append hprefix tailTrace_6120808
  have hstable : (prefixWord ++ tailWord_6120808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120808).length < 2 ^ (prefixWord ++ tailWord_6120808).sum := by decide
  have hdescent : baseEnd_6120808 < baseStart_6120808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120821 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6120821 : Nat := 118140960795 + 6120821 * 2 ^ 59
def prefixEnd_6120821 : Nat := 4983230072969 + 3 ^ 40 * 6120821 * 2
def baseEnd_6120821 : Nat := 3142923173133501993388363

theorem tailTrace_6120821 : CollatzResearch.WordTrace tailWord_6120821 prefixEnd_6120821 3142923173133501993388363 := by
  unfold tailWord_6120821
  simp only [CollatzResearch.WordTrace]
  refine ⟨223244682158318344847106317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148829788105545563231404211 223244682158318344847106317)
  ·
    refine ⟨83716755809369379317664869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223244682158318344847106317 83716755809369379317664869)
    ·
      refine ⟨15696891714256758622062163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83716755809369379317664869 15696891714256758622062163)
      ·
        refine ⟨23545337571385137933093245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15696891714256758622062163 23545337571385137933093245)
        ·
          refine ⟨8829501589269426724909967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23545337571385137933093245 8829501589269426724909967)
          ·
            refine ⟨13244252383904140087364951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829501589269426724909967 13244252383904140087364951)
            ·
              refine ⟨19866378575856210131047427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244252383904140087364951 19866378575856210131047427)
              ·
                refine ⟨29799567863784315196571141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866378575856210131047427 29799567863784315196571141)
                ·
                  refine ⟨5587418974459559099357089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29799567863784315196571141 5587418974459559099357089)
                  ·
                    refine ⟨4190564230844669324517817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587418974459559099357089 4190564230844669324517817)
                    ·
                      refine ⟨3142923173133501993388363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190564230844669324517817 3142923173133501993388363)
                      ·
                        rfl

theorem cell23_6120821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6120821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120821 prefixEnd_6120821 := by exact prefixLift 6120821
  have htrace : WordTrace (prefixWord ++ tailWord_6120821) baseStart_6120821 baseEnd_6120821 := by
    simpa [prefixWord, tailWord_6120821, baseEnd_6120821] using wordTrace_append hprefix tailTrace_6120821
  have hstable : (prefixWord ++ tailWord_6120821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120821).length < 2 ^ (prefixWord ++ tailWord_6120821).sum := by decide
  have hdescent : baseEnd_6120821 < baseStart_6120821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120834 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6120834 : Nat := 118140960795 + 6120834 * 2 ^ 59
def prefixEnd_6120834 : Nat := 4983230072969 + 3 ^ 40 * 6120834 * 2
def baseEnd_6120834 : Nat := 3142929848382010442525803

theorem tailTrace_6120834 : CollatzResearch.WordTrace tailWord_6120834 prefixEnd_6120834 3142929848382010442525803 := by
  unfold tailWord_6120834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55811289076817812016832389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148830104204847498711553037 55811289076817812016832389)
  ·
    refine ⟨10464616701903339753156073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55811289076817812016832389 10464616701903339753156073)
    ·
      refine ⟨7848462526427504814867055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10464616701903339753156073 7848462526427504814867055)
      ·
        refine ⟨11772693789641257222300583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848462526427504814867055 11772693789641257222300583)
        ·
          refine ⟨17659040684461885833450875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772693789641257222300583 17659040684461885833450875)
          ·
            refine ⟨26488561026692828750176313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17659040684461885833450875 26488561026692828750176313)
            ·
              refine ⟨19866420770019621562632235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26488561026692828750176313 19866420770019621562632235)
              ·
                refine ⟨29799631155029432343948353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866420770019621562632235 29799631155029432343948353)
                ·
                  refine ⟨22349723366272074257961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29799631155029432343948353 22349723366272074257961265)
                  ·
                    refine ⟨16762292524704055693470949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22349723366272074257961265 16762292524704055693470949)
                    ·
                      refine ⟨3142929848382010442525803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16762292524704055693470949 3142929848382010442525803)
                      ·
                        rfl

theorem cell23_6120834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6120834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120834 prefixEnd_6120834 := by exact prefixLift 6120834
  have htrace : WordTrace (prefixWord ++ tailWord_6120834) baseStart_6120834 baseEnd_6120834 := by
    simpa [prefixWord, tailWord_6120834, baseEnd_6120834] using wordTrace_append hprefix tailTrace_6120834
  have hstable : (prefixWord ++ tailWord_6120834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120834).length < 2 ^ (prefixWord ++ tailWord_6120834).sum := by decide
  have hdescent : baseEnd_6120834 < baseStart_6120834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120840 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6120840 : Nat := 118140960795 + 6120840 * 2 ^ 59
def prefixEnd_6120840 : Nat := 4983230072969 + 3 ^ 40 * 6120840 * 2
def baseEnd_6120840 : Nat := 1047644309755312473016925

theorem tailTrace_6120840 : CollatzResearch.WordTrace tailWord_6120840 prefixEnd_6120840 1047644309755312473016925 := by
  unfold tailWord_6120840
  simp only [CollatzResearch.WordTrace]
  refine ⟨111622687572624755546023987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148830250096833007394698649 111622687572624755546023987)
  ·
    refine ⟨167434031358937133319035981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111622687572624755546023987 167434031358937133319035981)
    ·
      refine ⟨62787761759601424994638493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167434031358937133319035981 62787761759601424994638493)
      ·
        refine ⟨23545410659850534372989435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62787761759601424994638493 23545410659850534372989435)
        ·
          refine ⟨35318115989775801559484153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23545410659850534372989435 35318115989775801559484153)
          ·
            refine ⟨26488586992331851169613115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35318115989775801559484153 26488586992331851169613115)
            ·
              refine ⟨39732880488497776754419673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26488586992331851169613115 39732880488497776754419673)
              ·
                refine ⟨29799660366373332565814755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39732880488497776754419673 29799660366373332565814755)
                ·
                  refine ⟨44699490549559998848722133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29799660366373332565814755 44699490549559998848722133)
                  ·
                    refine ⟨1047644309755312473016925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44699490549559998848722133 1047644309755312473016925)
                    ·
                      rfl

theorem cell23_6120840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6120840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120840 prefixEnd_6120840 := by exact prefixLift 6120840
  have htrace : WordTrace (prefixWord ++ tailWord_6120840) baseStart_6120840 baseEnd_6120840 := by
    simpa [prefixWord, tailWord_6120840, baseEnd_6120840] using wordTrace_append hprefix tailTrace_6120840
  have hstable : (prefixWord ++ tailWord_6120840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120840).length < 2 ^ (prefixWord ++ tailWord_6120840).sum := by decide
  have hdescent : baseEnd_6120840 < baseStart_6120840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120880 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_6120880 : Nat := 118140960795 + 6120880 * 2 ^ 59
def prefixEnd_6120880 : Nat := 4983230072969 + 3 ^ 40 * 6120880 * 2
def baseEnd_6120880 : Nat := 3142953468492117262550591

theorem tailTrace_6120880 : CollatzResearch.WordTrace tailWord_6120880 prefixEnd_6120880 3142953468492117262550591 := by
  unfold tailWord_6120880
  simp only [CollatzResearch.WordTrace]
  refine ⟨111623417032552298961752047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148831222710069731949002729 111623417032552298961752047)
  ·
    refine ⟨167435125548828448442628071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111623417032552298961752047 167435125548828448442628071)
    ·
      refine ⟨251152688323242672663942107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167435125548828448442628071 251152688323242672663942107)
      ·
        refine ⟨376729032484864008995913161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251152688323242672663942107 376729032484864008995913161)
        ·
          refine ⟨282546774363648006746934871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376729032484864008995913161 282546774363648006746934871)
          ·
            refine ⟨423820161545472010120402307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282546774363648006746934871 423820161545472010120402307)
            ·
              refine ⟨635730242318208015180603461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423820161545472010120402307 635730242318208015180603461)
              ·
                refine ⟨119199420434664002846363149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635730242318208015180603461 119199420434664002846363149)
                ·
                  refine ⟨44699782662999001067386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119199420434664002846363149 44699782662999001067386181)
                  ·
                    refine ⟨8381209249312312700134909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44699782662999001067386181 8381209249312312700134909)
                    ·
                      refine ⟨3142953468492117262550591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381209249312312700134909 3142953468492117262550591)
                      ·
                        rfl

theorem cell23_6120880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_6120880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120880 prefixEnd_6120880 := by exact prefixLift 6120880
  have htrace : WordTrace (prefixWord ++ tailWord_6120880) baseStart_6120880 baseEnd_6120880 := by
    simpa [prefixWord, tailWord_6120880, baseEnd_6120880] using wordTrace_append hprefix tailTrace_6120880
  have hstable : (prefixWord ++ tailWord_6120880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120880).length < 2 ^ (prefixWord ++ tailWord_6120880).sum := by decide
  have hdescent : baseEnd_6120880 < baseStart_6120880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120961 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6120961 : Nat := 118140960795 + 6120961 * 2 ^ 59
def prefixEnd_6120961 : Nat := 4983230072969 + 3 ^ 40 * 6120961 * 2
def baseEnd_6120961 : Nat := 3142995060425131445637719

theorem tailTrace_6120961 : CollatzResearch.WordTrace tailWord_6120961 prefixEnd_6120961 3142995060425131445637719 := by
  unfold tailWord_6120961
  simp only [CollatzResearch.WordTrace]
  refine ⟨223249788377811148757202737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148833192251874099171468491 223249788377811148757202737)
  ·
    refine ⟨167437341283358361567902053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223249788377811148757202737 167437341283358361567902053)
    ·
      refine ⟨31394501490629692793981635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167437341283358361567902053 31394501490629692793981635)
      ·
        refine ⟨47091752235944539190972453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31394501490629692793981635 47091752235944539190972453)
        ·
          refine ⟨8829703544239601098307335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47091752235944539190972453 8829703544239601098307335)
          ·
            refine ⟨13244555316359401647461003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829703544239601098307335 13244555316359401647461003)
            ·
              refine ⟨19866832974539102471191505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244555316359401647461003 19866832974539102471191505)
              ·
                refine ⟨14900124730904326853393629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19866832974539102471191505 14900124730904326853393629)
                ·
                  refine ⟨5587546774089122570022611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14900124730904326853393629 5587546774089122570022611)
                  ·
                    refine ⟨8381320161133683855033917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5587546774089122570022611 8381320161133683855033917)
                    ·
                      refine ⟨3142995060425131445637719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381320161133683855033917 3142995060425131445637719)
                      ·
                        rfl

theorem cell23_6120961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6120961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120961 prefixEnd_6120961 := by exact prefixLift 6120961
  have htrace : WordTrace (prefixWord ++ tailWord_6120961) baseStart_6120961 baseEnd_6120961 := by
    simpa [prefixWord, tailWord_6120961, baseEnd_6120961] using wordTrace_append hprefix tailTrace_6120961
  have hstable : (prefixWord ++ tailWord_6120961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120961).length < 2 ^ (prefixWord ++ tailWord_6120961).sum := by decide
  have hdescent : baseEnd_6120961 < baseStart_6120961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120977 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_6120977 : Nat := 118140960795 + 6120977 * 2 ^ 59
def prefixEnd_6120977 : Nat := 4983230072969 + 3 ^ 40 * 6120977 * 2
def baseEnd_6120977 : Nat := 1047667758705201127679215

theorem tailTrace_6120977 : CollatzResearch.WordTrace tailWord_6120977 prefixEnd_6120977 1047667758705201127679215 := by
  unfold tailWord_6120977
  simp only [CollatzResearch.WordTrace]
  refine ⟨223250371945753183489785185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148833581297168788993190123 223250371945753183489785185)
  ·
    refine ⟨167437778959314887617338889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223250371945753183489785185 167437778959314887617338889)
    ·
      refine ⟨125578334219486165713004167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167437778959314887617338889 125578334219486165713004167)
      ·
        refine ⟨188367501329229248569506251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125578334219486165713004167 188367501329229248569506251)
        ·
          refine ⟨282551251993843872854259377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188367501329229248569506251 282551251993843872854259377)
          ·
            refine ⟨211913438995382904640694533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282551251993843872854259377 211913438995382904640694533)
            ·
              refine ⟨39733769811634294620130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211913438995382904640694533 39733769811634294620130225)
              ·
                refine ⟨29800327358725720965097669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39733769811634294620130225 29800327358725720965097669)
                ·
                  refine ⟨5587561379761072680955813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29800327358725720965097669 5587561379761072680955813)
                  ·
                    refine ⟨1047667758705201127679215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5587561379761072680955813 1047667758705201127679215)
                    ·
                      rfl

theorem cell23_6120977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_6120977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120977 prefixEnd_6120977 := by exact prefixLift 6120977
  have htrace : WordTrace (prefixWord ++ tailWord_6120977) baseStart_6120977 baseEnd_6120977 := by
    simpa [prefixWord, tailWord_6120977, baseEnd_6120977] using wordTrace_append hprefix tailTrace_6120977
  have hstable : (prefixWord ++ tailWord_6120977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120977).length < 2 ^ (prefixWord ++ tailWord_6120977).sum := by decide
  have hdescent : baseEnd_6120977 < baseStart_6120977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6120981 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_6120981 : Nat := 118140960795 + 6120981 * 2 ^ 59
def prefixEnd_6120981 : Nat := 4983230072969 + 3 ^ 40 * 6120981 * 2
def baseEnd_6120981 : Nat := 1047668443346073789129209

theorem tailTrace_6120981 : CollatzResearch.WordTrace tailWord_6120981 prefixEnd_6120981 1047668443346073789129209 := by
  unfold tailWord_6120981
  simp only [CollatzResearch.WordTrace]
  refine ⟨223250517837738692172930797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148833678558492461448620531 223250517837738692172930797)
  ·
    refine ⟨83718944189152009564849049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223250517837738692172930797 83718944189152009564849049)
    ·
      refine ⟨62789208141864007173636787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83718944189152009564849049 62789208141864007173636787)
      ·
        refine ⟨94183812212796010760455181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62789208141864007173636787 94183812212796010760455181)
        ·
          refine ⟨35318929579798504035170693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94183812212796010760455181 35318929579798504035170693)
          ·
            refine ⟨6622299296212219506594505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35318929579798504035170693 6622299296212219506594505)
            ·
              refine ⟨4966724472159164629945879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6622299296212219506594505 4966724472159164629945879)
              ·
                refine ⟨7450086708238746944918819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966724472159164629945879 7450086708238746944918819)
                ·
                  refine ⟨11175130062358120417378229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450086708238746944918819 11175130062358120417378229)
                  ·
                    refine ⟨1047668443346073789129209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11175130062358120417378229 1047668443346073789129209)
                    ·
                      rfl

theorem cell23_6120981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_6120981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6120981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6120981 prefixEnd_6120981 := by exact prefixLift 6120981
  have htrace : WordTrace (prefixWord ++ tailWord_6120981) baseStart_6120981 baseEnd_6120981 := by
    simpa [prefixWord, tailWord_6120981, baseEnd_6120981] using wordTrace_append hprefix tailTrace_6120981
  have hstable : (prefixWord ++ tailWord_6120981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6120981).length < 2 ^ (prefixWord ++ tailWord_6120981).sum := by decide
  have hdescent : baseEnd_6120981 < baseStart_6120981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6120981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121011 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 2, 4]
def baseStart_6121011 : Nat := 118140960795 + 6121011 * 2 ^ 59
def prefixEnd_6121011 : Nat := 4983230072969 + 3 ^ 40 * 6121011 * 2
def baseEnd_6121011 : Nat := 1047673578152618750004163

theorem tailTrace_6121011 : CollatzResearch.WordTrace tailWord_6121011 prefixEnd_6121011 1047673578152618750004163 := by
  unfold tailWord_6121011
  simp only [CollatzResearch.WordTrace]
  refine ⟨223251612027630007296522887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148834408018420004864348591 223251612027630007296522887)
  ·
    refine ⟨334877418041445010944784331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223251612027630007296522887 334877418041445010944784331)
    ·
      refine ⟨502316127062167516417176497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334877418041445010944784331 502316127062167516417176497)
      ·
        refine ⟨376737095296625637312882373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502316127062167516417176497 376737095296625637312882373)
        ·
          refine ⟨70638205368117306996165445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376737095296625637312882373 70638205368117306996165445)
          ·
            refine ⟨13244663506521995061781021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70638205368117306996165445 13244663506521995061781021)
            ·
              refine ⟨4966748814945748148167883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13244663506521995061781021 4966748814945748148167883)
              ·
                refine ⟨7450123222418622222251825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966748814945748148167883 7450123222418622222251825)
                ·
                  refine ⟨5587592416813966666688869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7450123222418622222251825 5587592416813966666688869)
                  ·
                    refine ⟨1047673578152618750004163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5587592416813966666688869 1047673578152618750004163)
                    ·
                      rfl

theorem cell23_6121011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 4].length) (baseStart_6121011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121011 prefixEnd_6121011 := by exact prefixLift 6121011
  have htrace : WordTrace (prefixWord ++ tailWord_6121011) baseStart_6121011 baseEnd_6121011 := by
    simpa [prefixWord, tailWord_6121011, baseEnd_6121011] using wordTrace_append hprefix tailTrace_6121011
  have hstable : (prefixWord ++ tailWord_6121011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121011).length < 2 ^ (prefixWord ++ tailWord_6121011).sum := by decide
  have hdescent : baseEnd_6121011 < baseStart_6121011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121034 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_6121034 : Nat := 118140960795 + 6121034 * 2 ^ 59
def prefixEnd_6121034 : Nat := 4983230072969 + 3 ^ 40 * 6121034 * 2
def baseEnd_6121034 : Nat := 3143032544512909660024883

theorem tailTrace_6121034 : CollatzResearch.WordTrace tailWord_6121034 prefixEnd_6121034 3143032544512909660024883 := by
  unfold tailWord_6121034
  simp only [CollatzResearch.WordTrace]
  refine ⟨55813112726636670556152539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148834967271031121483073437 55813112726636670556152539)
  ·
    refine ⟨83719669089955005834228809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55813112726636670556152539 83719669089955005834228809)
    ·
      refine ⟨62789751817466254375671607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83719669089955005834228809 62789751817466254375671607)
      ·
        refine ⟨94184627726199381563507411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62789751817466254375671607 94184627726199381563507411)
        ·
          refine ⟨141276941589299072345261117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94184627726199381563507411 141276941589299072345261117)
          ·
            refine ⟨52978853095987152129472919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141276941589299072345261117 52978853095987152129472919)
            ·
              refine ⟨79468279643980728194209379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52978853095987152129472919 79468279643980728194209379)
              ·
                refine ⟨119202419465971092291314069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79468279643980728194209379 119202419465971092291314069)
                ·
                  refine ⟨5587613412467394951155347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119202419465971092291314069 5587613412467394951155347)
                  ·
                    refine ⟨8381420118701092426733021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5587613412467394951155347 8381420118701092426733021)
                    ·
                      refine ⟨3143032544512909660024883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381420118701092426733021 3143032544512909660024883)
                      ·
                        rfl

theorem cell23_6121034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_6121034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121034 prefixEnd_6121034 := by exact prefixLift 6121034
  have htrace : WordTrace (prefixWord ++ tailWord_6121034) baseStart_6121034 baseEnd_6121034 := by
    simpa [prefixWord, tailWord_6121034, baseEnd_6121034] using wordTrace_append hprefix tailTrace_6121034
  have hstable : (prefixWord ++ tailWord_6121034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121034).length < 2 ^ (prefixWord ++ tailWord_6121034).sum := by decide
  have hdescent : baseEnd_6121034 < baseStart_6121034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121052 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_6121052 : Nat := 118140960795 + 6121052 * 2 ^ 59
def prefixEnd_6121052 : Nat := 4983230072969 + 3 ^ 40 * 6121052 * 2
def baseEnd_6121052 : Nat := 3143041787164690589599801

theorem tailTrace_6121052 : CollatzResearch.WordTrace tailWord_6121052 prefixEnd_6121052 3143041787164690589599801 := by
  unfold tailWord_6121052
  simp only [CollatzResearch.WordTrace]
  refine ⟨111626553710240735649382705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148835404946987647532510273 111626553710240735649382705)
  ·
    refine ⟨83719915282680551737037029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111626553710240735649382705 83719915282680551737037029)
    ·
      refine ⟨15697484115502603450694443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83719915282680551737037029 15697484115502603450694443)
      ·
        refine ⟨23546226173253905176041665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15697484115502603450694443 23546226173253905176041665)
        ·
          refine ⟨17659669629940428882031249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23546226173253905176041665 17659669629940428882031249)
          ·
            refine ⟨13244752222455321661523437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17659669629940428882031249 13244752222455321661523437)
            ·
              refine ⟨4966782083420745623071289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13244752222455321661523437 4966782083420745623071289)
              ·
                refine ⟨3725086562565559217303467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966782083420745623071289 3725086562565559217303467)
                ·
                  refine ⟨5587629843848338825955201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725086562565559217303467 5587629843848338825955201)
                  ·
                    refine ⟨4190722382886254119466401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587629843848338825955201 4190722382886254119466401)
                    ·
                      refine ⟨3143041787164690589599801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190722382886254119466401 3143041787164690589599801)
                      ·
                        rfl

theorem cell23_6121052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_6121052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121052 prefixEnd_6121052 := by exact prefixLift 6121052
  have htrace : WordTrace (prefixWord ++ tailWord_6121052) baseStart_6121052 baseEnd_6121052 := by
    simpa [prefixWord, tailWord_6121052, baseEnd_6121052] using wordTrace_append hprefix tailTrace_6121052
  have hstable : (prefixWord ++ tailWord_6121052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121052).length < 2 ^ (prefixWord ++ tailWord_6121052).sum := by decide
  have hdescent : baseEnd_6121052 < baseStart_6121052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121057 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6121057 : Nat := 118140960795 + 6121057 * 2 ^ 59
def prefixEnd_6121057 : Nat := 4983230072969 + 3 ^ 40 * 6121057 * 2
def baseEnd_6121057 : Nat := 3143044354567963070037277

theorem tailTrace_6121057 : CollatzResearch.WordTrace tailWord_6121057 prefixEnd_6121057 3143044354567963070037277 := by
  unfold tailWord_6121057
  simp only [CollatzResearch.WordTrace]
  refine ⟨223253289785463357152697425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148835526523642238101798283 223253289785463357152697425)
  ·
    refine ⟨167439967339097517864523069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223253289785463357152697425 167439967339097517864523069)
    ·
      refine ⟨62789987752161569199196151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167439967339097517864523069 62789987752161569199196151)
      ·
        refine ⟨94184981628242353798794227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62789987752161569199196151 94184981628242353798794227)
        ·
          refine ⟨141277472442363530698191341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94184981628242353798794227 141277472442363530698191341)
          ·
            refine ⟨52979052165886324011821753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141277472442363530698191341 52979052165886324011821753)
            ·
              refine ⟨39734289124414743008866315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52979052165886324011821753 39734289124414743008866315)
              ·
                refine ⟨59601433686622114513299473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39734289124414743008866315 59601433686622114513299473)
                ·
                  refine ⟨44701075264966585884974605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59601433686622114513299473 44701075264966585884974605)
                  ·
                    refine ⟨16762903224362469706865477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44701075264966585884974605 16762903224362469706865477)
                    ·
                      refine ⟨3143044354567963070037277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16762903224362469706865477 3143044354567963070037277)
                      ·
                        rfl

theorem cell23_6121057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6121057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121057 prefixEnd_6121057 := by exact prefixLift 6121057
  have htrace : WordTrace (prefixWord ++ tailWord_6121057) baseStart_6121057 baseEnd_6121057 := by
    simpa [prefixWord, tailWord_6121057, baseEnd_6121057] using wordTrace_append hprefix tailTrace_6121057
  have hstable : (prefixWord ++ tailWord_6121057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121057).length < 2 ^ (prefixWord ++ tailWord_6121057).sum := by decide
  have hdescent : baseEnd_6121057 < baseStart_6121057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121078 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6121078 : Nat := 118140960795 + 6121078 * 2 ^ 59
def prefixEnd_6121078 : Nat := 4983230072969 + 3 ^ 40 * 6121078 * 2
def baseEnd_6121078 : Nat := 3143055137661707487874681

theorem tailTrace_6121078 : CollatzResearch.WordTrace tailWord_6121078 prefixEnd_6121078 3143055137661707487874681 := by
  unfold tailWord_6121078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13953378482399204858700743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148836037145591518492807925 13953378482399204858700743)
  ·
    refine ⟨20930067723598807288051115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13953378482399204858700743 20930067723598807288051115)
    ·
      refine ⟨31395101585398210932076673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20930067723598807288051115 31395101585398210932076673)
      ·
        refine ⟨23546326189048658199057505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31395101585398210932076673 23546326189048658199057505)
        ·
          refine ⟨17659744641786493649293129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23546326189048658199057505 17659744641786493649293129)
          ·
            refine ⟨13244808481339870236969847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17659744641786493649293129 13244808481339870236969847)
            ·
              refine ⟨19867212722009805355454771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13244808481339870236969847 19867212722009805355454771)
              ·
                refine ⟨29800819083014708033182157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19867212722009805355454771 29800819083014708033182157)
                ·
                  refine ⟨11175307156130515512443309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29800819083014708033182157 11175307156130515512443309)
                  ·
                    refine ⟨4190740183548943317166241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11175307156130515512443309 4190740183548943317166241)
                    ·
                      refine ⟨3143055137661707487874681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190740183548943317166241 3143055137661707487874681)
                      ·
                        rfl

theorem cell23_6121078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6121078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121078 prefixEnd_6121078 := by exact prefixLift 6121078
  have htrace : WordTrace (prefixWord ++ tailWord_6121078) baseStart_6121078 baseEnd_6121078 := by
    simpa [prefixWord, tailWord_6121078, baseEnd_6121078] using wordTrace_append hprefix tailTrace_6121078
  have hstable : (prefixWord ++ tailWord_6121078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121078).length < 2 ^ (prefixWord ++ tailWord_6121078).sum := by decide
  have hdescent : baseEnd_6121078 < baseStart_6121078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121117 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6121117 : Nat := 118140960795 + 6121117 * 2 ^ 59
def prefixEnd_6121117 : Nat := 4983230072969 + 3 ^ 40 * 6121117 * 2
def baseEnd_6121117 : Nat := 3143075163407232835287001

theorem tailTrace_6121117 : CollatzResearch.WordTrace tailWord_6121117 prefixEnd_6121117 3143075163407232835287001 := by
  unfold tailWord_6121117
  simp only [CollatzResearch.WordTrace]
  refine ⟨223255478165245987399881605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148836985443497324933254403 223255478165245987399881605)
  ·
    refine ⟨41860402155983622637477801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223255478165245987399881605 41860402155983622637477801)
    ·
      refine ⟨31395301616987716978108351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41860402155983622637477801 31395301616987716978108351)
      ·
        refine ⟨47092952425481575467162527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31395301616987716978108351 47092952425481575467162527)
        ·
          refine ⟨70639428638222363200743791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47092952425481575467162527 70639428638222363200743791)
          ·
            refine ⟨105959142957333544801115687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70639428638222363200743791 105959142957333544801115687)
            ·
              refine ⟨158938714436000317201673531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105959142957333544801115687 158938714436000317201673531)
              ·
                refine ⟨238408071654000475802510297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158938714436000317201673531 238408071654000475802510297)
                ·
                  refine ⟨178806053740500356851882723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238408071654000475802510297 178806053740500356851882723)
                  ·
                    refine ⟨268209080610750535277824085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178806053740500356851882723 268209080610750535277824085)
                    ·
                      refine ⟨3143075163407232835287001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268209080610750535277824085 3143075163407232835287001)
                      ·
                        rfl

theorem cell23_6121117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6121117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121117 prefixEnd_6121117 := by exact prefixLift 6121117
  have htrace : WordTrace (prefixWord ++ tailWord_6121117) baseStart_6121117 baseEnd_6121117 := by
    simpa [prefixWord, tailWord_6121117, baseEnd_6121117] using wordTrace_append hprefix tailTrace_6121117
  have hstable : (prefixWord ++ tailWord_6121117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121117).length < 2 ^ (prefixWord ++ tailWord_6121117).sum := by decide
  have hdescent : baseEnd_6121117 < baseStart_6121117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121124 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_6121124 : Nat := 118140960795 + 6121124 * 2 ^ 59
def prefixEnd_6121124 : Nat := 4983230072969 + 3 ^ 40 * 6121124 * 2
def baseEnd_6121124 : Nat := 3143078757771814307899469

theorem tailTrace_6121124 : CollatzResearch.WordTrace tailWord_6121124 prefixEnd_6121124 3143078757771814307899469 := by
  unfold tailWord_6121124
  simp only [CollatzResearch.WordTrace]
  refine ⟨111627866738110313797693213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148837155650813751730257617 111627866738110313797693213)
  ·
    refine ⟨41860450026791367674134955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111627866738110313797693213 41860450026791367674134955)
    ·
      refine ⟨62790675040187051511202433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41860450026791367674134955 62790675040187051511202433)
      ·
        refine ⟨47093006280140288633401825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62790675040187051511202433 47093006280140288633401825)
        ·
          refine ⟨35319754710105216475051369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47093006280140288633401825 35319754710105216475051369)
          ·
            refine ⟨26489816032578912356288527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35319754710105216475051369 26489816032578912356288527)
            ·
              refine ⟨39734724048868368534432791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26489816032578912356288527 39734724048868368534432791)
              ·
                refine ⟨59602086073302552801649187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39734724048868368534432791 59602086073302552801649187)
                ·
                  refine ⟨89403129109953829202473781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59602086073302552801649187 89403129109953829202473781)
                  ·
                    refine ⟨8381543354058171487731917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89403129109953829202473781 8381543354058171487731917)
                    ·
                      refine ⟨3143078757771814307899469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381543354058171487731917 3143078757771814307899469)
                      ·
                        rfl

theorem cell23_6121124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_6121124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121124 prefixEnd_6121124 := by exact prefixLift 6121124
  have htrace : WordTrace (prefixWord ++ tailWord_6121124) baseStart_6121124 baseEnd_6121124 := by
    simpa [prefixWord, tailWord_6121124, baseEnd_6121124] using wordTrace_append hprefix tailTrace_6121124
  have hstable : (prefixWord ++ tailWord_6121124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121124).length < 2 ^ (prefixWord ++ tailWord_6121124).sum := by decide
  have hdescent : baseEnd_6121124 < baseStart_6121124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121167 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_6121167 : Nat := 118140960795 + 6121167 * 2 ^ 59
def prefixEnd_6121167 : Nat := 4983230072969 + 3 ^ 40 * 6121167 * 2
def baseEnd_6121167 : Nat := 3143100837439957639661771

theorem tailTrace_6121167 : CollatzResearch.WordTrace tailWord_6121167 prefixEnd_6121167 3143100837439957639661771 := by
  unfold tailWord_6121167
  simp only [CollatzResearch.WordTrace]
  refine ⟨223257301815064845939201755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148838201210043230626134503 223257301815064845939201755)
  ·
    refine ⟨334885952722597268908802633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223257301815064845939201755 334885952722597268908802633)
    ·
      refine ⟨251164464541947951681601975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334885952722597268908802633 251164464541947951681601975)
      ·
        refine ⟨376746696812921927522402963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251164464541947951681601975 376746696812921927522402963)
        ·
          refine ⟨565120045219382891283604445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376746696812921927522402963 565120045219382891283604445)
          ·
            refine ⟨211920016957268584231351667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565120045219382891283604445 211920016957268584231351667)
            ·
              refine ⟨317880025435902876347027501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211920016957268584231351667 317880025435902876347027501)
              ·
                refine ⟨119205009538463578630135313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317880025435902876347027501 119205009538463578630135313)
                ·
                  refine ⟨89403757153847683972601485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119205009538463578630135313 89403757153847683972601485)
                  ·
                    refine ⟨33526408932692881489725557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89403757153847683972601485 33526408932692881489725557)
                    ·
                      refine ⟨3143100837439957639661771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33526408932692881489725557 3143100837439957639661771)
                      ·
                        rfl

theorem cell23_6121167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_6121167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121167 prefixEnd_6121167 := by exact prefixLift 6121167
  have htrace : WordTrace (prefixWord ++ tailWord_6121167) baseStart_6121167 baseEnd_6121167 := by
    simpa [prefixWord, tailWord_6121167, baseEnd_6121167] using wordTrace_append hprefix tailTrace_6121167
  have hstable : (prefixWord ++ tailWord_6121167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121167).length < 2 ^ (prefixWord ++ tailWord_6121167).sum := by decide
  have hdescent : baseEnd_6121167 < baseStart_6121167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121184 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_6121184 : Nat := 118140960795 + 6121184 * 2 ^ 59
def prefixEnd_6121184 : Nat := 4983230072969 + 3 ^ 40 * 6121184 * 2
def baseEnd_6121184 : Nat := 3143109566611084073149193

theorem tailTrace_6121184 : CollatzResearch.WordTrace tailWord_6121184 prefixEnd_6121184 3143109566611084073149193 := by
  unfold tailWord_6121184
  simp only [CollatzResearch.WordTrace]
  refine ⟨111628960928001628921285303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148838614570668838561713737 111628960928001628921285303)
  ·
    refine ⟨167443441392002443381927955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111628960928001628921285303 167443441392002443381927955)
    ·
      refine ⟨251165162088003665072891933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167443441392002443381927955 251165162088003665072891933)
      ·
        refine ⟨94186935783001374402334475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251165162088003665072891933 94186935783001374402334475)
        ·
          refine ⟨141280403674502061603501713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94186935783001374402334475 141280403674502061603501713)
          ·
            refine ⟨105960302755876546202626285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141280403674502061603501713 105960302755876546202626285)
            ·
              refine ⟨39735113533453704825984857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105960302755876546202626285 39735113533453704825984857)
              ·
                refine ⟨29801335150090278619488643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39735113533453704825984857 29801335150090278619488643)
                ·
                  refine ⟨44702002725135417929232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29801335150090278619488643 44702002725135417929232965)
                  ·
                    refine ⟨8381625510962890861731181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44702002725135417929232965 8381625510962890861731181)
                    ·
                      refine ⟨3143109566611084073149193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381625510962890861731181 3143109566611084073149193)
                      ·
                        rfl

theorem cell23_6121184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_6121184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121184 prefixEnd_6121184 := by exact prefixLift 6121184
  have htrace : WordTrace (prefixWord ++ tailWord_6121184) baseStart_6121184 baseEnd_6121184 := by
    simpa [prefixWord, tailWord_6121184, baseEnd_6121184] using wordTrace_append hprefix tailTrace_6121184
  have hstable : (prefixWord ++ tailWord_6121184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121184).length < 2 ^ (prefixWord ++ tailWord_6121184).sum := by decide
  have hdescent : baseEnd_6121184 < baseStart_6121184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121218 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6121218 : Nat := 118140960795 + 6121218 * 2 ^ 59
def prefixEnd_6121218 : Nat := 4983230072969 + 3 ^ 40 * 6121218 * 2
def baseEnd_6121218 : Nat := 3143127024953336940124037

theorem tailTrace_6121218 : CollatzResearch.WordTrace tailWord_6121218 prefixEnd_6121218 3143127024953336940124037 := by
  unfold tailWord_6121218
  simp only [CollatzResearch.WordTrace]
  refine ⟨55814790484470020412327077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148839441291920054432872205 55814790484470020412327077)
  ·
    refine ⟨10465273215838128827311327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55814790484470020412327077 10465273215838128827311327)
    ·
      refine ⟨15697909823757193240966991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10465273215838128827311327 15697909823757193240966991)
      ·
        refine ⟨23546864735635789861450487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15697909823757193240966991 23546864735635789861450487)
        ·
          refine ⟨35320297103453684792175731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23546864735635789861450487 35320297103453684792175731)
          ·
            refine ⟨52980445655180527188263597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35320297103453684792175731 52980445655180527188263597)
            ·
              refine ⟨19867667120692697695598849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52980445655180527188263597 19867667120692697695598849)
              ·
                refine ⟨14900750340519523271699137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19867667120692697695598849 14900750340519523271699137)
                ·
                  refine ⟨11175562755389642453774353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14900750340519523271699137 11175562755389642453774353)
                  ·
                    refine ⟨8381672066542231840330765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11175562755389642453774353 8381672066542231840330765)
                    ·
                      refine ⟨3143127024953336940124037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381672066542231840330765 3143127024953336940124037)
                      ·
                        rfl

theorem cell23_6121218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6121218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121218 prefixEnd_6121218 := by exact prefixLift 6121218
  have htrace : WordTrace (prefixWord ++ tailWord_6121218) baseStart_6121218 baseEnd_6121218 := by
    simpa [prefixWord, tailWord_6121218, baseEnd_6121218] using wordTrace_append hprefix tailTrace_6121218
  have hstable : (prefixWord ++ tailWord_6121218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121218).length < 2 ^ (prefixWord ++ tailWord_6121218).sum := by decide
  have hdescent : baseEnd_6121218 < baseStart_6121218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121231 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_6121231 : Nat := 118140960795 + 6121231 * 2 ^ 59
def prefixEnd_6121231 : Nat := 4983230072969 + 3 ^ 40 * 6121231 * 2
def baseEnd_6121231 : Nat := 3143133700201845389261477

theorem tailTrace_6121231 : CollatzResearch.WordTrace tailWord_6121231 prefixEnd_6121231 3143133700201845389261477 := by
  unfold tailWord_6121231
  simp only [CollatzResearch.WordTrace]
  refine ⟨223259636086832984869531547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148839757391221989913021031 223259636086832984869531547)
  ·
    refine ⟨334889454130249477304297321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223259636086832984869531547 334889454130249477304297321)
    ·
      refine ⟨251167090597687107978222991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334889454130249477304297321 251167090597687107978222991)
      ·
        refine ⟨376750635896530661967334487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251167090597687107978222991 376750635896530661967334487)
        ·
          refine ⟨565125953844795992951001731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376750635896530661967334487 565125953844795992951001731)
          ·
            refine ⟨847688930767193989426502597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565125953844795992951001731 847688930767193989426502597)
            ·
              refine ⟨158941674518848873017469237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 847688930767193989426502597 158941674518848873017469237)
              ·
                refine ⟨14900781986142081845387741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158941674518848873017469237 14900781986142081845387741)
                ·
                  refine ⟨5587793244803280692020403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14900781986142081845387741 5587793244803280692020403)
                  ·
                    refine ⟨8381689867204921038030605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5587793244803280692020403 8381689867204921038030605)
                    ·
                      refine ⟨3143133700201845389261477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381689867204921038030605 3143133700201845389261477)
                      ·
                        rfl

theorem cell23_6121231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_6121231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121231 prefixEnd_6121231 := by exact prefixLift 6121231
  have htrace : WordTrace (prefixWord ++ tailWord_6121231) baseStart_6121231 baseEnd_6121231 := by
    simpa [prefixWord, tailWord_6121231, baseEnd_6121231] using wordTrace_append hprefix tailTrace_6121231
  have hstable : (prefixWord ++ tailWord_6121231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121231).length < 2 ^ (prefixWord ++ tailWord_6121231).sum := by decide
  have hdescent : baseEnd_6121231 < baseStart_6121231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121251 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 1, 5]
def baseStart_6121251 : Nat := 118140960795 + 6121251 * 2 ^ 59
def prefixEnd_6121251 : Nat := 4983230072969 + 3 ^ 40 * 6121251 * 2
def baseEnd_6121251 : Nat := 1047714656604978437003795

theorem tailTrace_6121251 : CollatzResearch.WordTrace tailWord_6121251 prefixEnd_6121251 1047714656604978437003795 := by
  unfold tailWord_6121251
  simp only [CollatzResearch.WordTrace]
  refine ⟨223260365546760528285259607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148840243697840352190173071 223260365546760528285259607)
  ·
    refine ⟨334890548320140792427889411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223260365546760528285259607 334890548320140792427889411)
    ·
      refine ⟨502335822480211188641834117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334890548320140792427889411 502335822480211188641834117)
      ·
        refine ⟨94187966715039597870343897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502335822480211188641834117 94187966715039597870343897)
        ·
          refine ⟨70640975036279698402757923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94187966715039597870343897 70640975036279698402757923)
          ·
            refine ⟨105961462554419547604136885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70640975036279698402757923 105961462554419547604136885)
            ·
              refine ⟨9933887114476832587887833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105961462554419547604136885 9933887114476832587887833)
              ·
                refine ⟨7450415335857624440915875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9933887114476832587887833 7450415335857624440915875)
                ·
                  refine ⟨11175623003786436661373813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450415335857624440915875 11175623003786436661373813)
                  ·
                    refine ⟨1047714656604978437003795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11175623003786436661373813 1047714656604978437003795)
                    ·
                      rfl

theorem cell23_6121251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 5].length) (baseStart_6121251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121251 prefixEnd_6121251 := by exact prefixLift 6121251
  have htrace : WordTrace (prefixWord ++ tailWord_6121251) baseStart_6121251 baseEnd_6121251 := by
    simpa [prefixWord, tailWord_6121251, baseEnd_6121251] using wordTrace_append hprefix tailTrace_6121251
  have hstable : (prefixWord ++ tailWord_6121251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121251).length < 2 ^ (prefixWord ++ tailWord_6121251).sum := by decide
  have hdescent : baseEnd_6121251 < baseStart_6121251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121298 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_6121298 : Nat := 118140960795 + 6121298 * 2 ^ 59
def prefixEnd_6121298 : Nat := 4983230072969 + 3 ^ 40 * 6121298 * 2
def baseEnd_6121298 : Nat := 1047722701135232209041223

theorem tailTrace_6121298 : CollatzResearch.WordTrace tailWord_6121298 prefixEnd_6121298 1047722701135232209041223 := by
  unfold tailWord_6121298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55815519944397563828055137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148841386518393503541480365 55815519944397563828055137)
  ·
    refine ⟨41861639958298172871041353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55815519944397563828055137 41861639958298172871041353)
    ·
      refine ⟨31396229968723629653281015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41861639958298172871041353 31396229968723629653281015)
      ·
        refine ⟨47094344953085444479921523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31396229968723629653281015 47094344953085444479921523)
        ·
          refine ⟨70641517429628166719882285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47094344953085444479921523 70641517429628166719882285)
          ·
            refine ⟨26490569036110562519955857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70641517429628166719882285 26490569036110562519955857)
            ·
              refine ⟨19867926777082921889966893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26490569036110562519955857 19867926777082921889966893)
              ·
                refine ⟨7450472541406095708737585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19867926777082921889966893 7450472541406095708737585)
                ·
                  refine ⟨5587854406054571781553189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7450472541406095708737585 5587854406054571781553189)
                  ·
                    refine ⟨1047722701135232209041223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5587854406054571781553189 1047722701135232209041223)
                    ·
                      rfl

theorem cell23_6121298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_6121298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121298 prefixEnd_6121298 := by exact prefixLift 6121298
  have htrace : WordTrace (prefixWord ++ tailWord_6121298) baseStart_6121298 baseEnd_6121298 := by
    simpa [prefixWord, tailWord_6121298, baseEnd_6121298] using wordTrace_append hprefix tailTrace_6121298
  have hstable : (prefixWord ++ tailWord_6121298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121298).length < 2 ^ (prefixWord ++ tailWord_6121298).sum := by decide
  have hdescent : baseEnd_6121298 < baseStart_6121298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121301 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6121301 : Nat := 118140960795 + 6121301 * 2 ^ 59
def prefixEnd_6121301 : Nat := 4983230072969 + 3 ^ 40 * 6121301 * 2
def baseEnd_6121301 : Nat := 3143169643847660115386155

theorem tailTrace_6121301 : CollatzResearch.WordTrace tailWord_6121301 prefixEnd_6121301 3143169643847660115386155 := by
  unfold tailWord_6121301
  simp only [CollatzResearch.WordTrace]
  refine ⟨223262189196579386824579757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148841459464386257883053171 223262189196579386824579757)
  ·
    refine ⟨83723320948717270059217409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223262189196579386824579757 83723320948717270059217409)
    ·
      refine ⟨62792490711537952544413057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83723320948717270059217409 62792490711537952544413057)
      ·
        refine ⟨47094368033653464408309793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62792490711537952544413057 47094368033653464408309793)
        ·
          refine ⟨35320776025240098306232345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47094368033653464408309793 35320776025240098306232345)
          ·
            refine ⟨26490582018930073729674259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35320776025240098306232345 26490582018930073729674259)
            ·
              refine ⟨39735873028395110594511389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26490582018930073729674259 39735873028395110594511389)
              ·
                refine ⟨14900952385648166472941771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39735873028395110594511389 14900952385648166472941771)
                ·
                  refine ⟨22351428578472249709412657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14900952385648166472941771 22351428578472249709412657)
                  ·
                    refine ⟨16763571433854187282059493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22351428578472249709412657 16763571433854187282059493)
                    ·
                      refine ⟨3143169643847660115386155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16763571433854187282059493 3143169643847660115386155)
                      ·
                        rfl

theorem cell23_6121301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6121301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121301 prefixEnd_6121301 := by exact prefixLift 6121301
  have htrace : WordTrace (prefixWord ++ tailWord_6121301) baseStart_6121301 baseEnd_6121301 := by
    simpa [prefixWord, tailWord_6121301, baseEnd_6121301] using wordTrace_append hprefix tailTrace_6121301
  have hstable : (prefixWord ++ tailWord_6121301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121301).length < 2 ^ (prefixWord ++ tailWord_6121301).sum := by decide
  have hdescent : baseEnd_6121301 < baseStart_6121301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121311 : List Nat := [1, 1, 2, 3, 1, 5, 3, 7]
def baseStart_6121311 : Nat := 118140960795 + 6121311 * 2 ^ 59
def prefixEnd_6121311 : Nat := 4983230072969 + 3 ^ 40 * 6121311 * 2
def baseEnd_6121311 : Nat := 116413880690896484305967

theorem tailTrace_6121311 : CollatzResearch.WordTrace tailWord_6121311 prefixEnd_6121311 116413880690896484305967 := by
  unfold tailWord_6121311
  simp only [CollatzResearch.WordTrace]
  refine ⟨223262553926543158532443787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148841702617695439021629191 223262553926543158532443787)
  ·
    refine ⟨334893830889814737798665681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223262553926543158532443787 334893830889814737798665681)
    ·
      refine ⟨251170373167361053348999261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334893830889814737798665681 251170373167361053348999261)
      ·
        refine ⟨94188889937760395005874723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251170373167361053348999261 94188889937760395005874723)
        ·
          refine ⟨141283334906640592508812085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94188889937760395005874723 141283334906640592508812085)
          ·
            refine ⟨13245312647497555547701133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141283334906640592508812085 13245312647497555547701133)
            ·
              refine ⟨4966992242811583330387925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13245312647497555547701133 4966992242811583330387925)
              ·
                refine ⟨116413880690896484305967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4966992242811583330387925 116413880690896484305967)
                ·
                  rfl

theorem cell23_6121311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 7].length) (baseStart_6121311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121311 prefixEnd_6121311 := by exact prefixLift 6121311
  have htrace : WordTrace (prefixWord ++ tailWord_6121311) baseStart_6121311 baseEnd_6121311 := by
    simpa [prefixWord, tailWord_6121311, baseEnd_6121311] using wordTrace_append hprefix tailTrace_6121311
  have hstable : (prefixWord ++ tailWord_6121311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121311).length < 2 ^ (prefixWord ++ tailWord_6121311).sum := by decide
  have hdescent : baseEnd_6121311 < baseStart_6121311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121325 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6121325 : Nat := 118140960795 + 6121325 * 2 ^ 59
def prefixEnd_6121325 : Nat := 4983230072969 + 3 ^ 40 * 6121325 * 2
def baseEnd_6121325 : Nat := 3143181967383368021486045

theorem tailTrace_6121325 : CollatzResearch.WordTrace tailWord_6121325 prefixEnd_6121325 3143181967383368021486045 := by
  unfold tailWord_6121325
  simp only [CollatzResearch.WordTrace]
  refine ⟨223263064548492438923453429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148842043032328292615635619 223263064548492438923453429)
  ·
    refine ⟨20930912301421166149073759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223263064548492438923453429 20930912301421166149073759)
    ·
      refine ⟨31396368452131749223610639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20930912301421166149073759 31396368452131749223610639)
      ·
        refine ⟨47094552678197623835415959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31396368452131749223610639 47094552678197623835415959)
        ·
          refine ⟨70641829017296435753123939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47094552678197623835415959 70641829017296435753123939)
          ·
            refine ⟨105962743525944653629685909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70641829017296435753123939 105962743525944653629685909)
            ·
              refine ⟨4967003602778655638891527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105962743525944653629685909 4967003602778655638891527)
              ·
                refine ⟨7450505404167983458337291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967003602778655638891527 7450505404167983458337291)
                ·
                  refine ⟨11175758106251975187505937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450505404167983458337291 11175758106251975187505937)
                  ·
                    refine ⟨8381818579688981390629453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11175758106251975187505937 8381818579688981390629453)
                    ·
                      refine ⟨3143181967383368021486045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8381818579688981390629453 3143181967383368021486045)
                      ·
                        rfl

theorem cell23_6121325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6121325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121325 prefixEnd_6121325 := by exact prefixLift 6121325
  have htrace : WordTrace (prefixWord ++ tailWord_6121325) baseStart_6121325 baseEnd_6121325 := by
    simpa [prefixWord, tailWord_6121325, baseEnd_6121325] using wordTrace_append hprefix tailTrace_6121325
  have hstable : (prefixWord ++ tailWord_6121325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121325).length < 2 ^ (prefixWord ++ tailWord_6121325).sum := by decide
  have hdescent : baseEnd_6121325 < baseStart_6121325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121348 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_6121348 : Nat := 118140960795 + 6121348 * 2 ^ 59
def prefixEnd_6121348 : Nat := 4983230072969 + 3 ^ 40 * 6121348 * 2
def baseEnd_6121348 : Nat := 3143193777438421431498439

theorem tailTrace_6121348 : CollatzResearch.WordTrace tailWord_6121348 prefixEnd_6121348 3143193777438421431498439 := by
  unfold tailWord_6121348
  simp only [CollatzResearch.WordTrace]
  refine ⟨111631951713704556925770349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148842602284939409234360465 111631951713704556925770349)
  ·
    refine ⟨41861981892639208847163881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111631951713704556925770349 41861981892639208847163881)
    ·
      refine ⟨31396486419479406635372911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41861981892639208847163881 31396486419479406635372911)
      ·
        refine ⟨47094729629219109953059367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31396486419479406635372911 47094729629219109953059367)
        ·
          refine ⟨70642094443828664929589051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47094729629219109953059367 70642094443828664929589051)
          ·
            refine ⟨105963141665742997394383577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70642094443828664929589051 105963141665742997394383577)
            ·
              refine ⟨79472356249307248045787683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105963141665742997394383577 79472356249307248045787683)
              ·
                refine ⟨119208534373960872068681525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79472356249307248045787683 119208534373960872068681525)
                ·
                  refine ⟨11175800097558831756438893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119208534373960872068681525 11175800097558831756438893)
                  ·
                    refine ⟨4190925036584561908664585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11175800097558831756438893 4190925036584561908664585)
                    ·
                      refine ⟨3143193777438421431498439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190925036584561908664585 3143193777438421431498439)
                      ·
                        rfl

theorem cell23_6121348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_6121348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121348 prefixEnd_6121348 := by exact prefixLift 6121348
  have htrace : WordTrace (prefixWord ++ tailWord_6121348) baseStart_6121348 baseEnd_6121348 := by
    simpa [prefixWord, tailWord_6121348, baseEnd_6121348] using wordTrace_append hprefix tailTrace_6121348
  have hstable : (prefixWord ++ tailWord_6121348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121348).length < 2 ^ (prefixWord ++ tailWord_6121348).sum := by decide
  have hdescent : baseEnd_6121348 < baseStart_6121348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121365 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_6121365 : Nat := 118140960795 + 6121365 * 2 ^ 59
def prefixEnd_6121365 : Nat := 4983230072969 + 3 ^ 40 * 6121365 * 2
def baseEnd_6121365 : Nat := 3143202506609547864985861

theorem tailTrace_6121365 : CollatzResearch.WordTrace tailWord_6121365 prefixEnd_6121365 3143202506609547864985861 := by
  unfold tailWord_6121365
  simp only [CollatzResearch.WordTrace]
  refine ⟨223264523468347525754909549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148843015645565017169939699 223264523468347525754909549)
  ·
    refine ⟨83724196300630322158091081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223264523468347525754909549 83724196300630322158091081)
    ·
      refine ⟨62793147225472741618568311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83724196300630322158091081 62793147225472741618568311)
      ·
        refine ⟨94189720838209112427852467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62793147225472741618568311 94189720838209112427852467)
        ·
          refine ⟨141284581257313668641778701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94189720838209112427852467 141284581257313668641778701)
          ·
            refine ⟨52981717971492625740667013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141284581257313668641778701 52981717971492625740667013)
            ·
              refine ⟨9934072119654867326375065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52981717971492625740667013 9934072119654867326375065)
              ·
                refine ⟨7450554089741150494781299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9934072119654867326375065 7450554089741150494781299)
                ·
                  refine ⟨11175831134611725742171949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450554089741150494781299 11175831134611725742171949)
                  ·
                    refine ⟨4190936675479397153314481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11175831134611725742171949 4190936675479397153314481)
                    ·
                      refine ⟨3143202506609547864985861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190936675479397153314481 3143202506609547864985861)
                      ·
                        rfl

theorem cell23_6121365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_6121365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121365 prefixEnd_6121365 := by exact prefixLift 6121365
  have htrace : WordTrace (prefixWord ++ tailWord_6121365) baseStart_6121365 baseEnd_6121365 := by
    simpa [prefixWord, tailWord_6121365, baseEnd_6121365] using wordTrace_append hprefix tailTrace_6121365
  have hstable : (prefixWord ++ tailWord_6121365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121365).length < 2 ^ (prefixWord ++ tailWord_6121365).sum := by decide
  have hdescent : baseEnd_6121365 < baseStart_6121365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121390 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6121390 : Nat := 118140960795 + 6121390 * 2 ^ 59
def prefixEnd_6121390 : Nat := 4983230072969 + 3 ^ 40 * 6121390 * 2
def baseEnd_6121390 : Nat := 3143215343625910267173247

theorem tailTrace_6121390 : CollatzResearch.WordTrace tailWord_6121390 prefixEnd_6121390 3143215343625910267173247 := by
  unfold tailWord_6121390
  simp only [CollatzResearch.WordTrace]
  refine ⟨27908179411657119378071203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148843623528837970016379749 27908179411657119378071203)
  ·
    refine ⟨41862269117485679067106805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27908179411657119378071203 41862269117485679067106805)
    ·
      refine ⟨3924587729764282412541263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41862269117485679067106805 3924587729764282412541263)
      ·
        refine ⟨5886881594646423618811895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924587729764282412541263 5886881594646423618811895)
        ·
          refine ⟨8830322391969635428217843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886881594646423618811895 8830322391969635428217843)
          ·
            refine ⟨13245483587954453142326765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830322391969635428217843 13245483587954453142326765)
            ·
              refine ⟨4967056345482919928372537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13245483587954453142326765 4967056345482919928372537)
              ·
                refine ⟨3725292259112189946279403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4967056345482919928372537 3725292259112189946279403)
                ·
                  refine ⟨5587938388668284919419105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725292259112189946279403 5587938388668284919419105)
                  ·
                    refine ⟨4190953791501213689564329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587938388668284919419105 4190953791501213689564329)
                    ·
                      refine ⟨3143215343625910267173247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190953791501213689564329 3143215343625910267173247)
                      ·
                        rfl

theorem cell23_6121390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6121390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121390 prefixEnd_6121390 := by exact prefixLift 6121390
  have htrace : WordTrace (prefixWord ++ tailWord_6121390) baseStart_6121390 baseEnd_6121390 := by
    simpa [prefixWord, tailWord_6121390, baseEnd_6121390] using wordTrace_append hprefix tailTrace_6121390
  have hstable : (prefixWord ++ tailWord_6121390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121390).length < 2 ^ (prefixWord ++ tailWord_6121390).sum := by decide
  have hdescent : baseEnd_6121390 < baseStart_6121390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121395 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 2, 2, 2]
def baseStart_6121395 : Nat := 118140960795 + 6121395 * 2 ^ 59
def prefixEnd_6121395 : Nat := 4983230072969 + 3 ^ 40 * 6121395 * 2
def baseEnd_6121395 : Nat := 3143217911029182747610723

theorem tailTrace_6121395 : CollatzResearch.WordTrace tailWord_6121395 prefixEnd_6121395 3143217911029182747610723 := by
  unfold tailWord_6121395
  simp only [CollatzResearch.WordTrace]
  refine ⟨223265617658238840878501639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148843745105492560585667759 223265617658238840878501639)
  ·
    refine ⟨334898426487358261317752459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223265617658238840878501639 334898426487358261317752459)
    ·
      refine ⟨502347639731037391976628689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334898426487358261317752459 502347639731037391976628689)
      ·
        refine ⟨376760729798278043982471517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502347639731037391976628689 376760729798278043982471517)
        ·
          refine ⟨141285273674354266493426819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376760729798278043982471517 141285273674354266493426819)
          ·
            refine ⟨211927910511531399740140229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141285273674354266493426819 211927910511531399740140229)
            ·
              refine ⟨39736483220912137451276293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211927910511531399740140229 39736483220912137451276293)
              ·
                refine ⟨7450590603921025772114305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39736483220912137451276293 7450590603921025772114305)
                ·
                  refine ⟨5587942952940769329085729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7450590603921025772114305 5587942952940769329085729)
                  ·
                    refine ⟨4190957214705576996814297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587942952940769329085729 4190957214705576996814297)
                    ·
                      refine ⟨3143217911029182747610723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4190957214705576996814297 3143217911029182747610723)
                      ·
                        rfl

theorem cell23_6121395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2, 2].length) (baseStart_6121395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121395 prefixEnd_6121395 := by exact prefixLift 6121395
  have htrace : WordTrace (prefixWord ++ tailWord_6121395) baseStart_6121395 baseEnd_6121395 := by
    simpa [prefixWord, tailWord_6121395, baseEnd_6121395] using wordTrace_append hprefix tailTrace_6121395
  have hstable : (prefixWord ++ tailWord_6121395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121395).length < 2 ^ (prefixWord ++ tailWord_6121395).sum := by decide
  have hdescent : baseEnd_6121395 < baseStart_6121395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121441 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6121441 : Nat := 118140960795 + 6121441 * 2 ^ 59
def prefixEnd_6121441 : Nat := 4983230072969 + 3 ^ 40 * 6121441 * 2
def baseEnd_6121441 : Nat := 3143241531139289567635511

theorem tailTrace_6121441 : CollatzResearch.WordTrace tailWord_6121441 prefixEnd_6121441 3143241531139289567635511 := by
  unfold tailWord_6121441
  simp only [CollatzResearch.WordTrace]
  refine ⟨223267295416072190734676177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148844863610714793823117451 223267295416072190734676177)
  ·
    refine ⟨167450471562054143051007133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223267295416072190734676177 167450471562054143051007133)
    ·
      refine ⟨62793926835770303644127675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167450471562054143051007133 62793926835770303644127675)
      ·
        refine ⟨94190890253655455466191513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62793926835770303644127675 94190890253655455466191513)
        ·
          refine ⟨70643167690241591599643635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94190890253655455466191513 70643167690241591599643635)
          ·
            refine ⟨105964751535362387399465453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70643167690241591599643635 105964751535362387399465453)
            ·
              refine ⟨39736781825760895274799545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105964751535362387399465453 39736781825760895274799545)
              ·
                refine ⟨29802586369320671456099659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39736781825760895274799545 29802586369320671456099659)
                ·
                  refine ⟨44703879553981007184149489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29802586369320671456099659 44703879553981007184149489)
                  ·
                    refine ⟨33527909665485755388112117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44703879553981007184149489 33527909665485755388112117)
                    ·
                      refine ⟨3143241531139289567635511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33527909665485755388112117 3143241531139289567635511)
                      ·
                        rfl

theorem cell23_6121441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6121441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121441 prefixEnd_6121441 := by exact prefixLift 6121441
  have htrace : WordTrace (prefixWord ++ tailWord_6121441) baseStart_6121441 baseEnd_6121441 := by
    simpa [prefixWord, tailWord_6121441, baseEnd_6121441] using wordTrace_append hprefix tailTrace_6121441
  have hstable : (prefixWord ++ tailWord_6121441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121441).length < 2 ^ (prefixWord ++ tailWord_6121441).sum := by decide
  have hdescent : baseEnd_6121441 < baseStart_6121441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121482 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_6121482 : Nat := 118140960795 + 6121482 * 2 ^ 59
def prefixEnd_6121482 : Nat := 4983230072969 + 3 ^ 40 * 6121482 * 2
def baseEnd_6121482 : Nat := 1047754194615374635740941

theorem tailTrace_6121482 : CollatzResearch.WordTrace tailWord_6121482 prefixEnd_6121482 1047754194615374635740941 := by
  unfold tailWord_6121482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55817197702230913684229675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148845860539282436491279133 55817197702230913684229675)
  ·
    refine ⟨83725796553346370526344513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55817197702230913684229675 83725796553346370526344513)
    ·
      refine ⟨62794347415009777894758385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83725796553346370526344513 62794347415009777894758385)
      ·
        refine ⟨47095760561257333421068789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62794347415009777894758385 47095760561257333421068789)
        ·
          refine ⟨4415227552617875008225199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47095760561257333421068789 4415227552617875008225199)
          ·
            refine ⟨6622841328926812512337799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415227552617875008225199 6622841328926812512337799)
            ·
              refine ⟨9934261993390218768506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6622841328926812512337799 9934261993390218768506699)
              ·
                refine ⟨14901392990085328152760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9934261993390218768506699 14901392990085328152760049)
                ·
                  refine ⟨11176044742563996114570037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14901392990085328152760049 11176044742563996114570037)
                  ·
                    refine ⟨1047754194615374635740941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11176044742563996114570037 1047754194615374635740941)
                    ·
                      rfl

theorem cell23_6121482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_6121482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121482 prefixEnd_6121482 := by exact prefixLift 6121482
  have htrace : WordTrace (prefixWord ++ tailWord_6121482) baseStart_6121482 baseEnd_6121482 := by
    simpa [prefixWord, tailWord_6121482, baseEnd_6121482] using wordTrace_append hprefix tailTrace_6121482
  have hstable : (prefixWord ++ tailWord_6121482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121482).length < 2 ^ (prefixWord ++ tailWord_6121482).sum := by decide
  have hdescent : baseEnd_6121482 < baseStart_6121482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121535 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_6121535 : Nat := 118140960795 + 6121535 * 2 ^ 59
def prefixEnd_6121535 : Nat := 4983230072969 + 3 ^ 40 * 6121535 * 2
def baseEnd_6121535 : Nat := 3143289798320812199860079

theorem tailTrace_6121535 : CollatzResearch.WordTrace tailWord_6121535 prefixEnd_6121535 3143289798320812199860079 := by
  unfold tailWord_6121535
  simp only [CollatzResearch.WordTrace]
  refine ⟨223270723877731644788598059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148847149251821096525732039 223270723877731644788598059)
  ·
    refine ⟨334906085816597467182897089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223270723877731644788598059 334906085816597467182897089)
    ·
      refine ⟨251179564362448100387172817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334906085816597467182897089 251179564362448100387172817)
      ·
        refine ⟨188384673271836075290379613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251179564362448100387172817 188384673271836075290379613)
        ·
          refine ⟨70644252476938528233892355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188384673271836075290379613 70644252476938528233892355)
          ·
            refine ⟨105966378715407792350838533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70644252476938528233892355 105966378715407792350838533)
            ·
              refine ⟨19868696009138961065782225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105966378715407792350838533 19868696009138961065782225)
              ·
                refine ⟨14901522006854220799336669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19868696009138961065782225 14901522006854220799336669)
                ·
                  refine ⟨5588070752570332799751251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14901522006854220799336669 5588070752570332799751251)
                  ·
                    refine ⟨8382106128855499199626877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588070752570332799751251 8382106128855499199626877)
                    ·
                      refine ⟨3143289798320812199860079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382106128855499199626877 3143289798320812199860079)
                      ·
                        rfl

theorem cell23_6121535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_6121535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121535 prefixEnd_6121535 := by exact prefixLift 6121535
  have htrace : WordTrace (prefixWord ++ tailWord_6121535) baseStart_6121535 baseEnd_6121535 := by
    simpa [prefixWord, tailWord_6121535, baseEnd_6121535] using wordTrace_append hprefix tailTrace_6121535
  have hstable : (prefixWord ++ tailWord_6121535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121535).length < 2 ^ (prefixWord ++ tailWord_6121535).sum := by decide
  have hdescent : baseEnd_6121535 < baseStart_6121535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121545 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 2, 3, 2]
def baseStart_6121545 : Nat := 118140960795 + 6121545 * 2 ^ 59
def prefixEnd_6121545 : Nat := 4983230072969 + 3 ^ 40 * 6121545 * 2
def baseEnd_6121545 : Nat := 3143294933127357160735033

theorem tailTrace_6121545 : CollatzResearch.WordTrace tailWord_6121545 prefixEnd_6121545 3143294933127357160735033 := by
  unfold tailWord_6121545
  simp only [CollatzResearch.WordTrace]
  refine ⟨223271088607695416496462089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148847392405130277664308059 223271088607695416496462089)
  ·
    refine ⟨167453316455771562372346567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223271088607695416496462089 167453316455771562372346567)
    ·
      refine ⟨251179974683657343558519851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167453316455771562372346567 251179974683657343558519851)
      ·
        refine ⟨376769962025486015337779777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251179974683657343558519851 376769962025486015337779777)
        ·
          refine ⟨282577471519114511503334833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376769962025486015337779777 282577471519114511503334833)
          ·
            refine ⟨211933103639335883627501125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282577471519114511503334833 211933103639335883627501125)
            ·
              refine ⟨39737456932375478180156461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211933103639335883627501125 39737456932375478180156461)
              ·
                refine ⟨14901546349640804317558673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39737456932375478180156461 14901546349640804317558673)
                ·
                  refine ⟨11176159762230603238169005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14901546349640804317558673 11176159762230603238169005)
                  ·
                    refine ⟨4191059910836476214313377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11176159762230603238169005 4191059910836476214313377)
                    ·
                      refine ⟨3143294933127357160735033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191059910836476214313377 3143294933127357160735033)
                      ·
                        rfl

theorem cell23_6121545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3, 2].length) (baseStart_6121545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121545 prefixEnd_6121545 := by exact prefixLift 6121545
  have htrace : WordTrace (prefixWord ++ tailWord_6121545) baseStart_6121545 baseEnd_6121545 := by
    simpa [prefixWord, tailWord_6121545, baseEnd_6121545] using wordTrace_append hprefix tailTrace_6121545
  have hstable : (prefixWord ++ tailWord_6121545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121545).length < 2 ^ (prefixWord ++ tailWord_6121545).sum := by decide
  have hdescent : baseEnd_6121545 < baseStart_6121545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121585 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_6121585 : Nat := 118140960795 + 6121585 * 2 ^ 59
def prefixEnd_6121585 : Nat := 4983230072969 + 3 ^ 40 * 6121585 * 2
def baseEnd_6121585 : Nat := 1047771824117845668078283

theorem tailTrace_6121585 : CollatzResearch.WordTrace tailWord_6121585 prefixEnd_6121585 1047771824117845668078283 := by
  unfold tailWord_6121585
  simp only [CollatzResearch.WordTrace]
  refine ⟨223272547527550503327918209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148848365018367002218612139 223272547527550503327918209)
  ·
    refine ⟨167454410645662877495938657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223272547527550503327918209 167454410645662877495938657)
    ·
      refine ⟨125590807984247158121953993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167454410645662877495938657 125590807984247158121953993)
      ·
        refine ⟨94193105988185368591465495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125590807984247158121953993 94193105988185368591465495)
        ·
          refine ⟨141289658982278052887198243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94193105988185368591465495 141289658982278052887198243)
          ·
            refine ⟨211934488473417079330797365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141289658982278052887198243 211934488473417079330797365)
            ·
              refine ⟨19868858294382851187262253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211934488473417079330797365 19868858294382851187262253)
              ·
                refine ⟨7450821860393569195223345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19868858294382851187262253 7450821860393569195223345)
                ·
                  refine ⟨5588116395295176896417509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7450821860393569195223345 5588116395295176896417509)
                  ·
                    refine ⟨1047771824117845668078283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588116395295176896417509 1047771824117845668078283)
                    ·
                      rfl

theorem cell23_6121585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_6121585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121585 prefixEnd_6121585 := by exact prefixLift 6121585
  have htrace : WordTrace (prefixWord ++ tailWord_6121585) baseStart_6121585 baseEnd_6121585 := by
    simpa [prefixWord, tailWord_6121585, baseEnd_6121585] using wordTrace_append hprefix tailTrace_6121585
  have hstable : (prefixWord ++ tailWord_6121585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121585).length < 2 ^ (prefixWord ++ tailWord_6121585).sum := by decide
  have hdescent : baseEnd_6121585 < baseStart_6121585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121605 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_6121605 : Nat := 118140960795 + 6121605 * 2 ^ 59
def prefixEnd_6121605 : Nat := 4983230072969 + 3 ^ 40 * 6121605 * 2
def baseEnd_6121605 : Nat := 3143325741966626925984757

theorem tailTrace_6121605 : CollatzResearch.WordTrace tailWord_6121605 prefixEnd_6121605 3143325741966626925984757 := by
  unfold tailWord_6121605
  simp only [CollatzResearch.WordTrace]
  refine ⟨223273276987478046743646269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148848851324985364495764179 223273276987478046743646269)
  ·
    refine ⟨83727478870304267528867351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223273276987478046743646269 83727478870304267528867351)
    ·
      refine ⟨125591218305456401293301027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83727478870304267528867351 125591218305456401293301027)
      ·
        refine ⟨188386827458184601939951541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125591218305456401293301027 188386827458184601939951541)
        ·
          refine ⟨17661265074204806431870457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188386827458184601939951541 17661265074204806431870457)
          ·
            refine ⟨13245948805653604823902843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17661265074204806431870457 13245948805653604823902843)
            ·
              refine ⟨19868923208480407235854265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245948805653604823902843 19868923208480407235854265)
              ·
                refine ⟨14901692406360305426890699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19868923208480407235854265 14901692406360305426890699)
                ·
                  refine ⟨22352538609540458140336049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14901692406360305426890699 22352538609540458140336049)
                  ·
                    refine ⟨16764403957155343605252037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22352538609540458140336049 16764403957155343605252037)
                    ·
                      refine ⟨3143325741966626925984757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16764403957155343605252037 3143325741966626925984757)
                      ·
                        rfl

theorem cell23_6121605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_6121605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121605 prefixEnd_6121605 := by exact prefixLift 6121605
  have htrace : WordTrace (prefixWord ++ tailWord_6121605) baseStart_6121605 baseEnd_6121605 := by
    simpa [prefixWord, tailWord_6121605, baseEnd_6121605] using wordTrace_append hprefix tailTrace_6121605
  have hstable : (prefixWord ++ tailWord_6121605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121605).length < 2 ^ (prefixWord ++ tailWord_6121605).sum := by decide
  have hdescent : baseEnd_6121605 < baseStart_6121605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121609 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 1, 2, 2]
def baseStart_6121609 : Nat := 118140960795 + 6121609 * 2 ^ 59
def prefixEnd_6121609 : Nat := 4983230072969 + 3 ^ 40 * 6121609 * 2
def baseEnd_6121609 : Nat := 3143327795889244910334739

theorem tailTrace_6121609 : CollatzResearch.WordTrace tailWord_6121609 prefixEnd_6121609 3143327795889244910334739 := by
  unfold tailWord_6121609
  simp only [CollatzResearch.WordTrace]
  refine ⟨223273422879463555426791881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148848948586309036951194587 223273422879463555426791881)
  ·
    refine ⟨167455067159597666570093911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223273422879463555426791881 167455067159597666570093911)
    ·
      refine ⟨251182600739396499855140867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167455067159597666570093911 251182600739396499855140867)
      ·
        refine ⟨376773901109094749782711301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251182600739396499855140867 376773901109094749782711301)
        ·
          refine ⟨70645106457955265584258369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376773901109094749782711301 70645106457955265584258369)
          ·
            refine ⟨52983829843466449188193777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70645106457955265584258369 52983829843466449188193777)
            ·
              refine ⟨39737872382599836891145333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52983829843466449188193777 39737872382599836891145333)
              ·
                refine ⟨3725425535868734708544875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39737872382599836891145333 3725425535868734708544875)
                ·
                  refine ⟨5588138303803102062817313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725425535868734708544875 5588138303803102062817313)
                  ·
                    refine ⟨4191103727852326547112985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5588138303803102062817313 4191103727852326547112985)
                    ·
                      refine ⟨3143327795889244910334739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191103727852326547112985 3143327795889244910334739)
                      ·
                        rfl

theorem cell23_6121609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 2, 2].length) (baseStart_6121609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121609 prefixEnd_6121609 := by exact prefixLift 6121609
  have htrace : WordTrace (prefixWord ++ tailWord_6121609) baseStart_6121609 baseEnd_6121609 := by
    simpa [prefixWord, tailWord_6121609, baseEnd_6121609] using wordTrace_append hprefix tailTrace_6121609
  have hstable : (prefixWord ++ tailWord_6121609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121609).length < 2 ^ (prefixWord ++ tailWord_6121609).sum := by decide
  have hdescent : baseEnd_6121609 < baseStart_6121609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121620 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6121620 : Nat := 118140960795 + 6121620 * 2 ^ 59
def prefixEnd_6121620 : Nat := 4983230072969 + 3 ^ 40 * 6121620 * 2
def baseEnd_6121620 : Nat := 3143333444176444367297189

theorem tailTrace_6121620 : CollatzResearch.WordTrace tailWord_6121620 prefixEnd_6121620 3143333444176444367297189 := by
  unfold tailWord_6121620
  simp only [CollatzResearch.WordTrace]
  refine ⟨111636912041211852152721157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148849216054949136203628209 111636912041211852152721157)
  ·
    refine ⟨20931921007727222278635217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111636912041211852152721157 20931921007727222278635217)
    ·
      refine ⟨15698940755795416708976413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20931921007727222278635217 15698940755795416708976413)
      ·
        refine ⟨5887102783423281265866155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15698940755795416708976413 5887102783423281265866155)
        ·
          refine ⟨8830654175134921898799233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887102783423281265866155 8830654175134921898799233)
          ·
            refine ⟨6622990631351191424099425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8830654175134921898799233 6622990631351191424099425)
            ·
              refine ⟨4967242973513393568074569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6622990631351191424099425 4967242973513393568074569)
              ·
                refine ⟨3725432230135045176055927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4967242973513393568074569 3725432230135045176055927)
                ·
                  refine ⟨5588148345202567764083891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725432230135045176055927 5588148345202567764083891)
                  ·
                    refine ⟨8382222517803851646125837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588148345202567764083891 8382222517803851646125837)
                    ·
                      refine ⟨3143333444176444367297189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382222517803851646125837 3143333444176444367297189)
                      ·
                        rfl

theorem cell23_6121620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6121620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121620 prefixEnd_6121620 := by exact prefixLift 6121620
  have htrace : WordTrace (prefixWord ++ tailWord_6121620) baseStart_6121620 baseEnd_6121620 := by
    simpa [prefixWord, tailWord_6121620, baseEnd_6121620] using wordTrace_append hprefix tailTrace_6121620
  have hstable : (prefixWord ++ tailWord_6121620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121620).length < 2 ^ (prefixWord ++ tailWord_6121620).sum := by decide
  have hdescent : baseEnd_6121620 < baseStart_6121620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121625 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_6121625 : Nat := 118140960795 + 6121625 * 2 ^ 59
def prefixEnd_6121625 : Nat := 4983230072969 + 3 ^ 40 * 6121625 * 2
def baseEnd_6121625 : Nat := 3143336011579716847734665

theorem tailTrace_6121625 : CollatzResearch.WordTrace tailWord_6121625 prefixEnd_6121625 3143336011579716847734665 := by
  unfold tailWord_6121625
  simp only [CollatzResearch.WordTrace]
  refine ⟨223274006447405590159374329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148849337631603726772916219 223274006447405590159374329)
  ·
    refine ⟨167455504835554192619530747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223274006447405590159374329 167455504835554192619530747)
    ·
      refine ⟨251183257253331288929296121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167455504835554192619530747 251183257253331288929296121)
      ·
        refine ⟨188387442939998466696972091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251183257253331288929296121 188387442939998466696972091)
        ·
          refine ⟨282581164409997700045458137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188387442939998466696972091 282581164409997700045458137)
          ·
            refine ⟨211935873307498275034093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282581164409997700045458137 211935873307498275034093603)
            ·
              refine ⟨317903809961247412551140405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211935873307498275034093603 317903809961247412551140405)
              ·
                refine ⟨29803482183866944926669413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317903809961247412551140405 29803482183866944926669413)
                ·
                  refine ⟨5588152909475052173750515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29803482183866944926669413 5588152909475052173750515)
                  ·
                    refine ⟨8382229364212578260625773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588152909475052173750515 8382229364212578260625773)
                    ·
                      refine ⟨3143336011579716847734665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382229364212578260625773 3143336011579716847734665)
                      ·
                        rfl

theorem cell23_6121625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_6121625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121625 prefixEnd_6121625 := by exact prefixLift 6121625
  have htrace : WordTrace (prefixWord ++ tailWord_6121625) baseStart_6121625 baseEnd_6121625 := by
    simpa [prefixWord, tailWord_6121625, baseEnd_6121625] using wordTrace_append hprefix tailTrace_6121625
  have hstable : (prefixWord ++ tailWord_6121625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121625).length < 2 ^ (prefixWord ++ tailWord_6121625).sum := by decide
  have hdescent : baseEnd_6121625 < baseStart_6121625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
