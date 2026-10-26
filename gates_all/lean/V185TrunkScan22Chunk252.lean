import V185TrunkScan22Chunk251

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2247181 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2247181 : Nat := 118140960795 + 2247181 * 2 ^ 59
def prefixEnd_2247181 : Nat := 4983230072969 + 3 ^ 40 * 2247181 * 2
def baseEnd_2247181 : Nat := 769255980434185085135273

theorem tailTrace_2247181 : CollatzResearch.WordTrace tailWord_2247181 prefixEnd_2247181 769255980434185085135273 := by
  unfold tailWord_2247181
  simp only [CollatzResearch.WordTrace]
  refine ⟨81961424471854499804989397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54640949647902999869992931 81961424471854499804989397)
  ·
    refine ⟨1920970886059089839179439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81961424471854499804989397 1920970886059089839179439)
    ·
      refine ⟨2881456329088634758769159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920970886059089839179439 2881456329088634758769159)
      ·
        refine ⟨4322184493632952138153739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881456329088634758769159 4322184493632952138153739)
        ·
          refine ⟨6483276740449428207230609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322184493632952138153739 6483276740449428207230609)
          ·
            refine ⟨4862457555337071155422957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483276740449428207230609 4862457555337071155422957)
            ·
              refine ⟨1823421583251401683283609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4862457555337071155422957 1823421583251401683283609)
              ·
                refine ⟨1367566187438551262462707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823421583251401683283609 1367566187438551262462707)
                ·
                  refine ⟨2051349281157826893694061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367566187438551262462707 2051349281157826893694061)
                  ·
                    refine ⟨769255980434185085135273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051349281157826893694061 769255980434185085135273)
                    ·
                      rfl

theorem cell22_2247181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2247181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247181 prefixEnd_2247181 := by exact prefixLift 2247181
  have htrace : WordTrace (prefixWord ++ tailWord_2247181) baseStart_2247181 baseEnd_2247181 := by
    simpa [prefixWord, tailWord_2247181, baseEnd_2247181] using wordTrace_append hprefix tailTrace_2247181
  have hstable : (prefixWord ++ tailWord_2247181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247181).length < 2 ^ (prefixWord ++ tailWord_2247181).sum := by decide
  have hdescent : baseEnd_2247181 < baseStart_2247181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247201 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2247201 : Nat := 118140960795 + 2247201 * 2 ^ 59
def prefixEnd_2247201 : Nat := 4983230072969 + 3 ^ 40 * 2247201 * 2
def baseEnd_2247201 : Nat := 769262826842911699635211

theorem tailTrace_2247201 : CollatzResearch.WordTrace tailWord_2247201 prefixEnd_2247201 769262826842911699635211 := by
  unfold tailWord_2247201
  simp only [CollatzResearch.WordTrace]
  refine ⟨81962153931782043220717457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54641435954521362147144971 81962153931782043220717457)
  ·
    refine ⟨61471615448836532415538093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81962153931782043220717457 61471615448836532415538093)
    ·
      refine ⟨23051855793313699655826785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61471615448836532415538093 23051855793313699655826785)
      ·
        refine ⟨17288891844985274741870089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23051855793313699655826785 17288891844985274741870089)
        ·
          refine ⟨12966668883738956056402567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17288891844985274741870089 12966668883738956056402567)
          ·
            refine ⟨19450003325608434084603851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966668883738956056402567 19450003325608434084603851)
            ·
              refine ⟨29175004988412651126905777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19450003325608434084603851 29175004988412651126905777)
              ·
                refine ⟨21881253741309488345179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29175004988412651126905777 21881253741309488345179333)
                ·
                  refine ⟨4102735076495529064721125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21881253741309488345179333 4102735076495529064721125)
                  ·
                    refine ⟨769262826842911699635211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102735076495529064721125 769262826842911699635211)
                    ·
                      rfl

theorem cell22_2247201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2247201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247201 prefixEnd_2247201 := by exact prefixLift 2247201
  have htrace : WordTrace (prefixWord ++ tailWord_2247201) baseStart_2247201 baseEnd_2247201 := by
    simpa [prefixWord, tailWord_2247201, baseEnd_2247201] using wordTrace_append hprefix tailTrace_2247201
  have hstable : (prefixWord ++ tailWord_2247201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247201).length < 2 ^ (prefixWord ++ tailWord_2247201).sum := by decide
  have hdescent : baseEnd_2247201 < baseStart_2247201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247246 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2247246 : Nat := 118140960795 + 2247246 * 2 ^ 59
def prefixEnd_2247246 : Nat := 4983230072969 + 3 ^ 40 * 2247246 * 2
def baseEnd_2247246 : Nat := 769278231262546582260073

theorem tailTrace_2247246 : CollatzResearch.WordTrace tailWord_2247246 prefixEnd_2247246 769278231262546582260073 := by
  unfold tailWord_2247246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245474402077376988263199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54642530144412677270737061 10245474402077376988263199)
  ·
    refine ⟨15368211603116065482394799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245474402077376988263199 15368211603116065482394799)
    ·
      refine ⟨23052317404674098223592199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15368211603116065482394799 23052317404674098223592199)
      ·
        refine ⟨34578476107011147335388299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23052317404674098223592199 34578476107011147335388299)
        ·
          refine ⟨51867714160516721003082449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34578476107011147335388299 51867714160516721003082449)
          ·
            refine ⟨38900785620387540752311837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51867714160516721003082449 38900785620387540752311837)
            ·
              refine ⟨14587794607645327782116939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38900785620387540752311837 14587794607645327782116939)
              ·
                refine ⟨21881691911467991673175409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14587794607645327782116939 21881691911467991673175409)
                ·
                  refine ⟨16411268933600993754881557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21881691911467991673175409 16411268933600993754881557)
                  ·
                    refine ⟨769278231262546582260073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16411268933600993754881557 769278231262546582260073)
                    ·
                      rfl

theorem cell22_2247246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2247246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247246 prefixEnd_2247246 := by exact prefixLift 2247246
  have htrace : WordTrace (prefixWord ++ tailWord_2247246) baseStart_2247246 baseEnd_2247246 := by
    simpa [prefixWord, tailWord_2247246, baseEnd_2247246] using wordTrace_append hprefix tailTrace_2247246
  have hstable : (prefixWord ++ tailWord_2247246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247246).length < 2 ^ (prefixWord ++ tailWord_2247246).sum := by decide
  have hdescent : baseEnd_2247246 < baseStart_2247246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_2247291 : Nat := 118140960795 + 2247291 * 2 ^ 59
def prefixEnd_2247291 : Nat := 4983230072969 + 3 ^ 40 * 2247291 * 2
def baseEnd_2247291 : Nat := 769293635682181464884935

theorem tailTrace_2247291 : CollatzResearch.WordTrace tailWord_2247291 prefixEnd_2247291 769293635682181464884935 := by
  unfold tailWord_2247291
  simp only [CollatzResearch.WordTrace]
  refine ⟨81965436501455988591493727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54643624334303992394329151 81965436501455988591493727)
  ·
    refine ⟨122948154752183982887240591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81965436501455988591493727 122948154752183982887240591)
    ·
      refine ⟨184422232128275974330860887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122948154752183982887240591 184422232128275974330860887)
      ·
        refine ⟨276633348192413961496291331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184422232128275974330860887 276633348192413961496291331)
        ·
          refine ⟨414950022288620942244436997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276633348192413961496291331 414950022288620942244436997)
          ·
            refine ⟨77803129179116426670831937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414950022288620942244436997 77803129179116426670831937)
            ·
              refine ⟨58352346884337320003123953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77803129179116426670831937 58352346884337320003123953)
              ·
                refine ⟨43764260163252990002342965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58352346884337320003123953 43764260163252990002342965)
                ·
                  refine ⟨4102899390304967812719653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43764260163252990002342965 4102899390304967812719653)
                  ·
                    refine ⟨769293635682181464884935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102899390304967812719653 769293635682181464884935)
                    ·
                      rfl

theorem cell22_2247291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_2247291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247291 prefixEnd_2247291 := by exact prefixLift 2247291
  have htrace : WordTrace (prefixWord ++ tailWord_2247291) baseStart_2247291 baseEnd_2247291 := by
    simpa [prefixWord, tailWord_2247291, baseEnd_2247291] using wordTrace_append hprefix tailTrace_2247291
  have hstable : (prefixWord ++ tailWord_2247291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247291).length < 2 ^ (prefixWord ++ tailWord_2247291).sum := by decide
  have hdescent : baseEnd_2247291 < baseStart_2247291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247342 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2247342 : Nat := 118140960795 + 2247342 * 2 ^ 59
def prefixEnd_2247342 : Nat := 4983230072969 + 3 ^ 40 * 2247342 * 2
def baseEnd_2247342 : Nat := 769311094024434331859779

theorem tailTrace_2247342 : CollatzResearch.WordTrace tailWord_2247342 prefixEnd_2247342 769311094024434331859779 := by
  unfold tailWord_2247342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245912078033903037700035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54644864416180816201066853 10245912078033903037700035)
  ·
    refine ⟨15368868117050854556550053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245912078033903037700035 15368868117050854556550053)
    ·
      refine ⟨2881662771947035229353135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15368868117050854556550053 2881662771947035229353135)
      ·
        refine ⟨4322494157920552844029703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881662771947035229353135 4322494157920552844029703)
        ·
          refine ⟨6483741236880829266044555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322494157920552844029703 6483741236880829266044555)
          ·
            refine ⟨9725611855321243899066833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483741236880829266044555 9725611855321243899066833)
            ·
              refine ⟨7294208891490932924300125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9725611855321243899066833 7294208891490932924300125)
              ·
                refine ⟨2735328334309099846612547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7294208891490932924300125 2735328334309099846612547)
                ·
                  refine ⟨4102992501463649769918821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735328334309099846612547 4102992501463649769918821)
                  ·
                    refine ⟨769311094024434331859779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102992501463649769918821 769311094024434331859779)
                    ·
                      rfl

theorem cell22_2247342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2247342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247342 prefixEnd_2247342 := by exact prefixLift 2247342
  have htrace : WordTrace (prefixWord ++ tailWord_2247342) baseStart_2247342 baseEnd_2247342 := by
    simpa [prefixWord, tailWord_2247342, baseEnd_2247342] using wordTrace_append hprefix tailTrace_2247342
  have hstable : (prefixWord ++ tailWord_2247342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247342).length < 2 ^ (prefixWord ++ tailWord_2247342).sum := by decide
  have hdescent : baseEnd_2247342 < baseStart_2247342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247357 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2247357 : Nat := 118140960795 + 2247357 * 2 ^ 59
def prefixEnd_2247357 : Nat := 4983230072969 + 3 ^ 40 * 2247357 * 2
def baseEnd_2247357 : Nat := 256438742943659764244911

theorem tailTrace_2247357 : CollatzResearch.WordTrace tailWord_2247357 prefixEnd_2247357 256438742943659764244911 := by
  unfold tailWord_2247357
  simp only [CollatzResearch.WordTrace]
  refine ⟨81967843719216881863396325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54645229146144587908930883 81967843719216881863396325)
  ·
    refine ⟨15368970697353165349386811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81967843719216881863396325 15368970697353165349386811)
    ·
      refine ⟨23053456046029748024080217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15368970697353165349386811 23053456046029748024080217)
      ·
        refine ⟨17290092034522311018060163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23053456046029748024080217 17290092034522311018060163)
        ·
          refine ⟨25935138051783466527090245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17290092034522311018060163 25935138051783466527090245)
          ·
            refine ⟨4862838384709399973829421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25935138051783466527090245 4862838384709399973829421)
            ·
              refine ⟨1823564394266024990186033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4862838384709399973829421 1823564394266024990186033)
              ·
                refine ⟨1367673295699518742639525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823564394266024990186033 1367673295699518742639525)
                ·
                  refine ⟨256438742943659764244911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367673295699518742639525 256438742943659764244911)
                  ·
                    rfl

theorem cell22_2247357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2247357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247357 prefixEnd_2247357 := by exact prefixLift 2247357
  have htrace : WordTrace (prefixWord ++ tailWord_2247357) baseStart_2247357 baseEnd_2247357 := by
    simpa [prefixWord, tailWord_2247357, baseEnd_2247357] using wordTrace_append hprefix tailTrace_2247357
  have hstable : (prefixWord ++ tailWord_2247357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247357).length < 2 ^ (prefixWord ++ tailWord_2247357).sum := by decide
  have hdescent : baseEnd_2247357 < baseStart_2247357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247368 : List Nat := [2, 1, 3, 1, 2, 4, 2, 7]
def baseStart_2247368 : Nat := 118140960795 + 2247368 * 2 ^ 59
def prefixEnd_2247368 : Nat := 4983230072969 + 3 ^ 40 * 2247368 * 2
def baseEnd_2247368 : Nat := 85479999372864325634411

theorem tailTrace_2247368 : CollatzResearch.WordTrace tailWord_2247368 prefixEnd_2247368 85479999372864325634411 := by
  unfold tailWord_2247368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984122461088515371023379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54645496614784687161364505 40984122461088515371023379)
  ·
    refine ⟨61476183691632773056535069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40984122461088515371023379 61476183691632773056535069)
    ·
      refine ⟨23053568884362289896200651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61476183691632773056535069 23053568884362289896200651)
      ·
        refine ⟨34580353326543434844300977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23053568884362289896200651 34580353326543434844300977)
        ·
          refine ⟨25935264994907576133225733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34580353326543434844300977 25935264994907576133225733)
          ·
            refine ⟨4862862186545170524979825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25935264994907576133225733 4862862186545170524979825)
            ·
              refine ⟨3647146639908877893734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862862186545170524979825 3647146639908877893734869)
              ·
                refine ⟨85479999372864325634411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3647146639908877893734869 85479999372864325634411)
                ·
                  rfl

theorem cell22_2247368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_2247368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247368 prefixEnd_2247368 := by exact prefixLift 2247368
  have htrace : WordTrace (prefixWord ++ tailWord_2247368) baseStart_2247368 baseEnd_2247368 := by
    simpa [prefixWord, tailWord_2247368, baseEnd_2247368] using wordTrace_append hprefix tailTrace_2247368
  have hstable : (prefixWord ++ tailWord_2247368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247368).length < 2 ^ (prefixWord ++ tailWord_2247368).sum := by decide
  have hdescent : baseEnd_2247368 < baseStart_2247368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247372 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_2247372 : Nat := 118140960795 + 2247372 * 2 ^ 59
def prefixEnd_2247372 : Nat := 4983230072969 + 3 ^ 40 * 2247372 * 2
def baseEnd_2247372 : Nat := 769321363637524253609687

theorem tailTrace_2247372 : CollatzResearch.WordTrace tailWord_2247372 prefixEnd_2247372 769321363637524253609687 := by
  unfold tailWord_2247372
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984195407081269712596185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54645593876108359616794913 40984195407081269712596185)
  ·
    refine ⟨30738146555310952284447139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40984195407081269712596185 30738146555310952284447139)
    ·
      refine ⟨46107219832966428426670709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30738146555310952284447139 46107219832966428426670709)
      ·
        refine ⟨4322551859340602665000379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46107219832966428426670709 4322551859340602665000379)
        ·
          refine ⟨6483827789010903997500569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322551859340602665000379 6483827789010903997500569)
          ·
            refine ⟨4862870841758177998125427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483827789010903997500569 4862870841758177998125427)
            ·
              refine ⟨7294306262637266997188141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862870841758177998125427 7294306262637266997188141)
              ·
                refine ⟨2735364848488975123945553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7294306262637266997188141 2735364848488975123945553)
                ·
                  refine ⟨2051523636366731342959165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735364848488975123945553 2051523636366731342959165)
                  ·
                    refine ⟨769321363637524253609687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051523636366731342959165 769321363637524253609687)
                    ·
                      rfl

theorem cell22_2247372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_2247372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247372 prefixEnd_2247372 := by exact prefixLift 2247372
  have htrace : WordTrace (prefixWord ++ tailWord_2247372) baseStart_2247372 baseEnd_2247372 := by
    simpa [prefixWord, tailWord_2247372, baseEnd_2247372] using wordTrace_append hprefix tailTrace_2247372
  have hstable : (prefixWord ++ tailWord_2247372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247372).length < 2 ^ (prefixWord ++ tailWord_2247372).sum := by decide
  have hdescent : baseEnd_2247372 < baseStart_2247372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247443 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_2247443 : Nat := 118140960795 + 2247443 * 2 ^ 59
def prefixEnd_2247443 : Nat := 4983230072969 + 3 ^ 40 * 2247443 * 2
def baseEnd_2247443 : Nat := 769345668388503735084469

theorem tailTrace_2247443 : CollatzResearch.WordTrace tailWord_2247443 prefixEnd_2247443 769345668388503735084469 := by
  unfold tailWord_2247443
  simp only [CollatzResearch.WordTrace]
  refine ⟨81970980396905318551026983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54647320264603545700684655 81970980396905318551026983)
  ·
    refine ⟨122956470595357977826540475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81970980396905318551026983 122956470595357977826540475)
    ·
      refine ⟨184434705893036966739810713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122956470595357977826540475 184434705893036966739810713)
      ·
        refine ⟨138326029419777725054858035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184434705893036966739810713 138326029419777725054858035)
        ·
          refine ⟨207489044129666587582287053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138326029419777725054858035 207489044129666587582287053)
          ·
            refine ⟨77808391548624970343357645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207489044129666587582287053 77808391548624970343357645)
            ·
              refine ⟨29178146830734363878759117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77808391548624970343357645 29178146830734363878759117)
              ·
                refine ⟨10941805061525386454534669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29178146830734363878759117 10941805061525386454534669)
                ·
                  refine ⟨4103176898072019920450501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10941805061525386454534669 4103176898072019920450501)
                  ·
                    refine ⟨769345668388503735084469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103176898072019920450501 769345668388503735084469)
                    ·
                      rfl

theorem cell22_2247443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_2247443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247443 prefixEnd_2247443 := by exact prefixLift 2247443
  have htrace : WordTrace (prefixWord ++ tailWord_2247443) baseStart_2247443 baseEnd_2247443 := by
    simpa [prefixWord, tailWord_2247443, baseEnd_2247443] using wordTrace_append hprefix tailTrace_2247443
  have hstable : (prefixWord ++ tailWord_2247443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247443).length < 2 ^ (prefixWord ++ tailWord_2247443).sum := by decide
  have hdescent : baseEnd_2247443 < baseStart_2247443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247475 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 6]
def baseStart_2247475 : Nat := 118140960795 + 2247475 * 2 ^ 59
def prefixEnd_2247475 : Nat := 4983230072969 + 3 ^ 40 * 2247475 * 2
def baseEnd_2247475 : Nat := 256452207547488772761457

theorem tailTrace_2247475 : CollatzResearch.WordTrace tailWord_2247475 prefixEnd_2247475 256452207547488772761457 := by
  unfold tailWord_2247475
  simp only [CollatzResearch.WordTrace]
  refine ⟨81972147532789388016191879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54648098355192925344127919 81972147532789388016191879)
  ·
    refine ⟨122958221299184082024287819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81972147532789388016191879 122958221299184082024287819)
    ·
      refine ⟨184437331948776123036431729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122958221299184082024287819 184437331948776123036431729)
      ·
        refine ⟨138327998961582092277323797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184437331948776123036431729 138327998961582092277323797)
        ·
          refine ⟨6484124951324160575499553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138327998961582092277323797 6484124951324160575499553)
          ·
            refine ⟨4863093713493120431624665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484124951324160575499553 4863093713493120431624665)
            ·
              refine ⟨3647320285119840323718499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4863093713493120431624665 3647320285119840323718499)
              ·
                refine ⟨5470980427679760485577749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647320285119840323718499 5470980427679760485577749)
                ·
                  refine ⟨256452207547488772761457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5470980427679760485577749 256452207547488772761457)
                  ·
                    rfl

theorem cell22_2247475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_2247475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247475 prefixEnd_2247475 := by exact prefixLift 2247475
  have htrace : WordTrace (prefixWord ++ tailWord_2247475) baseStart_2247475 baseEnd_2247475 := by
    simpa [prefixWord, tailWord_2247475, baseEnd_2247475] using wordTrace_append hprefix tailTrace_2247475
  have hstable : (prefixWord ++ tailWord_2247475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247475).length < 2 ^ (prefixWord ++ tailWord_2247475).sum := by decide
  have hdescent : baseEnd_2247475 < baseStart_2247475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247541 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2247541 : Nat := 118140960795 + 2247541 * 2 ^ 59
def prefixEnd_2247541 : Nat := 4983230072969 + 3 ^ 40 * 2247541 * 2
def baseEnd_2247541 : Nat := 769379215791264146134169

theorem tailTrace_2247541 : CollatzResearch.WordTrace tailWord_2247541 prefixEnd_2247541 769379215791264146134169 := by
  unfold tailWord_2247541
  simp only [CollatzResearch.WordTrace]
  refine ⟨81974554750550281288094477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54649703167033520858729651 81974554750550281288094477)
  ·
    refine ⟨30740458031456355483035429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81974554750550281288094477 30740458031456355483035429)
    ·
      refine ⟨5763835880898066653069143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30740458031456355483035429 5763835880898066653069143)
      ·
        refine ⟨8645753821347099979603715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5763835880898066653069143 8645753821347099979603715)
        ·
          refine ⟨12968630732020649969405573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8645753821347099979603715 12968630732020649969405573)
          ·
            refine ⟨2431618262253871869263545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12968630732020649969405573 2431618262253871869263545)
            ·
              refine ⟨1823713696690403901947659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431618262253871869263545 1823713696690403901947659)
              ·
                refine ⟨2735570545035605852921489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823713696690403901947659 2735570545035605852921489)
                ·
                  refine ⟨2051677908776704389691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735570545035605852921489 2051677908776704389691117)
                  ·
                    refine ⟨769379215791264146134169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051677908776704389691117 769379215791264146134169)
                    ·
                      rfl

theorem cell22_2247541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2247541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247541 prefixEnd_2247541 := by exact prefixLift 2247541
  have htrace : WordTrace (prefixWord ++ tailWord_2247541) baseStart_2247541 baseEnd_2247541 := by
    simpa [prefixWord, tailWord_2247541, baseEnd_2247541] using wordTrace_append hprefix tailTrace_2247541
  have hstable : (prefixWord ++ tailWord_2247541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247541).length < 2 ^ (prefixWord ++ tailWord_2247541).sum := by decide
  have hdescent : baseEnd_2247541 < baseStart_2247541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247586 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2247586 : Nat := 118140960795 + 2247586 * 2 ^ 59
def prefixEnd_2247586 : Nat := 4983230072969 + 3 ^ 40 * 2247586 * 2
def baseEnd_2247586 : Nat := 769394620210899028759031

theorem tailTrace_2247586 : CollatzResearch.WordTrace tailWord_2247586 prefixEnd_2247586 769394620210899028759031 := by
  unfold tailWord_2247586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20494049008846813493370653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54650797356924835982321741 20494049008846813493370653)
  ·
    refine ⟨7685268378317555060013995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20494049008846813493370653 7685268378317555060013995)
    ·
      refine ⟨11527902567476332590020993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7685268378317555060013995 11527902567476332590020993)
      ·
        refine ⟨8645926925607249442515745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11527902567476332590020993 8645926925607249442515745)
        ·
          refine ⟨6484445194205437081886809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8645926925607249442515745 6484445194205437081886809)
          ·
            refine ⟨4863333895654077811415107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484445194205437081886809 4863333895654077811415107)
            ·
              refine ⟨7295000843481116717122661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863333895654077811415107 7295000843481116717122661)
              ·
                refine ⟨1367812658152709384460499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7295000843481116717122661 1367812658152709384460499)
                ·
                  refine ⟨2051718987229064076690749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367812658152709384460499 2051718987229064076690749)
                  ·
                    refine ⟨769394620210899028759031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051718987229064076690749 769394620210899028759031)
                    ·
                      rfl

theorem cell22_2247586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2247586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247586 prefixEnd_2247586 := by exact prefixLift 2247586
  have htrace : WordTrace (prefixWord ++ tailWord_2247586) baseStart_2247586 baseEnd_2247586 := by
    simpa [prefixWord, tailWord_2247586, baseEnd_2247586] using wordTrace_append hprefix tailTrace_2247586
  have hstable : (prefixWord ++ tailWord_2247586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247586).length < 2 ^ (prefixWord ++ tailWord_2247586).sum := by decide
  have hdescent : baseEnd_2247586 < baseStart_2247586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247610 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_2247610 : Nat := 118140960795 + 2247610 * 2 ^ 59
def prefixEnd_2247610 : Nat := 4983230072969 + 3 ^ 40 * 2247610 * 2
def baseEnd_2247610 : Nat := 256467611967123655386319

theorem tailTrace_2247610 : CollatzResearch.WordTrace tailWord_2247610 prefixEnd_2247610 256467611967123655386319 := by
  unfold tailWord_2247610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20494267846825076518089071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54651380924866870714904189 20494267846825076518089071)
  ·
    refine ⟨30741401770237614777133607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20494267846825076518089071 30741401770237614777133607)
    ·
      refine ⟨46112102655356422165700411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30741401770237614777133607 46112102655356422165700411)
      ·
        refine ⟨69168153983034633248550617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46112102655356422165700411 69168153983034633248550617)
        ·
          refine ⟨51876115487275974936412963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69168153983034633248550617 51876115487275974936412963)
          ·
            refine ⟨77814173230913962404619445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51876115487275974936412963 77814173230913962404619445)
            ·
              refine ⟨7295078740398183975433073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77814173230913962404619445 7295078740398183975433073)
              ·
                refine ⟨5471309055298637981574805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7295078740398183975433073 5471309055298637981574805)
                ·
                  refine ⟨256467611967123655386319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5471309055298637981574805 256467611967123655386319)
                  ·
                    rfl

theorem cell22_2247610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_2247610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247610 prefixEnd_2247610 := by exact prefixLift 2247610
  have htrace : WordTrace (prefixWord ++ tailWord_2247610) baseStart_2247610 baseEnd_2247610 := by
    simpa [prefixWord, tailWord_2247610, baseEnd_2247610] using wordTrace_append hprefix tailTrace_2247610
  have hstable : (prefixWord ++ tailWord_2247610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247610).length < 2 ^ (prefixWord ++ tailWord_2247610).sum := by decide
  have hdescent : baseEnd_2247610 < baseStart_2247610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247627 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 4]
def baseStart_2247627 : Nat := 118140960795 + 2247627 * 2 ^ 59
def prefixEnd_2247627 : Nat := 4983230072969 + 3 ^ 40 * 2247627 * 2
def baseEnd_2247627 : Nat := 256469551782929529494635

theorem tailTrace_2247627 : CollatzResearch.WordTrace tailWord_2247627 prefixEnd_2247627 256469551782929529494635 := by
  unfold tailWord_2247627
  simp only [CollatzResearch.WordTrace]
  refine ⟨81977691428238717975725135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54651794285492478650483423 81977691428238717975725135)
  ·
    refine ⟨122966537142358076963587703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81977691428238717975725135 122966537142358076963587703)
    ·
      refine ⟨184449805713537115445381555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122966537142358076963587703 184449805713537115445381555)
      ·
        refine ⟨276674708570305673168072333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184449805713537115445381555 276674708570305673168072333)
        ·
          refine ⟨103753015713864627438027125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276674708570305673168072333 103753015713864627438027125)
          ·
            refine ⟨9726845223174808822315043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103753015713864627438027125 9726845223174808822315043)
            ·
              refine ⟨14590267834762213233472565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726845223174808822315043 14590267834762213233472565)
              ·
                refine ⟨1367837609508957490638053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14590267834762213233472565 1367837609508957490638053)
                ·
                  refine ⟨256469551782929529494635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367837609508957490638053 256469551782929529494635)
                  ·
                    rfl

theorem cell22_2247627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 4].length) (baseStart_2247627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247627 prefixEnd_2247627 := by exact prefixLift 2247627
  have htrace : WordTrace (prefixWord ++ tailWord_2247627) baseStart_2247627 baseEnd_2247627 := by
    simpa [prefixWord, tailWord_2247627, baseEnd_2247627] using wordTrace_append hprefix tailTrace_2247627
  have hstable : (prefixWord ++ tailWord_2247627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247627).length < 2 ^ (prefixWord ++ tailWord_2247627).sum := by decide
  have hdescent : baseEnd_2247627 < baseStart_2247627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247678 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2247678 : Nat := 118140960795 + 2247678 * 2 ^ 59
def prefixEnd_2247678 : Nat := 4983230072969 + 3 ^ 40 * 2247678 * 2
def baseEnd_2247678 : Nat := 256475371230347151819583

theorem tailTrace_2247678 : CollatzResearch.WordTrace tailWord_2247678 prefixEnd_2247678 256475371230347151819583 := by
  unfold tailWord_2247678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247443943881744210728961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54653034367369302457221125 10247443943881744210728961)
  ·
    refine ⟨7685582957911308158046721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10247443943881744210728961 7685582957911308158046721)
    ·
      refine ⟨5764187218433481118535041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7685582957911308158046721 5764187218433481118535041)
      ·
        refine ⟨4323140413825110838901281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5764187218433481118535041 4323140413825110838901281)
        ·
          refine ⟨3242355310368833129175961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4323140413825110838901281 3242355310368833129175961)
          ·
            refine ⟨2431766482776624846881971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242355310368833129175961 2431766482776624846881971)
            ·
              refine ⟨3647649724164937270322957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431766482776624846881971 3647649724164937270322957)
              ·
                refine ⟨1367868646561851476371109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3647649724164937270322957 1367868646561851476371109)
                ·
                  refine ⟨256475371230347151819583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367868646561851476371109 256475371230347151819583)
                  ·
                    rfl

theorem cell22_2247678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2247678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247678 prefixEnd_2247678 := by exact prefixLift 2247678
  have htrace : WordTrace (prefixWord ++ tailWord_2247678) baseStart_2247678 baseEnd_2247678 := by
    simpa [prefixWord, tailWord_2247678, baseEnd_2247678] using wordTrace_append hprefix tailTrace_2247678
  have hstable : (prefixWord ++ tailWord_2247678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247678).length < 2 ^ (prefixWord ++ tailWord_2247678).sum := by decide
  have hdescent : baseEnd_2247678 < baseStart_2247678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247704 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_2247704 : Nat := 118140960795 + 2247704 * 2 ^ 59
def prefixEnd_2247704 : Nat := 4983230072969 + 3 ^ 40 * 2247704 * 2
def baseEnd_2247704 : Nat := 769435014022386054308669

theorem tailTrace_2247704 : CollatzResearch.WordTrace tailWord_2247704 prefixEnd_2247704 769435014022386054308669 := by
  unfold tailWord_2247704
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990249924479880063139083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54653666565973173417518777 40990249924479880063139083)
  ·
    refine ⟨61485374886719820094708625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40990249924479880063139083 61485374886719820094708625)
    ·
      refine ⟨46114031165039865071031469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61485374886719820094708625 46114031165039865071031469)
      ·
        refine ⟨17292761686889949401636801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46114031165039865071031469 17292761686889949401636801)
        ·
          refine ⟨12969571265167462051227601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17292761686889949401636801 12969571265167462051227601)
          ·
            refine ⟨9727178448875596538420701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12969571265167462051227601 9727178448875596538420701)
            ·
              refine ⟨3647691918328348701907763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9727178448875596538420701 3647691918328348701907763)
              ·
                refine ⟨5471537877492523052861645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647691918328348701907763 5471537877492523052861645)
                ·
                  refine ⟨2051826704059696144823117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5471537877492523052861645 2051826704059696144823117)
                  ·
                    refine ⟨769435014022386054308669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051826704059696144823117 769435014022386054308669)
                    ·
                      rfl

theorem cell22_2247704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_2247704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247704 prefixEnd_2247704 := by exact prefixLift 2247704
  have htrace : WordTrace (prefixWord ++ tailWord_2247704) baseStart_2247704 baseEnd_2247704 := by
    simpa [prefixWord, tailWord_2247704, baseEnd_2247704] using wordTrace_append hprefix tailTrace_2247704
  have hstable : (prefixWord ++ tailWord_2247704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247704).length < 2 ^ (prefixWord ++ tailWord_2247704).sum := by decide
  have hdescent : baseEnd_2247704 < baseStart_2247704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247717 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2247717 : Nat := 118140960795 + 2247717 * 2 ^ 59
def prefixEnd_2247717 : Nat := 4983230072969 + 3 ^ 40 * 2247717 * 2
def baseEnd_2247717 : Nat := 256479821396019451244543

theorem tailTrace_2247717 : CollatzResearch.WordTrace tailWord_2247717 prefixEnd_2247717 256479821396019451244543 := by
  unfold tailWord_2247717
  simp only [CollatzResearch.WordTrace]
  refine ⟨81980973997912663346501405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54653982665275108897667603 81980973997912663346501405)
  ·
    refine ⟨30742865249217248754938027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81980973997912663346501405 30742865249217248754938027)
    ·
      refine ⟨46114297873825873132407041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30742865249217248754938027 46114297873825873132407041)
      ·
        refine ⟨34585723405369404849305281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46114297873825873132407041 34585723405369404849305281)
        ·
          refine ⟨25939292554027053636978961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34585723405369404849305281 25939292554027053636978961)
          ·
            refine ⟨19454469415520290227734221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25939292554027053636978961 19454469415520290227734221)
            ·
              refine ⟨7295426030820108835400333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19454469415520290227734221 7295426030820108835400333)
              ·
                refine ⟨2735784761557540813275125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7295426030820108835400333 2735784761557540813275125)
                ·
                  refine ⟨256479821396019451244543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735784761557540813275125 256479821396019451244543)
                  ·
                    rfl

theorem cell22_2247717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2247717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247717 prefixEnd_2247717 := by exact prefixLift 2247717
  have htrace : WordTrace (prefixWord ++ tailWord_2247717) baseStart_2247717 baseEnd_2247717 := by
    simpa [prefixWord, tailWord_2247717, baseEnd_2247717] using wordTrace_append hprefix tailTrace_2247717
  have hstable : (prefixWord ++ tailWord_2247717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247717).length < 2 ^ (prefixWord ++ tailWord_2247717).sum := by decide
  have hdescent : baseEnd_2247717 < baseStart_2247717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247777 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2247777 : Nat := 118140960795 + 2247777 * 2 ^ 59
def prefixEnd_2247777 : Nat := 4983230072969 + 3 ^ 40 * 2247777 * 2
def baseEnd_2247777 : Nat := 769460003414238197233445

theorem tailTrace_2247777 : CollatzResearch.WordTrace tailWord_2247777 prefixEnd_2247777 769460003414238197233445 := by
  unfold tailWord_2247777
  simp only [CollatzResearch.WordTrace]
  refine ⟨81983162377695293593685585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54655441585130195729123723 81983162377695293593685585)
  ·
    refine ⟨61487371783271470195264189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81983162377695293593685585 61487371783271470195264189)
    ·
      refine ⟨23057764418726801323224071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61487371783271470195264189 23057764418726801323224071)
      ·
        refine ⟨34586646628090201984836107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23057764418726801323224071 34586646628090201984836107)
        ·
          refine ⟨51879969942135302977254161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586646628090201984836107 51879969942135302977254161)
          ·
            refine ⟨38909977456601477232940621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51879969942135302977254161 38909977456601477232940621)
            ·
              refine ⟨14591241546225553962352733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38909977456601477232940621 14591241546225553962352733)
              ·
                refine ⟨5471715579834582735882275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14591241546225553962352733 5471715579834582735882275)
                ·
                  refine ⟨8207573369751874103823413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471715579834582735882275 8207573369751874103823413)
                  ·
                    refine ⟨769460003414238197233445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8207573369751874103823413 769460003414238197233445)
                    ·
                      rfl

theorem cell22_2247777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2247777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247777 prefixEnd_2247777 := by exact prefixLift 2247777
  have htrace : WordTrace (prefixWord ++ tailWord_2247777) baseStart_2247777 baseEnd_2247777 := by
    simpa [prefixWord, tailWord_2247777, baseEnd_2247777] using wordTrace_append hprefix tailTrace_2247777
  have hstable : (prefixWord ++ tailWord_2247777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247777).length < 2 ^ (prefixWord ++ tailWord_2247777).sum := by decide
  have hdescent : baseEnd_2247777 < baseStart_2247777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247792 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_2247792 : Nat := 118140960795 + 2247792 * 2 ^ 59
def prefixEnd_2247792 : Nat := 4983230072969 + 3 ^ 40 * 2247792 * 2
def baseEnd_2247792 : Nat := 769465138220783158108399

theorem tailTrace_2247792 : CollatzResearch.WordTrace tailWord_2247792 prefixEnd_2247792 769465138220783158108399 := by
  unfold tailWord_2247792
  simp only [CollatzResearch.WordTrace]
  refine ⟨40991854736320475577740815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54655806315093967436987753 40991854736320475577740815)
  ·
    refine ⟨61487782104480713366611223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40991854736320475577740815 61487782104480713366611223)
    ·
      refine ⟨92231673156721070049916835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61487782104480713366611223 92231673156721070049916835)
      ·
        refine ⟨138347509735081605074875253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92231673156721070049916835 138347509735081605074875253)
        ·
          refine ⟨12970079037663900475769555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138347509735081605074875253 12970079037663900475769555)
          ·
            refine ⟨19455118556495850713654333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12970079037663900475769555 19455118556495850713654333)
            ·
              refine ⟨7295669458685944017620375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19455118556495850713654333 7295669458685944017620375)
              ·
                refine ⟨10943504188028916026430563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295669458685944017620375 10943504188028916026430563)
                ·
                  refine ⟨16415256282043374039645845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10943504188028916026430563 16415256282043374039645845)
                  ·
                    refine ⟨769465138220783158108399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16415256282043374039645845 769465138220783158108399)
                    ·
                      rfl

theorem cell22_2247792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_2247792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247792 prefixEnd_2247792 := by exact prefixLift 2247792
  have htrace : WordTrace (prefixWord ++ tailWord_2247792) baseStart_2247792 baseEnd_2247792 := by
    simpa [prefixWord, tailWord_2247792, baseEnd_2247792] using wordTrace_append hprefix tailTrace_2247792
  have hstable : (prefixWord ++ tailWord_2247792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247792).length < 2 ^ (prefixWord ++ tailWord_2247792).sum := by decide
  have hdescent : baseEnd_2247792 < baseStart_2247792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247794 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_2247794 : Nat := 118140960795 + 2247794 * 2 ^ 59
def prefixEnd_2247794 : Nat := 4983230072969 + 3 ^ 40 * 2247794 * 2
def baseEnd_2247794 : Nat := 769465822861655819558393

theorem tailTrace_2247794 : CollatzResearch.WordTrace tailWord_2247794 prefixEnd_2247794 769465822861655819558393 := by
  unfold tailWord_2247794
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495945604658426374263609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54655854945755803664702957 20495945604658426374263609)
  ·
    refine ⟨15371959203493819780697707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20495945604658426374263609 15371959203493819780697707)
    ·
      refine ⟨23057938805240729671046561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15371959203493819780697707 23057938805240729671046561)
      ·
        refine ⟨17293454103930547253284921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23057938805240729671046561 17293454103930547253284921)
        ·
          refine ⟨12970090577947910439963691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17293454103930547253284921 12970090577947910439963691)
          ·
            refine ⟨19455135866921865659945537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12970090577947910439963691 19455135866921865659945537)
            ·
              refine ⟨14591351900191399244959153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19455135866921865659945537 14591351900191399244959153)
              ·
                refine ⟨10943513925143549433719365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14591351900191399244959153 10943513925143549433719365)
                ·
                  refine ⟨2051908860964415518822381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10943513925143549433719365 2051908860964415518822381)
                  ·
                    refine ⟨769465822861655819558393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051908860964415518822381 769465822861655819558393)
                    ·
                      rfl

theorem cell22_2247794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_2247794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247794 prefixEnd_2247794 := by exact prefixLift 2247794
  have htrace : WordTrace (prefixWord ++ tailWord_2247794) baseStart_2247794 baseEnd_2247794 := by
    simpa [prefixWord, tailWord_2247794, baseEnd_2247794] using wordTrace_append hprefix tailTrace_2247794
  have hstable : (prefixWord ++ tailWord_2247794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247794).length < 2 ^ (prefixWord ++ tailWord_2247794).sum := by decide
  have hdescent : baseEnd_2247794 < baseStart_2247794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_2247867 : Nat := 118140960795 + 2247867 * 2 ^ 59
def prefixEnd_2247867 : Nat := 4983230072969 + 3 ^ 40 * 2247867 * 2
def baseEnd_2247867 : Nat := 769490812253507962483169

theorem tailTrace_2247867 : CollatzResearch.WordTrace tailWord_2247867 prefixEnd_2247867 769490812253507962483169 := by
  unfold tailWord_2247867
  simp only [CollatzResearch.WordTrace]
  refine ⟨81986444947369238964461855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54657629964912825976307903 81986444947369238964461855)
  ·
    refine ⟨122979667421053858446692783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81986444947369238964461855 122979667421053858446692783)
    ·
      refine ⟨184469501131580787670039175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122979667421053858446692783 184469501131580787670039175)
      ·
        refine ⟨276704251697371181505058763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184469501131580787670039175 276704251697371181505058763)
        ·
          refine ⟨415056377546056772257588145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276704251697371181505058763 415056377546056772257588145)
          ·
            refine ⟨311292283159542579193191109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415056377546056772257588145 311292283159542579193191109)
            ·
              refine ⟨58367303092414233598723333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 311292283159542579193191109 58367303092414233598723333)
              ·
                refine ⟨10943869329827668799760625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58367303092414233598723333 10943869329827668799760625)
                ·
                  refine ⟨8207901997370751599820469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10943869329827668799760625 8207901997370751599820469)
                  ·
                    refine ⟨769490812253507962483169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8207901997370751599820469 769490812253507962483169)
                    ·
                      rfl

theorem cell22_2247867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_2247867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247867 prefixEnd_2247867 := by exact prefixLift 2247867
  have htrace : WordTrace (prefixWord ++ tailWord_2247867) baseStart_2247867 baseEnd_2247867 := by
    simpa [prefixWord, tailWord_2247867, baseEnd_2247867] using wordTrace_append hprefix tailTrace_2247867
  have hstable : (prefixWord ++ tailWord_2247867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247867).length < 2 ^ (prefixWord ++ tailWord_2247867).sum := by decide
  have hdescent : baseEnd_2247867 < baseStart_2247867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247873 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2247873 : Nat := 118140960795 + 2247873 * 2 ^ 59
def prefixEnd_2247873 : Nat := 4983230072969 + 3 ^ 40 * 2247873 * 2
def baseEnd_2247873 : Nat := 769492866176125946833151

theorem tailTrace_2247873 : CollatzResearch.WordTrace tailWord_2247873 prefixEnd_2247873 769492866176125946833151 := by
  unfold tailWord_2247873
  simp only [CollatzResearch.WordTrace]
  refine ⟨81986663785347501989180273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54657775856898334659453515 81986663785347501989180273)
  ·
    refine ⟨61489997839010626491885205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81986663785347501989180273 61489997839010626491885205)
    ·
      refine ⟨2882343648703623116807119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61489997839010626491885205 2882343648703623116807119)
      ·
        refine ⟨4323515473055434675210679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882343648703623116807119 4323515473055434675210679)
        ·
          refine ⟨6485273209583152012816019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323515473055434675210679 6485273209583152012816019)
          ·
            refine ⟨9727909814374728019224029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6485273209583152012816019 9727909814374728019224029)
            ·
              refine ⟨3647966180390523007209011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9727909814374728019224029 3647966180390523007209011)
              ·
                refine ⟨5471949270585784510813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647966180390523007209011 5471949270585784510813517)
                ·
                  refine ⟨2051980976469669191555069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5471949270585784510813517 2051980976469669191555069)
                  ·
                    refine ⟨769492866176125946833151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051980976469669191555069 769492866176125946833151)
                    ·
                      rfl

theorem cell22_2247873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2247873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247873 prefixEnd_2247873 := by exact prefixLift 2247873
  have htrace : WordTrace (prefixWord ++ tailWord_2247873) baseStart_2247873 baseEnd_2247873 := by
    simpa [prefixWord, tailWord_2247873, baseEnd_2247873] using wordTrace_append hprefix tailTrace_2247873
  have hstable : (prefixWord ++ tailWord_2247873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247873).length < 2 ^ (prefixWord ++ tailWord_2247873).sum := by decide
  have hdescent : baseEnd_2247873 < baseStart_2247873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247886 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2247886 : Nat := 118140960795 + 2247886 * 2 ^ 59
def prefixEnd_2247886 : Nat := 4983230072969 + 3 ^ 40 * 2247886 * 2
def baseEnd_2247886 : Nat := 256499105447266082086037

theorem tailTrace_2247886 : CollatzResearch.WordTrace tailWord_2247886 prefixEnd_2247886 256499105447266082086037 := by
  unfold tailWord_2247886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10248392241787550651175439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54658091956200270139602341 10248392241787550651175439)
  ·
    refine ⟨15372588362681325976763159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10248392241787550651175439 15372588362681325976763159)
    ·
      refine ⟨23058882544021988965144739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15372588362681325976763159 23058882544021988965144739)
      ·
        refine ⟨34588323816032983447717109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23058882544021988965144739 34588323816032983447717109)
        ·
          refine ⟨3242655357753092198223479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34588323816032983447717109 3242655357753092198223479)
          ·
            refine ⟨4863983036629638297335219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242655357753092198223479 4863983036629638297335219)
            ·
              refine ⟨7295974554944457446002829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863983036629638297335219 7295974554944457446002829)
              ·
                refine ⟨2735990458104171542251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7295974554944457446002829 2735990458104171542251061)
                ·
                  refine ⟨256499105447266082086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735990458104171542251061 256499105447266082086037)
                  ·
                    rfl

theorem cell22_2247886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2247886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247886 prefixEnd_2247886 := by exact prefixLift 2247886
  have htrace : WordTrace (prefixWord ++ tailWord_2247886) baseStart_2247886 baseEnd_2247886 := by
    simpa [prefixWord, tailWord_2247886, baseEnd_2247886] using wordTrace_append hprefix tailTrace_2247886
  have hstable : (prefixWord ++ tailWord_2247886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247886).length < 2 ^ (prefixWord ++ tailWord_2247886).sum := by decide
  have hdescent : baseEnd_2247886 < baseStart_2247886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247897 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 8]
def baseStart_2247897 : Nat := 118140960795 + 2247897 * 2 ^ 59
def prefixEnd_2247897 : Nat := 4983230072969 + 3 ^ 40 * 2247897 * 2
def baseEnd_2247897 : Nat := 256500360622199294744359

theorem tailTrace_2247897 : CollatzResearch.WordTrace tailWord_2247897 prefixEnd_2247897 256500360622199294744359 := by
  unfold tailWord_2247897
  simp only [CollatzResearch.WordTrace]
  refine ⟨81987539137260554088053945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54658359424840369392035963 81987539137260554088053945)
  ·
    refine ⟨61490654352945415566040459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81987539137260554088053945 61490654352945415566040459)
    ·
      refine ⟨92235981529418123349060689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61490654352945415566040459 92235981529418123349060689)
      ·
        refine ⟨69176986147063592511795517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92235981529418123349060689 69176986147063592511795517)
        ·
          refine ⟨25941369805148847191923319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69176986147063592511795517 25941369805148847191923319)
          ·
            refine ⟨38912054707723270787884979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25941369805148847191923319 38912054707723270787884979)
            ·
              refine ⟨58368082061584906181827469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38912054707723270787884979 58368082061584906181827469)
              ·
                refine ⟨21888030773094339818185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58368082061584906181827469 21888030773094339818185301)
                ·
                  refine ⟨256500360622199294744359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21888030773094339818185301 256500360622199294744359)
                  ·
                    rfl

theorem cell22_2247897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_2247897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247897 prefixEnd_2247897 := by exact prefixLift 2247897
  have htrace : WordTrace (prefixWord ++ tailWord_2247897) baseStart_2247897 baseEnd_2247897 := by
    simpa [prefixWord, tailWord_2247897, baseEnd_2247897] using wordTrace_append hprefix tailTrace_2247897
  have hstable : (prefixWord ++ tailWord_2247897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247897).length < 2 ^ (prefixWord ++ tailWord_2247897).sum := by decide
  have hdescent : baseEnd_2247897 < baseStart_2247897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247924 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2247924 : Nat := 118140960795 + 2247924 * 2 ^ 59
def prefixEnd_2247924 : Nat := 4983230072969 + 3 ^ 40 * 2247924 * 2
def baseEnd_2247924 : Nat := 769510324518378813807995

theorem tailTrace_2247924 : CollatzResearch.WordTrace tailWord_2247924 prefixEnd_2247924 769510324518378813807995 := by
  unfold tailWord_2247924
  simp only [CollatzResearch.WordTrace]
  refine ⟨40994261954081368849643413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54659015938775158466191217 40994261954081368849643413)
  ·
    refine ⟨1921606029097564164827035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40994261954081368849643413 1921606029097564164827035)
    ·
      refine ⟨2882409043646346247240553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921606029097564164827035 2882409043646346247240553)
      ·
        refine ⟨2161806782734759685430415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2882409043646346247240553 2161806782734759685430415)
        ·
          refine ⟨3242710174102139528145623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161806782734759685430415 3242710174102139528145623)
          ·
            refine ⟨4864065261153209292218435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242710174102139528145623 4864065261153209292218435)
            ·
              refine ⟨7296097891729813938327653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4864065261153209292218435 7296097891729813938327653)
              ·
                refine ⟨1368018354699340113436435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7296097891729813938327653 1368018354699340113436435)
                ·
                  refine ⟨2052027532049010170154653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368018354699340113436435 2052027532049010170154653)
                  ·
                    refine ⟨769510324518378813807995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052027532049010170154653 769510324518378813807995)
                    ·
                      rfl

theorem cell22_2247924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2247924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247924 prefixEnd_2247924 := by exact prefixLift 2247924
  have htrace : WordTrace (prefixWord ++ tailWord_2247924) baseStart_2247924 baseEnd_2247924 := by
    simpa [prefixWord, tailWord_2247924, baseEnd_2247924] using wordTrace_append hprefix tailTrace_2247924
  have hstable : (prefixWord ++ tailWord_2247924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247924).length < 2 ^ (prefixWord ++ tailWord_2247924).sum := by decide
  have hdescent : baseEnd_2247924 < baseStart_2247924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247997 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_2247997 : Nat := 118140960795 + 2247997 * 2 ^ 59
def prefixEnd_2247997 : Nat := 4983230072969 + 3 ^ 40 * 2247997 * 2
def baseEnd_2247997 : Nat := 769535313910230956732771

theorem tailTrace_2247997 : CollatzResearch.WordTrace tailWord_2247997 prefixEnd_2247997 769535313910230956732771 := by
  unfold tailWord_2247997
  simp only [CollatzResearch.WordTrace]
  refine ⟨81991186436898271166694245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54660790957932180777796163 81991186436898271166694245)
  ·
    refine ⟨15373347456918425843755171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81991186436898271166694245 15373347456918425843755171)
    ·
      refine ⟨23060021185377638765632757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15373347456918425843755171 23060021185377638765632757)
      ·
        refine ⟨2161876986129153634278071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23060021185377638765632757 2161876986129153634278071)
        ·
          refine ⟨3242815479193730451417107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161876986129153634278071 3242815479193730451417107)
          ·
            refine ⟨4864223218790595677125661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242815479193730451417107 4864223218790595677125661)
            ·
              refine ⟨1824083707046473378922123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4864223218790595677125661 1824083707046473378922123)
              ·
                refine ⟨2736125560569710068383185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824083707046473378922123 2736125560569710068383185)
                ·
                  refine ⟨2052094170427282551287389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736125560569710068383185 2052094170427282551287389)
                  ·
                    refine ⟨769535313910230956732771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052094170427282551287389 769535313910230956732771)
                    ·
                      rfl

theorem cell22_2247997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_2247997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2247997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2247997 prefixEnd_2247997 := by exact prefixLift 2247997
  have htrace : WordTrace (prefixWord ++ tailWord_2247997) baseStart_2247997 baseEnd_2247997 := by
    simpa [prefixWord, tailWord_2247997, baseEnd_2247997] using wordTrace_append hprefix tailTrace_2247997
  have hstable : (prefixWord ++ tailWord_2247997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247997).length < 2 ^ (prefixWord ++ tailWord_2247997).sum := by decide
  have hdescent : baseEnd_2247997 < baseStart_2247997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248042 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2248042 : Nat := 118140960795 + 2248042 * 2 ^ 59
def prefixEnd_2248042 : Nat := 4983230072969 + 3 ^ 40 * 2248042 * 2
def baseEnd_2248042 : Nat := 769550718329865839357633

theorem tailTrace_2248042 : CollatzResearch.WordTrace tailWord_2248042 prefixEnd_2248042 769550718329865839357633 := by
  unfold tailWord_2248042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498206930433810963020595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54661885147823495901388253 20498206930433810963020595)
  ·
    refine ⟨30747310395650716444530893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20498206930433810963020595 30747310395650716444530893)
    ·
      refine ⟨11530241398369018666699085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30747310395650716444530893 11530241398369018666699085)
      ·
        refine ⟨4323840524388382000012157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11530241398369018666699085 4323840524388382000012157)
        ·
          refine ⟨1621440196645643250004559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4323840524388382000012157 1621440196645643250004559)
          ·
            refine ⟨2432160294968464875006839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621440196645643250004559 2432160294968464875006839)
            ·
              refine ⟨3648240442452697312510259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432160294968464875006839 3648240442452697312510259)
              ·
                refine ⟨5472360663679045968765389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648240442452697312510259 5472360663679045968765389)
                ·
                  refine ⟨2052135248879642238287021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5472360663679045968765389 2052135248879642238287021)
                  ·
                    refine ⟨769550718329865839357633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052135248879642238287021 769550718329865839357633)
                    ·
                      rfl

theorem cell22_2248042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2248042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248042 prefixEnd_2248042 := by exact prefixLift 2248042
  have htrace : WordTrace (prefixWord ++ tailWord_2248042) baseStart_2248042 baseEnd_2248042 := by
    simpa [prefixWord, tailWord_2248042, baseEnd_2248042] using wordTrace_append hprefix tailTrace_2248042
  have hstable : (prefixWord ++ tailWord_2248042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248042).length < 2 ^ (prefixWord ++ tailWord_2248042).sum := by decide
  have hdescent : baseEnd_2248042 < baseStart_2248042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248064 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_2248064 : Nat := 118140960795 + 2248064 * 2 ^ 59
def prefixEnd_2248064 : Nat := 4983230072969 + 3 ^ 40 * 2248064 * 2
def baseEnd_2248064 : Nat := 769558249379465115307565

theorem tailTrace_2248064 : CollatzResearch.WordTrace tailWord_2248064 prefixEnd_2248064 769558249379465115307565 := by
  unfold tailWord_2248064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40996815063827770804691623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54662420085103694406255497 40996815063827770804691623)
  ·
    refine ⟨61495222595741656207037435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40996815063827770804691623 61495222595741656207037435)
    ·
      refine ⟨92242833893612484310556153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61495222595741656207037435 92242833893612484310556153)
      ·
        refine ⟨69182125420209363232917115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92242833893612484310556153 69182125420209363232917115)
        ·
          refine ⟨103773188130314044849375673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69182125420209363232917115 103773188130314044849375673)
          ·
            refine ⟨77829891097735533637031755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103773188130314044849375673 77829891097735533637031755)
            ·
              refine ⟨116744836646603300455547633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77829891097735533637031755 116744836646603300455547633)
              ·
                refine ⟨87558627484952475341660725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116744836646603300455547633 87558627484952475341660725)
                ·
                  refine ⟨8208621326714294563280693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87558627484952475341660725 8208621326714294563280693)
                  ·
                    refine ⟨769558249379465115307565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8208621326714294563280693 769558249379465115307565)
                    ·
                      rfl

theorem cell22_2248064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_2248064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248064 prefixEnd_2248064 := by exact prefixLift 2248064
  have htrace : WordTrace (prefixWord ++ tailWord_2248064) baseStart_2248064 baseEnd_2248064 := by
    simpa [prefixWord, tailWord_2248064, baseEnd_2248064] using wordTrace_append hprefix tailTrace_2248064
  have hstable : (prefixWord ++ tailWord_2248064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248064).length < 2 ^ (prefixWord ++ tailWord_2248064).sum := by decide
  have hdescent : baseEnd_2248064 < baseStart_2248064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248068 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2248068 : Nat := 118140960795 + 2248068 * 2 ^ 59
def prefixEnd_2248068 : Nat := 4983230072969 + 3 ^ 40 * 2248068 * 2
def baseEnd_2248068 : Nat := 769559618661210438207553

theorem tailTrace_2248068 : CollatzResearch.WordTrace tailWord_2248068 prefixEnd_2248068 769559618661210438207553 := by
  unfold tailWord_2248068
  simp only [CollatzResearch.WordTrace]
  refine ⟨40996888009820525146264429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54662517346427366861685905 40996888009820525146264429)
  ·
    refine ⟨15373833003682696929849161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40996888009820525146264429 15373833003682696929849161)
    ·
      refine ⟨11530374752762022697386871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15373833003682696929849161 11530374752762022697386871)
      ·
        refine ⟨17295562129143034046080307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11530374752762022697386871 17295562129143034046080307)
        ·
          refine ⟨25943343193714551069120461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17295562129143034046080307 25943343193714551069120461)
          ·
            refine ⟨9728753697642956650920173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25943343193714551069120461 9728753697642956650920173)
            ·
              refine ⟨3648282636616108744095065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9728753697642956650920173 3648282636616108744095065)
              ·
                refine ⟨2736211977462081558071299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648282636616108744095065 2736211977462081558071299)
                ·
                  refine ⟨4104317966193122337106949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736211977462081558071299 4104317966193122337106949)
                  ·
                    refine ⟨769559618661210438207553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104317966193122337106949 769559618661210438207553)
                    ·
                      rfl

theorem cell22_2248068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2248068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248068 prefixEnd_2248068 := by exact prefixLift 2248068
  have htrace : WordTrace (prefixWord ++ tailWord_2248068) baseStart_2248068 baseEnd_2248068 := by
    simpa [prefixWord, tailWord_2248068, baseEnd_2248068] using wordTrace_append hprefix tailTrace_2248068
  have hstable : (prefixWord ++ tailWord_2248068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248068).length < 2 ^ (prefixWord ++ tailWord_2248068).sum := by decide
  have hdescent : baseEnd_2248068 < baseStart_2248068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248096 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_2248096 : Nat := 118140960795 + 2248096 * 2 ^ 59
def prefixEnd_2248096 : Nat := 4983230072969 + 3 ^ 40 * 2248096 * 2
def baseEnd_2248096 : Nat := 769569203633427698507467

theorem tailTrace_2248096 : CollatzResearch.WordTrace tailWord_2248096 prefixEnd_2248096 769569203633427698507467 := by
  unfold tailWord_2248096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40997398631769805537274071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54663198175693074049698761 40997398631769805537274071)
  ·
    refine ⟨61496097947654708305911107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40997398631769805537274071 61496097947654708305911107)
    ·
      refine ⟨92244146921482062458866661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61496097947654708305911107 92244146921482062458866661)
      ·
        refine ⟨17295777547777886711037499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92244146921482062458866661 17295777547777886711037499)
        ·
          refine ⟨25943666321666830066556249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17295777547777886711037499 25943666321666830066556249)
          ·
            refine ⟨19457749741250122549917187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25943666321666830066556249 19457749741250122549917187)
            ·
              refine ⟨29186624611875183824875781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19457749741250122549917187 29186624611875183824875781)
              ·
                refine ⟨5472492114726596967164209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29186624611875183824875781 5472492114726596967164209)
                ·
                  refine ⟨4104369086044947725373157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5472492114726596967164209 4104369086044947725373157)
                  ·
                    refine ⟨769569203633427698507467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104369086044947725373157 769569203633427698507467)
                    ·
                      rfl

theorem cell22_2248096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_2248096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248096 prefixEnd_2248096 := by exact prefixLift 2248096
  have htrace : WordTrace (prefixWord ++ tailWord_2248096) baseStart_2248096 baseEnd_2248096 := by
    simpa [prefixWord, tailWord_2248096, baseEnd_2248096] using wordTrace_append hprefix tailTrace_2248096
  have hstable : (prefixWord ++ tailWord_2248096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248096).length < 2 ^ (prefixWord ++ tailWord_2248096).sum := by decide
  have hdescent : baseEnd_2248096 < baseStart_2248096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248194 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2248194 : Nat := 118140960795 + 2248194 * 2 ^ 59
def prefixEnd_2248194 : Nat := 4983230072969 + 3 ^ 40 * 2248194 * 2
def baseEnd_2248194 : Nat := 769602751036188109557167

theorem tailTrace_2248194 : CollatzResearch.WordTrace tailWord_2248194 prefixEnd_2248194 769602751036188109557167 := by
  unfold tailWord_2248194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499592904296143452903909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54665581078123049207743757 20499592904296143452903909)
  ·
    refine ⟨3843673669555526897419483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20499592904296143452903909 3843673669555526897419483)
    ·
      refine ⟨5765510504333290346129225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3843673669555526897419483 5765510504333290346129225)
      ·
        refine ⟨4324132878249967759596919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5765510504333290346129225 4324132878249967759596919)
        ·
          refine ⟨6486199317374951639395379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324132878249967759596919 6486199317374951639395379)
          ·
            refine ⟨9729298976062427459093069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486199317374951639395379 9729298976062427459093069)
            ·
              refine ⟨3648487116023410297159901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9729298976062427459093069 3648487116023410297159901)
              ·
                refine ⟨1368182668508778861434963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3648487116023410297159901 1368182668508778861434963)
                ·
                  refine ⟨2052274002763168292152445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368182668508778861434963 2052274002763168292152445)
                  ·
                    refine ⟨769602751036188109557167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052274002763168292152445 769602751036188109557167)
                    ·
                      rfl

theorem cell22_2248194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2248194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248194 prefixEnd_2248194 := by exact prefixLift 2248194
  have htrace : WordTrace (prefixWord ++ tailWord_2248194) baseStart_2248194 baseEnd_2248194 := by
    simpa [prefixWord, tailWord_2248194, baseEnd_2248194] using wordTrace_append hprefix tailTrace_2248194
  have hstable : (prefixWord ++ tailWord_2248194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248194).length < 2 ^ (prefixWord ++ tailWord_2248194).sum := by decide
  have hdescent : baseEnd_2248194 < baseStart_2248194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248248 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2248248 : Nat := 118140960795 + 2248248 * 2 ^ 59
def prefixEnd_2248248 : Nat := 4983230072969 + 3 ^ 40 * 2248248 * 2
def baseEnd_2248248 : Nat := 769621236339749968707001

theorem tailTrace_2248248 : CollatzResearch.WordTrace tailWord_2248248 prefixEnd_2248248 769621236339749968707001 := by
  unfold tailWord_2248248
  simp only [CollatzResearch.WordTrace]
  refine ⟨41000170579494470517040699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54666894105992627356054265 41000170579494470517040699)
  ·
    refine ⟨61500255869241705775561049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41000170579494470517040699 61500255869241705775561049)
    ·
      refine ⟨46125191901931279331670787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61500255869241705775561049 46125191901931279331670787)
      ·
        refine ⟨69187787852896918997506181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46125191901931279331670787 69187787852896918997506181)
        ·
          refine ⟨12972710222418172312032409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69187787852896918997506181 12972710222418172312032409)
          ·
            refine ⟨9729532666813629234024307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12972710222418172312032409 9729532666813629234024307)
            ·
              refine ⟨14594299000220443851036461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9729532666813629234024307 14594299000220443851036461)
              ·
                refine ⟨5472862125082666444138673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14594299000220443851036461 5472862125082666444138673)
                ·
                  refine ⟨4104646593811999833104005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5472862125082666444138673 4104646593811999833104005)
                  ·
                    refine ⟨769621236339749968707001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104646593811999833104005 769621236339749968707001)
                    ·
                      rfl

theorem cell22_2248248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2248248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248248 prefixEnd_2248248 := by exact prefixLift 2248248
  have htrace : WordTrace (prefixWord ++ tailWord_2248248) baseStart_2248248 baseEnd_2248248 := by
    simpa [prefixWord, tailWord_2248248, baseEnd_2248248] using wordTrace_append hprefix tailTrace_2248248
  have hstable : (prefixWord ++ tailWord_2248248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248248).length < 2 ^ (prefixWord ++ tailWord_2248248).sum := by decide
  have hdescent : baseEnd_2248248 < baseStart_2248248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248263 : List Nat := [1, 1, 4, 1, 6, 9]
def baseStart_2248263 : Nat := 118140960795 + 2248263 * 2 ^ 59
def prefixEnd_2248263 : Nat := 4983230072969 + 3 ^ 40 * 2248263 * 2
def baseEnd_2248263 : Nat := 9501560137608579377555

theorem tailTrace_2248263 : CollatzResearch.WordTrace tailWord_2248263 prefixEnd_2248263 9501560137608579377555 := by
  unfold tailWord_2248263
  simp only [CollatzResearch.WordTrace]
  refine ⟨82000888253934598595877443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54667258835956399063918295 82000888253934598595877443)
  ·
    refine ⟨123001332380901897893816165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82000888253934598595877443 123001332380901897893816165)
    ·
      refine ⟨23062749821419105855090531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123001332380901897893816165 23062749821419105855090531)
      ·
        refine ⟨34594124732128658782635797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23062749821419105855090531 34594124732128658782635797)
        ·
          refine ⟨1621599596818530880436053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34594124732128658782635797 1621599596818530880436053)
          ·
            refine ⟨9501560137608579377555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1621599596818530880436053 9501560137608579377555)
            ·
              rfl

theorem cell22_2248263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 9].length) (baseStart_2248263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248263 prefixEnd_2248263 := by exact prefixLift 2248263
  have htrace : WordTrace (prefixWord ++ tailWord_2248263) baseStart_2248263 baseEnd_2248263 := by
    simpa [prefixWord, tailWord_2248263, baseEnd_2248263] using wordTrace_append hprefix tailTrace_2248263
  have hstable : (prefixWord ++ tailWord_2248263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248263).length < 2 ^ (prefixWord ++ tailWord_2248263).sum := by decide
  have hdescent : baseEnd_2248263 < baseStart_2248263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248355 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 1, 4]
def baseStart_2248355 : Nat := 118140960795 + 2248355 * 2 ^ 59
def prefixEnd_2248355 : Nat := 4983230072969 + 3 ^ 40 * 2248355 * 2
def baseEnd_2248355 : Nat := 769657864626437356281673

theorem tailTrace_2248355 : CollatzResearch.WordTrace tailWord_2248355 prefixEnd_2248355 769657864626437356281673 := by
  unfold tailWord_2248355
  simp only [CollatzResearch.WordTrace]
  refine ⟨82004243769601298308226519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54669495846400865538817679 82004243769601298308226519)
  ·
    refine ⟨123006365654401947462339779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82004243769601298308226519 123006365654401947462339779)
    ·
      refine ⟨184509548481602921193509669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123006365654401947462339779 184509548481602921193509669)
      ·
        refine ⟨34595540340300547723783063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184509548481602921193509669 34595540340300547723783063)
        ·
          refine ⟨51893310510450821585674595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34595540340300547723783063 51893310510450821585674595)
          ·
            refine ⟨77839965765676232378511893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51893310510450821585674595 77839965765676232378511893)
            ·
              refine ⟨3648748395266073392742745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77839965765676232378511893 3648748395266073392742745)
              ·
                refine ⟨2736561296449555044557059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648748395266073392742745 2736561296449555044557059)
                ·
                  refine ⟨4104841944674332566835589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736561296449555044557059 4104841944674332566835589)
                  ·
                    refine ⟨769657864626437356281673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104841944674332566835589 769657864626437356281673)
                    ·
                      rfl

theorem cell22_2248355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_2248355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248355 prefixEnd_2248355 := by exact prefixLift 2248355
  have htrace : WordTrace (prefixWord ++ tailWord_2248355) baseStart_2248355 baseEnd_2248355 := by
    simpa [prefixWord, tailWord_2248355, baseEnd_2248355] using wordTrace_append hprefix tailTrace_2248355
  have hstable : (prefixWord ++ tailWord_2248355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248355).length < 2 ^ (prefixWord ++ tailWord_2248355).sum := by decide
  have hdescent : baseEnd_2248355 < baseStart_2248355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248368 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_2248368 : Nat := 118140960795 + 2248368 * 2 ^ 59
def prefixEnd_2248368 : Nat := 4983230072969 + 3 ^ 40 * 2248368 * 2
def baseEnd_2248368 : Nat := 769662314792109655706633

theorem tailTrace_2248368 : CollatzResearch.WordTrace tailWord_2248368 prefixEnd_2248368 769662314792109655706633 := by
  unfold tailWord_2248368
  simp only [CollatzResearch.WordTrace]
  refine ⟨41002358959277100764224879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54669811945702801018966505 41002358959277100764224879)
  ·
    refine ⟨61503538438915651146337319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41002358959277100764224879 61503538438915651146337319)
    ·
      refine ⟨92255307658373476719505979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61503538438915651146337319 92255307658373476719505979)
      ·
        refine ⟨138382961487560215079258969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92255307658373476719505979 138382961487560215079258969)
        ·
          refine ⟨103787221115670161309444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138382961487560215079258969 103787221115670161309444227)
          ·
            refine ⟨155680831673505241964166341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103787221115670161309444227 155680831673505241964166341)
            ·
              refine ⟨29190155938782232868281189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155680831673505241964166341 29190155938782232868281189)
              ·
                refine ⟨5473154238521668662802723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29190155938782232868281189 5473154238521668662802723)
                ·
                  refine ⟨8209731357782502994204085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473154238521668662802723 8209731357782502994204085)
                  ·
                    refine ⟨769662314792109655706633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8209731357782502994204085 769662314792109655706633)
                    ·
                      rfl

theorem cell22_2248368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_2248368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248368 prefixEnd_2248368 := by exact prefixLift 2248368
  have htrace : WordTrace (prefixWord ++ tailWord_2248368) baseStart_2248368 baseEnd_2248368 := by
    simpa [prefixWord, tailWord_2248368, baseEnd_2248368] using wordTrace_append hprefix tailTrace_2248368
  have hstable : (prefixWord ++ tailWord_2248368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248368).length < 2 ^ (prefixWord ++ tailWord_2248368).sum := by decide
  have hdescent : baseEnd_2248368 < baseStart_2248368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248417 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2248417 : Nat := 118140960795 + 2248417 * 2 ^ 59
def prefixEnd_2248417 : Nat := 4983230072969 + 3 ^ 40 * 2248417 * 2
def baseEnd_2248417 : Nat := 769679088493489861231483

theorem tailTrace_2248417 : CollatzResearch.WordTrace tailWord_2248417 prefixEnd_2248417 769679088493489861231483 := by
  unfold tailWord_2248417
  simp only [CollatzResearch.WordTrace]
  refine ⟨82006505095376682896983505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54671003396917788597989003 82006505095376682896983505)
  ·
    refine ⟨61504878821532512172737629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82006505095376682896983505 61504878821532512172737629)
    ·
      refine ⟨23064329558074692064776611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61504878821532512172737629 23064329558074692064776611)
      ·
        refine ⟨34596494337112038097164917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23064329558074692064776611 34596494337112038097164917)
        ·
          refine ⟨3243421344104253571609211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34596494337112038097164917 3243421344104253571609211)
          ·
            refine ⟨4865132016156380357413817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243421344104253571609211 4865132016156380357413817)
            ·
              refine ⟨3648849012117285268060363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865132016156380357413817 3648849012117285268060363)
              ·
                refine ⟨5473273518175927902090545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648849012117285268060363 5473273518175927902090545)
                ·
                  refine ⟨4104955138631945926567909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473273518175927902090545 4104955138631945926567909)
                  ·
                    refine ⟨769679088493489861231483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104955138631945926567909 769679088493489861231483)
                    ·
                      rfl

theorem cell22_2248417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2248417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248417 prefixEnd_2248417 := by exact prefixLift 2248417
  have htrace : WordTrace (prefixWord ++ tailWord_2248417) baseStart_2248417 baseEnd_2248417 := by
    simpa [prefixWord, tailWord_2248417, baseEnd_2248417] using wordTrace_append hprefix tailTrace_2248417
  have hstable : (prefixWord ++ tailWord_2248417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248417).length < 2 ^ (prefixWord ++ tailWord_2248417).sum := by decide
  have hdescent : baseEnd_2248417 < baseStart_2248417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248436 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2248436 : Nat := 118140960795 + 2248436 * 2 ^ 59
def prefixEnd_2248436 : Nat := 4983230072969 + 3 ^ 40 * 2248436 * 2
def baseEnd_2248436 : Nat := 769685592581780145006425

theorem tailTrace_2248436 : CollatzResearch.WordTrace tailWord_2248436 prefixEnd_2248436 769685592581780145006425 := by
  unfold tailWord_2248436
  simp only [CollatzResearch.WordTrace]
  refine ⟨41003599041153924570962581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54671465388205232761283441 41003599041153924570962581)
  ·
    refine ⟨1922043705054090214263871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41003599041153924570962581 1922043705054090214263871)
    ·
      refine ⟨2883065557581135321395807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922043705054090214263871 2883065557581135321395807)
      ·
        refine ⟨4324598336371702982093711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883065557581135321395807 4324598336371702982093711)
        ·
          refine ⟨6486897504557554473140567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324598336371702982093711 6486897504557554473140567)
          ·
            refine ⟨9730346256836331709710851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486897504557554473140567 9730346256836331709710851)
            ·
              refine ⟨14595519385254497564566277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9730346256836331709710851 14595519385254497564566277)
              ·
                refine ⟨2736659884735218293356177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14595519385254497564566277 2736659884735218293356177)
                ·
                  refine ⟨2052494913551413720017133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736659884735218293356177 2052494913551413720017133)
                  ·
                    refine ⟨769685592581780145006425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052494913551413720017133 769685592581780145006425)
                    ·
                      rfl

theorem cell22_2248436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2248436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248436 prefixEnd_2248436 := by exact prefixLift 2248436
  have htrace : WordTrace (prefixWord ++ tailWord_2248436) baseStart_2248436 baseEnd_2248436 := by
    simpa [prefixWord, tailWord_2248436, baseEnd_2248436] using wordTrace_append hprefix tailTrace_2248436
  have hstable : (prefixWord ++ tailWord_2248436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248436).length < 2 ^ (prefixWord ++ tailWord_2248436).sum := by decide
  have hdescent : baseEnd_2248436 < baseStart_2248436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248460 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_2248460 : Nat := 118140960795 + 2248460 * 2 ^ 59
def prefixEnd_2248460 : Nat := 4983230072969 + 3 ^ 40 * 2248460 * 2
def baseEnd_2248460 : Nat := 256564602757417360802117

theorem tailTrace_2248460 : CollatzResearch.WordTrace tailWord_2248460 prefixEnd_2248460 256564602757417360802117 := by
  unfold tailWord_2248460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41004036717110450620399417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54672048956147267493865889 41004036717110450620399417)
  ·
    refine ⟨30753027537832837965299563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41004036717110450620399417 30753027537832837965299563)
    ·
      refine ⟨46129541306749256947949345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30753027537832837965299563 46129541306749256947949345)
      ·
        refine ⟨34597155980061942710962009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46129541306749256947949345 34597155980061942710962009)
        ·
          refine ⟨25947866985046457033221507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34597155980061942710962009 25947866985046457033221507)
          ·
            refine ⟨38921800477569685549832261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25947866985046457033221507 38921800477569685549832261)
            ·
              refine ⟨7297837589544316040593549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38921800477569685549832261 7297837589544316040593549)
              ·
                refine ⟨2736689096079118515222581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7297837589544316040593549 2736689096079118515222581)
                ·
                  refine ⟨256564602757417360802117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736689096079118515222581 256564602757417360802117)
                  ·
                    rfl

theorem cell22_2248460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_2248460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248460 prefixEnd_2248460 := by exact prefixLift 2248460
  have htrace : WordTrace (prefixWord ++ tailWord_2248460) baseStart_2248460 baseEnd_2248460 := by
    simpa [prefixWord, tailWord_2248460, baseEnd_2248460] using wordTrace_append hprefix tailTrace_2248460
  have hstable : (prefixWord ++ tailWord_2248460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248460).length < 2 ^ (prefixWord ++ tailWord_2248460).sum := by decide
  have hdescent : baseEnd_2248460 < baseStart_2248460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248468 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2248468 : Nat := 118140960795 + 2248468 * 2 ^ 59
def prefixEnd_2248468 : Nat := 4983230072969 + 3 ^ 40 * 2248468 * 2
def baseEnd_2248468 : Nat := 769696546835742728206327

theorem tailTrace_2248468 : CollatzResearch.WordTrace tailWord_2248468 prefixEnd_2248468 769696546835742728206327 := by
  unfold tailWord_2248468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41004182609095959303545029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54672243478794612404726705 41004182609095959303545029)
  ·
    refine ⟨7688284239205492369414693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41004182609095959303545029 7688284239205492369414693)
    ·
      refine ⟨1441553294851029819265255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7688284239205492369414693 1441553294851029819265255)
      ·
        refine ⟨2162329942276544728897883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441553294851029819265255 2162329942276544728897883)
        ·
          refine ⟨3243494913414817093346825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162329942276544728897883 3243494913414817093346825)
          ·
            refine ⟨2432621185061112820010119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243494913414817093346825 2432621185061112820010119)
            ·
              refine ⟨3648931777591669230015179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432621185061112820010119 3648931777591669230015179)
              ·
                refine ⟨5473397666387503845022769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648931777591669230015179 5473397666387503845022769)
                ·
                  refine ⟨4105048249790627883767077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473397666387503845022769 4105048249790627883767077)
                  ·
                    refine ⟨769696546835742728206327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105048249790627883767077 769696546835742728206327)
                    ·
                      rfl

theorem cell22_2248468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2248468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248468 prefixEnd_2248468 := by exact prefixLift 2248468
  have htrace : WordTrace (prefixWord ++ tailWord_2248468) baseStart_2248468 baseEnd_2248468 := by
    simpa [prefixWord, tailWord_2248468, baseEnd_2248468] using wordTrace_append hprefix tailTrace_2248468
  have hstable : (prefixWord ++ tailWord_2248468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248468).length < 2 ^ (prefixWord ++ tailWord_2248468).sum := by decide
  have hdescent : baseEnd_2248468 < baseStart_2248468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248524 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_2248524 : Nat := 118140960795 + 2248524 * 2 ^ 59
def prefixEnd_2248524 : Nat := 4983230072969 + 3 ^ 40 * 2248524 * 2
def baseEnd_2248524 : Nat := 769715716780177248806155

theorem tailTrace_2248524 : CollatzResearch.WordTrace tailWord_2248524 prefixEnd_2248524 769715716780177248806155 := by
  unfold tailWord_2248524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41005203852994520085564313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54673605137326026780752417 41005203852994520085564313)
  ·
    refine ⟨30753902889745890064173235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41005203852994520085564313 30753902889745890064173235)
    ·
      refine ⟨46130854334618835096259853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30753902889745890064173235 46130854334618835096259853)
      ·
        refine ⟨17299070375482063161097445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46130854334618835096259853 17299070375482063161097445)
        ·
          refine ⟨3243575695402886842705771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17299070375482063161097445 3243575695402886842705771)
          ·
            refine ⟨4865363543104330264058657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243575695402886842705771 4865363543104330264058657)
            ·
              refine ⟨3649022657328247698043993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865363543104330264058657 3649022657328247698043993)
              ·
                refine ⟨2736766992996185773532995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649022657328247698043993 2736766992996185773532995)
                ·
                  refine ⟨4105150489494278660299493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736766992996185773532995 4105150489494278660299493)
                  ·
                    refine ⟨769715716780177248806155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105150489494278660299493 769715716780177248806155)
                    ·
                      rfl

theorem cell22_2248524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_2248524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248524 prefixEnd_2248524 := by exact prefixLift 2248524
  have htrace : WordTrace (prefixWord ++ tailWord_2248524) baseStart_2248524 baseEnd_2248524 := by
    simpa [prefixWord, tailWord_2248524, baseEnd_2248524] using wordTrace_append hprefix tailTrace_2248524
  have hstable : (prefixWord ++ tailWord_2248524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248524).length < 2 ^ (prefixWord ++ tailWord_2248524).sum := by decide
  have hdescent : baseEnd_2248524 < baseStart_2248524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248552 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2248552 : Nat := 118140960795 + 2248552 * 2 ^ 59
def prefixEnd_2248552 : Nat := 4983230072969 + 3 ^ 40 * 2248552 * 2
def baseEnd_2248552 : Nat := 769725301752394509106069

theorem tailTrace_2248552 : CollatzResearch.WordTrace tailWord_2248552 prefixEnd_2248552 769725301752394509106069 := by
  unfold tailWord_2248552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41005714474943800476573955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54674285966591733968765273 41005714474943800476573955)
  ·
    refine ⟨61508571712415700714860933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41005714474943800476573955 61508571712415700714860933)
    ·
      refine ⟨11532857196077943884036425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61508571712415700714860933 11532857196077943884036425)
      ·
        refine ⟨8649642897058457913027319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11532857196077943884036425 8649642897058457913027319)
        ·
          refine ⟨12974464345587686869540979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8649642897058457913027319 12974464345587686869540979)
          ·
            refine ⟨19461696518381530304311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974464345587686869540979 19461696518381530304311469)
            ·
              refine ⟨7298136194393073864116801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19461696518381530304311469 7298136194393073864116801)
              ·
                refine ⟨5473602145794805398087601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7298136194393073864116801 5473602145794805398087601)
                ·
                  refine ⟨4105201609346104048565701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473602145794805398087601 4105201609346104048565701)
                  ·
                    refine ⟨769725301752394509106069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105201609346104048565701 769725301752394509106069)
                    ·
                      rfl

theorem cell22_2248552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2248552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248552 prefixEnd_2248552 := by exact prefixLift 2248552
  have htrace : WordTrace (prefixWord ++ tailWord_2248552) baseStart_2248552 baseEnd_2248552 := by
    simpa [prefixWord, tailWord_2248552, baseEnd_2248552] using wordTrace_append hprefix tailTrace_2248552
  have hstable : (prefixWord ++ tailWord_2248552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248552).length < 2 ^ (prefixWord ++ tailWord_2248552).sum := by decide
  have hdescent : baseEnd_2248552 < baseStart_2248552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248612 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_2248612 : Nat := 118140960795 + 2248612 * 2 ^ 59
def prefixEnd_2248612 : Nat := 4983230072969 + 3 ^ 40 * 2248612 * 2
def baseEnd_2248612 : Nat := 256581946992858117535295

theorem tailTrace_2248612 : CollatzResearch.WordTrace tailWord_2248612 prefixEnd_2248612 256581946992858117535295 := by
  unfold tailWord_2248612
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006808664835115600166045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54675744886446820800221393 41006808664835115600166045)
  ·
    refine ⟨15377553249313168350062267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41006808664835115600166045 15377553249313168350062267)
    ·
      refine ⟨23066329873969752525093401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377553249313168350062267 23066329873969752525093401)
      ·
        refine ⟨17299747405477314393820051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23066329873969752525093401 17299747405477314393820051)
        ·
          refine ⟨25949621108215971590730077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17299747405477314393820051 25949621108215971590730077)
          ·
            refine ⟨9731107915580989346523779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25949621108215971590730077 9731107915580989346523779)
            ·
              refine ⟨14596661873371484019785669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9731107915580989346523779 14596661873371484019785669)
              ·
                refine ⟨2736874101257153253709813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14596661873371484019785669 2736874101257153253709813)
                ·
                  refine ⟨256581946992858117535295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736874101257153253709813 256581946992858117535295)
                  ·
                    rfl

theorem cell22_2248612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_2248612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248612 prefixEnd_2248612 := by exact prefixLift 2248612
  have htrace : WordTrace (prefixWord ++ tailWord_2248612) baseStart_2248612 baseEnd_2248612 := by
    simpa [prefixWord, tailWord_2248612, baseEnd_2248612] using wordTrace_append hprefix tailTrace_2248612
  have hstable : (prefixWord ++ tailWord_2248612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248612).length < 2 ^ (prefixWord ++ tailWord_2248612).sum := by decide
  have hdescent : baseEnd_2248612 < baseStart_2248612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248740 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_2248740 : Nat := 118140960795 + 2248740 * 2 ^ 59
def prefixEnd_2248740 : Nat := 4983230072969 + 3 ^ 40 * 2248740 * 2
def baseEnd_2248740 : Nat := 769789657994424685405493

theorem tailTrace_2248740 : CollatzResearch.WordTrace tailWord_2248740 prefixEnd_2248740 769789657994424685405493 := by
  unfold tailWord_2248740
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009142936603254530495837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54678857248804339373994449 41009142936603254530495837)
  ·
    refine ⟨15378428601226220448935939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41009142936603254530495837 15378428601226220448935939)
    ·
      refine ⟨23067642901839330673403909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15378428601226220448935939 23067642901839330673403909)
      ·
        refine ⟨4325183044094874501263233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23067642901839330673403909 4325183044094874501263233)
        ·
          refine ⟨3243887283071155875947425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4325183044094874501263233 3243887283071155875947425)
          ·
            refine ⟨2432915462303366906960569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243887283071155875947425 2432915462303366906960569)
            ·
              refine ⟨1824686596727525180220427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432915462303366906960569 1824686596727525180220427)
              ·
                refine ⟨2737029895091287770330641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824686596727525180220427 2737029895091287770330641)
                ·
                  refine ⟨2052772421318465827747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737029895091287770330641 2052772421318465827747981)
                  ·
                    refine ⟨769789657994424685405493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052772421318465827747981 769789657994424685405493)
                    ·
                      rfl

theorem cell22_2248740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_2248740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248740 prefixEnd_2248740 := by exact prefixLift 2248740
  have htrace : WordTrace (prefixWord ++ tailWord_2248740) baseStart_2248740 baseEnd_2248740 := by
    simpa [prefixWord, tailWord_2248740, baseEnd_2248740] using wordTrace_append hprefix tailTrace_2248740
  have hstable : (prefixWord ++ tailWord_2248740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248740).length < 2 ^ (prefixWord ++ tailWord_2248740).sum := by decide
  have hdescent : baseEnd_2248740 < baseStart_2248740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248762 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_2248762 : Nat := 118140960795 + 2248762 * 2 ^ 59
def prefixEnd_2248762 : Nat := 4983230072969 + 3 ^ 40 * 2248762 * 2
def baseEnd_2248762 : Nat := 769797189044023961355425

theorem tailTrace_2248762 : CollatzResearch.WordTrace tailWord_2248762 prefixEnd_2248762 769797189044023961355425 := by
  unfold tailWord_2248762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20504772069781701704573135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54679392186084537878861693 20504772069781701704573135)
  ·
    refine ⟨30757158104672552556859703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20504772069781701704573135 30757158104672552556859703)
    ·
      refine ⟨46135737157008828835289555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30757158104672552556859703 46135737157008828835289555)
      ·
        refine ⟨69203605735513243252934333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46135737157008828835289555 69203605735513243252934333)
        ·
          refine ⟨25951352150817466219850375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69203605735513243252934333 25951352150817466219850375)
          ·
            refine ⟨38927028226226199329775563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25951352150817466219850375 38927028226226199329775563)
            ·
              refine ⟨58390542339339298994663345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38927028226226199329775563 58390542339339298994663345)
              ·
                refine ⟨43792906754504474245997509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58390542339339298994663345 43792906754504474245997509)
                ·
                  refine ⟨8211170016469588921124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43792906754504474245997509 8211170016469588921124533)
                  ·
                    refine ⟨769797189044023961355425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211170016469588921124533 769797189044023961355425)
                    ·
                      rfl

theorem cell22_2248762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_2248762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248762 prefixEnd_2248762 := by exact prefixLift 2248762
  have htrace : WordTrace (prefixWord ++ tailWord_2248762) baseStart_2248762 baseEnd_2248762 := by
    simpa [prefixWord, tailWord_2248762, baseEnd_2248762] using wordTrace_append hprefix tailTrace_2248762
  have hstable : (prefixWord ++ tailWord_2248762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248762).length < 2 ^ (prefixWord ++ tailWord_2248762).sum := by decide
  have hdescent : baseEnd_2248762 < baseStart_2248762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248781 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2248781 : Nat := 118140960795 + 2248781 * 2 ^ 59
def prefixEnd_2248781 : Nat := 4983230072969 + 3 ^ 40 * 2248781 * 2
def baseEnd_2248781 : Nat := 256601231044104748376789

theorem tailTrace_2248781 : CollatzResearch.WordTrace tailWord_2248781 prefixEnd_2248781 256601231044104748376789 := by
  unfold tailWord_2248781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82019781266057973063234197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54679854177371982042156131 82019781266057973063234197)
  ·
    refine ⟨3844677246846467487339103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82019781266057973063234197 3844677246846467487339103)
    ·
      refine ⟨5767015870269701231008655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3844677246846467487339103 5767015870269701231008655)
      ·
        refine ⟨8650523805404551846512983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767015870269701231008655 8650523805404551846512983)
        ·
          refine ⟨12975785708106827769769475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8650523805404551846512983 12975785708106827769769475)
          ·
            refine ⟨19463678562160241654654213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12975785708106827769769475 19463678562160241654654213)
            ·
              refine ⟨3649439730405045310247665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19463678562160241654654213 3649439730405045310247665)
              ·
                refine ⟨2737079797803783982685749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649439730405045310247665 2737079797803783982685749)
                ·
                  refine ⟨256601231044104748376789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737079797803783982685749 256601231044104748376789)
                  ·
                    rfl

theorem cell22_2248781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2248781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248781 prefixEnd_2248781 := by exact prefixLift 2248781
  have htrace : WordTrace (prefixWord ++ tailWord_2248781) baseStart_2248781 baseEnd_2248781 := by
    simpa [prefixWord, tailWord_2248781, baseEnd_2248781] using wordTrace_append hprefix tailTrace_2248781
  have hstable : (prefixWord ++ tailWord_2248781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248781).length < 2 ^ (prefixWord ++ tailWord_2248781).sum := by decide
  have hdescent : baseEnd_2248781 < baseStart_2248781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248824 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_2248824 : Nat := 118140960795 + 2248824 * 2 ^ 59
def prefixEnd_2248824 : Nat := 4983230072969 + 3 ^ 40 * 2248824 * 2
def baseEnd_2248824 : Nat := 769818412911076466305235

theorem tailTrace_2248824 : CollatzResearch.WordTrace tailWord_2248824 prefixEnd_2248824 769818412911076466305235 := by
  unfold tailWord_2248824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41010674802451095703524763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54680899736601460938033017 41010674802451095703524763)
  ·
    refine ⟨61516012203676643555287145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41010674802451095703524763 61516012203676643555287145)
    ·
      refine ⟨46137009152757482666465359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61516012203676643555287145 46137009152757482666465359)
      ·
        refine ⟨69205513729136223999698039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46137009152757482666465359 69205513729136223999698039)
        ·
          refine ⟨103808270593704335999547059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69205513729136223999698039 103808270593704335999547059)
          ·
            refine ⟨155712405890556503999320589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103808270593704335999547059 155712405890556503999320589)
            ·
              refine ⟨58392152208958688999745221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155712405890556503999320589 58392152208958688999745221)
              ·
                refine ⟨10948528539179754187452229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58392152208958688999745221 10948528539179754187452229)
                ·
                  refine ⟨2052849101096203910147293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10948528539179754187452229 2052849101096203910147293)
                  ·
                    refine ⟨769818412911076466305235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052849101096203910147293 769818412911076466305235)
                    ·
                      rfl

theorem cell22_2248824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_2248824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248824 prefixEnd_2248824 := by exact prefixLift 2248824
  have htrace : WordTrace (prefixWord ++ tailWord_2248824) baseStart_2248824 baseEnd_2248824 := by
    simpa [prefixWord, tailWord_2248824, baseEnd_2248824] using wordTrace_append hprefix tailTrace_2248824
  have hstable : (prefixWord ++ tailWord_2248824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248824).length < 2 ^ (prefixWord ++ tailWord_2248824).sum := by decide
  have hdescent : baseEnd_2248824 < baseStart_2248824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248828 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2248828 : Nat := 118140960795 + 2248828 * 2 ^ 59
def prefixEnd_2248828 : Nat := 4983230072969 + 3 ^ 40 * 2248828 * 2
def baseEnd_2248828 : Nat := 769819782192821789205223

theorem tailTrace_2248828 : CollatzResearch.WordTrace tailWord_2248828 prefixEnd_2248828 769819782192821789205223 := by
  unfold tailWord_2248828
  simp only [CollatzResearch.WordTrace]
  refine ⟨41010747748443850045097569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54680996997925133393463425 41010747748443850045097569)
  ·
    refine ⟨30758060811332887533823177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41010747748443850045097569 30758060811332887533823177)
    ·
      refine ⟨23068545608499665650367383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30758060811332887533823177 23068545608499665650367383)
      ·
        refine ⟨34602818412749498475551075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23068545608499665650367383 34602818412749498475551075)
        ·
          refine ⟨51904227619124247713326613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34602818412749498475551075 51904227619124247713326613)
          ·
            refine ⟨2433010669646449111562185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51904227619124247713326613 2433010669646449111562185)
            ·
              refine ⟨1824758002234836833671639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433010669646449111562185 1824758002234836833671639)
              ·
                refine ⟨2737137003352255250507459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824758002234836833671639 2737137003352255250507459)
                ·
                  refine ⟨4105705505028382875761189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737137003352255250507459 4105705505028382875761189)
                  ·
                    refine ⟨769819782192821789205223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105705505028382875761189 769819782192821789205223)
                    ·
                      rfl

theorem cell22_2248828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2248828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248828 prefixEnd_2248828 := by exact prefixLift 2248828
  have htrace : WordTrace (prefixWord ++ tailWord_2248828) baseStart_2248828 baseEnd_2248828 := by
    simpa [prefixWord, tailWord_2248828, baseEnd_2248828] using wordTrace_append hprefix tailTrace_2248828
  have hstable : (prefixWord ++ tailWord_2248828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248828).length < 2 ^ (prefixWord ++ tailWord_2248828).sum := by decide
  have hdescent : baseEnd_2248828 < baseStart_2248828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248839 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2248839 : Nat := 118140960795 + 2248839 * 2 ^ 59
def prefixEnd_2248839 : Nat := 4983230072969 + 3 ^ 40 * 2248839 * 2
def baseEnd_2248839 : Nat := 769823547717621427180189

theorem tailTrace_2248839 : CollatzResearch.WordTrace tailWord_2248839 prefixEnd_2248839 769823547717621427180189 := by
  unfold tailWord_2248839
  simp only [CollatzResearch.WordTrace]
  refine ⟨82021896699847848968845571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54681264466565232645897047 82021896699847848968845571)
  ·
    refine ⟨123032845049771773453268357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82021896699847848968845571 123032845049771773453268357)
    ·
      refine ⟨23068658446832207522487817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123032845049771773453268357 23068658446832207522487817)
      ·
        refine ⟨17301493835124155641865863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23068658446832207522487817 17301493835124155641865863)
        ·
          refine ⟨25952240752686233462798795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17301493835124155641865863 25952240752686233462798795)
          ·
            refine ⟨38928361129029350194198193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25952240752686233462798795 38928361129029350194198193)
            ·
              refine ⟨29196270846772012645648645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38928361129029350194198193 29196270846772012645648645)
              ·
                refine ⟨5474300783769752371059121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29196270846772012645648645 5474300783769752371059121)
                ·
                  refine ⟨4105725587827314278294341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5474300783769752371059121 4105725587827314278294341)
                  ·
                    refine ⟨769823547717621427180189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105725587827314278294341 769823547717621427180189)
                    ·
                      rfl

theorem cell22_2248839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2248839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248839 prefixEnd_2248839 := by exact prefixLift 2248839
  have htrace : WordTrace (prefixWord ++ tailWord_2248839) baseStart_2248839 baseEnd_2248839 := by
    simpa [prefixWord, tailWord_2248839, baseEnd_2248839] using wordTrace_append hprefix tailTrace_2248839
  have hstable : (prefixWord ++ tailWord_2248839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248839).length < 2 ^ (prefixWord ++ tailWord_2248839).sum := by decide
  have hdescent : baseEnd_2248839 < baseStart_2248839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248858 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_2248858 : Nat := 118140960795 + 2248858 * 2 ^ 59
def prefixEnd_2248858 : Nat := 4983230072969 + 3 ^ 40 * 2248858 * 2
def baseEnd_2248858 : Nat := 769830051805911710955131

theorem tailTrace_2248858 : CollatzResearch.WordTrace tailWord_2248858 prefixEnd_2248858 769830051805911710955131 := by
  unfold tailWord_2248858
  simp only [CollatzResearch.WordTrace]
  refine ⟨20505647421694753803446807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54681726457852676809191485 20505647421694753803446807)
  ·
    refine ⟨30758471132542130705170211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20505647421694753803446807 30758471132542130705170211)
    ·
      refine ⟨46137706698813196057755317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30758471132542130705170211 46137706698813196057755317)
      ·
        refine ⟨4325410003013737130414561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46137706698813196057755317 4325410003013737130414561)
        ·
          refine ⟨3244057502260302847810921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4325410003013737130414561 3244057502260302847810921)
          ·
            refine ⟨2433043126695227135858191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244057502260302847810921 2433043126695227135858191)
            ·
              refine ⟨3649564690042840703787287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433043126695227135858191 3649564690042840703787287)
              ·
                refine ⟨5474347035064261055680931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649564690042840703787287 5474347035064261055680931)
                ·
                  refine ⟨8211520552596391583521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5474347035064261055680931 8211520552596391583521397)
                  ·
                    refine ⟨769830051805911710955131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211520552596391583521397 769830051805911710955131)
                    ·
                      rfl

theorem cell22_2248858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_2248858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248858 prefixEnd_2248858 := by exact prefixLift 2248858
  have htrace : WordTrace (prefixWord ++ tailWord_2248858) baseStart_2248858 baseEnd_2248858 := by
    simpa [prefixWord, tailWord_2248858, baseEnd_2248858] using wordTrace_append hprefix tailTrace_2248858
  have hstable : (prefixWord ++ tailWord_2248858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248858).length < 2 ^ (prefixWord ++ tailWord_2248858).sum := by decide
  have hdescent : baseEnd_2248858 < baseStart_2248858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248871 : List Nat := [1, 1, 6, 2, 2, 1, 1, 8]
def baseStart_2248871 : Nat := 118140960795 + 2248871 * 2 ^ 59
def prefixEnd_2248871 : Nat := 4983230072969 + 3 ^ 40 * 2248871 * 2
def baseEnd_2248871 : Nat := 85537166885731556708899

theorem tailTrace_2248871 : CollatzResearch.WordTrace tailWord_2248871 prefixEnd_2248871 85537166885731556708899 := by
  unfold tailWord_2248871
  simp only [CollatzResearch.WordTrace]
  refine ⟨82023063835731918434010467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54682042557154612289340311 82023063835731918434010467)
  ·
    refine ⟨123034595753597877651015701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82023063835731918434010467 123034595753597877651015701)
    ·
      refine ⟨5767246675949900514891361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123034595753597877651015701 5767246675949900514891361)
      ·
        refine ⟨4325435006962425386168521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5767246675949900514891361 4325435006962425386168521)
        ·
          refine ⟨3244076255221819039626391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4325435006962425386168521 3244076255221819039626391)
          ·
            refine ⟨4866114382832728559439587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244076255221819039626391 4866114382832728559439587)
            ·
              refine ⟨7299171574249092839159381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866114382832728559439587 7299171574249092839159381)
              ·
                refine ⟨85537166885731556708899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7299171574249092839159381 85537166885731556708899)
                ·
                  rfl

theorem cell22_2248871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 8].length) (baseStart_2248871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248871 prefixEnd_2248871 := by exact prefixLift 2248871
  have htrace : WordTrace (prefixWord ++ tailWord_2248871) baseStart_2248871 baseEnd_2248871 := by
    simpa [prefixWord, tailWord_2248871, baseEnd_2248871] using wordTrace_append hprefix tailTrace_2248871
  have hstable : (prefixWord ++ tailWord_2248871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248871).length < 2 ^ (prefixWord ++ tailWord_2248871).sum := by decide
  have hdescent : baseEnd_2248871 < baseStart_2248871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248959 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_2248959 : Nat := 118140960795 + 2248959 * 2 ^ 59
def prefixEnd_2248959 : Nat := 4983230072969 + 3 ^ 40 * 2248959 * 2
def baseEnd_2248959 : Nat := 769864626169981114179821

theorem tailTrace_2248959 : CollatzResearch.WordTrace tailWord_2248959 prefixEnd_2248959 769864626169981114179821 := by
  unfold tailWord_2248959
  simp only [CollatzResearch.WordTrace]
  refine ⟨82026273459413109463213931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54684182306275406308809287 82026273459413109463213931)
  ·
    refine ⟨123039410189119664194820897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82026273459413109463213931 123039410189119664194820897)
    ·
      refine ⟨92279557641839748146115673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123039410189119664194820897 92279557641839748146115673)
      ·
        refine ⟨69209668231379811109586755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92279557641839748146115673 69209668231379811109586755)
        ·
          refine ⟨103814502347069716664380133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69209668231379811109586755 103814502347069716664380133)
          ·
            refine ⟨19465219190075571874571275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103814502347069716664380133 19465219190075571874571275)
            ·
              refine ⟨29197828785113357811856913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19465219190075571874571275 29197828785113357811856913)
              ·
                refine ⟨21898371588835018358892685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29197828785113357811856913 21898371588835018358892685)
                ·
                  refine ⟨8211889345813131884584757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21898371588835018358892685 8211889345813131884584757)
                  ·
                    refine ⟨769864626169981114179821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211889345813131884584757 769864626169981114179821)
                    ·
                      rfl

theorem cell22_2248959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_2248959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248959 prefixEnd_2248959 := by exact prefixLift 2248959
  have htrace : WordTrace (prefixWord ++ tailWord_2248959) baseStart_2248959 baseEnd_2248959 := by
    simpa [prefixWord, tailWord_2248959, baseEnd_2248959] using wordTrace_append hprefix tailTrace_2248959
  have hstable : (prefixWord ++ tailWord_2248959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248959).length < 2 ^ (prefixWord ++ tailWord_2248959).sum := by decide
  have hdescent : baseEnd_2248959 < baseStart_2248959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248991 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_2248991 : Nat := 118140960795 + 2248991 * 2 ^ 59
def prefixEnd_2248991 : Nat := 4983230072969 + 3 ^ 40 * 2248991 * 2
def baseEnd_2248991 : Nat := 769875580423943697379723

theorem tailTrace_2248991 : CollatzResearch.WordTrace tailWord_2248991 prefixEnd_2248991 769875580423943697379723 := by
  unfold tailWord_2248991
  simp only [CollatzResearch.WordTrace]
  refine ⟨82027440595297178928378827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54684960396864785952252551 82027440595297178928378827)
  ·
    refine ⟨123041160892945768392568241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82027440595297178928378827 123041160892945768392568241)
    ·
      refine ⟨92280870669709326294426181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123041160892945768392568241 92280870669709326294426181)
      ·
        refine ⟨17302663250570498680204909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92280870669709326294426181 17302663250570498680204909)
        ·
          refine ⟨6488498718963937005076841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17302663250570498680204909 6488498718963937005076841)
          ·
            refine ⟨4866374039222952753807631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6488498718963937005076841 4866374039222952753807631)
            ·
              refine ⟨7299561058834429130711447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866374039222952753807631 7299561058834429130711447)
              ·
                refine ⟨10949341588251643696067171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299561058834429130711447 10949341588251643696067171)
                ·
                  refine ⟨16424012382377465544100757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10949341588251643696067171 16424012382377465544100757)
                  ·
                    refine ⟨769875580423943697379723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16424012382377465544100757 769875580423943697379723)
                    ·
                      rfl

theorem cell22_2248991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_2248991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248991 prefixEnd_2248991 := by exact prefixLift 2248991
  have htrace : WordTrace (prefixWord ++ tailWord_2248991) baseStart_2248991 baseEnd_2248991 := by
    simpa [prefixWord, tailWord_2248991, baseEnd_2248991] using wordTrace_append hprefix tailTrace_2248991
  have hstable : (prefixWord ++ tailWord_2248991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248991).length < 2 ^ (prefixWord ++ tailWord_2248991).sum := by decide
  have hdescent : baseEnd_2248991 < baseStart_2248991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248997 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_2248997 : Nat := 118140960795 + 2248997 * 2 ^ 59
def prefixEnd_2248997 : Nat := 4983230072969 + 3 ^ 40 * 2248997 * 2
def baseEnd_2248997 : Nat := 769877634346561681729705

theorem tailTrace_2248997 : CollatzResearch.WordTrace tailWord_2248997 prefixEnd_2248997 769877634346561681729705 := by
  unfold tailWord_2248997
  simp only [CollatzResearch.WordTrace]
  refine ⟨82027659433275441953097245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54685106288850294635398163 82027659433275441953097245)
  ·
    refine ⟨30760372287478290732411467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82027659433275441953097245 30760372287478290732411467)
    ·
      refine ⟨46140558431217436098617201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30760372287478290732411467 46140558431217436098617201)
      ·
        refine ⟨34605418823413077073962901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46140558431217436098617201 34605418823413077073962901)
        ·
          refine ⟨1622129007347487987842011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34605418823413077073962901 1622129007347487987842011)
          ·
            refine ⟨2433193511021231981763017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622129007347487987842011 2433193511021231981763017)
            ·
              refine ⟨1824895133265923986322263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433193511021231981763017 1824895133265923986322263)
              ·
                refine ⟨2737342699898885979483395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824895133265923986322263 2737342699898885979483395)
                ·
                  refine ⟨4106014049848328969225093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737342699898885979483395 4106014049848328969225093)
                  ·
                    refine ⟨769877634346561681729705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106014049848328969225093 769877634346561681729705)
                    ·
                      rfl

theorem cell22_2248997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_2248997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2248997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2248997 prefixEnd_2248997 := by exact prefixLift 2248997
  have htrace : WordTrace (prefixWord ++ tailWord_2248997) baseStart_2248997 baseEnd_2248997 := by
    simpa [prefixWord, tailWord_2248997, baseEnd_2248997] using wordTrace_append hprefix tailTrace_2248997
  have hstable : (prefixWord ++ tailWord_2248997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248997).length < 2 ^ (prefixWord ++ tailWord_2248997).sum := by decide
  have hdescent : baseEnd_2248997 < baseStart_2248997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249055 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 1, 3]
def baseStart_2249055 : Nat := 118140960795 + 2249055 * 2 ^ 59
def prefixEnd_2249055 : Nat := 4983230072969 + 3 ^ 40 * 2249055 * 2
def baseEnd_2249055 : Nat := 769897488931868863779527

theorem tailTrace_2249055 : CollatzResearch.WordTrace tailWord_2249055 prefixEnd_2249055 769897488931868863779527 := by
  unfold tailWord_2249055
  simp only [CollatzResearch.WordTrace]
  refine ⟨82029774867065317858708619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54686516578043545239139079 82029774867065317858708619)
  ·
    refine ⟨123044662300597976788062929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82029774867065317858708619 123044662300597976788062929)
    ·
      refine ⟨92283496725448482591047197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123044662300597976788062929 92283496725448482591047197)
      ·
        refine ⟨34606311272043180971642699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92283496725448482591047197 34606311272043180971642699)
        ·
          refine ⟨51909466908064771457464049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34606311272043180971642699 51909466908064771457464049)
          ·
            refine ⟨38932100181048578593098037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51909466908064771457464049 38932100181048578593098037)
            ·
              refine ⟨3649884391973304243102941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38932100181048578593098037 3649884391973304243102941)
              ·
                refine ⟨1368706646989989091163603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3649884391973304243102941 1368706646989989091163603)
                ·
                  refine ⟨2053059970484983636745405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368706646989989091163603 2053059970484983636745405)
                  ·
                    refine ⟨769897488931868863779527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053059970484983636745405 769897488931868863779527)
                    ·
                      rfl

theorem cell22_2249055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_2249055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249055 prefixEnd_2249055 := by exact prefixLift 2249055
  have htrace : WordTrace (prefixWord ++ tailWord_2249055) baseStart_2249055 baseEnd_2249055 := by
    simpa [prefixWord, tailWord_2249055, baseEnd_2249055] using wordTrace_append hprefix tailTrace_2249055
  have hstable : (prefixWord ++ tailWord_2249055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249055).length < 2 ^ (prefixWord ++ tailWord_2249055).sum := by decide
  have hdescent : baseEnd_2249055 < baseStart_2249055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249072 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_2249072 : Nat := 118140960795 + 2249072 * 2 ^ 59
def prefixEnd_2249072 : Nat := 4983230072969 + 3 ^ 40 * 2249072 * 2
def baseEnd_2249072 : Nat := 769903308379286486104475

theorem tailTrace_2249072 : CollatzResearch.WordTrace tailWord_2249072 prefixEnd_2249072 769903308379286486104475 := by
  unfold tailWord_2249072
  simp only [CollatzResearch.WordTrace]
  refine ⟨41015197454001864881038735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54686929938669153174718313 41015197454001864881038735)
  ·
    refine ⟨61522796181002797321558103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41015197454001864881038735 61522796181002797321558103)
    ·
      refine ⟨92284194271504195982337155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61522796181002797321558103 92284194271504195982337155)
      ·
        refine ⟨138426291407256293973505733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92284194271504195982337155 138426291407256293973505733)
        ·
          refine ⟨25954929638860555120032325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138426291407256293973505733 25954929638860555120032325)
          ·
            refine ⟨4866549307286354085006061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25954929638860555120032325 4866549307286354085006061)
            ·
              refine ⟨1824955990232382781877273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4866549307286354085006061 1824955990232382781877273)
              ·
                refine ⟨1368716992674287086407955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824955990232382781877273 1368716992674287086407955)
                ·
                  refine ⟨2053075489011430629611933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368716992674287086407955 2053075489011430629611933)
                  ·
                    refine ⟨769903308379286486104475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053075489011430629611933 769903308379286486104475)
                    ·
                      rfl

theorem cell22_2249072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_2249072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249072 prefixEnd_2249072 := by exact prefixLift 2249072
  have htrace : WordTrace (prefixWord ++ tailWord_2249072) baseStart_2249072 baseEnd_2249072 := by
    simpa [prefixWord, tailWord_2249072, baseEnd_2249072] using wordTrace_append hprefix tailTrace_2249072
  have hstable : (prefixWord ++ tailWord_2249072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249072).length < 2 ^ (prefixWord ++ tailWord_2249072).sum := by decide
  have hdescent : baseEnd_2249072 < baseStart_2249072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249081 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_2249081 : Nat := 118140960795 + 2249081 * 2 ^ 59
def prefixEnd_2249081 : Nat := 4983230072969 + 3 ^ 40 * 2249081 * 2
def baseEnd_2249081 : Nat := 769906389263213462629447

theorem tailTrace_2249081 : CollatzResearch.WordTrace tailWord_2249081 prefixEnd_2249081 769906389263213462629447 := by
  unfold tailWord_2249081
  simp only [CollatzResearch.WordTrace]
  refine ⟨82030723164971124299155097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54687148776647416199436731 82030723164971124299155097)
  ·
    refine ⟨61523042373728343224366323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82030723164971124299155097 61523042373728343224366323)
    ·
      refine ⟨92284563560592514836549485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61523042373728343224366323 92284563560592514836549485)
      ·
        refine ⟨34606711335222193063706057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92284563560592514836549485 34606711335222193063706057)
        ·
          refine ⟨25955033501416644797779543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34606711335222193063706057 25955033501416644797779543)
          ·
            refine ⟨38932550252124967196669315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25955033501416644797779543 38932550252124967196669315)
            ·
              refine ⟨58398825378187450795003973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38932550252124967196669315 58398825378187450795003973)
              ·
                refine ⟨10949779758410147024063245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58398825378187450795003973 10949779758410147024063245)
                ·
                  refine ⟨4106167409403805134023717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10949779758410147024063245 4106167409403805134023717)
                  ·
                    refine ⟨769906389263213462629447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106167409403805134023717 769906389263213462629447)
                    ·
                      rfl

theorem cell22_2249081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_2249081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249081 prefixEnd_2249081 := by exact prefixLift 2249081
  have htrace : WordTrace (prefixWord ++ tailWord_2249081) baseStart_2249081 baseEnd_2249081 := by
    simpa [prefixWord, tailWord_2249081, baseEnd_2249081] using wordTrace_append hprefix tailTrace_2249081
  have hstable : (prefixWord ++ tailWord_2249081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249081).length < 2 ^ (prefixWord ++ tailWord_2249081).sum := by decide
  have hdescent : baseEnd_2249081 < baseStart_2249081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249085 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2249085 : Nat := 118140960795 + 2249085 * 2 ^ 59
def prefixEnd_2249085 : Nat := 4983230072969 + 3 ^ 40 * 2249085 * 2
def baseEnd_2249085 : Nat := 256635919514986261843145

theorem tailTrace_2249085 : CollatzResearch.WordTrace tailWord_2249085 prefixEnd_2249085 256635919514986261843145 := by
  unfold tailWord_2249085
  simp only [CollatzResearch.WordTrace]
  refine ⟨82030869056956632982300709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54687246037971088654867139 82030869056956632982300709)
  ·
    refine ⟨15380787948179368684181383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82030869056956632982300709 15380787948179368684181383)
    ·
      refine ⟨23071181922269053026272075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15380787948179368684181383 23071181922269053026272075)
      ·
        refine ⟨34606772883403579539408113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23071181922269053026272075 34606772883403579539408113)
        ·
          refine ⟨25955079662552684654556085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34606772883403579539408113 25955079662552684654556085)
          ·
            refine ⟨2433288718364314186364633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25955079662552684654556085 2433288718364314186364633)
            ·
              refine ⟨1824966538773235639773475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433288718364314186364633 1824966538773235639773475)
              ·
                refine ⟨2737449808159853459660213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824966538773235639773475 2737449808159853459660213)
                ·
                  refine ⟨256635919514986261843145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737449808159853459660213 256635919514986261843145)
                  ·
                    rfl

theorem cell22_2249085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2249085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249085 prefixEnd_2249085 := by exact prefixLift 2249085
  have htrace : WordTrace (prefixWord ++ tailWord_2249085) baseStart_2249085 baseEnd_2249085 := by
    simpa [prefixWord, tailWord_2249085, baseEnd_2249085] using wordTrace_append hprefix tailTrace_2249085
  have hstable : (prefixWord ++ tailWord_2249085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249085).length < 2 ^ (prefixWord ++ tailWord_2249085).sum := by decide
  have hdescent : baseEnd_2249085 < baseStart_2249085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249096 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_2249096 : Nat := 118140960795 + 2249096 * 2 ^ 59
def prefixEnd_2249096 : Nat := 4983230072969 + 3 ^ 40 * 2249096 * 2
def baseEnd_2249096 : Nat := 256637174689919474501467

theorem tailTrace_2249096 : CollatzResearch.WordTrace tailWord_2249096 prefixEnd_2249096 256637174689919474501467 := by
  unfold tailWord_2249096
  simp only [CollatzResearch.WordTrace]
  refine ⟨41015635129958390930475571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54687513506611187907300761 41015635129958390930475571)
  ·
    refine ⟨61523452694937586395713357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41015635129958390930475571 61523452694937586395713357)
    ·
      refine ⟨23071294760601594898392509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61523452694937586395713357 23071294760601594898392509)
      ·
        refine ⟨8651735535225598086897191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23071294760601594898392509 8651735535225598086897191)
        ·
          refine ⟨12977603302838397130345787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8651735535225598086897191 12977603302838397130345787)
          ·
            refine ⟨19466404954257595695518681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12977603302838397130345787 19466404954257595695518681)
            ·
              refine ⟨14599803715693196771639011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19466404954257595695518681 14599803715693196771639011)
              ·
                refine ⟨21899705573539795157458517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14599803715693196771639011 21899705573539795157458517)
                ·
                  refine ⟨256637174689919474501467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21899705573539795157458517 256637174689919474501467)
                  ·
                    rfl

theorem cell22_2249096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_2249096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249096 prefixEnd_2249096 := by exact prefixLift 2249096
  have htrace : WordTrace (prefixWord ++ tailWord_2249096) baseStart_2249096 baseEnd_2249096 := by
    simpa [prefixWord, tailWord_2249096, baseEnd_2249096] using wordTrace_append hprefix tailTrace_2249096
  have hstable : (prefixWord ++ tailWord_2249096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249096).length < 2 ^ (prefixWord ++ tailWord_2249096).sum := by decide
  have hdescent : baseEnd_2249096 < baseStart_2249096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249111 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2249111 : Nat := 118140960795 + 2249111 * 2 ^ 59
def prefixEnd_2249111 : Nat := 4983230072969 + 3 ^ 40 * 2249111 * 2
def baseEnd_2249111 : Nat := 769916658876303384379355

theorem tailTrace_2249111 : CollatzResearch.WordTrace tailWord_2249111 prefixEnd_2249111 769916658876303384379355 := by
  unfold tailWord_2249111
  simp only [CollatzResearch.WordTrace]
  refine ⟨82031817354862439422747187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54687878236574959615164791 82031817354862439422747187)
  ·
    refine ⟨123047726032293659134120781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82031817354862439422747187 123047726032293659134120781)
    ·
      refine ⟨46142897262110122175295293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123047726032293659134120781 46142897262110122175295293)
      ·
        refine ⟨17303586473291295815735735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46142897262110122175295293 17303586473291295815735735)
        ·
          refine ⟨25955379709936943723603603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303586473291295815735735 25955379709936943723603603)
          ·
            refine ⟨38933069564905415585405405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25955379709936943723603603 38933069564905415585405405)
            ·
              refine ⟨14599901086839530844527027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38933069564905415585405405 14599901086839530844527027)
              ·
                refine ⟨21899851630259296266790541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14599901086839530844527027 21899851630259296266790541)
                ·
                  refine ⟨8212444361347236100046453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21899851630259296266790541 8212444361347236100046453)
                  ·
                    refine ⟨769916658876303384379355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8212444361347236100046453 769916658876303384379355)
                    ·
                      rfl

theorem cell22_2249111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2249111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249111 prefixEnd_2249111 := by exact prefixLift 2249111
  have htrace : WordTrace (prefixWord ++ tailWord_2249111) baseStart_2249111 baseEnd_2249111 := by
    simpa [prefixWord, tailWord_2249111, baseEnd_2249111] using wordTrace_append hprefix tailTrace_2249111
  have hstable : (prefixWord ++ tailWord_2249111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249111).length < 2 ^ (prefixWord ++ tailWord_2249111).sum := by decide
  have hdescent : baseEnd_2249111 < baseStart_2249111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249113 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 4]
def baseStart_2249113 : Nat := 118140960795 + 2249113 * 2 ^ 59
def prefixEnd_2249113 : Nat := 4983230072969 + 3 ^ 40 * 2249113 * 2
def baseEnd_2249113 : Nat := 256639114505725348609783

theorem tailTrace_2249113 : CollatzResearch.WordTrace tailWord_2249113 prefixEnd_2249113 256639114505725348609783 := by
  unfold tailWord_2249113
  simp only [CollatzResearch.WordTrace]
  refine ⟨82031890300855193764319993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54687926867236795842879995 82031890300855193764319993)
  ·
    refine ⟨61523917725641395323239995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82031890300855193764319993 61523917725641395323239995)
    ·
      refine ⟨92285876588462092984859993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61523917725641395323239995 92285876588462092984859993)
      ·
        refine ⟨69214407441346569738644995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92285876588462092984859993 69214407441346569738644995)
        ·
          refine ⟨103821611162019854607967493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69214407441346569738644995 103821611162019854607967493)
          ·
            refine ⟨19466552092878722738993905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103821611162019854607967493 19466552092878722738993905)
            ·
              refine ⟨14599914069659042054245429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19466552092878722738993905 14599914069659042054245429)
              ·
                refine ⟨1368741944030535192585509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14599914069659042054245429 1368741944030535192585509)
                ·
                  refine ⟨256639114505725348609783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368741944030535192585509 256639114505725348609783)
                  ·
                    rfl

theorem cell22_2249113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_2249113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249113 prefixEnd_2249113 := by exact prefixLift 2249113
  have htrace : WordTrace (prefixWord ++ tailWord_2249113) baseStart_2249113 baseEnd_2249113 := by
    simpa [prefixWord, tailWord_2249113, baseEnd_2249113] using wordTrace_append hprefix tailTrace_2249113
  have hstable : (prefixWord ++ tailWord_2249113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249113).length < 2 ^ (prefixWord ++ tailWord_2249113).sum := by decide
  have hdescent : baseEnd_2249113 < baseStart_2249113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249145 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_2249145 : Nat := 118140960795 + 2249145 * 2 ^ 59
def prefixEnd_2249145 : Nat := 4983230072969 + 3 ^ 40 * 2249145 * 2
def baseEnd_2249145 : Nat := 769928297771138629029251

theorem tailTrace_2249145 : CollatzResearch.WordTrace tailWord_2249145 prefixEnd_2249145 769928297771138629029251 := by
  unfold tailWord_2249145
  simp only [CollatzResearch.WordTrace]
  refine ⟨82033057436739263229484889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54688704957826175486323259 82033057436739263229484889)
  ·
    refine ⟨61524793077554447422113667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82033057436739263229484889 61524793077554447422113667)
    ·
      refine ⟨92287189616331671133170501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61524793077554447422113667 92287189616331671133170501)
      ·
        refine ⟨17303848053062188337469469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92287189616331671133170501 17303848053062188337469469)
        ·
          refine ⟨6488943019898320626551051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17303848053062188337469469 6488943019898320626551051)
          ·
            refine ⟨9733414529847480939826577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488943019898320626551051 9733414529847480939826577)
            ·
              refine ⟨7300060897385610704869933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9733414529847480939826577 7300060897385610704869933)
              ·
                refine ⟨2737522836519604014326225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7300060897385610704869933 2737522836519604014326225)
                ·
                  refine ⟨2053142127389703010744669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737522836519604014326225 2053142127389703010744669)
                  ·
                    refine ⟨769928297771138629029251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053142127389703010744669 769928297771138629029251)
                    ·
                      rfl

theorem cell22_2249145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_2249145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249145 prefixEnd_2249145 := by exact prefixLift 2249145
  have htrace : WordTrace (prefixWord ++ tailWord_2249145) baseStart_2249145 baseEnd_2249145 := by
    simpa [prefixWord, tailWord_2249145, baseEnd_2249145] using wordTrace_append hprefix tailTrace_2249145
  have hstable : (prefixWord ++ tailWord_2249145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249145).length < 2 ^ (prefixWord ++ tailWord_2249145).sum := by decide
  have hdescent : baseEnd_2249145 < baseStart_2249145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249160 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2249160 : Nat := 118140960795 + 2249160 * 2 ^ 59
def prefixEnd_2249160 : Nat := 4983230072969 + 3 ^ 40 * 2249160 * 2
def baseEnd_2249160 : Nat := 769933432577683589904205

theorem tailTrace_2249160 : CollatzResearch.WordTrace tailWord_2249160 prefixEnd_2249160 769933432577683589904205 := by
  unfold tailWord_2249160
  simp only [CollatzResearch.WordTrace]
  refine ⟨41016802265842460395640467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54689069687789947194187289 41016802265842460395640467)
  ·
    refine ⟨61525203398763690593460701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41016802265842460395640467 61525203398763690593460701)
    ·
      refine ⟨23071951274536383972547763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61525203398763690593460701 23071951274536383972547763)
      ·
        refine ⟨34607926911804575958821645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23071951274536383972547763 34607926911804575958821645)
        ·
          refine ⟨12977972591926715984558117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34607926911804575958821645 12977972591926715984558117)
          ·
            refine ⟨2433369860986259247104647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12977972591926715984558117 2433369860986259247104647)
            ·
              refine ⟨3650054791479388870656971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433369860986259247104647 3650054791479388870656971)
              ·
                refine ⟨5475082187219083305985457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650054791479388870656971 5475082187219083305985457)
                ·
                  refine ⟨4106311640414312479489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475082187219083305985457 4106311640414312479489093)
                  ·
                    refine ⟨769933432577683589904205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106311640414312479489093 769933432577683589904205)
                    ·
                      rfl

theorem cell22_2249160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2249160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249160 prefixEnd_2249160 := by exact prefixLift 2249160
  have htrace : WordTrace (prefixWord ++ tailWord_2249160) baseStart_2249160 baseEnd_2249160 := by
    simpa [prefixWord, tailWord_2249160, baseEnd_2249160] using wordTrace_append hprefix tailTrace_2249160
  have hstable : (prefixWord ++ tailWord_2249160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249160).length < 2 ^ (prefixWord ++ tailWord_2249160).sum := by decide
  have hdescent : baseEnd_2249160 < baseStart_2249160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249216 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_2249216 : Nat := 118140960795 + 2249216 * 2 ^ 59
def prefixEnd_2249216 : Nat := 4983230072969 + 3 ^ 40 * 2249216 * 2
def baseEnd_2249216 : Nat := 769952602522118110504033

theorem tailTrace_2249216 : CollatzResearch.WordTrace tailWord_2249216 prefixEnd_2249216 769952602522118110504033 := by
  unfold tailWord_2249216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41017823509741021177659751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54690431346321361570213001 41017823509741021177659751)
  ·
    refine ⟨61526735264611531766489627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41017823509741021177659751 61526735264611531766489627)
    ·
      refine ⟨92290102896917297649734441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61526735264611531766489627 92290102896917297649734441)
      ·
        refine ⟨69217577172687973237300831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92290102896917297649734441 69217577172687973237300831)
        ·
          refine ⟨103826365759031959855951247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69217577172687973237300831 103826365759031959855951247)
          ·
            refine ⟨155739548638547939783926871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103826365759031959855951247 155739548638547939783926871)
            ·
              refine ⟨233609322957821909675890307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155739548638547939783926871 233609322957821909675890307)
              ·
                refine ⟨350413984436732864513835461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233609322957821909675890307 350413984436732864513835461)
                ·
                  refine ⟨65702622081887412096344149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350413984436732864513835461 65702622081887412096344149)
                  ·
                    refine ⟨769952602522118110504033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65702622081887412096344149 769952602522118110504033)
                    ·
                      rfl

theorem cell22_2249216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_2249216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249216 prefixEnd_2249216 := by exact prefixLift 2249216
  have htrace : WordTrace (prefixWord ++ tailWord_2249216) baseStart_2249216 baseEnd_2249216 := by
    simpa [prefixWord, tailWord_2249216, baseEnd_2249216] using wordTrace_append hprefix tailTrace_2249216
  have hstable : (prefixWord ++ tailWord_2249216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249216).length < 2 ^ (prefixWord ++ tailWord_2249216).sum := by decide
  have hdescent : baseEnd_2249216 < baseStart_2249216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249231 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 10]
def baseStart_2249231 : Nat := 118140960795 + 2249231 * 2 ^ 59
def prefixEnd_2249231 : Nat := 4983230072969 + 3 ^ 40 * 2249231 * 2
def baseEnd_2249231 : Nat := 256652579109554357126329

theorem tailTrace_2249231 : CollatzResearch.WordTrace tailWord_2249231 prefixEnd_2249231 256652579109554357126329 := by
  unfold tailWord_2249231
  simp only [CollatzResearch.WordTrace]
  refine ⟨82036194114427699917115547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54690796076285133278077031 82036194114427699917115547)
  ·
    refine ⟨123054291171641549875673321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82036194114427699917115547 123054291171641549875673321)
    ·
      refine ⟨92290718378731162406754991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123054291171641549875673321 92290718378731162406754991)
      ·
        refine ⟨138436077568096743610132487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92290718378731162406754991 138436077568096743610132487)
        ·
          refine ⟨207654116352145115415198731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138436077568096743610132487 207654116352145115415198731)
          ·
            refine ⟨311481174528217673122798097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207654116352145115415198731 311481174528217673122798097)
            ·
              refine ⟨233610880896163254842098573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311481174528217673122798097 233610880896163254842098573)
              ·
                refine ⟨87604080336061220565786965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233610880896163254842098573 87604080336061220565786965)
                ·
                  refine ⟨256652579109554357126329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87604080336061220565786965 256652579109554357126329)
                  ·
                    rfl

theorem cell22_2249231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_2249231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249231 prefixEnd_2249231 := by exact prefixLift 2249231
  have htrace : WordTrace (prefixWord ++ tailWord_2249231) baseStart_2249231 baseEnd_2249231 := by
    simpa [prefixWord, tailWord_2249231, baseEnd_2249231] using wordTrace_append hprefix tailTrace_2249231
  have hstable : (prefixWord ++ tailWord_2249231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249231).length < 2 ^ (prefixWord ++ tailWord_2249231).sum := by decide
  have hdescent : baseEnd_2249231 < baseStart_2249231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249297 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_2249297 : Nat := 118140960795 + 2249297 * 2 ^ 59
def prefixEnd_2249297 : Nat := 4983230072969 + 3 ^ 40 * 2249297 * 2
def baseEnd_2249297 : Nat := 769980330477460899228785

theorem tailTrace_2249297 : CollatzResearch.WordTrace tailWord_2249297 prefixEnd_2249297 769980330477460899228785 := by
  unfold tailWord_2249297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82038601332188593189018145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54692400888125728792678763 82038601332188593189018145)
  ·
    refine ⟨61528950999141444891763609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82038601332188593189018145 61528950999141444891763609)
    ·
      refine ⟨46146713249356083668822707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61528950999141444891763609 46146713249356083668822707)
      ·
        refine ⟨69220069874034125503234061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46146713249356083668822707 69220069874034125503234061)
        ·
          refine ⟨25957526202762797063712773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69220069874034125503234061 25957526202762797063712773)
          ·
            refine ⟨4867036163018024449446145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25957526202762797063712773 4867036163018024449446145)
            ·
              refine ⟨3650277122263518337084609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4867036163018024449446145 3650277122263518337084609)
              ·
                refine ⟨2737707841697638752813457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650277122263518337084609 2737707841697638752813457)
                ·
                  refine ⟨2053280881273229064610093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737707841697638752813457 2053280881273229064610093)
                  ·
                    refine ⟨769980330477460899228785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053280881273229064610093 769980330477460899228785)
                    ·
                      rfl

theorem cell22_2249297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_2249297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249297 prefixEnd_2249297 := by exact prefixLift 2249297
  have htrace : WordTrace (prefixWord ++ tailWord_2249297) baseStart_2249297 baseEnd_2249297 := by
    simpa [prefixWord, tailWord_2249297, baseEnd_2249297] using wordTrace_append hprefix tailTrace_2249297
  have hstable : (prefixWord ++ tailWord_2249297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249297).length < 2 ^ (prefixWord ++ tailWord_2249297).sum := by decide
  have hdescent : baseEnd_2249297 < baseStart_2249297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249314 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2249314 : Nat := 118140960795 + 2249314 * 2 ^ 59
def prefixEnd_2249314 : Nat := 4983230072969 + 3 ^ 40 * 2249314 * 2
def baseEnd_2249314 : Nat := 769986149924878521553733

theorem tailTrace_2249314 : CollatzResearch.WordTrace tailWord_2249314 prefixEnd_2249314 769986149924878521553733 := by
  unfold tailWord_2249314
  simp only [CollatzResearch.WordTrace]
  refine ⟨20509805343281751273096749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54692814248751336728257997 20509805343281751273096749)
  ·
    refine ⟨7691177003730656727411281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20509805343281751273096749 7691177003730656727411281)
    ·
      refine ⟨5768382752797992545558461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7691177003730656727411281 5768382752797992545558461)
      ·
        refine ⟨2163143532299247204584423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5768382752797992545558461 2163143532299247204584423)
        ·
          refine ⟨3244715298448870806876635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163143532299247204584423 3244715298448870806876635)
          ·
            refine ⟨4867072947673306210314953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244715298448870806876635 4867072947673306210314953)
            ·
              refine ⟨3650304710754979657736215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4867072947673306210314953 3650304710754979657736215)
              ·
                refine ⟨5475457066132469486604323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650304710754979657736215 5475457066132469486604323)
                ·
                  refine ⟨8213185599198704229906485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475457066132469486604323 8213185599198704229906485)
                  ·
                    refine ⟨769986149924878521553733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8213185599198704229906485 769986149924878521553733)
                    ·
                      rfl

theorem cell22_2249314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2249314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249314 prefixEnd_2249314 := by exact prefixLift 2249314
  have htrace : WordTrace (prefixWord ++ tailWord_2249314) baseStart_2249314 baseEnd_2249314 := by
    simpa [prefixWord, tailWord_2249314, baseEnd_2249314] using wordTrace_append hprefix tailTrace_2249314
  have hstable : (prefixWord ++ tailWord_2249314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249314).length < 2 ^ (prefixWord ++ tailWord_2249314).sum := by decide
  have hdescent : baseEnd_2249314 < baseStart_2249314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249385 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_2249385 : Nat := 118140960795 + 2249385 * 2 ^ 59
def prefixEnd_2249385 : Nat := 4983230072969 + 3 ^ 40 * 2249385 * 2
def baseEnd_2249385 : Nat := 770010454675858003028515

theorem tailTrace_2249385 : CollatzResearch.WordTrace tailWord_2249385 prefixEnd_2249385 770010454675858003028515 := by
  unfold tailWord_2249385
  simp only [CollatzResearch.WordTrace]
  refine ⟨82041810955869784218221609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54694540637246522812147739 82041810955869784218221609)
  ·
    refine ⟨61531358216902338163666207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82041810955869784218221609 61531358216902338163666207)
    ·
      refine ⟨92297037325353507245499311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61531358216902338163666207 92297037325353507245499311)
      ·
        refine ⟨138445555988030260868248967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92297037325353507245499311 138445555988030260868248967)
        ·
          refine ⟨207668333982045391302373451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138445555988030260868248967 207668333982045391302373451)
          ·
            refine ⟨311502500973068086953560177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207668333982045391302373451 311502500973068086953560177)
            ·
              refine ⟨233626875729801065215170133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311502500973068086953560177 233626875729801065215170133)
              ·
                refine ⟨2737814949958606232990275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 233626875729801065215170133 2737814949958606232990275)
                ·
                  refine ⟨4106722424937909349485413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737814949958606232990275 4106722424937909349485413)
                  ·
                    refine ⟨770010454675858003028515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106722424937909349485413 770010454675858003028515)
                    ·
                      rfl

theorem cell22_2249385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_2249385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249385 prefixEnd_2249385 := by exact prefixLift 2249385
  have htrace : WordTrace (prefixWord ++ tailWord_2249385) baseStart_2249385 baseEnd_2249385 := by
    simpa [prefixWord, tailWord_2249385, baseEnd_2249385] using wordTrace_append hprefix tailTrace_2249385
  have hstable : (prefixWord ++ tailWord_2249385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249385).length < 2 ^ (prefixWord ++ tailWord_2249385).sum := by decide
  have hdescent : baseEnd_2249385 < baseStart_2249385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249393 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_2249393 : Nat := 118140960795 + 2249393 * 2 ^ 59
def prefixEnd_2249393 : Nat := 4983230072969 + 3 ^ 40 * 2249393 * 2
def baseEnd_2249393 : Nat := 770013193239348648828491

theorem tailTrace_2249393 : CollatzResearch.WordTrace tailWord_2249393 prefixEnd_2249393 770013193239348648828491 := by
  unfold tailWord_2249393
  simp only [CollatzResearch.WordTrace]
  refine ⟨82042102739840801584512833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54694735159893867723008555 82042102739840801584512833)
  ·
    refine ⟨61531577054880601188384625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82042102739840801584512833 61531577054880601188384625)
    ·
      refine ⟨46148682791160450891288469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61531577054880601188384625 46148682791160450891288469)
      ·
        refine ⟨2163219505835646135529147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46148682791160450891288469 2163219505835646135529147)
        ·
          refine ⟨3244829258753469203293721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163219505835646135529147 3244829258753469203293721)
          ·
            refine ⟨2433621944065101902470291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244829258753469203293721 2433621944065101902470291)
            ·
              refine ⟨3650432916097652853705437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433621944065101902470291 3650432916097652853705437)
              ·
                refine ⟨1368912343536619820139539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3650432916097652853705437 1368912343536619820139539)
                ·
                  refine ⟨2053368515304929730209309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368912343536619820139539 2053368515304929730209309)
                  ·
                    refine ⟨770013193239348648828491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053368515304929730209309 770013193239348648828491)
                    ·
                      rfl

theorem cell22_2249393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_2249393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249393 prefixEnd_2249393 := by exact prefixLift 2249393
  have htrace : WordTrace (prefixWord ++ tailWord_2249393) baseStart_2249393 baseEnd_2249393 := by
    simpa [prefixWord, tailWord_2249393, baseEnd_2249393] using wordTrace_append hprefix tailTrace_2249393
  have hstable : (prefixWord ++ tailWord_2249393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249393).length < 2 ^ (prefixWord ++ tailWord_2249393).sum := by decide
  have hdescent : baseEnd_2249393 < baseStart_2249393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249436 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2249436 : Nat := 118140960795 + 2249436 * 2 ^ 59
def prefixEnd_2249436 : Nat := 4983230072969 + 3 ^ 40 * 2249436 * 2
def baseEnd_2249436 : Nat := 770027913018110870003359

theorem tailTrace_2249436 : CollatzResearch.WordTrace tailWord_2249436 prefixEnd_2249436 770027913018110870003359 := by
  unfold tailWord_2249436
  simp only [CollatzResearch.WordTrace]
  refine ⟨41021835539342509964164081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54695780719123346618885441 41021835539342509964164081)
  ·
    refine ⟨30766376654506882473123061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41021835539342509964164081 30766376654506882473123061)
    ·
      refine ⟨2884347811360020231855287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30766376654506882473123061 2884347811360020231855287)
      ·
        refine ⟨4326521717040030347782931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884347811360020231855287 4326521717040030347782931)
        ·
          refine ⟨6489782575560045521674397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326521717040030347782931 6489782575560045521674397)
          ·
            refine ⟨2433668465835017070627899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6489782575560045521674397 2433668465835017070627899)
            ·
              refine ⟨3650502698752525605941849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433668465835017070627899 3650502698752525605941849)
              ·
                refine ⟨2737877024064394204456387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650502698752525605941849 2737877024064394204456387)
                ·
                  refine ⟨4106815536096591306684581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737877024064394204456387 4106815536096591306684581)
                  ·
                    refine ⟨770027913018110870003359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106815536096591306684581 770027913018110870003359)
                    ·
                      rfl

theorem cell22_2249436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2249436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249436 prefixEnd_2249436 := by exact prefixLift 2249436
  have htrace : WordTrace (prefixWord ++ tailWord_2249436) baseStart_2249436 baseEnd_2249436 := by
    simpa [prefixWord, tailWord_2249436, baseEnd_2249436] using wordTrace_append hprefix tailTrace_2249436
  have hstable : (prefixWord ++ tailWord_2249436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249436).length < 2 ^ (prefixWord ++ tailWord_2249436).sum := by decide
  have hdescent : baseEnd_2249436 < baseStart_2249436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249445 : List Nat := [1, 3, 1, 4, 1, 2, 2, 8]
def baseStart_2249445 : Nat := 118140960795 + 2249445 * 2 ^ 59
def prefixEnd_2249445 : Nat := 4983230072969 + 3 ^ 40 * 2249445 * 2
def baseEnd_2249445 : Nat := 85558999322448649614259

theorem tailTrace_2249445 : CollatzResearch.WordTrace tailWord_2249445 prefixEnd_2249445 85558999322448649614259 := by
  unfold tailWord_2249445
  simp only [CollatzResearch.WordTrace]
  refine ⟨82043999335652414465405789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54695999557101609643603859 82043999335652414465405789)
  ·
    refine ⟨30766499750869655424527171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82043999335652414465405789 30766499750869655424527171)
    ·
      refine ⟨46149749626304483136790757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30766499750869655424527171 46149749626304483136790757)
      ·
        refine ⟨8653078054932090588148267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46149749626304483136790757 8653078054932090588148267)
        ·
          refine ⟨12979617082398135882222401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8653078054932090588148267 12979617082398135882222401)
          ·
            refine ⟨9734712811798601911666801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12979617082398135882222401 9734712811798601911666801)
            ·
              refine ⟨7301034608848951433750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9734712811798601911666801 7301034608848951433750101)
              ·
                refine ⟨85558999322448649614259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7301034608848951433750101 85558999322448649614259)
                ·
                  rfl

theorem cell22_2249445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 8].length) (baseStart_2249445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249445 prefixEnd_2249445 := by exact prefixLift 2249445
  have htrace : WordTrace (prefixWord ++ tailWord_2249445) baseStart_2249445 baseEnd_2249445 := by
    simpa [prefixWord, tailWord_2249445, baseEnd_2249445] using wordTrace_append hprefix tailTrace_2249445
  have hstable : (prefixWord ++ tailWord_2249445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249445).length < 2 ^ (prefixWord ++ tailWord_2249445).sum := by decide
  have hdescent : baseEnd_2249445 < baseStart_2249445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249505 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2249505 : Nat := 118140960795 + 2249505 * 2 ^ 59
def prefixEnd_2249505 : Nat := 4983230072969 + 3 ^ 40 * 2249505 * 2
def baseEnd_2249505 : Nat := 770051533128217690028147

theorem tailTrace_2249505 : CollatzResearch.WordTrace tailWord_2249505 prefixEnd_2249505 770051533128217690028147 := by
  unfold tailWord_2249505
  simp only [CollatzResearch.WordTrace]
  refine ⟨82046187715435044712589969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54697458476956696475059979 82046187715435044712589969)
  ·
    refine ⟨61534640786576283534442477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82046187715435044712589969 61534640786576283534442477)
    ·
      refine ⟨23075490294966106325415929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61534640786576283534442477 23075490294966106325415929)
      ·
        refine ⟨17306617721224579744061947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23075490294966106325415929 17306617721224579744061947)
        ·
          refine ⟨25959926581836869616092921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17306617721224579744061947 25959926581836869616092921)
          ·
            refine ⟨19469944936377652212069691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25959926581836869616092921 19469944936377652212069691)
            ·
              refine ⟨29204917404566478318104537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19469944936377652212069691 29204917404566478318104537)
              ·
                refine ⟨21903688053424858738578403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29204917404566478318104537 21903688053424858738578403)
                ·
                  refine ⟨32855532080137288107867605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21903688053424858738578403 32855532080137288107867605)
                  ·
                    refine ⟨770051533128217690028147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32855532080137288107867605 770051533128217690028147)
                    ·
                      rfl

theorem cell22_2249505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2249505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249505 prefixEnd_2249505 := by exact prefixLift 2249505
  have htrace : WordTrace (prefixWord ++ tailWord_2249505) baseStart_2249505 baseEnd_2249505 := by
    simpa [prefixWord, tailWord_2249505, baseEnd_2249505] using wordTrace_append hprefix tailTrace_2249505
  have hstable : (prefixWord ++ tailWord_2249505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249505).length < 2 ^ (prefixWord ++ tailWord_2249505).sum := by decide
  have hdescent : baseEnd_2249505 < baseStart_2249505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249524 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2249524 : Nat := 118140960795 + 2249524 * 2 ^ 59
def prefixEnd_2249524 : Nat := 4983230072969 + 3 ^ 40 * 2249524 * 2
def baseEnd_2249524 : Nat := 256686012405502657934363

theorem tailTrace_2249524 : CollatzResearch.WordTrace tailWord_2249524 prefixEnd_2249524 256686012405502657934363 := by
  unfold tailWord_2249524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41023440351183105478765813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54697920468244140638354417 41023440351183105478765813)
  ·
    refine ⟨3845947532923416138634295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41023440351183105478765813 3845947532923416138634295)
    ·
      refine ⟨5768921299385124207951443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845947532923416138634295 5768921299385124207951443)
      ·
        refine ⟨8653381949077686311927165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768921299385124207951443 8653381949077686311927165)
        ·
          refine ⟨3245018230904132366972687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8653381949077686311927165 3245018230904132366972687)
          ·
            refine ⟨4867527346356198550459031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245018230904132366972687 4867527346356198550459031)
            ·
              refine ⟨7301291019534297825688547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867527346356198550459031 7301291019534297825688547)
              ·
                refine ⟨10951936529301446738532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7301291019534297825688547 10951936529301446738532821)
                ·
                  refine ⟨256686012405502657934363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10951936529301446738532821 256686012405502657934363)
                  ·
                    rfl

theorem cell22_2249524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2249524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249524 prefixEnd_2249524 := by exact prefixLift 2249524
  have htrace : WordTrace (prefixWord ++ tailWord_2249524) baseStart_2249524 baseEnd_2249524 := by
    simpa [prefixWord, tailWord_2249524, baseEnd_2249524] using wordTrace_append hprefix tailTrace_2249524
  have hstable : (prefixWord ++ tailWord_2249524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249524).length < 2 ^ (prefixWord ++ tailWord_2249524).sum := by decide
  have hdescent : baseEnd_2249524 < baseStart_2249524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249554 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2249554 : Nat := 118140960795 + 2249554 * 2 ^ 59
def prefixEnd_2249554 : Nat := 4983230072969 + 3 ^ 40 * 2249554 * 2
def baseEnd_2249554 : Nat := 770068306829597895552997

theorem tailTrace_2249554 : CollatzResearch.WordTrace tailWord_2249554 prefixEnd_2249554 770068306829597895552997 := by
  unfold tailWord_2249554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20511993723064381520280929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54698649928171684054082477 20511993723064381520280929)
  ·
    refine ⟨15383995292298286140210697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20511993723064381520280929 15383995292298286140210697)
    ·
      refine ⟨11537996469223714605158023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15383995292298286140210697 11537996469223714605158023)
      ·
        refine ⟨17306994703835571907737035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11537996469223714605158023 17306994703835571907737035)
        ·
          refine ⟨25960492055753357861605553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17306994703835571907737035 25960492055753357861605553)
          ·
            refine ⟨19470369041815018396204165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25960492055753357861605553 19470369041815018396204165)
            ·
              refine ⟨3650694195340315949288281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19470369041815018396204165 3650694195340315949288281)
              ·
                refine ⟨2738020646505236961966211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650694195340315949288281 2738020646505236961966211)
                ·
                  refine ⟨4107030969757855442949317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738020646505236961966211 4107030969757855442949317)
                  ·
                    refine ⟨770068306829597895552997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4107030969757855442949317 770068306829597895552997)
                    ·
                      rfl

theorem cell22_2249554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2249554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249554 prefixEnd_2249554 := by exact prefixLift 2249554
  have htrace : WordTrace (prefixWord ++ tailWord_2249554) baseStart_2249554 baseEnd_2249554 := by
    simpa [prefixWord, tailWord_2249554, baseEnd_2249554] using wordTrace_append hprefix tailTrace_2249554
  have hstable : (prefixWord ++ tailWord_2249554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249554).length < 2 ^ (prefixWord ++ tailWord_2249554).sum := by decide
  have hdescent : baseEnd_2249554 < baseStart_2249554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249567 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 6, 3]
def baseStart_2249567 : Nat := 118140960795 + 2249567 * 2 ^ 59
def prefixEnd_2249567 : Nat := 4983230072969 + 3 ^ 40 * 2249567 * 2
def baseEnd_2249567 : Nat := 770072756995270194977957

theorem tailTrace_2249567 : CollatzResearch.WordTrace tailWord_2249567 prefixEnd_2249567 770072756995270194977957 := by
  unfold tailWord_2249567
  simp only [CollatzResearch.WordTrace]
  refine ⟨82048449041210429301346955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54698966027473619534231303 82048449041210429301346955)
  ·
    refine ⟨123072673561815643952020433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82048449041210429301346955 123072673561815643952020433)
    ·
      refine ⟨92304505171361732964015325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123072673561815643952020433 92304505171361732964015325)
      ·
        refine ⟨34614189439260649861505747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92304505171361732964015325 34614189439260649861505747)
        ·
          refine ⟨51921284158890974792258621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34614189439260649861505747 51921284158890974792258621)
          ·
            refine ⟨19470481559584115547096983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51921284158890974792258621 19470481559584115547096983)
            ·
              refine ⟨29205722339376173320645475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19470481559584115547096983 29205722339376173320645475)
              ·
                refine ⟨43808583509064259980968213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29205722339376173320645475 43808583509064259980968213)
                ·
                  refine ⟨2053527351987387186607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43808583509064259980968213 2053527351987387186607885)
                  ·
                    refine ⟨770072756995270194977957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053527351987387186607885 770072756995270194977957)
                    ·
                      rfl

theorem cell22_2249567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_2249567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249567 prefixEnd_2249567 := by exact prefixLift 2249567
  have htrace : WordTrace (prefixWord ++ tailWord_2249567) baseStart_2249567 baseEnd_2249567 := by
    simpa [prefixWord, tailWord_2249567, baseEnd_2249567] using wordTrace_append hprefix tailTrace_2249567
  have hstable : (prefixWord ++ tailWord_2249567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249567).length < 2 ^ (prefixWord ++ tailWord_2249567).sum := by decide
  have hdescent : baseEnd_2249567 < baseStart_2249567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249657 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_2249657 : Nat := 118140960795 + 2249657 * 2 ^ 59
def prefixEnd_2249657 : Nat := 4983230072969 + 3 ^ 40 * 2249657 * 2
def baseEnd_2249657 : Nat := 770103565834539960227681

theorem tailTrace_2249657 : CollatzResearch.WordTrace tailWord_2249657 prefixEnd_2249657 770103565834539960227681 := by
  unfold tailWord_2249657
  simp only [CollatzResearch.WordTrace]
  refine ⟨82051731610884374672123225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54701154407256249781415483 82051731610884374672123225)
  ·
    refine ⟨61538798708163281004092419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82051731610884374672123225 61538798708163281004092419)
    ·
      refine ⟨92308198062244921506138629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61538798708163281004092419 92308198062244921506138629)
      ·
        refine ⟨17307787136670922782400993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92308198062244921506138629 17307787136670922782400993)
        ·
          refine ⟨12980840352503192086800745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17307787136670922782400993 12980840352503192086800745)
          ·
            refine ⟨9735630264377394065100559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12980840352503192086800745 9735630264377394065100559)
            ·
              refine ⟨14603445396566091097650839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9735630264377394065100559 14603445396566091097650839)
              ·
                refine ⟨21905168094849136646476259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14603445396566091097650839 21905168094849136646476259)
                ·
                  refine ⟨32857752142273704969714389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21905168094849136646476259 32857752142273704969714389)
                  ·
                    refine ⟨770103565834539960227681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32857752142273704969714389 770103565834539960227681)
                    ·
                      rfl

theorem cell22_2249657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_2249657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249657 prefixEnd_2249657 := by exact prefixLift 2249657
  have htrace : WordTrace (prefixWord ++ tailWord_2249657) baseStart_2249657 baseEnd_2249657 := by
    simpa [prefixWord, tailWord_2249657, baseEnd_2249657] using wordTrace_append hprefix tailTrace_2249657
  have hstable : (prefixWord ++ tailWord_2249657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249657).length < 2 ^ (prefixWord ++ tailWord_2249657).sum := by decide
  have hdescent : baseEnd_2249657 < baseStart_2249657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249738 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_2249738 : Nat := 118140960795 + 2249738 * 2 ^ 59
def prefixEnd_2249738 : Nat := 4983230072969 + 3 ^ 40 * 2249738 * 2
def baseEnd_2249738 : Nat := 256710431263294249650811

theorem tailTrace_2249738 : CollatzResearch.WordTrace tailWord_2249738 prefixEnd_2249738 256710431263294249650811 := by
  unfold tailWord_2249738
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513671480897731376455467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54703123949060617003881245 20513671480897731376455467)
  ·
    refine ⟨30770507221346597064683201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20513671480897731376455467 30770507221346597064683201)
    ·
      refine ⟨23077880416009947798512401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30770507221346597064683201 23077880416009947798512401)
      ·
        refine ⟨17308410312007460848884301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23077880416009947798512401 17308410312007460848884301)
        ·
          refine ⟨6490653867002797818331613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17308410312007460848884301 6490653867002797818331613)
          ·
            refine ⟨2433995200126049181874355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6490653867002797818331613 2433995200126049181874355)
            ·
              refine ⟨3650992800189073772811533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433995200126049181874355 3650992800189073772811533)
              ·
                refine ⟨1369122300070902664804325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3650992800189073772811533 1369122300070902664804325)
                ·
                  refine ⟨256710431263294249650811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369122300070902664804325 256710431263294249650811)
                  ·
                    rfl

theorem cell22_2249738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_2249738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249738 prefixEnd_2249738 := by exact prefixLift 2249738
  have htrace : WordTrace (prefixWord ++ tailWord_2249738) baseStart_2249738 baseEnd_2249738 := by
    simpa [prefixWord, tailWord_2249738, baseEnd_2249738] using wordTrace_append hprefix tailTrace_2249738
  have hstable : (prefixWord ++ tailWord_2249738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249738).length < 2 ^ (prefixWord ++ tailWord_2249738).sum := by decide
  have hdescent : baseEnd_2249738 < baseStart_2249738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249749 : List Nat := [1, 3, 2, 1, 4, 3, 8]
def baseStart_2249749 : Nat := 118140960795 + 2249749 * 2 ^ 59
def prefixEnd_2249749 : Nat := 4983230072969 + 3 ^ 40 * 2249749 * 2
def baseEnd_2249749 : Nat := 28523520715358606923237

theorem tailTrace_2249749 : CollatzResearch.WordTrace tailWord_2249749 prefixEnd_2249749 28523520715358606923237 := by
  unfold tailWord_2249749
  simp only [CollatzResearch.WordTrace]
  refine ⟨82055087126551074384472301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54703391417700716256314867 82055087126551074384472301)
  ·
    refine ⟨30770657672456652894177113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82055087126551074384472301 30770657672456652894177113)
    ·
      refine ⟨23077993254342489670632835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30770657672456652894177113 23077993254342489670632835)
      ·
        refine ⟨34616989881513734505949253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23077993254342489670632835 34616989881513734505949253)
        ·
          refine ⟨6490685602783825219865485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34616989881513734505949253 6490685602783825219865485)
          ·
            refine ⟨2434007101043934457449557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6490685602783825219865485 2434007101043934457449557)
            ·
              refine ⟨28523520715358606923237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2434007101043934457449557 28523520715358606923237)
              ·
                rfl

theorem cell22_2249749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 8].length) (baseStart_2249749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249749 prefixEnd_2249749 := by exact prefixLift 2249749
  have htrace : WordTrace (prefixWord ++ tailWord_2249749) baseStart_2249749 baseEnd_2249749 := by
    simpa [prefixWord, tailWord_2249749, baseEnd_2249749] using wordTrace_append hprefix tailTrace_2249749
  have hstable : (prefixWord ++ tailWord_2249749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249749).length < 2 ^ (prefixWord ++ tailWord_2249749).sum := by decide
  have hdescent : baseEnd_2249749 < baseStart_2249749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249751 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2249751 : Nat := 118140960795 + 2249751 * 2 ^ 59
def prefixEnd_2249751 : Nat := 4983230072969 + 3 ^ 40 * 2249751 * 2
def baseEnd_2249751 : Nat := 770135743955555048377393

theorem tailTrace_2249751 : CollatzResearch.WordTrace tailWord_2249751 prefixEnd_2249751 770135743955555048377393 := by
  unfold tailWord_2249751
  simp only [CollatzResearch.WordTrace]
  refine ⟨82055160072543828726045107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54703440048362552484030071 82055160072543828726045107)
  ·
    refine ⟨123082740108815743089067661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82055160072543828726045107 123082740108815743089067661)
    ·
      refine ⟨46156027540805903658400373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123082740108815743089067661 46156027540805903658400373)
      ·
        refine ⟨4327127581950553467975035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46156027540805903658400373 4327127581950553467975035)
        ·
          refine ⟨6490691372925830201962553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327127581950553467975035 6490691372925830201962553)
          ·
            refine ⟨4868018529694372651471915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6490691372925830201962553 4868018529694372651471915)
            ·
              refine ⟨7302027794541558977207873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868018529694372651471915 7302027794541558977207873)
              ·
                refine ⟨5476520845906169232905905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302027794541558977207873 5476520845906169232905905)
                ·
                  refine ⟨4107390634429626924679429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476520845906169232905905 4107390634429626924679429)
                  ·
                    refine ⟨770135743955555048377393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4107390634429626924679429 770135743955555048377393)
                    ·
                      rfl

theorem cell22_2249751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2249751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249751 prefixEnd_2249751 := by exact prefixLift 2249751
  have htrace : WordTrace (prefixWord ++ tailWord_2249751) baseStart_2249751 baseEnd_2249751 := by
    simpa [prefixWord, tailWord_2249751, baseEnd_2249751] using wordTrace_append hprefix tailTrace_2249751
  have hstable : (prefixWord ++ tailWord_2249751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249751).length < 2 ^ (prefixWord ++ tailWord_2249751).sum := by decide
  have hdescent : baseEnd_2249751 < baseStart_2249751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249824 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_2249824 : Nat := 118140960795 + 2249824 * 2 ^ 59
def prefixEnd_2249824 : Nat := 4983230072969 + 3 ^ 40 * 2249824 * 2
def baseEnd_2249824 : Nat := 770160733347407191302169

theorem tailTrace_2249824 : CollatzResearch.WordTrace tailWord_2249824 prefixEnd_2249824 770160733347407191302169 := by
  unfold tailWord_2249824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41028911300639681096726263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54705215067519574795635017 41028911300639681096726263)
  ·
    refine ⟨61543366950959521645089395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41028911300639681096726263 61543366950959521645089395)
    ·
      refine ⟨92315050426439282467634093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61543366950959521645089395 92315050426439282467634093)
      ·
        refine ⟨34618143909914730925362785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92315050426439282467634093 34618143909914730925362785)
        ·
          refine ⟨25963607932436048194022089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34618143909914730925362785 25963607932436048194022089)
          ·
            refine ⟨19472705949327036145516567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25963607932436048194022089 19472705949327036145516567)
            ·
              refine ⟨29209058923990554218274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19472705949327036145516567 29209058923990554218274851)
              ·
                refine ⟨43813588385985831327412277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29209058923990554218274851 43813588385985831327412277)
                ·
                  refine ⟨4107523911186171686944901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43813588385985831327412277 4107523911186171686944901)
                  ·
                    refine ⟨770160733347407191302169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4107523911186171686944901 770160733347407191302169)
                    ·
                      rfl

theorem cell22_2249824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_2249824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249824 prefixEnd_2249824 := by exact prefixLift 2249824
  have htrace : WordTrace (prefixWord ++ tailWord_2249824) baseStart_2249824 baseEnd_2249824 := by
    simpa [prefixWord, tailWord_2249824, baseEnd_2249824] using wordTrace_append hprefix tailTrace_2249824
  have hstable : (prefixWord ++ tailWord_2249824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249824).length < 2 ^ (prefixWord ++ tailWord_2249824).sum := by decide
  have hdescent : baseEnd_2249824 < baseStart_2249824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249826 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2249826 : Nat := 118140960795 + 2249826 * 2 ^ 59
def prefixEnd_2249826 : Nat := 4983230072969 + 3 ^ 40 * 2249826 * 2
def baseEnd_2249826 : Nat := 770161417988279852752163

theorem tailTrace_2249826 : CollatzResearch.WordTrace tailWord_2249826 prefixEnd_2249826 770161417988279852752163 := by
  unfold tailWord_2249826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20514473886818029133756333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54705263698181411023350221 20514473886818029133756333)
  ·
    refine ⟨7692927707556760925158625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20514473886818029133756333 7692927707556760925158625)
    ·
      refine ⟨5769695780667570693868969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7692927707556760925158625 5769695780667570693868969)
      ·
        refine ⟨4327271835500678020401727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5769695780667570693868969 4327271835500678020401727)
        ·
          refine ⟨6490907753251017030602591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327271835500678020401727 6490907753251017030602591)
          ·
            refine ⟨9736361629876525545903887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490907753251017030602591 9736361629876525545903887)
            ·
              refine ⟨14604542444814788318855831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9736361629876525545903887 14604542444814788318855831)
              ·
                refine ⟨21906813667222182478283747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14604542444814788318855831 21906813667222182478283747)
                ·
                  refine ⟨32860220500833273717425621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21906813667222182478283747 32860220500833273717425621)
                  ·
                    refine ⟨770161417988279852752163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32860220500833273717425621 770161417988279852752163)
                    ·
                      rfl

theorem cell22_2249826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2249826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249826 prefixEnd_2249826 := by exact prefixLift 2249826
  have htrace : WordTrace (prefixWord ++ tailWord_2249826) baseStart_2249826 baseEnd_2249826 := by
    simpa [prefixWord, tailWord_2249826, baseEnd_2249826] using wordTrace_append hprefix tailTrace_2249826
  have hstable : (prefixWord ++ tailWord_2249826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249826).length < 2 ^ (prefixWord ++ tailWord_2249826).sum := by decide
  have hdescent : baseEnd_2249826 < baseStart_2249826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249839 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 6]
def baseStart_2249839 : Nat := 118140960795 + 2249839 * 2 ^ 59
def prefixEnd_2249839 : Nat := 4983230072969 + 3 ^ 40 * 2249839 * 2
def baseEnd_2249839 : Nat := 256721956051317384059041

theorem tailTrace_2249839 : CollatzResearch.WordTrace tailWord_2249839 prefixEnd_2249839 256721956051317384059041 := by
  unfold tailWord_2249839
  simp only [CollatzResearch.WordTrace]
  refine ⟨82058369696225019755248571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54705579797483346503499047 82058369696225019755248571)
  ·
    refine ⟨123087554544337529632872857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82058369696225019755248571 123087554544337529632872857)
    ·
      refine ⟨92315665908253147224654643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123087554544337529632872857 92315665908253147224654643)
      ·
        refine ⟨138473498862379720836981965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92315665908253147224654643 138473498862379720836981965)
        ·
          refine ⟨51927562073392395313868237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138473498862379720836981965 51927562073392395313868237)
          ·
            refine ⟨19472835777522148242700589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51927562073392395313868237 19472835777522148242700589)
            ·
              refine ⟨7302313416570805591012721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19472835777522148242700589 7302313416570805591012721)
              ·
                refine ⟨5476735062428104193259541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302313416570805591012721 5476735062428104193259541)
                ·
                  refine ⟨256721956051317384059041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5476735062428104193259541 256721956051317384059041)
                  ·
                    rfl

theorem cell22_2249839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_2249839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249839 prefixEnd_2249839 := by exact prefixLift 2249839
  have htrace : WordTrace (prefixWord ++ tailWord_2249839) baseStart_2249839 baseEnd_2249839 := by
    simpa [prefixWord, tailWord_2249839, baseEnd_2249839] using wordTrace_append hprefix tailTrace_2249839
  have hstable : (prefixWord ++ tailWord_2249839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249839).length < 2 ^ (prefixWord ++ tailWord_2249839).sum := by decide
  have hdescent : baseEnd_2249839 < baseStart_2249839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249856 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_2249856 : Nat := 118140960795 + 2249856 * 2 ^ 59
def prefixEnd_2249856 : Nat := 4983230072969 + 3 ^ 40 * 2249856 * 2
def baseEnd_2249856 : Nat := 256723895867123258167357

theorem tailTrace_2249856 : CollatzResearch.WordTrace tailWord_2249856 prefixEnd_2249856 256723895867123258167357 := by
  unfold tailWord_2249856
  simp only [CollatzResearch.WordTrace]
  refine ⟨41029494868581715829308711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54705993158108954439078281 41029494868581715829308711)
  ·
    refine ⟨61544242302872573743963067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41029494868581715829308711 61544242302872573743963067)
    ·
      refine ⟨92316363454308860615944601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61544242302872573743963067 92316363454308860615944601)
      ·
        refine ⟨69237272590731645461958451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92316363454308860615944601 69237272590731645461958451)
        ·
          refine ⟨103855908886097468192937677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69237272590731645461958451 103855908886097468192937677)
          ·
            refine ⟨38945965832286550572351629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103855908886097468192937677 38945965832286550572351629)
            ·
              refine ⟨14604737187107456464631861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38945965832286550572351629 14604737187107456464631861)
              ·
                refine ⟨1369194111291324043559237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14604737187107456464631861 1369194111291324043559237)
                ·
                  refine ⟨256723895867123258167357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369194111291324043559237 256723895867123258167357)
                  ·
                    rfl

theorem cell22_2249856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_2249856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249856 prefixEnd_2249856 := by exact prefixLift 2249856
  have htrace : WordTrace (prefixWord ++ tailWord_2249856) baseStart_2249856 baseEnd_2249856 := by
    simpa [prefixWord, tailWord_2249856, baseEnd_2249856] using wordTrace_append hprefix tailTrace_2249856
  have hstable : (prefixWord ++ tailWord_2249856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249856).length < 2 ^ (prefixWord ++ tailWord_2249856).sum := by decide
  have hdescent : baseEnd_2249856 < baseStart_2249856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249914 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_2249914 : Nat := 118140960795 + 2249914 * 2 ^ 59
def prefixEnd_2249914 : Nat := 4983230072969 + 3 ^ 40 * 2249914 * 2
def baseEnd_2249914 : Nat := 770191542186676956551893

theorem tailTrace_2249914 : CollatzResearch.WordTrace tailWord_2249914 prefixEnd_2249914 770191542186676956551893 := by
  unfold tailWord_2249914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515276292738326891057199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54707403447302205042819197 20515276292738326891057199)
  ·
    refine ⟨30772914439107490336585799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20515276292738326891057199 30772914439107490336585799)
    ·
      refine ⟨46159371658661235504878699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30772914439107490336585799 46159371658661235504878699)
      ·
        refine ⟨69239057487991853257318049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46159371658661235504878699 69239057487991853257318049)
        ·
          refine ⟨51929293115993889942988537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69239057487991853257318049 51929293115993889942988537)
          ·
            refine ⟨38946969836995417457241403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51929293115993889942988537 38946969836995417457241403)
            ·
              refine ⟨58420454755493126185862105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38946969836995417457241403 58420454755493126185862105)
              ·
                refine ⟨43815341066619844639396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58420454755493126185862105 43815341066619844639396579)
                ·
                  refine ⟨65723011599929766959094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43815341066619844639396579 65723011599929766959094869)
                  ·
                    refine ⟨770191542186676956551893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65723011599929766959094869 770191542186676956551893)
                    ·
                      rfl

theorem cell22_2249914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_2249914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2249914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2249914 prefixEnd_2249914 := by exact prefixLift 2249914
  have htrace : WordTrace (prefixWord ++ tailWord_2249914) baseStart_2249914 baseEnd_2249914 := by
    simpa [prefixWord, tailWord_2249914, baseEnd_2249914] using wordTrace_append hprefix tailTrace_2249914
  have hstable : (prefixWord ++ tailWord_2249914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249914).length < 2 ^ (prefixWord ++ tailWord_2249914).sum := by decide
  have hdescent : baseEnd_2249914 < baseStart_2249914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250098 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_2250098 : Nat := 118140960795 + 2250098 * 2 ^ 59
def prefixEnd_2250098 : Nat := 4983230072969 + 3 ^ 40 * 2250098 * 2
def baseEnd_2250098 : Nat := 256751509715653936650443

theorem tailTrace_2250098 : CollatzResearch.WordTrace tailWord_2250098 prefixEnd_2250098 256751509715653936650443 := by
  unfold tailWord_2250098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516954050571676747231737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54711877468191137992617965 20516954050571676747231737)
  ·
    refine ⟨15387715537928757560423803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20516954050571676747231737 15387715537928757560423803)
    ·
      refine ⟨23081573306893136340635705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387715537928757560423803 23081573306893136340635705)
      ·
        refine ⟨17311179980169852255476779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23081573306893136340635705 17311179980169852255476779)
        ·
          refine ⟨25966769970254778383215169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17311179980169852255476779 25966769970254778383215169)
          ·
            refine ⟨19475077477691083787411377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25966769970254778383215169 19475077477691083787411377)
            ·
              refine ⟨14606308108268312840558533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475077477691083787411377 14606308108268312840558533)
              ·
                refine ⟨2738682770300308657604725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14606308108268312840558533 2738682770300308657604725)
                ·
                  refine ⟨256751509715653936650443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738682770300308657604725 256751509715653936650443)
                  ·
                    rfl

theorem cell22_2250098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_2250098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250098 prefixEnd_2250098 := by exact prefixLift 2250098
  have htrace : WordTrace (prefixWord ++ tailWord_2250098) baseStart_2250098 baseEnd_2250098 := by
    simpa [prefixWord, tailWord_2250098, baseEnd_2250098] using wordTrace_append hprefix tailTrace_2250098
  have hstable : (prefixWord ++ tailWord_2250098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250098).length < 2 ^ (prefixWord ++ tailWord_2250098).sum := by decide
  have hdescent : baseEnd_2250098 < baseStart_2250098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250115 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 5]
def baseStart_2250115 : Nat := 118140960795 + 2250115 * 2 ^ 59
def prefixEnd_2250115 : Nat := 4983230072969 + 3 ^ 40 * 2250115 * 2
def baseEnd_2250115 : Nat := 256753449531459810758759

theorem tailTrace_2250115 : CollatzResearch.WordTrace tailWord_2250115 prefixEnd_2250115 256753449531459810758759 := by
  unfold tailWord_2250115
  simp only [CollatzResearch.WordTrace]
  refine ⟨82068436243225118892295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54712290828816745928197199 82068436243225118892295799)
  ·
    refine ⟨123102654364837678338443699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82068436243225118892295799 123102654364837678338443699)
    ·
      refine ⟨184653981547256517507665549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123102654364837678338443699 184653981547256517507665549)
      ·
        refine ⟨69245243080221194065374581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184653981547256517507665549 69245243080221194065374581)
        ·
          refine ⟨6491741538770736943628867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69245243080221194065374581 6491741538770736943628867)
          ·
            refine ⟨9737612308156105415443301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6491741538770736943628867 9737612308156105415443301)
            ·
              refine ⟨1825802307779269765395619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9737612308156105415443301 1825802307779269765395619)
              ·
                refine ⟨2738703461668904648093429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825802307779269765395619 2738703461668904648093429)
                ·
                  refine ⟨256753449531459810758759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738703461668904648093429 256753449531459810758759)
                  ·
                    rfl

theorem cell22_2250115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 5].length) (baseStart_2250115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250115 prefixEnd_2250115 := by exact prefixLift 2250115
  have htrace : WordTrace (prefixWord ++ tailWord_2250115) baseStart_2250115 baseEnd_2250115 := by
    simpa [prefixWord, tailWord_2250115, baseEnd_2250115] using wordTrace_append hprefix tailTrace_2250115
  have hstable : (prefixWord ++ tailWord_2250115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250115).length < 2 ^ (prefixWord ++ tailWord_2250115).sum := by decide
  have hdescent : baseEnd_2250115 < baseStart_2250115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250173 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2250173 : Nat := 118140960795 + 2250173 * 2 ^ 59
def prefixEnd_2250173 : Nat := 4983230072969 + 3 ^ 40 * 2250173 * 2
def baseEnd_2250173 : Nat := 770280203179686614326099

theorem tailTrace_2250173 : CollatzResearch.WordTrace tailWord_2250173 prefixEnd_2250173 770280203179686614326099 := by
  unfold tailWord_2250173
  simp only [CollatzResearch.WordTrace]
  refine ⟨82070551677014994797907173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54713701118009996531938115 82070551677014994797907173)
  ·
    refine ⟨15388228439440311524607595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82070551677014994797907173 15388228439440311524607595)
    ·
      refine ⟨23082342659160467286911393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388228439440311524607595 23082342659160467286911393)
      ·
        refine ⟨17311756994370350465183545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23082342659160467286911393 17311756994370350465183545)
        ·
          refine ⟨12983817745777762848887659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17311756994370350465183545 12983817745777762848887659)
          ·
            refine ⟨19475726618666644273331489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12983817745777762848887659 19475726618666644273331489)
            ·
              refine ⟨14606794963999983204998617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475726618666644273331489 14606794963999983204998617)
              ·
                refine ⟨10955096222999987403748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14606794963999983204998617 10955096222999987403748963)
                ·
                  refine ⟨16432644334499981105623445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10955096222999987403748963 16432644334499981105623445)
                  ·
                    refine ⟨770280203179686614326099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16432644334499981105623445 770280203179686614326099)
                    ·
                      rfl

theorem cell22_2250173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2250173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250173 prefixEnd_2250173 := by exact prefixLift 2250173
  have htrace : WordTrace (prefixWord ++ tailWord_2250173) baseStart_2250173 baseEnd_2250173 := by
    simpa [prefixWord, tailWord_2250173, baseEnd_2250173] using wordTrace_append hprefix tailTrace_2250173
  have hstable : (prefixWord ++ tailWord_2250173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250173).length < 2 ^ (prefixWord ++ tailWord_2250173).sum := by decide
  have hdescent : baseEnd_2250173 < baseStart_2250173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250190 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2250190 : Nat := 118140960795 + 2250190 * 2 ^ 59
def prefixEnd_2250190 : Nat := 4983230072969 + 3 ^ 40 * 2250190 * 2
def baseEnd_2250190 : Nat := 770286022627104236651047

theorem tailTrace_2250190 : CollatzResearch.WordTrace tailWord_2250190 prefixEnd_2250190 770286022627104236651047 := by
  unfold tailWord_2250190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258896464744175837659503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54714114478635604467517349 10258896464744175837659503)
  ·
    refine ⟨15388344697116263756489255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258896464744175837659503 15388344697116263756489255)
    ·
      refine ⟨23082517045674395634733883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388344697116263756489255 23082517045674395634733883)
      ·
        refine ⟨34623775568511593452100825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23082517045674395634733883 34623775568511593452100825)
        ·
          refine ⟨25967831676383695089075619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34623775568511593452100825 25967831676383695089075619)
          ·
            refine ⟨38951747514575542633613429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25967831676383695089075619 38951747514575542633613429)
            ·
              refine ⟨3651726329491457121901259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38951747514575542633613429 3651726329491457121901259)
              ·
                refine ⟨5477589494237185682851889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651726329491457121901259 5477589494237185682851889)
                ·
                  refine ⟨4108192120677889262138917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477589494237185682851889 4108192120677889262138917)
                  ·
                    refine ⟨770286022627104236651047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108192120677889262138917 770286022627104236651047)
                    ·
                      rfl

theorem cell22_2250190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2250190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250190 prefixEnd_2250190 := by exact prefixLift 2250190
  have htrace : WordTrace (prefixWord ++ tailWord_2250190) baseStart_2250190 baseEnd_2250190 := by
    simpa [prefixWord, tailWord_2250190, baseEnd_2250190] using wordTrace_append hprefix tailTrace_2250190
  have hstable : (prefixWord ++ tailWord_2250190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250190).length < 2 ^ (prefixWord ++ tailWord_2250190).sum := by decide
  have hdescent : baseEnd_2250190 < baseStart_2250190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250196 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2250196 : Nat := 118140960795 + 2250196 * 2 ^ 59
def prefixEnd_2250196 : Nat := 4983230072969 + 3 ^ 40 * 2250196 * 2
def baseEnd_2250196 : Nat := 770288076549722221001029

theorem tailTrace_2250196 : CollatzResearch.WordTrace tailWord_2250196 prefixEnd_2250196 770288076549722221001029 := by
  unfold tailWord_2250196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41035695277965834862997221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54714260370621113150662961 41035695277965834862997221)
  ·
    refine ⟨7694192864618594036811979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41035695277965834862997221 7694192864618594036811979)
    ·
      refine ⟨11541289296927891055217969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694192864618594036811979 11541289296927891055217969)
      ·
        refine ⟨8655966972695918291413477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11541289296927891055217969 8655966972695918291413477)
        ·
          refine ⟨1622993807380484679640027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8655966972695918291413477 1622993807380484679640027)
          ·
            refine ⟨2434490711070727019460041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622993807380484679640027 2434490711070727019460041)
            ·
              refine ⟨1825868033303045264595031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2434490711070727019460041 1825868033303045264595031)
              ·
                refine ⟨2738802049954567896892547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825868033303045264595031 2738802049954567896892547)
                ·
                  refine ⟨4108203074931851845338821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738802049954567896892547 4108203074931851845338821)
                  ·
                    refine ⟨770288076549722221001029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108203074931851845338821 770288076549722221001029)
                    ·
                      rfl

theorem cell22_2250196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2250196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250196 prefixEnd_2250196 := by exact prefixLift 2250196
  have htrace : WordTrace (prefixWord ++ tailWord_2250196) baseStart_2250196 baseEnd_2250196 := by
    simpa [prefixWord, tailWord_2250196, baseEnd_2250196] using wordTrace_append hprefix tailTrace_2250196
  have hstable : (prefixWord ++ tailWord_2250196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250196).length < 2 ^ (prefixWord ++ tailWord_2250196).sum := by decide
  have hdescent : baseEnd_2250196 < baseStart_2250196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250248 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2250248 : Nat := 118140960795 + 2250248 * 2 ^ 59
def prefixEnd_2250248 : Nat := 4983230072969 + 3 ^ 40 * 2250248 * 2
def baseEnd_2250248 : Nat := 770305877212411418700869

theorem tailTrace_2250248 : CollatzResearch.WordTrace tailWord_2250248 prefixEnd_2250248 770305877212411418700869 := by
  unfold tailWord_2250248
  simp only [CollatzResearch.WordTrace]
  refine ⟨41036643575871641303443699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54715524767828855071258265 41036643575871641303443699)
  ·
    refine ⟨61554965363807461955165549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41036643575871641303443699 61554965363807461955165549)
    ·
      refine ⟨23083112011427798233187081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61554965363807461955165549 23083112011427798233187081)
      ·
        refine ⟨17312334008570848674890311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23083112011427798233187081 17312334008570848674890311)
        ·
          refine ⟨25968501012856273012335467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17312334008570848674890311 25968501012856273012335467)
          ·
            refine ⟨38952751519284409518503201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25968501012856273012335467 38952751519284409518503201)
            ·
              refine ⟨29214563639463307138877401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38952751519284409518503201 29214563639463307138877401)
              ·
                refine ⟨21910922729597480354158051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29214563639463307138877401 21910922729597480354158051)
                ·
                  refine ⟨32866384094396220531237077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21910922729597480354158051 32866384094396220531237077)
                  ·
                    refine ⟨770305877212411418700869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32866384094396220531237077 770305877212411418700869)
                    ·
                      rfl

theorem cell22_2250248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2250248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250248 prefixEnd_2250248 := by exact prefixLift 2250248
  have htrace : WordTrace (prefixWord ++ tailWord_2250248) baseStart_2250248 baseEnd_2250248 := by
    simpa [prefixWord, tailWord_2250248, baseEnd_2250248] using wordTrace_append hprefix tailTrace_2250248
  have hstable : (prefixWord ++ tailWord_2250248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250248).length < 2 ^ (prefixWord ++ tailWord_2250248).sum := by decide
  have hdescent : baseEnd_2250248 < baseStart_2250248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250297 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_2250297 : Nat := 118140960795 + 2250297 * 2 ^ 59
def prefixEnd_2250297 : Nat := 4983230072969 + 3 ^ 40 * 2250297 * 2
def baseEnd_2250297 : Nat := 770322650913791624225719

theorem tailTrace_2250297 : CollatzResearch.WordTrace tailWord_2250297 prefixEnd_2250297 770322650913791624225719 := by
  unfold tailWord_2250297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82075074328565763975421145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54716716219043842650280763 82075074328565763975421145)
  ·
    refine ⟨61556305746424322981565859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82075074328565763975421145 61556305746424322981565859)
    ·
      refine ⟨92334458619636484472348789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61556305746424322981565859 92334458619636484472348789)
      ·
        refine ⟨8656355495590920419282699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92334458619636484472348789 8656355495590920419282699)
        ·
          refine ⟨12984533243386380628924049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656355495590920419282699 12984533243386380628924049)
          ·
            refine ⟨9738399932539785471693037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12984533243386380628924049 9738399932539785471693037)
            ·
              refine ⟨3651899974702419551884889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9738399932539785471693037 3651899974702419551884889)
              ·
                refine ⟨2738924981026814663913667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3651899974702419551884889 2738924981026814663913667)
                ·
                  refine ⟨4108387471540221995870501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738924981026814663913667 4108387471540221995870501)
                  ·
                    refine ⟨770322650913791624225719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108387471540221995870501 770322650913791624225719)
                    ·
                      rfl

theorem cell22_2250297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_2250297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250297 prefixEnd_2250297 := by exact prefixLift 2250297
  have htrace : WordTrace (prefixWord ++ tailWord_2250297) baseStart_2250297 baseEnd_2250297 := by
    simpa [prefixWord, tailWord_2250297, baseEnd_2250297] using wordTrace_append hprefix tailTrace_2250297
  have hstable : (prefixWord ++ tailWord_2250297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250297).length < 2 ^ (prefixWord ++ tailWord_2250297).sum := by decide
  have hdescent : baseEnd_2250297 < baseStart_2250297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250327 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 2, 3]
def baseStart_2250327 : Nat := 118140960795 + 2250327 * 2 ^ 59
def prefixEnd_2250327 : Nat := 4983230072969 + 3 ^ 40 * 2250327 * 2
def baseEnd_2250327 : Nat := 770332920526881545975627

theorem tailTrace_2250327 : CollatzResearch.WordTrace tailWord_2250327 prefixEnd_2250327 770332920526881545975627 := by
  unfold tailWord_2250327
  simp only [CollatzResearch.WordTrace]
  refine ⟨82076168518457079099013235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54717445678971386066008823 82076168518457079099013235)
  ·
    refine ⟨123114252777685618648519853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82076168518457079099013235 123114252777685618648519853)
    ·
      refine ⟨46167844791632106993194945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123114252777685618648519853 46167844791632106993194945)
      ·
        refine ⟨34625883593724080244896209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46167844791632106993194945 34625883593724080244896209)
        ·
          refine ⟨25969412695293060183672157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34625883593724080244896209 25969412695293060183672157)
          ·
            refine ⟨9738529760734897568877059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25969412695293060183672157 9738529760734897568877059)
            ·
              refine ⟨14607794641102346353315589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9738529760734897568877059 14607794641102346353315589)
              ·
                refine ⟨2738961495206689941246673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14607794641102346353315589 2738961495206689941246673)
                ·
                  refine ⟨2054221121405017455935005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738961495206689941246673 2054221121405017455935005)
                  ·
                    refine ⟨770332920526881545975627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054221121405017455935005 770332920526881545975627)
                    ·
                      rfl

theorem cell22_2250327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_2250327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250327 prefixEnd_2250327 := by exact prefixLift 2250327
  have htrace : WordTrace (prefixWord ++ tailWord_2250327) baseStart_2250327 baseEnd_2250327 := by
    simpa [prefixWord, tailWord_2250327, baseEnd_2250327] using wordTrace_append hprefix tailTrace_2250327
  have hstable : (prefixWord ++ tailWord_2250327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250327).length < 2 ^ (prefixWord ++ tailWord_2250327).sum := by decide
  have hdescent : baseEnd_2250327 < baseStart_2250327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250340 : List Nat := [2, 3, 1, 1, 2, 3, 3, 7]
def baseStart_2250340 : Nat := 118140960795 + 2250340 * 2 ^ 59
def prefixEnd_2250340 : Nat := 4983230072969 + 3 ^ 40 * 2250340 * 2
def baseEnd_2250340 : Nat := 85593041188061538377843

theorem tailTrace_2250340 : CollatzResearch.WordTrace tailWord_2250340 prefixEnd_2250340 85593041188061538377843 := by
  unfold tailWord_2250340
  simp only [CollatzResearch.WordTrace]
  refine ⟨41038321333704991159618237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54717761778273321546157649 41038321333704991159618237)
  ·
    refine ⟨15389370500139371684856839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41038321333704991159618237 15389370500139371684856839)
    ·
      refine ⟨23084055750209057527285259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15389370500139371684856839 23084055750209057527285259)
      ·
        refine ⟨34626083625313586290927889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23084055750209057527285259 34626083625313586290927889)
        ·
          refine ⟨25969562718985189718195917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34626083625313586290927889 25969562718985189718195917)
          ·
            refine ⟨9738586019619446144323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25969562718985189718195917 9738586019619446144323469)
            ·
              refine ⟨3651969757357292304121301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9738586019619446144323469 3651969757357292304121301)
              ·
                refine ⟨85593041188061538377843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3651969757357292304121301 85593041188061538377843)
                ·
                  rfl

theorem cell22_2250340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_2250340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250340 prefixEnd_2250340 := by exact prefixLift 2250340
  have htrace : WordTrace (prefixWord ++ tailWord_2250340) baseStart_2250340 baseEnd_2250340 := by
    simpa [prefixWord, tailWord_2250340, baseEnd_2250340] using wordTrace_append hprefix tailTrace_2250340
  have hstable : (prefixWord ++ tailWord_2250340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250340).length < 2 ^ (prefixWord ++ tailWord_2250340).sum := by decide
  have hdescent : baseEnd_2250340 < baseStart_2250340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250344 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2250344 : Nat := 118140960795 + 2250344 * 2 ^ 59
def prefixEnd_2250344 : Nat := 4983230072969 + 3 ^ 40 * 2250344 * 2
def baseEnd_2250344 : Nat := 770338739974299168300575

theorem tailTrace_2250344 : CollatzResearch.WordTrace tailWord_2250344 prefixEnd_2250344 770338739974299168300575 := by
  unfold tailWord_2250344
  simp only [CollatzResearch.WordTrace]
  refine ⟨41038394279697745501191043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54717859039596994001588057 41038394279697745501191043)
  ·
    refine ⟨61557591419546618251786565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41038394279697745501191043 61557591419546618251786565)
    ·
      refine ⟨11542048391164990922209981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61557591419546618251786565 11542048391164990922209981)
      ·
        refine ⟨4328268146686871595828743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11542048391164990922209981 4328268146686871595828743)
        ·
          refine ⟨6492402220030307393743115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328268146686871595828743 6492402220030307393743115)
          ·
            refine ⟨9738603330045461090614673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6492402220030307393743115 9738603330045461090614673)
            ·
              refine ⟨7303952497534095817961005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738603330045461090614673 7303952497534095817961005)
              ·
                refine ⟨2738982186575285931735377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7303952497534095817961005 2738982186575285931735377)
                ·
                  refine ⟨2054236639931464448801533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738982186575285931735377 2054236639931464448801533)
                  ·
                    refine ⟨770338739974299168300575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054236639931464448801533 770338739974299168300575)
                    ·
                      rfl

theorem cell22_2250344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2250344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250344 prefixEnd_2250344 := by exact prefixLift 2250344
  have htrace : WordTrace (prefixWord ++ tailWord_2250344) baseStart_2250344 baseEnd_2250344 := by
    simpa [prefixWord, tailWord_2250344, baseEnd_2250344] using wordTrace_append hprefix tailTrace_2250344
  have hstable : (prefixWord ++ tailWord_2250344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250344).length < 2 ^ (prefixWord ++ tailWord_2250344).sum := by decide
  have hdescent : baseEnd_2250344 < baseStart_2250344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250385 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 5]
def baseStart_2250385 : Nat := 118140960795 + 2250385 * 2 ^ 59
def prefixEnd_2250385 : Nat := 4983230072969 + 3 ^ 40 * 2250385 * 2
def baseEnd_2250385 : Nat := 256784258370729576008483

theorem tailTrace_2250385 : CollatzResearch.WordTrace tailWord_2250385 prefixEnd_2250385 256784258370729576008483 := by
  unfold tailWord_2250385
  simp only [CollatzResearch.WordTrace]
  refine ⟨82078283952246955004624609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54718855968164636669749739 82078283952246955004624609)
  ·
    refine ⟨61558712964185216253468457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82078283952246955004624609 61558712964185216253468457)
    ·
      refine ⟨46169034723138912190101343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61558712964185216253468457 46169034723138912190101343)
      ·
        refine ⟨69253552084708368285152015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46169034723138912190101343 69253552084708368285152015)
        ·
          refine ⟨103880328127062552427728023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69253552084708368285152015 103880328127062552427728023)
          ·
            refine ⟨155820492190593828641592035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103880328127062552427728023 155820492190593828641592035)
            ·
              refine ⟨233730738285890742962388053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155820492190593828641592035 233730738285890742962388053)
              ·
                refine ⟨2739032089287782144090485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 233730738285890742962388053 2739032089287782144090485)
                ·
                  refine ⟨256784258370729576008483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739032089287782144090485 256784258370729576008483)
                  ·
                    rfl

theorem cell22_2250385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_2250385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250385 prefixEnd_2250385 := by exact prefixLift 2250385
  have htrace : WordTrace (prefixWord ++ tailWord_2250385) baseStart_2250385 baseEnd_2250385 := by
    simpa [prefixWord, tailWord_2250385, baseEnd_2250385] using wordTrace_append hprefix tailTrace_2250385
  have hstable : (prefixWord ++ tailWord_2250385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250385).length < 2 ^ (prefixWord ++ tailWord_2250385).sum := by decide
  have hdescent : baseEnd_2250385 < baseStart_2250385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250408 : List Nat := [2, 1, 7, 1, 1, 2, 2, 6]
def baseStart_2250408 : Nat := 118140960795 + 2250408 * 2 ^ 59
def prefixEnd_2250408 : Nat := 4983230072969 + 3 ^ 40 * 2250408 * 2
def baseEnd_2250408 : Nat := 85595627609136037188931

theorem tailTrace_2250408 : CollatzResearch.WordTrace tailWord_2250408 prefixEnd_2250408 85595627609136037188931 := by
  unfold tailWord_2250408
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039561415581814966355939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54719415220775753288474585 41039561415581814966355939)
  ·
    refine ⟨61559342123372722449533909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41039561415581814966355939 61559342123372722449533909)
    ·
      refine ⟨1442797081016548182410951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61559342123372722449533909 1442797081016548182410951)
      ·
        refine ⟨2164195621524822273616427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442797081016548182410951 2164195621524822273616427)
        ·
          refine ⟨3246293432287233410424641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164195621524822273616427 3246293432287233410424641)
          ·
            refine ⟨2434720074215425057818481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246293432287233410424641 2434720074215425057818481)
            ·
              refine ⟨1826040055661568793363861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2434720074215425057818481 1826040055661568793363861)
              ·
                refine ⟨85595627609136037188931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1826040055661568793363861 85595627609136037188931)
                ·
                  rfl

theorem cell22_2250408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_2250408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250408 prefixEnd_2250408 := by exact prefixLift 2250408
  have htrace : WordTrace (prefixWord ++ tailWord_2250408) baseStart_2250408 baseEnd_2250408 := by
    simpa [prefixWord, tailWord_2250408, baseEnd_2250408] using wordTrace_append hprefix tailTrace_2250408
  have hstable : (prefixWord ++ tailWord_2250408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250408).length < 2 ^ (prefixWord ++ tailWord_2250408).sum := by decide
  have hdescent : baseEnd_2250408 < baseStart_2250408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250432 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_2250432 : Nat := 118140960795 + 2250432 * 2 ^ 59
def prefixEnd_2250432 : Nat := 4983230072969 + 3 ^ 40 * 2250432 * 2
def baseEnd_2250432 : Nat := 770368864172696272100305

theorem tailTrace_2250432 : CollatzResearch.WordTrace tailWord_2250432 prefixEnd_2250432 770368864172696272100305 := by
  unfold tailWord_2250432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039999091538341015792775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54719998788717788021057033 41039999091538341015792775)
  ·
    refine ⟨61559998637307511523689163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41039999091538341015792775 61559998637307511523689163)
    ·
      refine ⟨92339997955961267285533745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61559998637307511523689163 92339997955961267285533745)
      ·
        refine ⟨69254998466970950464150309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92339997955961267285533745 69254998466970950464150309)
        ·
          refine ⟨12985312212557053212028183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69254998466970950464150309 12985312212557053212028183)
          ·
            refine ⟨19477968318835579818042275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12985312212557053212028183 19477968318835579818042275)
            ·
              refine ⟨29216952478253369727063413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19477968318835579818042275 29216952478253369727063413)
              ·
                refine ⟨2739089294836253411912195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29216952478253369727063413 2739089294836253411912195)
                ·
                  refine ⟨4108633942254380117868293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739089294836253411912195 4108633942254380117868293)
                  ·
                    refine ⟨770368864172696272100305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108633942254380117868293 770368864172696272100305)
                    ·
                      rfl

theorem cell22_2250432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_2250432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250432 prefixEnd_2250432 := by exact prefixLift 2250432
  have htrace : WordTrace (prefixWord ++ tailWord_2250432) baseStart_2250432 baseEnd_2250432 := by
    simpa [prefixWord, tailWord_2250432, baseEnd_2250432] using wordTrace_append hprefix tailTrace_2250432
  have hstable : (prefixWord ++ tailWord_2250432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250432).length < 2 ^ (prefixWord ++ tailWord_2250432).sum := by decide
  have hdescent : baseEnd_2250432 < baseStart_2250432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250447 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 4]
def baseStart_2250447 : Nat := 118140960795 + 2250447 * 2 ^ 59
def prefixEnd_2250447 : Nat := 4983230072969 + 3 ^ 40 * 2250447 * 2
def baseEnd_2250447 : Nat := 256791332993080410991753

theorem tailTrace_2250447 : CollatzResearch.WordTrace tailWord_2250447 prefixEnd_2250447 256791332993080410991753 := by
  unfold tailWord_2250447
  simp only [CollatzResearch.WordTrace]
  refine ⟨82080545278022339593381595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54720363518681559728921063 82080545278022339593381595)
  ·
    refine ⟨123120817917033509390072393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82080545278022339593381595 123120817917033509390072393)
    ·
      refine ⟨92340613437775132042554295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123120817917033509390072393 92340613437775132042554295)
      ·
        refine ⟨138510920156662698063831443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92340613437775132042554295 138510920156662698063831443)
        ·
          refine ⟨207766380234994047095747165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138510920156662698063831443 207766380234994047095747165)
          ·
            refine ⟨77912392588122767660905187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207766380234994047095747165 77912392588122767660905187)
            ·
              refine ⟨116868588882184151491357781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77912392588122767660905187 116868588882184151491357781)
              ·
                refine ⟨1369553775963095525289349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 116868588882184151491357781 1369553775963095525289349)
                ·
                  refine ⟨256791332993080410991753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369553775963095525289349 256791332993080410991753)
                  ·
                    rfl

theorem cell22_2250447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 4].length) (baseStart_2250447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250447 prefixEnd_2250447 := by exact prefixLift 2250447
  have htrace : WordTrace (prefixWord ++ tailWord_2250447) baseStart_2250447 baseEnd_2250447 := by
    simpa [prefixWord, tailWord_2250447, baseEnd_2250447] using wordTrace_append hprefix tailTrace_2250447
  have hstable : (prefixWord ++ tailWord_2250447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250447).length < 2 ^ (prefixWord ++ tailWord_2250447).sum := by decide
  have hdescent : baseEnd_2250447 < baseStart_2250447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250475 : List Nat := [1, 1, 1, 1, 2, 4, 4, 8]
def baseStart_2250475 : Nat := 118140960795 + 2250475 * 2 ^ 59
def prefixEnd_2250475 : Nat := 4983230072969 + 3 ^ 40 * 2250475 * 2
def baseEnd_2250475 : Nat := 85598175994606499252797

theorem tailTrace_2250475 : CollatzResearch.WordTrace tailWord_2250475 prefixEnd_2250475 85598175994606499252797 := by
  unfold tailWord_2250475
  simp only [CollatzResearch.WordTrace]
  refine ⟨82081566521920900375400879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54721044347947266916933919 82081566521920900375400879)
  ·
    refine ⟨123122349782881350563101319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82081566521920900375400879 123122349782881350563101319)
    ·
      refine ⟨184683524674322025844651979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123122349782881350563101319 184683524674322025844651979)
      ·
        refine ⟨277025287011483038766977969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184683524674322025844651979 277025287011483038766977969)
        ·
          refine ⟨207768965258612279075233477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277025287011483038766977969 207768965258612279075233477)
          ·
            refine ⟨38956680985989802326606277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207768965258612279075233477 38956680985989802326606277)
            ·
              refine ⟨7304377684873087936238677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38956680985989802326606277 7304377684873087936238677)
              ·
                refine ⟨85598175994606499252797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7304377684873087936238677 85598175994606499252797)
                ·
                  rfl

theorem cell22_2250475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_2250475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250475 prefixEnd_2250475 := by exact prefixLift 2250475
  have htrace : WordTrace (prefixWord ++ tailWord_2250475) baseStart_2250475 baseEnd_2250475 := by
    simpa [prefixWord, tailWord_2250475, baseEnd_2250475] using wordTrace_append hprefix tailTrace_2250475
  have hstable : (prefixWord ++ tailWord_2250475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250475).length < 2 ^ (prefixWord ++ tailWord_2250475).sum := by decide
  have hdescent : baseEnd_2250475 < baseStart_2250475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250524 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2250524 : Nat := 118140960795 + 2250524 * 2 ^ 59
def prefixEnd_2250524 : Nat := 4983230072969 + 3 ^ 40 * 2250524 * 2
def baseEnd_2250524 : Nat := 770400357652838698800023

theorem tailTrace_2250524 : CollatzResearch.WordTrace tailWord_2250524 prefixEnd_2250524 770400357652838698800023 := by
  unfold tailWord_2250524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41041676849371690871967313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54722235799162254495956417 41041676849371690871967313)
  ·
    refine ⟨30781257637028768153975485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41041676849371690871967313 30781257637028768153975485)
    ·
      refine ⟨11542971613885788057740807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30781257637028768153975485 11542971613885788057740807)
      ·
        refine ⟨17314457420828682086611211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11542971613885788057740807 17314457420828682086611211)
        ·
          refine ⟨25971686131243023129916817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17314457420828682086611211 25971686131243023129916817)
          ·
            refine ⟨19478764598432267347437613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25971686131243023129916817 19478764598432267347437613)
            ·
              refine ⟨7304536724412100255289105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19478764598432267347437613 7304536724412100255289105)
              ·
                refine ⟨5478402543309075191466829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7304536724412100255289105 5478402543309075191466829)
                ·
                  refine ⟨2054400953740903196800061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5478402543309075191466829 2054400953740903196800061)
                  ·
                    refine ⟨770400357652838698800023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054400953740903196800061 770400357652838698800023)
                    ·
                      rfl

theorem cell22_2250524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2250524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250524 prefixEnd_2250524 := by exact prefixLift 2250524
  have htrace : WordTrace (prefixWord ++ tailWord_2250524) baseStart_2250524 baseEnd_2250524 := by
    simpa [prefixWord, tailWord_2250524, baseEnd_2250524] using wordTrace_append hprefix tailTrace_2250524
  have hstable : (prefixWord ++ tailWord_2250524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250524).length < 2 ^ (prefixWord ++ tailWord_2250524).sum := by decide
  have hdescent : baseEnd_2250524 < baseStart_2250524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250552 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2250552 : Nat := 118140960795 + 2250552 * 2 ^ 59
def prefixEnd_2250552 : Nat := 4983230072969 + 3 ^ 40 * 2250552 * 2
def baseEnd_2250552 : Nat := 770409942625055959099937

theorem tailTrace_2250552 : CollatzResearch.WordTrace tailWord_2250552 prefixEnd_2250552 770409942625055959099937 := by
  unfold tailWord_2250552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042187471320971262976955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54722916628427961683969273 41042187471320971262976955)
  ·
    refine ⟨61563281206981456894465433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41042187471320971262976955 61563281206981456894465433)
    ·
      refine ⟨46172460905236092670849075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61563281206981456894465433 46172460905236092670849075)
      ·
        refine ⟨69258691357854139006273613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46172460905236092670849075 69258691357854139006273613)
        ·
          refine ⟨25972009259195302127352605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69258691357854139006273613 25972009259195302127352605)
          ·
            refine ⟨9739503472198238297757227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25972009259195302127352605 9739503472198238297757227)
            ·
              refine ⟨14609255208297357446635841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9739503472198238297757227 14609255208297357446635841)
              ·
                refine ⟨10956941406223018084976881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14609255208297357446635841 10956941406223018084976881)
                ·
                  refine ⟨8217706054667263563732661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10956941406223018084976881 8217706054667263563732661)
                  ·
                    refine ⟨770409942625055959099937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8217706054667263563732661 770409942625055959099937)
                    ·
                      rfl

theorem cell22_2250552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2250552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250552 prefixEnd_2250552 := by exact prefixLift 2250552
  have htrace : WordTrace (prefixWord ++ tailWord_2250552) baseStart_2250552 baseEnd_2250552 := by
    simpa [prefixWord, tailWord_2250552, baseEnd_2250552] using wordTrace_append hprefix tailTrace_2250552
  have hstable : (prefixWord ++ tailWord_2250552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250552).length < 2 ^ (prefixWord ++ tailWord_2250552).sum := by decide
  have hdescent : baseEnd_2250552 < baseStart_2250552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250554 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_2250554 : Nat := 118140960795 + 2250554 * 2 ^ 59
def prefixEnd_2250554 : Nat := 4983230072969 + 3 ^ 40 * 2250554 * 2
def baseEnd_2250554 : Nat := 256803542421976206849977

theorem tailTrace_2250554 : CollatzResearch.WordTrace tailWord_2250554 prefixEnd_2250554 256803542421976206849977 := by
  unfold tailWord_2250554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20521111972158674216881679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54722965259089797911684477 20521111972158674216881679)
  ·
    refine ⟨30781667958238011325322519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20521111972158674216881679 30781667958238011325322519)
    ·
      refine ⟨46172501937357016987983779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30781667958238011325322519 46172501937357016987983779)
      ·
        refine ⟨69258752906035525481975669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46172501937357016987983779 69258752906035525481975669)
        ·
          refine ⟨6493008084940830513935219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69258752906035525481975669 6493008084940830513935219)
          ·
            refine ⟨9739512127411245770902829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493008084940830513935219 9739512127411245770902829)
            ·
              refine ⟨3652317047779217164088561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9739512127411245770902829 3652317047779217164088561)
              ·
                refine ⟨2739237785834412873066421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652317047779217164088561 2739237785834412873066421)
                ·
                  refine ⟨256803542421976206849977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739237785834412873066421 256803542421976206849977)
                  ·
                    rfl

theorem cell22_2250554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_2250554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250554 prefixEnd_2250554 := by exact prefixLift 2250554
  have htrace : WordTrace (prefixWord ++ tailWord_2250554) baseStart_2250554 baseEnd_2250554 := by
    simpa [prefixWord, tailWord_2250554, baseEnd_2250554] using wordTrace_append hprefix tailTrace_2250554
  have hstable : (prefixWord ++ tailWord_2250554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250554).length < 2 ^ (prefixWord ++ tailWord_2250554).sum := by decide
  have hdescent : baseEnd_2250554 < baseStart_2250554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250558 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_2250558 : Nat := 118140960795 + 2250558 * 2 ^ 59
def prefixEnd_2250558 : Nat := 4983230072969 + 3 ^ 40 * 2250558 * 2
def baseEnd_2250558 : Nat := 770411996547673943449919

theorem tailTrace_2250558 : CollatzResearch.WordTrace tailWord_2250558 prefixEnd_2250558 770411996547673943449919 := by
  unfold tailWord_2250558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260574222577525693834041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54723062520413470367114885 10260574222577525693834041)
  ·
    refine ⟨7695430666933144270375531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10260574222577525693834041 7695430666933144270375531)
    ·
      refine ⟨11543146000399716405563297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7695430666933144270375531 11543146000399716405563297)
      ·
        refine ⟨8657359500299787304172473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11543146000399716405563297 8657359500299787304172473)
        ·
          refine ⟨6493019625224840478129355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8657359500299787304172473 6493019625224840478129355)
          ·
            refine ⟨9739529437837260717194033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493019625224840478129355 9739529437837260717194033)
            ·
              refine ⟨7304647078377945537895525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9739529437837260717194033 7304647078377945537895525)
              ·
                refine ⟨1369621327195864788355411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7304647078377945537895525 1369621327195864788355411)
                ·
                  refine ⟨2054431990793797182533117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369621327195864788355411 2054431990793797182533117)
                  ·
                    refine ⟨770411996547673943449919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054431990793797182533117 770411996547673943449919)
                    ·
                      rfl

theorem cell22_2250558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_2250558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250558 prefixEnd_2250558 := by exact prefixLift 2250558
  have htrace : WordTrace (prefixWord ++ tailWord_2250558) baseStart_2250558 baseEnd_2250558 := by
    simpa [prefixWord, tailWord_2250558, baseEnd_2250558] using wordTrace_append hprefix tailTrace_2250558
  have hstable : (prefixWord ++ tailWord_2250558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250558).length < 2 ^ (prefixWord ++ tailWord_2250558).sum := by decide
  have hdescent : baseEnd_2250558 < baseStart_2250558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250567 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2250567 : Nat := 118140960795 + 2250567 * 2 ^ 59
def prefixEnd_2250567 : Nat := 4983230072969 + 3 ^ 40 * 2250567 * 2
def baseEnd_2250567 : Nat := 770415077431600919974891

theorem tailTrace_2250567 : CollatzResearch.WordTrace tailWord_2250567 prefixEnd_2250567 770415077431600919974891 := by
  unfold tailWord_2250567
  simp only [CollatzResearch.WordTrace]
  refine ⟨82084922037587600087749955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54723281358391733391833303 82084922037587600087749955)
  ·
    refine ⟨123127383056381400131624933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82084922037587600087749955 123127383056381400131624933)
    ·
      refine ⟨23086384323071512524679675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123127383056381400131624933 23086384323071512524679675)
      ·
        refine ⟨34629576484607268787019513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23086384323071512524679675 34629576484607268787019513)
        ·
          refine ⟨25972182363455451590264635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34629576484607268787019513 25972182363455451590264635)
          ·
            refine ⟨38958273545183177385396953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25972182363455451590264635 38958273545183177385396953)
            ·
              refine ⟨29218705158887383039047715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38958273545183177385396953 29218705158887383039047715)
              ·
                refine ⟨43828057738331074558571573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29218705158887383039047715 43828057738331074558571573)
                ·
                  refine ⟨4108880412968538239866085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43828057738331074558571573 4108880412968538239866085)
                  ·
                    refine ⟨770415077431600919974891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108880412968538239866085 770415077431600919974891)
                    ·
                      rfl

theorem cell22_2250567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2250567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250567 prefixEnd_2250567 := by exact prefixLift 2250567
  have htrace : WordTrace (prefixWord ++ tailWord_2250567) baseStart_2250567 baseEnd_2250567 := by
    simpa [prefixWord, tailWord_2250567, baseEnd_2250567] using wordTrace_append hprefix tailTrace_2250567
  have hstable : (prefixWord ++ tailWord_2250567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250567).length < 2 ^ (prefixWord ++ tailWord_2250567).sum := by decide
  have hdescent : baseEnd_2250567 < baseStart_2250567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250597 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2250597 : Nat := 118140960795 + 2250597 * 2 ^ 59
def prefixEnd_2250597 : Nat := 4983230072969 + 3 ^ 40 * 2250597 * 2
def baseEnd_2250597 : Nat := 770425347044690841724799

theorem tailTrace_2250597 : CollatzResearch.WordTrace tailWord_2250597 prefixEnd_2250597 770425347044690841724799 := by
  unfold tailWord_2250597
  simp only [CollatzResearch.WordTrace]
  refine ⟨82086016227478915211342045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54724010818319276807561363 82086016227478915211342045)
  ·
    refine ⟨30782256085304593204253267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82086016227478915211342045 30782256085304593204253267)
    ·
      refine ⟨46173384127956889806379901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30782256085304593204253267 46173384127956889806379901)
      ·
        refine ⟨17315019047983833677392463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46173384127956889806379901 17315019047983833677392463)
        ·
          refine ⟨25972528571975750516088695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17315019047983833677392463 25972528571975750516088695)
          ·
            refine ⟨38958792857963625774133043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25972528571975750516088695 38958792857963625774133043)
            ·
              refine ⟨58438189286945438661199565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38958792857963625774133043 58438189286945438661199565)
              ·
                refine ⟨21914320982604539497949837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58438189286945438661199565 21914320982604539497949837)
                ·
                  refine ⟨8217870368476702311731189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21914320982604539497949837 8217870368476702311731189)
                  ·
                    refine ⟨770425347044690841724799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8217870368476702311731189 770425347044690841724799)
                    ·
                      rfl

theorem cell22_2250597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2250597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250597 prefixEnd_2250597 := by exact prefixLift 2250597
  have htrace : WordTrace (prefixWord ++ tailWord_2250597) baseStart_2250597 baseEnd_2250597 := by
    simpa [prefixWord, tailWord_2250597, baseEnd_2250597] using wordTrace_append hprefix tailTrace_2250597
  have hstable : (prefixWord ++ tailWord_2250597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250597).length < 2 ^ (prefixWord ++ tailWord_2250597).sum := by decide
  have hdescent : baseEnd_2250597 < baseStart_2250597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250627 : List Nat := [1, 1, 1, 3, 4, 2, 1, 9]
def baseStart_2250627 : Nat := 118140960795 + 2250627 * 2 ^ 59
def prefixEnd_2250627 : Nat := 4983230072969 + 3 ^ 40 * 2250627 * 2
def baseEnd_2250627 : Nat := 85603957406420084830523

theorem tailTrace_2250627 : CollatzResearch.WordTrace tailWord_2250627 prefixEnd_2250627 85603957406420084830523 := by
  unfold tailWord_2250627
  simp only [CollatzResearch.WordTrace]
  refine ⟨82087110417370230334934135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54724740278246820223289423 82087110417370230334934135)
  ·
    refine ⟨123130665626055345502401203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82087110417370230334934135 123130665626055345502401203)
    ·
      refine ⟨184695998439083018253601805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123130665626055345502401203 184695998439083018253601805)
      ·
        refine ⟨69260999414656131845100677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184695998439083018253601805 69260999414656131845100677)
        ·
          refine ⟨12986437390248024720956377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69260999414656131845100677 12986437390248024720956377)
          ·
            refine ⟨9739828042686018540717283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12986437390248024720956377 9739828042686018540717283)
            ·
              refine ⟨14609742064029027811075925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9739828042686018540717283 14609742064029027811075925)
              ·
                refine ⟨85603957406420084830523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14609742064029027811075925 85603957406420084830523)
                ·
                  rfl

theorem cell22_2250627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_2250627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250627 prefixEnd_2250627 := by exact prefixLift 2250627
  have htrace : WordTrace (prefixWord ++ tailWord_2250627) baseStart_2250627 baseEnd_2250627 := by
    simpa [prefixWord, tailWord_2250627, baseEnd_2250627] using wordTrace_append hprefix tailTrace_2250627
  have hstable : (prefixWord ++ tailWord_2250627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250627).length < 2 ^ (prefixWord ++ tailWord_2250627).sum := by decide
  have hdescent : baseEnd_2250627 < baseStart_2250627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250644 : List Nat := [2, 4, 2, 1, 1, 2, 2, 8]
def baseStart_2250644 : Nat := 118140960795 + 2250644 * 2 ^ 59
def prefixEnd_2250644 : Nat := 4983230072969 + 3 ^ 40 * 2250644 * 2
def baseEnd_2250644 : Nat := 85604604011688709533295

theorem tailTrace_2250644 : CollatzResearch.WordTrace tailWord_2250644 prefixEnd_2250644 85604604011688709533295 := by
  unfold tailWord_2250644
  simp only [CollatzResearch.WordTrace]
  refine ⟨41043865229154321119151493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54725153638872428158868657 41043865229154321119151493)
  ·
    refine ⟨7695724730466435209840905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41043865229154321119151493 7695724730466435209840905)
    ·
      refine ⟨5771793547849826407380679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7695724730466435209840905 5771793547849826407380679)
      ·
        refine ⟨8657690321774739611071019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771793547849826407380679 8657690321774739611071019)
        ·
          refine ⟨12986535482662109416606529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657690321774739611071019 12986535482662109416606529)
          ·
            refine ⟨9739901611996582062454897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12986535482662109416606529 9739901611996582062454897)
            ·
              refine ⟨7304926208997436546841173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9739901611996582062454897 7304926208997436546841173)
              ·
                refine ⟨85604604011688709533295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7304926208997436546841173 85604604011688709533295)
                ·
                  rfl

theorem cell22_2250644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_2250644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250644 prefixEnd_2250644 := by exact prefixLift 2250644
  have htrace : WordTrace (prefixWord ++ tailWord_2250644) baseStart_2250644 baseEnd_2250644 := by
    simpa [prefixWord, tailWord_2250644, baseEnd_2250644] using wordTrace_append hprefix tailTrace_2250644
  have hstable : (prefixWord ++ tailWord_2250644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250644).length < 2 ^ (prefixWord ++ tailWord_2250644).sum := by decide
  have hdescent : baseEnd_2250644 < baseStart_2250644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250764 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_2250764 : Nat := 118140960795 + 2250764 * 2 ^ 59
def prefixEnd_2250764 : Nat := 4983230072969 + 3 ^ 40 * 2250764 * 2
def baseEnd_2250764 : Nat := 770482514557558072799287

theorem tailTrace_2250764 : CollatzResearch.WordTrace tailWord_2250764 prefixEnd_2250764 770482514557558072799287 := by
  unfold tailWord_2250764
  simp only [CollatzResearch.WordTrace]
  refine ⟨41046053608936951366335673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54728071478582601821780897 41046053608936951366335673)
  ·
    refine ⟨30784540206702713524751755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41046053608936951366335673 30784540206702713524751755)
    ·
      refine ⟨46176810310054070287127633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30784540206702713524751755 46176810310054070287127633)
      ·
        refine ⟨34632607732540552715345725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46176810310054070287127633 34632607732540552715345725)
        ·
          refine ⟨12987227899702707268254647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34632607732540552715345725 12987227899702707268254647)
          ·
            refine ⟨19480841849554060902381971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12987227899702707268254647 19480841849554060902381971)
            ·
              refine ⟨29221262774331091353572957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19480841849554060902381971 29221262774331091353572957)
              ·
                refine ⟨10957973540374159257589859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29221262774331091353572957 10957973540374159257589859)
                ·
                  refine ⟨16436960310561238886384789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10957973540374159257589859 16436960310561238886384789)
                  ·
                    refine ⟨770482514557558072799287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16436960310561238886384789 770482514557558072799287)
                    ·
                      rfl

theorem cell22_2250764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_2250764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250764 prefixEnd_2250764 := by exact prefixLift 2250764
  have htrace : WordTrace (prefixWord ++ tailWord_2250764) baseStart_2250764 baseEnd_2250764 := by
    simpa [prefixWord, tailWord_2250764, baseEnd_2250764] using wordTrace_append hprefix tailTrace_2250764
  have hstable : (prefixWord ++ tailWord_2250764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250764).length < 2 ^ (prefixWord ++ tailWord_2250764).sum := by decide
  have hdescent : baseEnd_2250764 < baseStart_2250764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250766 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2250766 : Nat := 118140960795 + 2250766 * 2 ^ 59
def prefixEnd_2250766 : Nat := 4983230072969 + 3 ^ 40 * 2250766 * 2
def baseEnd_2250766 : Nat := 770483199198430734249281

theorem tailTrace_2250766 : CollatzResearch.WordTrace tailWord_2250766 prefixEnd_2250766 770483199198430734249281 := by
  unfold tailWord_2250766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261522520483332134280519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54728120109244438049496101 10261522520483332134280519)
  ·
    refine ⟨15392283780724998201420779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261522520483332134280519 15392283780724998201420779)
    ·
      refine ⟨23088425671087497302131169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15392283780724998201420779 23088425671087497302131169)
      ·
        refine ⟨17316319253315622976598377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23088425671087497302131169 17316319253315622976598377)
        ·
          refine ⟨12987239439986717232448783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17316319253315622976598377 12987239439986717232448783)
          ·
            refine ⟨19480859159980075848673175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12987239439986717232448783 19480859159980075848673175)
            ·
              refine ⟨29221288739970113773009763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19480859159980075848673175 29221288739970113773009763)
              ·
                refine ⟨43831933109955170659514645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29221288739970113773009763 43831933109955170659514645)
                ·
                  refine ⟨2054621864529148624664749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43831933109955170659514645 2054621864529148624664749)
                  ·
                    refine ⟨770483199198430734249281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054621864529148624664749 770483199198430734249281)
                    ·
                      rfl

theorem cell22_2250766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2250766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250766 prefixEnd_2250766 := by exact prefixLift 2250766
  have htrace : WordTrace (prefixWord ++ tailWord_2250766) baseStart_2250766 baseEnd_2250766 := by
    simpa [prefixWord, tailWord_2250766, baseEnd_2250766] using wordTrace_append hprefix tailTrace_2250766
  have hstable : (prefixWord ++ tailWord_2250766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250766).length < 2 ^ (prefixWord ++ tailWord_2250766).sum := by decide
  have hdescent : baseEnd_2250766 < baseStart_2250766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250781 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2250781 : Nat := 118140960795 + 2250781 * 2 ^ 59
def prefixEnd_2250781 : Nat := 4983230072969 + 3 ^ 40 * 2250781 * 2
def baseEnd_2250781 : Nat := 770488334004975695124235

theorem tailTrace_2250781 : CollatzResearch.WordTrace tailWord_2250781 prefixEnd_2250781 770488334004975695124235 := by
  unfold tailWord_2250781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82092727258812314636040197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54728484839208209757360131 82092727258812314636040197)
  ·
    refine ⟨15392386361027308994257537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82092727258812314636040197 15392386361027308994257537)
    ·
      refine ⟨11544289770770481745693153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15392386361027308994257537 11544289770770481745693153)
      ·
        refine ⟨8658217328077861309269865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11544289770770481745693153 8658217328077861309269865)
        ·
          refine ⟨6493662996058395981952399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8658217328077861309269865 6493662996058395981952399)
          ·
            refine ⟨9740494494087593972928599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493662996058395981952399 9740494494087593972928599)
            ·
              refine ⟨14610741741131390959392899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740494494087593972928599 14610741741131390959392899)
              ·
                refine ⟨21916112611697086439089349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14610741741131390959392899 21916112611697086439089349)
                ·
                  refine ⟨4109271114693203707329253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21916112611697086439089349 4109271114693203707329253)
                  ·
                    refine ⟨770488334004975695124235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109271114693203707329253 770488334004975695124235)
                    ·
                      rfl

theorem cell22_2250781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2250781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250781 prefixEnd_2250781 := by exact prefixLift 2250781
  have htrace : WordTrace (prefixWord ++ tailWord_2250781) baseStart_2250781 baseEnd_2250781 := by
    simpa [prefixWord, tailWord_2250781, baseEnd_2250781] using wordTrace_append hprefix tailTrace_2250781
  have hstable : (prefixWord ++ tailWord_2250781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250781).length < 2 ^ (prefixWord ++ tailWord_2250781).sum := by decide
  have hdescent : baseEnd_2250781 < baseStart_2250781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250785 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 4]
def baseStart_2250785 : Nat := 118140960795 + 2250785 * 2 ^ 59
def prefixEnd_2250785 : Nat := 4983230072969 + 3 ^ 40 * 2250785 * 2
def baseEnd_2250785 : Nat := 256829901095573672674741

theorem tailTrace_2250785 : CollatzResearch.WordTrace tailWord_2250785 prefixEnd_2250785 256829901095573672674741 := by
  unfold tailWord_2250785
  simp only [CollatzResearch.WordTrace]
  refine ⟨82092873150797823319185809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54728582100531882212790539 82092873150797823319185809)
  ·
    refine ⟨61569654863098367489389357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82092873150797823319185809 61569654863098367489389357)
    ·
      refine ⟨23088620573661887808521009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61569654863098367489389357 23088620573661887808521009)
      ·
        refine ⟨17316465430246415856390757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23088620573661887808521009 17316465430246415856390757)
        ·
          refine ⟨3246837268171202973073267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17316465430246415856390757 3246837268171202973073267)
          ·
            refine ⟨4870255902256804459609901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246837268171202973073267 4870255902256804459609901)
            ·
              refine ⟨1826345963346301672353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4870255902256804459609901 1826345963346301672353713)
              ·
                refine ⟨1369759472509726254265285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826345963346301672353713 1369759472509726254265285)
                ·
                  refine ⟨256829901095573672674741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369759472509726254265285 256829901095573672674741)
                  ·
                    rfl

theorem cell22_2250785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_2250785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250785 prefixEnd_2250785 := by exact prefixLift 2250785
  have htrace : WordTrace (prefixWord ++ tailWord_2250785) baseStart_2250785 baseEnd_2250785 := by
    simpa [prefixWord, tailWord_2250785, baseEnd_2250785] using wordTrace_append hprefix tailTrace_2250785
  have hstable : (prefixWord ++ tailWord_2250785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250785).length < 2 ^ (prefixWord ++ tailWord_2250785).sum := by decide
  have hdescent : baseEnd_2250785 < baseStart_2250785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250800 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_2250800 : Nat := 118140960795 + 2250800 * 2 ^ 59
def prefixEnd_2250800 : Nat := 4983230072969 + 3 ^ 40 * 2250800 * 2
def baseEnd_2250800 : Nat := 770494838093265978899177

theorem tailTrace_2250800 : CollatzResearch.WordTrace tailWord_2250800 prefixEnd_2250800 770494838093265978899177 := by
  unfold tailWord_2250800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41046710122871740440490927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54728946830495653920654569 41046710122871740440490927)
  ·
    refine ⟨61570065184307610660736391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41046710122871740440490927 61570065184307610660736391)
    ·
      refine ⟨92355097776461415991104587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61570065184307610660736391 92355097776461415991104587)
      ·
        refine ⟨138532646664692123986656881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92355097776461415991104587 138532646664692123986656881)
        ·
          refine ⟨103899484998519092989992661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138532646664692123986656881 103899484998519092989992661)
          ·
            refine ⟨2435144179652791241952953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103899484998519092989992661 2435144179652791241952953)
            ·
              refine ⟨1826358134739593431464715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435144179652791241952953 1826358134739593431464715)
              ·
                refine ⟨2739537202109390147197073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826358134739593431464715 2739537202109390147197073)
                ·
                  refine ⟨2054652901582042610397805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739537202109390147197073 2054652901582042610397805)
                  ·
                    refine ⟨770494838093265978899177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054652901582042610397805 770494838093265978899177)
                    ·
                      rfl

theorem cell22_2250800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_2250800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250800 prefixEnd_2250800 := by exact prefixLift 2250800
  have htrace : WordTrace (prefixWord ++ tailWord_2250800) baseStart_2250800 baseEnd_2250800 := by
    simpa [prefixWord, tailWord_2250800, baseEnd_2250800] using wordTrace_append hprefix tailTrace_2250800
  have hstable : (prefixWord ++ tailWord_2250800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250800).length < 2 ^ (prefixWord ++ tailWord_2250800).sum := by decide
  have hdescent : baseEnd_2250800 < baseStart_2250800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250824 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_2250824 : Nat := 118140960795 + 2250824 * 2 ^ 59
def prefixEnd_2250824 : Nat := 4983230072969 + 3 ^ 40 * 2250824 * 2
def baseEnd_2250824 : Nat := 256834351261245972099701

theorem tailTrace_2250824 : CollatzResearch.WordTrace tailWord_2250824 prefixEnd_2250824 256834351261245972099701 := by
  unfold tailWord_2250824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41047147798828266489927763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54729530398437688653237017 41047147798828266489927763)
  ·
    refine ⟨61570721698242399734891645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41047147798828266489927763 61570721698242399734891645)
    ·
      refine ⟨23089020636840899900584367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61570721698242399734891645 23089020636840899900584367)
      ·
        refine ⟨34633530955261349850876551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23089020636840899900584367 34633530955261349850876551)
        ·
          refine ⟨51950296432892024776314827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34633530955261349850876551 51950296432892024776314827)
          ·
            refine ⟨77925444649338037164472241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51950296432892024776314827 77925444649338037164472241)
            ·
              refine ⟨58444083487003527873354181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77925444649338037164472241 58444083487003527873354181)
              ·
                refine ⟨10958265653813161476253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58444083487003527873354181 10958265653813161476253909)
                ·
                  refine ⟨256834351261245972099701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10958265653813161476253909 256834351261245972099701)
                  ·
                    rfl

theorem cell22_2250824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_2250824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250824 prefixEnd_2250824 := by exact prefixLift 2250824
  have htrace : WordTrace (prefixWord ++ tailWord_2250824) baseStart_2250824 baseEnd_2250824 := by
    simpa [prefixWord, tailWord_2250824, baseEnd_2250824] using wordTrace_append hprefix tailTrace_2250824
  have hstable : (prefixWord ++ tailWord_2250824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250824).length < 2 ^ (prefixWord ++ tailWord_2250824).sum := by decide
  have hdescent : baseEnd_2250824 < baseStart_2250824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250841 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 5]
def baseStart_2250841 : Nat := 118140960795 + 2250841 * 2 ^ 59
def prefixEnd_2250841 : Nat := 4983230072969 + 3 ^ 40 * 2250841 * 2
def baseEnd_2250841 : Nat := 256836291077051846208017

theorem tailTrace_2250841 : CollatzResearch.WordTrace tailWord_2250841 prefixEnd_2250841 256836291077051846208017 := by
  unfold tailWord_2250841
  simp only [CollatzResearch.WordTrace]
  refine ⟨82094915638594944883224377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54729943759063296588816251 82094915638594944883224377)
  ·
    refine ⟨61571186728946208662418283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82094915638594944883224377 61571186728946208662418283)
    ·
      refine ⟨92356780093419312993627425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61571186728946208662418283 92356780093419312993627425)
      ·
        refine ⟨69267585070064484745220569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92356780093419312993627425 69267585070064484745220569)
        ·
          refine ⟨51950688802548363558915427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69267585070064484745220569 51950688802548363558915427)
          ·
            refine ⟨77926033203822545338373141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51950688802548363558915427 77926033203822545338373141)
            ·
              refine ⟨3652782806429181812736241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77926033203822545338373141 3652782806429181812736241)
              ·
                refine ⟨2739587104821886359552181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652782806429181812736241 2739587104821886359552181)
                ·
                  refine ⟨256836291077051846208017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739587104821886359552181 256836291077051846208017)
                  ·
                    rfl

theorem cell22_2250841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_2250841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250841 prefixEnd_2250841 := by exact prefixLift 2250841
  have htrace : WordTrace (prefixWord ++ tailWord_2250841) baseStart_2250841 baseEnd_2250841 := by
    simpa [prefixWord, tailWord_2250841, baseEnd_2250841] using wordTrace_append hprefix tailTrace_2250841
  have hstable : (prefixWord ++ tailWord_2250841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250841).length < 2 ^ (prefixWord ++ tailWord_2250841).sum := by decide
  have hdescent : baseEnd_2250841 < baseStart_2250841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250871 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2250871 : Nat := 118140960795 + 2250871 * 2 ^ 59
def prefixEnd_2250871 : Nat := 4983230072969 + 3 ^ 40 * 2250871 * 2
def baseEnd_2250871 : Nat := 770519142844245460373959

theorem tailTrace_2250871 : CollatzResearch.WordTrace tailWord_2250871 prefixEnd_2250871 770519142844245460373959 := by
  unfold tailWord_2250871
  simp only [CollatzResearch.WordTrace]
  refine ⟨82096009828486260006816467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54730673218990840004544311 82096009828486260006816467)
  ·
    refine ⟨123144014742729390010224701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82096009828486260006816467 123144014742729390010224701)
    ·
      refine ⟨46179005528523521253834263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123144014742729390010224701 46179005528523521253834263)
      ·
        refine ⟨69268508292785281880751395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46179005528523521253834263 69268508292785281880751395)
        ·
          refine ⟨103902762439177922821127093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69268508292785281880751395 103902762439177922821127093)
          ·
            refine ⟨9740883978672930264480665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103902762439177922821127093 9740883978672930264480665)
            ·
              refine ⟨7305662984004697698360499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9740883978672930264480665 7305662984004697698360499)
              ·
                refine ⟨10958494476007046547540749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305662984004697698360499 10958494476007046547540749)
                ·
                  refine ⟨4109435428502642455327781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10958494476007046547540749 4109435428502642455327781)
                  ·
                    refine ⟨770519142844245460373959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109435428502642455327781 770519142844245460373959)
                    ·
                      rfl

theorem cell22_2250871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2250871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250871 prefixEnd_2250871 := by exact prefixLift 2250871
  have htrace : WordTrace (prefixWord ++ tailWord_2250871) baseStart_2250871 baseEnd_2250871 := by
    simpa [prefixWord, tailWord_2250871, baseEnd_2250871] using wordTrace_append hprefix tailTrace_2250871
  have hstable : (prefixWord ++ tailWord_2250871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250871).length < 2 ^ (prefixWord ++ tailWord_2250871).sum := by decide
  have hdescent : baseEnd_2250871 < baseStart_2250871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250903 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 6]
def baseStart_2250903 : Nat := 118140960795 + 2250903 * 2 ^ 59
def prefixEnd_2250903 : Nat := 4983230072969 + 3 ^ 40 * 2250903 * 2
def baseEnd_2250903 : Nat := 256843365699402681191287

theorem tailTrace_2250903 : CollatzResearch.WordTrace tailWord_2250903 prefixEnd_2250903 256843365699402681191287 := by
  unfold tailWord_2250903
  simp only [CollatzResearch.WordTrace]
  refine ⟨82097176964370329471981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54731451309580219647987575 82097176964370329471981363)
  ·
    refine ⟨123145765446555494207972045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82097176964370329471981363 123145765446555494207972045)
    ·
      refine ⟨46179662042458310327989517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123145765446555494207972045 46179662042458310327989517)
      ·
        refine ⟨17317373265921866372996069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46179662042458310327989517 17317373265921866372996069)
        ·
          refine ⟨3247007487360349944936763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17317373265921866372996069 3247007487360349944936763)
          ·
            refine ⟨4870511231040524917405145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247007487360349944936763 4870511231040524917405145)
            ·
              refine ⟨3652883423280393688053859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4870511231040524917405145 3652883423280393688053859)
              ·
                refine ⟨5479325134920590532080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652883423280393688053859 5479325134920590532080789)
                ·
                  refine ⟨256843365699402681191287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5479325134920590532080789 256843365699402681191287)
                  ·
                    rfl

theorem cell22_2250903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_2250903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250903 prefixEnd_2250903 := by exact prefixLift 2250903
  have htrace : WordTrace (prefixWord ++ tailWord_2250903) baseStart_2250903 baseEnd_2250903 := by
    simpa [prefixWord, tailWord_2250903, baseEnd_2250903] using wordTrace_append hprefix tailTrace_2250903
  have hstable : (prefixWord ++ tailWord_2250903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250903).length < 2 ^ (prefixWord ++ tailWord_2250903).sum := by decide
  have hdescent : baseEnd_2250903 < baseStart_2250903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250922 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2250922 : Nat := 118140960795 + 2250922 * 2 ^ 59
def prefixEnd_2250922 : Nat := 4983230072969 + 3 ^ 40 * 2250922 * 2
def baseEnd_2250922 : Nat := 770536601186498327348803

theorem tailTrace_2250922 : CollatzResearch.WordTrace tailWord_2250922 prefixEnd_2250922 770536601186498327348803 := by
  unfold tailWord_2250922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20524467487825373929230755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54731913300867663811282013 20524467487825373929230755)
  ·
    refine ⟨30786701231738060893846133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20524467487825373929230755 30786701231738060893846133)
    ·
      refine ⟨2886253240475443208798075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30786701231738060893846133 2886253240475443208798075)
      ·
        refine ⟨4329379860713164813197113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886253240475443208798075 4329379860713164813197113)
        ·
          refine ⟨3247034895534873609897835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4329379860713164813197113 3247034895534873609897835)
          ·
            refine ⟨4870552343302310414846753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247034895534873609897835 4870552343302310414846753)
            ·
              refine ⟨3652914257476732811135065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4870552343302310414846753 3652914257476732811135065)
              ·
                refine ⟨2739685693107549608351299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652914257476732811135065 2739685693107549608351299)
                ·
                  refine ⟨4109528539661324412526949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739685693107549608351299 4109528539661324412526949)
                  ·
                    refine ⟨770536601186498327348803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109528539661324412526949 770536601186498327348803)
                    ·
                      rfl

theorem cell22_2250922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2250922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250922 prefixEnd_2250922 := by exact prefixLift 2250922
  have htrace : WordTrace (prefixWord ++ tailWord_2250922) baseStart_2250922 baseEnd_2250922 := by
    simpa [prefixWord, tailWord_2250922, baseEnd_2250922] using wordTrace_append hprefix tailTrace_2250922
  have hstable : (prefixWord ++ tailWord_2250922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250922).length < 2 ^ (prefixWord ++ tailWord_2250922).sum := by decide
  have hdescent : baseEnd_2250922 < baseStart_2250922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250948 : List Nat := [2, 3, 3, 1, 2, 3, 8]
def baseStart_2250948 : Nat := 118140960795 + 2250948 * 2 ^ 59
def prefixEnd_2250948 : Nat := 4983230072969 + 3 ^ 40 * 2250948 * 2
def baseEnd_2250948 : Nat := 28538722278438626896249

theorem tailTrace_2250948 : CollatzResearch.WordTrace tailWord_2250948 prefixEnd_2250948 28538722278438626896249 := by
  unfold tailWord_2250948
  simp only [CollatzResearch.WordTrace]
  refine ⟨41049409124603651078684749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54732545499471534771579665 41049409124603651078684749)
  ·
    refine ⟨15393528421726369154506781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41049409124603651078684749 15393528421726369154506781)
    ·
      refine ⟨5772573158147388432940043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15393528421726369154506781 5772573158147388432940043)
      ·
        refine ⟨8658859737221082649410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772573158147388432940043 8658859737221082649410065)
        ·
          refine ⟨6494144802915811987057549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8658859737221082649410065 6494144802915811987057549)
          ·
            refine ⟨2435304301093429495146581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6494144802915811987057549 2435304301093429495146581)
            ·
              refine ⟨28538722278438626896249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2435304301093429495146581 28538722278438626896249)
              ·
                rfl

theorem cell22_2250948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 8].length) (baseStart_2250948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2250948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2250948 prefixEnd_2250948 := by exact prefixLift 2250948
  have htrace : WordTrace (prefixWord ++ tailWord_2250948) baseStart_2250948 baseEnd_2250948 := by
    simpa [prefixWord, tailWord_2250948, baseEnd_2250948] using wordTrace_append hprefix tailTrace_2250948
  have hstable : (prefixWord ++ tailWord_2250948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250948).length < 2 ^ (prefixWord ++ tailWord_2250948).sum := by decide
  have hdescent : baseEnd_2250948 < baseStart_2250948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251010 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2251010 : Nat := 118140960795 + 2251010 * 2 ^ 59
def prefixEnd_2251010 : Nat := 4983230072969 + 3 ^ 40 * 2251010 * 2
def baseEnd_2251010 : Nat := 256855575128298477049511

theorem tailTrace_2251010 : CollatzResearch.WordTrace tailWord_2251010 prefixEnd_2251010 256855575128298477049511 := by
  unfold tailWord_2251010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525269893745671686531621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54734053049988457830750989 20525269893745671686531621)
  ·
    refine ⟨3848488105077313441224679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20525269893745671686531621 3848488105077313441224679)
    ·
      refine ⟨5772732157615970161837019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3848488105077313441224679 5772732157615970161837019)
      ·
        refine ⟨8659098236423955242755529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772732157615970161837019 8659098236423955242755529)
        ·
          refine ⟨6494323677317966432066647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8659098236423955242755529 6494323677317966432066647)
          ·
            refine ⟨9741485515976949648099971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494323677317966432066647 9741485515976949648099971)
            ·
              refine ⟨14612228273965424472149957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9741485515976949648099971 14612228273965424472149957)
              ·
                refine ⟨2739792801368517088528117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14612228273965424472149957 2739792801368517088528117)
                ·
                  refine ⟨256855575128298477049511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739792801368517088528117 256855575128298477049511)
                  ·
                    rfl

theorem cell22_2251010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2251010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251010 prefixEnd_2251010 := by exact prefixLift 2251010
  have htrace : WordTrace (prefixWord ++ tailWord_2251010) baseStart_2251010 baseEnd_2251010 := by
    simpa [prefixWord, tailWord_2251010, baseEnd_2251010] using wordTrace_append hprefix tailTrace_2251010
  have hstable : (prefixWord ++ tailWord_2251010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251010).length < 2 ^ (prefixWord ++ tailWord_2251010).sum := by decide
  have hdescent : baseEnd_2251010 < baseStart_2251010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251068 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2251068 : Nat := 118140960795 + 2251068 * 2 ^ 59
def prefixEnd_2251068 : Nat := 4983230072969 + 3 ^ 40 * 2251068 * 2
def baseEnd_2251068 : Nat := 770586579970202613198355

theorem tailTrace_2251068 : CollatzResearch.WordTrace tailWord_2251068 prefixEnd_2251068 770586579970202613198355 := by
  unfold tailWord_2251068
  simp only [CollatzResearch.WordTrace]
  refine ⟨41051597504386281325868929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54735463339181708434491905 41051597504386281325868929)
  ·
    refine ⟨30788698128289710994401697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41051597504386281325868929 30788698128289710994401697)
    ·
      refine ⟨23091523596217283245801273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30788698128289710994401697 23091523596217283245801273)
      ·
        refine ⟨17318642697162962434350955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23091523596217283245801273 17318642697162962434350955)
        ·
          refine ⟨25977964045744443651526433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17318642697162962434350955 25977964045744443651526433)
          ·
            refine ⟨19483473034308332738644825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25977964045744443651526433 19483473034308332738644825)
            ·
              refine ⟨14612604775731249553983619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19483473034308332738644825 14612604775731249553983619)
              ·
                refine ⟨21918907163596874330975429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14612604775731249553983619 21918907163596874330975429)
                ·
                  refine ⟨4109795093174413937057893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21918907163596874330975429 4109795093174413937057893)
                  ·
                    refine ⟨770586579970202613198355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109795093174413937057893 770586579970202613198355)
                    ·
                      rfl

theorem cell22_2251068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2251068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251068 prefixEnd_2251068 := by exact prefixLift 2251068
  have htrace : WordTrace (prefixWord ++ tailWord_2251068) baseStart_2251068 baseEnd_2251068 := by
    simpa [prefixWord, tailWord_2251068, baseEnd_2251068] using wordTrace_append hprefix tailTrace_2251068
  have hstable : (prefixWord ++ tailWord_2251068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251068).length < 2 ^ (prefixWord ++ tailWord_2251068).sum := by decide
  have hdescent : baseEnd_2251068 < baseStart_2251068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251138 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2251138 : Nat := 118140960795 + 2251138 * 2 ^ 59
def prefixEnd_2251138 : Nat := 4983230072969 + 3 ^ 40 * 2251138 * 2
def baseEnd_2251138 : Nat := 770610542400745763948141

theorem tailTrace_2251138 : CollatzResearch.WordTrace tailWord_2251138 prefixEnd_2251138 770610542400745763948141 := by
  unfold tailWord_2251138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20526437029629741151696517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54737165412345976404524045 20526437029629741151696517)
  ·
    refine ⟨3848706943055576465943097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20526437029629741151696517 3848706943055576465943097)
    ·
      refine ⟨2886530207291682349457323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3848706943055576465943097 2886530207291682349457323)
      ·
        refine ⟨4329795310937523524185985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886530207291682349457323 4329795310937523524185985)
        ·
          refine ⟨3247346483203142643139489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4329795310937523524185985 3247346483203142643139489)
          ·
            refine ⟨2435509862402356982354617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3247346483203142643139489 2435509862402356982354617)
            ·
              refine ⟨1826632396801767736765963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435509862402356982354617 1826632396801767736765963)
              ·
                refine ⟨2739948595202651605148945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826632396801767736765963 2739948595202651605148945)
                ·
                  refine ⟨2054961446401988703861709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739948595202651605148945 2054961446401988703861709)
                  ·
                    refine ⟨770610542400745763948141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054961446401988703861709 770610542400745763948141)
                    ·
                      rfl

theorem cell22_2251138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2251138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251138 prefixEnd_2251138 := by exact prefixLift 2251138
  have htrace : WordTrace (prefixWord ++ tailWord_2251138) baseStart_2251138 baseEnd_2251138 := by
    simpa [prefixWord, tailWord_2251138, baseEnd_2251138] using wordTrace_append hprefix tailTrace_2251138
  have hstable : (prefixWord ++ tailWord_2251138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251138).length < 2 ^ (prefixWord ++ tailWord_2251138).sum := by decide
  have hdescent : baseEnd_2251138 < baseStart_2251138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251143 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2251143 : Nat := 118140960795 + 2251143 * 2 ^ 59
def prefixEnd_2251143 : Nat := 4983230072969 + 3 ^ 40 * 2251143 * 2
def baseEnd_2251143 : Nat := 770612254002927417573125

theorem tailTrace_2251143 : CollatzResearch.WordTrace tailWord_2251143 prefixEnd_2251143 770612254002927417573125 := by
  unfold tailWord_2251143
  simp only [CollatzResearch.WordTrace]
  refine ⟨82105930483500850460718083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54737286989000566973812055 82105930483500850460718083)
  ·
    refine ⟨123158895725251275691077125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82105930483500850460718083 123158895725251275691077125)
    ·
      refine ⟨23092292948484614192076961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123158895725251275691077125 23092292948484614192076961)
      ·
        refine ⟨17319219711363460644057721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23092292948484614192076961 17319219711363460644057721)
        ·
          refine ⟨12989414783522595483043291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17319219711363460644057721 12989414783522595483043291)
          ·
            refine ⟨19484122175283893224564937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12989414783522595483043291 19484122175283893224564937)
            ·
              refine ⟨14613091631462919918423703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19484122175283893224564937 14613091631462919918423703)
              ·
                refine ⟨21919637447194379877635555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14613091631462919918423703 21919637447194379877635555)
                ·
                  refine ⟨32879456170791569816453333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21919637447194379877635555 32879456170791569816453333)
                  ·
                    refine ⟨770612254002927417573125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32879456170791569816453333 770612254002927417573125)
                    ·
                      rfl

theorem cell22_2251143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2251143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251143 prefixEnd_2251143 := by exact prefixLift 2251143
  have htrace : WordTrace (prefixWord ++ tailWord_2251143) baseStart_2251143 baseEnd_2251143 := by
    simpa [prefixWord, tailWord_2251143, baseEnd_2251143] using wordTrace_append hprefix tailTrace_2251143
  have hstable : (prefixWord ++ tailWord_2251143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251143).length < 2 ^ (prefixWord ++ tailWord_2251143).sum := by decide
  have hdescent : baseEnd_2251143 < baseStart_2251143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251145 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 5]
def baseStart_2251145 : Nat := 118140960795 + 2251145 * 2 ^ 59
def prefixEnd_2251145 : Nat := 4983230072969 + 3 ^ 40 * 2251145 * 2
def baseEnd_2251145 : Nat := 256870979547933359674373

theorem tailTrace_2251145 : CollatzResearch.WordTrace tailWord_2251145 prefixEnd_2251145 256870979547933359674373 := by
  unfold tailWord_2251145
  simp only [CollatzResearch.WordTrace]
  refine ⟨82106003429493604802290889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54737335619662403201527259 82106003429493604802290889)
  ·
    refine ⟨61579502572120203601718167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82106003429493604802290889 61579502572120203601718167)
    ·
      refine ⟨92369253858180305402577251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61579502572120203601718167 92369253858180305402577251)
      ·
        refine ⟨138553880787270458103865877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92369253858180305402577251 138553880787270458103865877)
        ·
          refine ⟨6494713161903302723618713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138553880787270458103865877 6494713161903302723618713)
          ·
            refine ⟨4871034871427477042714035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6494713161903302723618713 4871034871427477042714035)
            ·
              refine ⟨7306552307141215564071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871034871427477042714035 7306552307141215564071053)
              ·
                refine ⟨2739957115177955836526645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7306552307141215564071053 2739957115177955836526645)
                ·
                  refine ⟨256870979547933359674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739957115177955836526645 256870979547933359674373)
                  ·
                    rfl

theorem cell22_2251145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_2251145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251145 prefixEnd_2251145 := by exact prefixLift 2251145
  have htrace : WordTrace (prefixWord ++ tailWord_2251145) baseStart_2251145 baseEnd_2251145 := by
    simpa [prefixWord, tailWord_2251145, baseEnd_2251145] using wordTrace_append hprefix tailTrace_2251145
  have hstable : (prefixWord ++ tailWord_2251145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251145).length < 2 ^ (prefixWord ++ tailWord_2251145).sum := by decide
  have hdescent : baseEnd_2251145 < baseStart_2251145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251203 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_2251203 : Nat := 118140960795 + 2251203 * 2 ^ 59
def prefixEnd_2251203 : Nat := 4983230072969 + 3 ^ 40 * 2251203 * 2
def baseEnd_2251203 : Nat := 770632793229107261072941

theorem tailTrace_2251203 : CollatzResearch.WordTrace tailWord_2251203 prefixEnd_2251203 770632793229107261072941 := by
  unfold tailWord_2251203
  simp only [CollatzResearch.WordTrace]
  refine ⟨82108118863283480707902263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54738745908855653805268175 82108118863283480707902263)
  ·
    refine ⟨123162178294925221061853395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82108118863283480707902263 123162178294925221061853395)
    ·
      refine ⟨184743267442387831592780093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123162178294925221061853395 184743267442387831592780093)
      ·
        refine ⟨69278725290895436847292535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184743267442387831592780093 69278725290895436847292535)
        ·
          refine ⟨103918087936343155270938803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69278725290895436847292535 103918087936343155270938803)
          ·
            refine ⟨155877131904514732906408205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103918087936343155270938803 155877131904514732906408205)
            ·
              refine ⟨58453924464193024839903077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155877131904514732906408205 58453924464193024839903077)
              ·
                refine ⟨10960110837036192157481827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58453924464193024839903077 10960110837036192157481827)
                ·
                  refine ⟨16440166255554288236222741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10960110837036192157481827 16440166255554288236222741)
                  ·
                    refine ⟨770632793229107261072941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16440166255554288236222741 770632793229107261072941)
                    ·
                      rfl

theorem cell22_2251203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_2251203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251203 prefixEnd_2251203 := by exact prefixLift 2251203
  have htrace : WordTrace (prefixWord ++ tailWord_2251203) baseStart_2251203 baseEnd_2251203 := by
    simpa [prefixWord, tailWord_2251203, baseEnd_2251203] using wordTrace_append hprefix tailTrace_2251203
  have hstable : (prefixWord ++ tailWord_2251203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251203).length < 2 ^ (prefixWord ++ tailWord_2251203).sum := by decide
  have hdescent : baseEnd_2251203 < baseStart_2251203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251222 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2251222 : Nat := 118140960795 + 2251222 * 2 ^ 59
def prefixEnd_2251222 : Nat := 4983230072969 + 3 ^ 40 * 2251222 * 2
def baseEnd_2251222 : Nat := 770639297317397544847883

theorem tailTrace_2251222 : CollatzResearch.WordTrace tailWord_2251222 prefixEnd_2251222 770639297317397544847883 := by
  unfold tailWord_2251222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131800740638415434552745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54739207900143097968562613 5131800740638415434552745)
  ·
    refine ⟨3848850555478811575914559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5131800740638415434552745 3848850555478811575914559)
    ·
      refine ⟨5773275833218217363871839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3848850555478811575914559 5773275833218217363871839)
      ·
        refine ⟨8659913749827326045807759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773275833218217363871839 8659913749827326045807759)
        ·
          refine ⟨12989870624740989068711639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8659913749827326045807759 12989870624740989068711639)
          ·
            refine ⟨19484805937111483603067459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12989870624740989068711639 19484805937111483603067459)
            ·
              refine ⟨29227208905667225404601189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19484805937111483603067459 29227208905667225404601189)
              ·
                refine ⟨5480101669812604763362723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29227208905667225404601189 5480101669812604763362723)
                ·
                  refine ⟨8220152504718907145044085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480101669812604763362723 8220152504718907145044085)
                  ·
                    refine ⟨770639297317397544847883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8220152504718907145044085 770639297317397544847883)
                    ·
                      rfl

theorem cell22_2251222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2251222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251222 prefixEnd_2251222 := by exact prefixLift 2251222
  have htrace : WordTrace (prefixWord ++ tailWord_2251222) baseStart_2251222 baseEnd_2251222 := by
    simpa [prefixWord, tailWord_2251222, baseEnd_2251222] using wordTrace_append hprefix tailTrace_2251222
  have hstable : (prefixWord ++ tailWord_2251222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251222).length < 2 ^ (prefixWord ++ tailWord_2251222).sum := by decide
  have hdescent : baseEnd_2251222 < baseStart_2251222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251235 : List Nat := [1, 1, 1, 6, 3, 1, 9]
def baseStart_2251235 : Nat := 118140960795 + 2251235 * 2 ^ 59
def prefixEnd_2251235 : Nat := 4983230072969 + 3 ^ 40 * 2251235 * 2
def baseEnd_2251235 : Nat := 28542361017891475713809

theorem tailTrace_2251235 : CollatzResearch.WordTrace tailWord_2251235 prefixEnd_2251235 28542361017891475713809 := by
  unfold tailWord_2251235
  simp only [CollatzResearch.WordTrace]
  refine ⟨82109285999167550173067159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54739523999445033448711439 82109285999167550173067159)
  ·
    refine ⟨123163928998751325259600739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82109285999167550173067159 123163928998751325259600739)
    ·
      refine ⟨184745893498126987889401109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123163928998751325259600739 184745893498126987889401109)
      ·
        refine ⟨8659963757724702557315677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184745893498126987889401109 8659963757724702557315677)
        ·
          refine ⟨3247486409146763458993379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8659963757724702557315677 3247486409146763458993379)
          ·
            refine ⟨4871229613720145188490069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247486409146763458993379 4871229613720145188490069)
            ·
              refine ⟨28542361017891475713809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4871229613720145188490069 28542361017891475713809)
              ·
                rfl

theorem cell22_2251235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 9].length) (baseStart_2251235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251235 prefixEnd_2251235 := by exact prefixLift 2251235
  have htrace : WordTrace (prefixWord ++ tailWord_2251235) baseStart_2251235 baseEnd_2251235 := by
    simpa [prefixWord, tailWord_2251235, baseEnd_2251235] using wordTrace_append hprefix tailTrace_2251235
  have hstable : (prefixWord ++ tailWord_2251235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251235).length < 2 ^ (prefixWord ++ tailWord_2251235).sum := by decide
  have hdescent : baseEnd_2251235 < baseStart_2251235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251374 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2251374 : Nat := 118140960795 + 2251374 * 2 ^ 59
def prefixEnd_2251374 : Nat := 4983230072969 + 3 ^ 40 * 2251374 * 2
def baseEnd_2251374 : Nat := 770691330023719815047417

theorem tailTrace_2251374 : CollatzResearch.WordTrace tailWord_2251374 prefixEnd_2251374 770691330023719815047417 := by
  unfold tailWord_2251374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264294468207997114047147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54742903830442651274918117 10264294468207997114047147)
  ·
    refine ⟨15396441702311995671070721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10264294468207997114047147 15396441702311995671070721)
    ·
      refine ⟨11547331276733996753303041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15396441702311995671070721 11547331276733996753303041)
      ·
        refine ⟨8660498457550497564977281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11547331276733996753303041 8660498457550497564977281)
        ·
          refine ⟨6495373843162873173732961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8660498457550497564977281 6495373843162873173732961)
          ·
            refine ⟨4871530382372154880299721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6495373843162873173732961 4871530382372154880299721)
            ·
              refine ⟨3653647786779116160224791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871530382372154880299721 3653647786779116160224791)
              ·
                refine ⟨5480471680168674240337187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653647786779116160224791 5480471680168674240337187)
                ·
                  refine ⟨8220707520253011360505781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480471680168674240337187 8220707520253011360505781)
                  ·
                    refine ⟨770691330023719815047417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8220707520253011360505781 770691330023719815047417)
                    ·
                      rfl

theorem cell22_2251374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2251374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251374 prefixEnd_2251374 := by exact prefixLift 2251374
  have htrace : WordTrace (prefixWord ++ tailWord_2251374) baseStart_2251374 baseEnd_2251374 := by
    simpa [prefixWord, tailWord_2251374, baseEnd_2251374] using wordTrace_append hprefix tailTrace_2251374
  have hstable : (prefixWord ++ tailWord_2251374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251374).length < 2 ^ (prefixWord ++ tailWord_2251374).sum := by decide
  have hdescent : baseEnd_2251374 < baseStart_2251374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251453 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_2251453 : Nat := 118140960795 + 2251453 * 2 ^ 59
def prefixEnd_2251453 : Nat := 4983230072969 + 3 ^ 40 * 2251453 * 2
def baseEnd_2251453 : Nat := 770718373338189942322175

theorem tailTrace_2251453 : CollatzResearch.WordTrace tailWord_2251453 prefixEnd_2251453 770718373338189942322175 := by
  unfold tailWord_2251453
  simp only [CollatzResearch.WordTrace]
  refine ⟨82117237112377773404503013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54744824741585182269668675 82117237112377773404503013)
  ·
    refine ⟨15396981958570832513344315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82117237112377773404503013 15396981958570832513344315)
    ·
      refine ⟨23095472937856248770016473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396981958570832513344315 23095472937856248770016473)
      ·
        refine ⟨17321604703392186577512355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095472937856248770016473 17321604703392186577512355)
        ·
          refine ⟨25982407055088279866268533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17321604703392186577512355 25982407055088279866268533)
          ·
            refine ⟨2435850661414526237462675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25982407055088279866268533 2435850661414526237462675)
            ·
              refine ⟨3653775992121789356194013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435850661414526237462675 3653775992121789356194013)
              ·
                refine ⟨1370165997045671008572755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3653775992121789356194013 1370165997045671008572755)
                ·
                  refine ⟨2055248995568506512859133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370165997045671008572755 2055248995568506512859133)
                  ·
                    refine ⟨770718373338189942322175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055248995568506512859133 770718373338189942322175)
                    ·
                      rfl

theorem cell22_2251453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_2251453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251453 prefixEnd_2251453 := by exact prefixLift 2251453
  have htrace : WordTrace (prefixWord ++ tailWord_2251453) baseStart_2251453 baseEnd_2251453 := by
    simpa [prefixWord, tailWord_2251453, baseEnd_2251453] using wordTrace_append hprefix tailTrace_2251453
  have hstable : (prefixWord ++ tailWord_2251453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251453).length < 2 ^ (prefixWord ++ tailWord_2251453).sum := by decide
  have hdescent : baseEnd_2251453 < baseStart_2251453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251524 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2251524 : Nat := 118140960795 + 2251524 * 2 ^ 59
def prefixEnd_2251524 : Nat := 4983230072969 + 3 ^ 40 * 2251524 * 2
def baseEnd_2251524 : Nat := 770742678089169423796957

theorem tailTrace_2251524 : CollatzResearch.WordTrace tailWord_2251524 prefixEnd_2251524 770742678089169423796957 := by
  unfold tailWord_2251524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41059913347560276265168813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54746551130080368353558417 41059913347560276265168813)
  ·
    refine ⟨15397467505335103599438305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41059913347560276265168813 15397467505335103599438305)
    ·
      refine ⟨11548100629001327699578729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15397467505335103599438305 11548100629001327699578729)
      ·
        refine ⟨8661075471750995774684047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11548100629001327699578729 8661075471750995774684047)
        ·
          refine ⟨12991613207626493662026071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8661075471750995774684047 12991613207626493662026071)
          ·
            refine ⟨19487419811439740493039107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12991613207626493662026071 19487419811439740493039107)
            ·
              refine ⟨29231129717159610739558661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19487419811439740493039107 29231129717159610739558661)
              ·
                refine ⟨5480836821967427013667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29231129717159610739558661 5480836821967427013667249)
                ·
                  refine ⟨4110627616475570260250437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5480836821967427013667249 4110627616475570260250437)
                  ·
                    refine ⟨770742678089169423796957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110627616475570260250437 770742678089169423796957)
                    ·
                      rfl

theorem cell22_2251524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2251524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251524 prefixEnd_2251524 := by exact prefixLift 2251524
  have htrace : WordTrace (prefixWord ++ tailWord_2251524) baseStart_2251524 baseEnd_2251524 := by
    simpa [prefixWord, tailWord_2251524, baseEnd_2251524] using wordTrace_append hprefix tailTrace_2251524
  have hstable : (prefixWord ++ tailWord_2251524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251524).length < 2 ^ (prefixWord ++ tailWord_2251524).sum := by decide
  have hdescent : baseEnd_2251524 < baseStart_2251524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251528 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_2251528 : Nat := 118140960795 + 2251528 * 2 ^ 59
def prefixEnd_2251528 : Nat := 4983230072969 + 3 ^ 40 * 2251528 * 2
def baseEnd_2251528 : Nat := 256914682456971582232315

theorem tailTrace_2251528 : CollatzResearch.WordTrace tailWord_2251528 prefixEnd_2251528 256914682456971582232315 := by
  unfold tailWord_2251528
  simp only [CollatzResearch.WordTrace]
  refine ⟨41059986293553030606741619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54746648391404040808988825 41059986293553030606741619)
  ·
    refine ⟨61589979440329545910112429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41059986293553030606741619 61589979440329545910112429)
    ·
      refine ⟨23096242290123579716292161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61589979440329545910112429 23096242290123579716292161)
      ·
        refine ⟨17322181717592684787219121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23096242290123579716292161 17322181717592684787219121)
        ·
          refine ⟨12991636288194513590414341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17322181717592684787219121 12991636288194513590414341)
          ·
            refine ⟨2435931804036471298202689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12991636288194513590414341 2435931804036471298202689)
            ·
              refine ⟨1826948853027353473652017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435931804036471298202689 1826948853027353473652017)
              ·
                refine ⟨1370211639770515105239013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826948853027353473652017 1370211639770515105239013)
                ·
                  refine ⟨256914682456971582232315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370211639770515105239013 256914682456971582232315)
                  ·
                    rfl

theorem cell22_2251528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_2251528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251528 prefixEnd_2251528 := by exact prefixLift 2251528
  have htrace : WordTrace (prefixWord ++ tailWord_2251528) baseStart_2251528 baseEnd_2251528 := by
    simpa [prefixWord, tailWord_2251528, baseEnd_2251528] using wordTrace_append hprefix tailTrace_2251528
  have hstable : (prefixWord ++ tailWord_2251528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251528).length < 2 ^ (prefixWord ++ tailWord_2251528).sum := by decide
  have hdescent : baseEnd_2251528 < baseStart_2251528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251556 : List Nat := [2, 3, 1, 3, 3, 1, 3, 6]
def baseStart_2251556 : Nat := 118140960795 + 2251556 * 2 ^ 59
def prefixEnd_2251556 : Nat := 4983230072969 + 3 ^ 40 * 2251556 * 2
def baseEnd_2251556 : Nat := 85639292482570222999651

theorem tailTrace_2251556 : CollatzResearch.WordTrace tailWord_2251556 prefixEnd_2251556 85639292482570222999651 := by
  unfold tailWord_2251556
  simp only [CollatzResearch.WordTrace]
  refine ⟨41060496915502310997751261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54747329220669747997001681 41060496915502310997751261)
  ·
    refine ⟨15397686343313366624156723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41060496915502310997751261 15397686343313366624156723)
    ·
      refine ⟨23096529514970049936235085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15397686343313366624156723 23096529514970049936235085)
      ·
        refine ⟨8661198568113768726088157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23096529514970049936235085 8661198568113768726088157)
        ·
          refine ⟨3247949463042663272283059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8661198568113768726088157 3247949463042663272283059)
          ·
            refine ⟨4871924194563994908424589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247949463042663272283059 4871924194563994908424589)
            ·
              refine ⟨1826971572961498090659221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4871924194563994908424589 1826971572961498090659221)
              ·
                refine ⟨85639292482570222999651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1826971572961498090659221 85639292482570222999651)
                ·
                  rfl

theorem cell22_2251556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_2251556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251556 prefixEnd_2251556 := by exact prefixLift 2251556
  have htrace : WordTrace (prefixWord ++ tailWord_2251556) baseStart_2251556 baseEnd_2251556 := by
    simpa [prefixWord, tailWord_2251556, baseEnd_2251556] using wordTrace_append hprefix tailTrace_2251556
  have hstable : (prefixWord ++ tailWord_2251556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251556).length < 2 ^ (prefixWord ++ tailWord_2251556).sum := by decide
  have hdescent : baseEnd_2251556 < baseStart_2251556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251697 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 4]
def baseStart_2251697 : Nat := 118140960795 + 2251697 * 2 ^ 59
def prefixEnd_2251697 : Nat := 4983230072969 + 3 ^ 40 * 2251697 * 2
def baseEnd_2251697 : Nat := 256933966508218213073809

theorem tailTrace_2251697 : CollatzResearch.WordTrace tailWord_2251697 prefixEnd_2251697 256933966508218213073809 := by
  unfold tailWord_2251697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82126136523493803076385345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54750757682329202050923563 82126136523493803076385345)
  ·
    refine ⟨61594602392620352307289009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82126136523493803076385345 61594602392620352307289009)
    ·
      refine ⟨46195951794465264230466757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61594602392620352307289009 46195951794465264230466757)
      ·
        refine ⟨8661740961462237043212517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46195951794465264230466757 8661740961462237043212517)
        ·
          refine ⟨1624076430274169445602347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8661740961462237043212517 1624076430274169445602347)
          ·
            refine ⟨2436114645411254168403521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624076430274169445602347 2436114645411254168403521)
            ·
              refine ⟨1827085984058440626302641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436114645411254168403521 1827085984058440626302641)
              ·
                refine ⟨1370314488043830469726981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827085984058440626302641 1370314488043830469726981)
                ·
                  refine ⟨256933966508218213073809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370314488043830469726981 256933966508218213073809)
                  ·
                    rfl

theorem cell22_2251697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_2251697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251697 prefixEnd_2251697 := by exact prefixLift 2251697
  have htrace : WordTrace (prefixWord ++ tailWord_2251697) baseStart_2251697 baseEnd_2251697 := by
    simpa [prefixWord, tailWord_2251697, baseEnd_2251697] using wordTrace_append hprefix tailTrace_2251697
  have hstable : (prefixWord ++ tailWord_2251697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251697).length < 2 ^ (prefixWord ++ tailWord_2251697).sum := by decide
  have hdescent : baseEnd_2251697 < baseStart_2251697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251704 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2251704 : Nat := 118140960795 + 2251704 * 2 ^ 59
def prefixEnd_2251704 : Nat := 4983230072969 + 3 ^ 40 * 2251704 * 2
def baseEnd_2251704 : Nat := 770804295767708954296405

theorem tailTrace_2251704 : CollatzResearch.WordTrace tailWord_2251704 prefixEnd_2251704 770804295767708954296405 := by
  unfold tailWord_2251704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41063195917234221635945083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54750927889645628847926777 41063195917234221635945083)
  ·
    refine ⟨61594793875851332453917625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41063195917234221635945083 61594793875851332453917625)
    ·
      refine ⟨46196095406888499340438219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61594793875851332453917625 46196095406888499340438219)
      ·
        refine ⟨69294143110332749010657329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46196095406888499340438219 69294143110332749010657329)
        ·
          refine ⟨51970607332749561757992997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69294143110332749010657329 51970607332749561757992997)
          ·
            refine ⟨9744488874890542829623687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51970607332749561757992997 9744488874890542829623687)
            ·
              refine ⟨14616733312335814244435531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9744488874890542829623687 14616733312335814244435531)
              ·
                refine ⟨21925099968503721366653297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14616733312335814244435531 21925099968503721366653297)
                ·
                  refine ⟨16443824976377791024989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21925099968503721366653297 16443824976377791024989973)
                  ·
                    refine ⟨770804295767708954296405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16443824976377791024989973 770804295767708954296405)
                    ·
                      rfl

theorem cell22_2251704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2251704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251704 prefixEnd_2251704 := by exact prefixLift 2251704
  have htrace : WordTrace (prefixWord ++ tailWord_2251704) baseStart_2251704 baseEnd_2251704 := by
    simpa [prefixWord, tailWord_2251704, baseEnd_2251704] using wordTrace_append hprefix tailTrace_2251704
  have hstable : (prefixWord ++ tailWord_2251704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251704).length < 2 ^ (prefixWord ++ tailWord_2251704).sum := by decide
  have hdescent : baseEnd_2251704 < baseStart_2251704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251706 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_2251706 : Nat := 118140960795 + 2251706 * 2 ^ 59
def prefixEnd_2251706 : Nat := 4983230072969 + 3 ^ 40 * 2251706 * 2
def baseEnd_2251706 : Nat := 770804980408581615746399

theorem tailTrace_2251706 : CollatzResearch.WordTrace tailWord_2251706 prefixEnd_2251706 770804980408581615746399 := by
  unfold tailWord_2251706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20531616195115299403365743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54750976520307465075641981 20531616195115299403365743)
  ·
    refine ⟨30797424292672949105048615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20531616195115299403365743 30797424292672949105048615)
    ·
      refine ⟨46196136439009423657572923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30797424292672949105048615 46196136439009423657572923)
      ·
        refine ⟨69294204658514135486359385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46196136439009423657572923 69294204658514135486359385)
        ·
          refine ⟨51970653493885601614769539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69294204658514135486359385 51970653493885601614769539)
          ·
            refine ⟨77955980240828402422154309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51970653493885601614769539 77955980240828402422154309)
            ·
              refine ⟨14616746295155325454153933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77955980240828402422154309 14616746295155325454153933)
              ·
                refine ⟨5481279860683247045307725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14616746295155325454153933 5481279860683247045307725)
                ·
                  refine ⟨2055479947756217641990397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5481279860683247045307725 2055479947756217641990397)
                  ·
                    refine ⟨770804980408581615746399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055479947756217641990397 770804980408581615746399)
                    ·
                      rfl

theorem cell22_2251706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_2251706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251706 prefixEnd_2251706 := by exact prefixLift 2251706
  have htrace : WordTrace (prefixWord ++ tailWord_2251706) baseStart_2251706 baseEnd_2251706 := by
    simpa [prefixWord, tailWord_2251706, baseEnd_2251706] using wordTrace_append hprefix tailTrace_2251706
  have hstable : (prefixWord ++ tailWord_2251706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251706).length < 2 ^ (prefixWord ++ tailWord_2251706).sum := by decide
  have hdescent : baseEnd_2251706 < baseStart_2251706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251751 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2251751 : Nat := 118140960795 + 2251751 * 2 ^ 59
def prefixEnd_2251751 : Nat := 4983230072969 + 3 ^ 40 * 2251751 * 2
def baseEnd_2251751 : Nat := 770820384828216498371261

theorem tailTrace_2251751 : CollatzResearch.WordTrace tailWord_2251751 prefixEnd_2251751 770820384828216498371261 := by
  unfold tailWord_2251751
  simp only [CollatzResearch.WordTrace]
  refine ⟨82128106065298170298851107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54752070710198780199234071 82128106065298170298851107)
  ·
    refine ⟨123192159097947255448276661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82128106065298170298851107 123192159097947255448276661)
    ·
      refine ⟨11549264915432555198275937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123192159097947255448276661 11549264915432555198275937)
      ·
        refine ⟨8661948686574416398706953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11549264915432555198275937 8661948686574416398706953)
        ·
          refine ⟨6496461514930812299030215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8661948686574416398706953 6496461514930812299030215)
          ·
            refine ⟨9744692272396218448545323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496461514930812299030215 9744692272396218448545323)
            ·
              refine ⟨14617038408594327672817985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9744692272396218448545323 14617038408594327672817985)
              ·
                refine ⟨10962778806445745754613489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14617038408594327672817985 10962778806445745754613489)
                ·
                  refine ⟨8222084104834309315960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10962778806445745754613489 8222084104834309315960117)
                  ·
                    refine ⟨770820384828216498371261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8222084104834309315960117 770820384828216498371261)
                    ·
                      rfl

theorem cell22_2251751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2251751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251751 prefixEnd_2251751 := by exact prefixLift 2251751
  have htrace : WordTrace (prefixWord ++ tailWord_2251751) baseStart_2251751 baseEnd_2251751 := by
    simpa [prefixWord, tailWord_2251751, baseEnd_2251751] using wordTrace_append hprefix tailTrace_2251751
  have hstable : (prefixWord ++ tailWord_2251751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251751).length < 2 ^ (prefixWord ++ tailWord_2251751).sum := by decide
  have hdescent : baseEnd_2251751 < baseStart_2251751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251783 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2251783 : Nat := 118140960795 + 2251783 * 2 ^ 59
def prefixEnd_2251783 : Nat := 4983230072969 + 3 ^ 40 * 2251783 * 2
def baseEnd_2251783 : Nat := 770831339082179081571163

theorem tailTrace_2251783 : CollatzResearch.WordTrace tailWord_2251783 prefixEnd_2251783 770831339082179081571163 := by
  unfold tailWord_2251783
  simp only [CollatzResearch.WordTrace]
  refine ⟨82129273201182239764016003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54752848800788159842677335 82129273201182239764016003)
  ·
    refine ⟨123193909801773359646024005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82129273201182239764016003 123193909801773359646024005)
    ·
      refine ⟨23098858087832504933629501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123193909801773359646024005 23098858087832504933629501)
      ·
        refine ⟨8662071782937189350111063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23098858087832504933629501 8662071782937189350111063)
        ·
          refine ⟨12993107674405784025166595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662071782937189350111063 12993107674405784025166595)
          ·
            refine ⟨19489661511608676037749893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993107674405784025166595 19489661511608676037749893)
            ·
              refine ⟨3654311533426626757078105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19489661511608676037749893 3654311533426626757078105)
              ·
                refine ⟨2740733650069970067808579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654311533426626757078105 2740733650069970067808579)
                ·
                  refine ⟨4111100475104955101712869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740733650069970067808579 4111100475104955101712869)
                  ·
                    refine ⟨770831339082179081571163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4111100475104955101712869 770831339082179081571163)
                    ·
                      rfl

theorem cell22_2251783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2251783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251783 prefixEnd_2251783 := by exact prefixLift 2251783
  have htrace : WordTrace (prefixWord ++ tailWord_2251783) baseStart_2251783 baseEnd_2251783 := by
    simpa [prefixWord, tailWord_2251783, baseEnd_2251783] using wordTrace_append hprefix tailTrace_2251783
  have hstable : (prefixWord ++ tailWord_2251783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251783).length < 2 ^ (prefixWord ++ tailWord_2251783).sum := by decide
  have hdescent : baseEnd_2251783 < baseStart_2251783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251811 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_2251811 : Nat := 118140960795 + 2251811 * 2 ^ 59
def prefixEnd_2251811 : Nat := 4983230072969 + 3 ^ 40 * 2251811 * 2
def baseEnd_2251811 : Nat := 770840924054396341871077

theorem tailTrace_2251811 : CollatzResearch.WordTrace tailWord_2251811 prefixEnd_2251811 770840924054396341871077 := by
  unfold tailWord_2251811
  simp only [CollatzResearch.WordTrace]
  refine ⟨82130294445080800546035287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54753529630053867030690191 82130294445080800546035287)
  ·
    refine ⟨123195441667621200819052931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82130294445080800546035287 123195441667621200819052931)
    ·
      refine ⟨184793162501431801228579397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123195441667621200819052931 184793162501431801228579397)
      ·
        refine ⟨34648717969018462730358637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184793162501431801228579397 34648717969018462730358637)
        ·
          refine ⟨12993269238381923523884489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34648717969018462730358637 12993269238381923523884489)
          ·
            refine ⟨9744951928786442642913367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12993269238381923523884489 9744951928786442642913367)
            ·
              refine ⟨14617427893179663964370051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9744951928786442642913367 14617427893179663964370051)
              ·
                refine ⟨21926141839769495946555077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14617427893179663964370051 21926141839769495946555077)
                ·
                  refine ⟨4111151594956780489979077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21926141839769495946555077 4111151594956780489979077)
                  ·
                    refine ⟨770840924054396341871077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4111151594956780489979077 770840924054396341871077)
                    ·
                      rfl

theorem cell22_2251811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_2251811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251811 prefixEnd_2251811 := by exact prefixLift 2251811
  have htrace : WordTrace (prefixWord ++ tailWord_2251811) baseStart_2251811 baseEnd_2251811 := by
    simpa [prefixWord, tailWord_2251811, baseEnd_2251811] using wordTrace_append hprefix tailTrace_2251811
  have hstable : (prefixWord ++ tailWord_2251811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251811).length < 2 ^ (prefixWord ++ tailWord_2251811).sum := by decide
  have hdescent : baseEnd_2251811 < baseStart_2251811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251813 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_2251813 : Nat := 118140960795 + 2251813 * 2 ^ 59
def prefixEnd_2251813 : Nat := 4983230072969 + 3 ^ 40 * 2251813 * 2
def baseEnd_2251813 : Nat := 770841608695269003321071

theorem tailTrace_2251813 : CollatzResearch.WordTrace tailWord_2251813 prefixEnd_2251813 770841608695269003321071 := by
  unfold tailWord_2251813
  simp only [CollatzResearch.WordTrace]
  refine ⟨82130367391073554887608093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54753578260715703258405395 82130367391073554887608093)
  ·
    refine ⟨30798887771652583082853035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82130367391073554887608093 30798887771652583082853035)
    ·
      refine ⟨46198331657478874624279553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30798887771652583082853035 46198331657478874624279553)
      ·
        refine ⟨34648748743109155968209665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46198331657478874624279553 34648748743109155968209665)
        ·
          refine ⟨25986561557331866976157249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34648748743109155968209665 25986561557331866976157249)
          ·
            refine ⟨19489921167998900232117937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25986561557331866976157249 19489921167998900232117937)
            ·
              refine ⟨14617440875999175174088453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19489921167998900232117937 14617440875999175174088453)
              ·
                refine ⟨2740770164249845345141585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14617440875999175174088453 2740770164249845345141585)
                ·
                  refine ⟨2055577623187384008856189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740770164249845345141585 2055577623187384008856189)
                  ·
                    refine ⟨770841608695269003321071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055577623187384008856189 770841608695269003321071)
                    ·
                      rfl

theorem cell22_2251813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_2251813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251813 prefixEnd_2251813 := by exact prefixLift 2251813
  have htrace : WordTrace (prefixWord ++ tailWord_2251813) baseStart_2251813 baseEnd_2251813 := by
    simpa [prefixWord, tailWord_2251813, baseEnd_2251813] using wordTrace_append hprefix tailTrace_2251813
  have hstable : (prefixWord ++ tailWord_2251813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251813).length < 2 ^ (prefixWord ++ tailWord_2251813).sum := by decide
  have hdescent : baseEnd_2251813 < baseStart_2251813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251815 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 6]
def baseStart_2251815 : Nat := 118140960795 + 2251815 * 2 ^ 59
def prefixEnd_2251815 : Nat := 4983230072969 + 3 ^ 40 * 2251815 * 2
def baseEnd_2251815 : Nat := 256947431112047221590355

theorem tailTrace_2251815 : CollatzResearch.WordTrace tailWord_2251815 prefixEnd_2251815 256947431112047221590355 := by
  unfold tailWord_2251815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82130440337066309229180899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54753626891377539486120599 82130440337066309229180899)
  ·
    refine ⟨123195660505599463843771349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82130440337066309229180899 123195660505599463843771349)
    ·
      refine ⟨2887398293099987433838391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 123195660505599463843771349 2887398293099987433838391)
      ·
        refine ⟨4331097439649981150757587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2887398293099987433838391 4331097439649981150757587)
        ·
          refine ⟨6496646159474971726136381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331097439649981150757587 6496646159474971726136381)
          ·
            refine ⟨2436242309803114397301143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6496646159474971726136381 2436242309803114397301143)
            ·
              refine ⟨3654363464704671595951715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436242309803114397301143 3654363464704671595951715)
              ·
                refine ⟨5481545197057007393927573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654363464704671595951715 5481545197057007393927573)
                ·
                  refine ⟨256947431112047221590355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5481545197057007393927573 256947431112047221590355)
                  ·
                    rfl

theorem cell22_2251815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].length) (baseStart_2251815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251815 prefixEnd_2251815 := by exact prefixLift 2251815
  have htrace : WordTrace (prefixWord ++ tailWord_2251815) baseStart_2251815 baseEnd_2251815 := by
    simpa [prefixWord, tailWord_2251815, baseEnd_2251815] using wordTrace_append hprefix tailTrace_2251815
  have hstable : (prefixWord ++ tailWord_2251815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251815).length < 2 ^ (prefixWord ++ tailWord_2251815).sum := by decide
  have hdescent : baseEnd_2251815 < baseStart_2251815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251826 : List Nat := [3, 2, 1, 1, 2, 2, 4, 7]
def baseStart_2251826 : Nat := 118140960795 + 2251826 * 2 ^ 59
def prefixEnd_2251826 : Nat := 4983230072969 + 3 ^ 40 * 2251826 * 2
def baseEnd_2251826 : Nat := 85649562095660144749559

theorem tailTrace_2251826 : CollatzResearch.WordTrace tailWord_2251826 prefixEnd_2251826 85649562095660144749559 := by
  unfold tailWord_2251826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532710385006614526957833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54753894360017638738554221 20532710385006614526957833)
  ·
    refine ⟨15399532788754960895218375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20532710385006614526957833 15399532788754960895218375)
    ·
      refine ⟨23099299183132441342827563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15399532788754960895218375 23099299183132441342827563)
      ·
        refine ⟨34648948774698662014241345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23099299183132441342827563 34648948774698662014241345)
        ·
          refine ⟨25986711581023996510681009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34648948774698662014241345 25986711581023996510681009)
          ·
            refine ⟨19490033685767997383010757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25986711581023996510681009 19490033685767997383010757)
            ·
              refine ⟨3654381316081499509314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19490033685767997383010757 3654381316081499509314517)
              ·
                refine ⟨85649562095660144749559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3654381316081499509314517 85649562095660144749559)
                ·
                  rfl

theorem cell22_2251826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_2251826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251826 prefixEnd_2251826 := by exact prefixLift 2251826
  have htrace : WordTrace (prefixWord ++ tailWord_2251826) baseStart_2251826 baseEnd_2251826 := by
    simpa [prefixWord, tailWord_2251826, baseEnd_2251826] using wordTrace_append hprefix tailTrace_2251826
  have hstable : (prefixWord ++ tailWord_2251826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251826).length < 2 ^ (prefixWord ++ tailWord_2251826).sum := by decide
  have hdescent : baseEnd_2251826 < baseStart_2251826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251933 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 6]
def baseStart_2251933 : Nat := 118140960795 + 2251933 * 2 ^ 59
def prefixEnd_2251933 : Nat := 4983230072969 + 3 ^ 40 * 2251933 * 2
def baseEnd_2251933 : Nat := 256960895715876230106901

theorem tailTrace_2251933 : CollatzResearch.WordTrace tailWord_2251933 prefixEnd_2251933 256960895715876230106901 := by
  unfold tailWord_2251933
  simp only [CollatzResearch.WordTrace]
  refine ⟨82134744150638815381976453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54756496100425876921317635 82134744150638815381976453)
  ·
    refine ⟨15400264528244777884120585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82134744150638815381976453 15400264528244777884120585)
    ·
      refine ⟨11550198396183583413090439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15400264528244777884120585 11550198396183583413090439)
      ·
        refine ⟨17325297594275375119635659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11550198396183583413090439 17325297594275375119635659)
        ·
          refine ⟨25987946391413062679453489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17325297594275375119635659 25987946391413062679453489)
          ·
            refine ⟨19490959793559797009590117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25987946391413062679453489 19490959793559797009590117)
            ·
              refine ⟨3654554961292461939298147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19490959793559797009590117 3654554961292461939298147)
              ·
                refine ⟨5481832441938692908947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654554961292461939298147 5481832441938692908947221)
                ·
                  refine ⟨256960895715876230106901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5481832441938692908947221 256960895715876230106901)
                  ·
                    rfl

theorem cell22_2251933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_2251933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251933 prefixEnd_2251933 := by exact prefixLift 2251933
  have htrace : WordTrace (prefixWord ++ tailWord_2251933) baseStart_2251933 baseEnd_2251933 := by
    simpa [prefixWord, tailWord_2251933, baseEnd_2251933] using wordTrace_append hprefix tailTrace_2251933
  have hstable : (prefixWord ++ tailWord_2251933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251933).length < 2 ^ (prefixWord ++ tailWord_2251933).sum := by decide
  have hdescent : baseEnd_2251933 < baseStart_2251933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251978 : List Nat := [3, 1, 2, 1, 3, 4, 8]
def baseStart_2251978 : Nat := 118140960795 + 2251978 * 2 ^ 59
def prefixEnd_2251978 : Nat := 4983230072969 + 3 ^ 40 * 2251978 * 2
def baseEnd_2251978 : Nat := 28551781169157910109095

theorem tailTrace_2251978 : CollatzResearch.WordTrace tailWord_2251978 prefixEnd_2251978 28551781169157910109095 := by
  unfold tailWord_2251978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20534096358868947016841147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54757590290317192044909725 20534096358868947016841147)
  ·
    refine ⟨30801144538303420525261721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20534096358868947016841147 30801144538303420525261721)
    ·
      refine ⟨23100858403727565393946291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30801144538303420525261721 23100858403727565393946291)
      ·
        refine ⟨34651287605591348090919437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23100858403727565393946291 34651287605591348090919437)
        ·
          refine ⟨12994232852096755534094789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34651287605591348090919437 12994232852096755534094789)
          ·
            refine ⟨2436418659768141662642773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12994232852096755534094789 2436418659768141662642773)
            ·
              refine ⟨28551781169157910109095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2436418659768141662642773 28551781169157910109095)
              ·
                rfl

theorem cell22_2251978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 8].length) (baseStart_2251978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2251978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2251978 prefixEnd_2251978 := by exact prefixLift 2251978
  have htrace : WordTrace (prefixWord ++ tailWord_2251978) baseStart_2251978 baseEnd_2251978 := by
    simpa [prefixWord, tailWord_2251978, baseEnd_2251978] using wordTrace_append hprefix tailTrace_2251978
  have hstable : (prefixWord ++ tailWord_2251978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251978).length < 2 ^ (prefixWord ++ tailWord_2251978).sum := by decide
  have hdescent : baseEnd_2251978 < baseStart_2251978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252044 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_2252044 : Nat := 118140960795 + 2252044 * 2 ^ 59
def prefixEnd_2252044 : Nat := 4983230072969 + 3 ^ 40 * 2252044 * 2
def baseEnd_2252044 : Nat := 770920684716061400795363

theorem tailTrace_2252044 : CollatzResearch.WordTrace tailWord_2252044 prefixEnd_2252044 770920684716061400795363 := by
  unfold tailWord_2252044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41069396326618340669633593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54759195102157787559511457 41069396326618340669633593)
  ·
    refine ⟨30802047244963755502225195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41069396326618340669633593 30802047244963755502225195)
    ·
      refine ⟨46203070867445633253337793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30802047244963755502225195 46203070867445633253337793)
      ·
        refine ⟨34652303150584224940003345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46203070867445633253337793 34652303150584224940003345)
        ·
          refine ⟨25989227362938168705002509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34652303150584224940003345 25989227362938168705002509)
          ·
            refine ⟨9745960261101813264375941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25989227362938168705002509 9745960261101813264375941)
            ·
              refine ⟨1827367548956589987070489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9745960261101813264375941 1827367548956589987070489)
              ·
                refine ⟨1370525661717442490302867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827367548956589987070489 1370525661717442490302867)
                ·
                  refine ⟨2055788492576163735454301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370525661717442490302867 2055788492576163735454301)
                  ·
                    refine ⟨770920684716061400795363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055788492576163735454301 770920684716061400795363)
                    ·
                      rfl

theorem cell22_2252044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_2252044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252044 prefixEnd_2252044 := by exact prefixLift 2252044
  have htrace : WordTrace (prefixWord ++ tailWord_2252044) baseStart_2252044 baseEnd_2252044 := by
    simpa [prefixWord, tailWord_2252044, baseEnd_2252044] using wordTrace_append hprefix tailTrace_2252044
  have hstable : (prefixWord ++ tailWord_2252044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252044).length < 2 ^ (prefixWord ++ tailWord_2252044).sum := by decide
  have hdescent : baseEnd_2252044 < baseStart_2252044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252113 : List Nat := [1, 2, 2, 1, 4, 1, 2, 9]
def baseStart_2252113 : Nat := 118140960795 + 2252113 * 2 ^ 59
def prefixEnd_2252113 : Nat := 4983230072969 + 3 ^ 40 * 2252113 * 2
def baseEnd_2252113 : Nat := 85660478314018691202239

theorem tailTrace_2252113 : CollatzResearch.WordTrace tailWord_2252113 prefixEnd_2252113 85660478314018691202239 := by
  unfold tailWord_2252113
  simp only [CollatzResearch.WordTrace]
  refine ⟨82141309289986706123528993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54760872859991137415685995 82141309289986706123528993)
  ·
    refine ⟨61605981967490029592646745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82141309289986706123528993 61605981967490029592646745)
    ·
      refine ⟨46204486475617522194485059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61605981967490029592646745 46204486475617522194485059)
      ·
        refine ⟨69306729713426283291727589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46204486475617522194485059 69306729713426283291727589)
        ·
          refine ⟨12995011821267428117198923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69306729713426283291727589 12995011821267428117198923)
          ·
            refine ⟨19492517731901142175798385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12995011821267428117198923 19492517731901142175798385)
            ·
              refine ⟨14619388298925856631848789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19492517731901142175798385 14619388298925856631848789)
              ·
                refine ⟨85660478314018691202239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14619388298925856631848789 85660478314018691202239)
                ·
                  rfl

theorem cell22_2252113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 9].length) (baseStart_2252113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252113 prefixEnd_2252113 := by exact prefixLift 2252113
  have htrace : WordTrace (prefixWord ++ tailWord_2252113) baseStart_2252113 baseEnd_2252113 := by
    simpa [prefixWord, tailWord_2252113, baseEnd_2252113] using wordTrace_append hprefix tailTrace_2252113
  have hstable : (prefixWord ++ tailWord_2252113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252113).length < 2 ^ (prefixWord ++ tailWord_2252113).sum := by decide
  have hdescent : baseEnd_2252113 < baseStart_2252113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252117 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_2252117 : Nat := 118140960795 + 2252117 * 2 ^ 59
def prefixEnd_2252117 : Nat := 4983230072969 + 3 ^ 40 * 2252117 * 2
def baseEnd_2252117 : Nat := 770945674107913543720139

theorem tailTrace_2252117 : CollatzResearch.WordTrace tailWord_2252117 prefixEnd_2252117 770945674107913543720139 := by
  unfold tailWord_2252117
  simp only [CollatzResearch.WordTrace]
  refine ⟨82141455181972214806674605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54760970121314809871116403 82141455181972214806674605)
  ·
    refine ⟨30803045693239580552502977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82141455181972214806674605 30803045693239580552502977)
    ·
      refine ⟨23102284269929685414377233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30803045693239580552502977 23102284269929685414377233)
      ·
        refine ⟨17326713202447264060782925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23102284269929685414377233 17326713202447264060782925)
        ·
          refine ⟨6497517450917724022793597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17326713202447264060782925 6497517450917724022793597)
          ·
            refine ⟨2436569044094146508547599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6497517450917724022793597 2436569044094146508547599)
            ·
              refine ⟨3654853566141219762821399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436569044094146508547599 3654853566141219762821399)
              ·
                refine ⟨5482280349211829644232099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654853566141219762821399 5482280349211829644232099)
                ·
                  refine ⟨8223420523817744466348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482280349211829644232099 8223420523817744466348149)
                  ·
                    refine ⟨770945674107913543720139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8223420523817744466348149 770945674107913543720139)
                    ·
                      rfl

theorem cell22_2252117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_2252117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252117 prefixEnd_2252117 := by exact prefixLift 2252117
  have htrace : WordTrace (prefixWord ++ tailWord_2252117) baseStart_2252117 baseEnd_2252117 := by
    simpa [prefixWord, tailWord_2252117, baseEnd_2252117] using wordTrace_append hprefix tailTrace_2252117
  have hstable : (prefixWord ++ tailWord_2252117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252117).length < 2 ^ (prefixWord ++ tailWord_2252117).sum := by decide
  have hdescent : baseEnd_2252117 < baseStart_2252117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252130 : List Nat := [3, 3, 2, 1, 1, 1, 3, 8]
def baseStart_2252130 : Nat := 118140960795 + 2252130 * 2 ^ 59
def prefixEnd_2252130 : Nat := 4983230072969 + 3 ^ 40 * 2252130 * 2
def baseEnd_2252130 : Nat := 85661124919287315905011

theorem tailTrace_2252130 : CollatzResearch.WordTrace tailWord_2252130 prefixEnd_2252130 85661124919287315905011 := by
  unfold tailWord_2252130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20535482332731279506724461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54761286220616745351265229 20535482332731279506724461)
  ·
    refine ⟨7700805874774229815021673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20535482332731279506724461 7700805874774229815021673)
    ·
      refine ⟨5775604406080672361266255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7700805874774229815021673 5775604406080672361266255)
      ·
        refine ⟨8663406609121008541899383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775604406080672361266255 8663406609121008541899383)
        ·
          refine ⟨12995109913681512812849075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8663406609121008541899383 12995109913681512812849075)
          ·
            refine ⟨19492664870522269219273613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12995109913681512812849075 19492664870522269219273613)
            ·
              refine ⟨7309749326445850957227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19492664870522269219273613 7309749326445850957227605)
              ·
                refine ⟨85661124919287315905011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7309749326445850957227605 85661124919287315905011)
                ·
                  rfl

theorem cell22_2252130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_2252130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252130 prefixEnd_2252130 := by exact prefixLift 2252130
  have htrace : WordTrace (prefixWord ++ tailWord_2252130) baseStart_2252130 baseEnd_2252130 := by
    simpa [prefixWord, tailWord_2252130, baseEnd_2252130] using wordTrace_append hprefix tailTrace_2252130
  have hstable : (prefixWord ++ tailWord_2252130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252130).length < 2 ^ (prefixWord ++ tailWord_2252130).sum := by decide
  have hdescent : baseEnd_2252130 < baseStart_2252130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252136 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_2252136 : Nat := 118140960795 + 2252136 * 2 ^ 59
def prefixEnd_2252136 : Nat := 4983230072969 + 3 ^ 40 * 2252136 * 2
def baseEnd_2252136 : Nat := 256984059398734609165027

theorem tailTrace_2252136 : CollatzResearch.WordTrace tailWord_2252136 prefixEnd_2252136 256984059398734609165027 := by
  unfold tailWord_2252136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41071074084451690525808131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54761432112602254034410841 41071074084451690525808131)
  ·
    refine ⟨61606611126677535788712197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41071074084451690525808131 61606611126677535788712197)
    ·
      refine ⟨11551239586252037960383537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61606611126677535788712197 11551239586252037960383537)
      ·
        refine ⟨8663429689689028470287653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11551239586252037960383537 8663429689689028470287653)
        ·
          refine ⟨1624393066816692838178935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8663429689689028470287653 1624393066816692838178935)
          ·
            refine ⟨2436589600225039257268403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624393066816692838178935 2436589600225039257268403)
            ·
              refine ⟨3654884400337558885902605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436589600225039257268403 3654884400337558885902605)
              ·
                refine ⟨1370581650126584582213477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3654884400337558885902605 1370581650126584582213477)
                ·
                  refine ⟨256984059398734609165027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370581650126584582213477 256984059398734609165027)
                  ·
                    rfl

theorem cell22_2252136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_2252136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252136 prefixEnd_2252136 := by exact prefixLift 2252136
  have htrace : WordTrace (prefixWord ++ tailWord_2252136) baseStart_2252136 baseEnd_2252136 := by
    simpa [prefixWord, tailWord_2252136, baseEnd_2252136] using wordTrace_append hprefix tailTrace_2252136
  have hstable : (prefixWord ++ tailWord_2252136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252136).length < 2 ^ (prefixWord ++ tailWord_2252136).sum := by decide
  have hdescent : baseEnd_2252136 < baseStart_2252136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252145 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2252145 : Nat := 118140960795 + 2252145 * 2 ^ 59
def prefixEnd_2252145 : Nat := 4983230072969 + 3 ^ 40 * 2252145 * 2
def baseEnd_2252145 : Nat := 770955259080130804020053

theorem tailTrace_2252145 : CollatzResearch.WordTrace tailWord_2252145 prefixEnd_2252145 770955259080130804020053 := by
  unfold tailWord_2252145
  simp only [CollatzResearch.WordTrace]
  refine ⟨82142476425870775588693889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54761650950580517059129259 82142476425870775588693889)
  ·
    refine ⟨61606857319403081691520417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82142476425870775588693889 61606857319403081691520417)
    ·
      refine ⟨46205142989552311268640313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61606857319403081691520417 46205142989552311268640313)
      ·
        refine ⟨34653857242164233451480235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46205142989552311268640313 34653857242164233451480235)
        ·
          refine ⟨51980785863246350177220353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34653857242164233451480235 51980785863246350177220353)
          ·
            refine ⟨38985589397434762632915265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51980785863246350177220353 38985589397434762632915265)
            ·
              refine ⟨29239192048076071974686449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38985589397434762632915265 29239192048076071974686449)
              ·
                refine ⟨21929394036057053981014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29239192048076071974686449 21929394036057053981014837)
                ·
                  refine ⟨2055880690880348810720141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21929394036057053981014837 2055880690880348810720141)
                  ·
                    refine ⟨770955259080130804020053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055880690880348810720141 770955259080130804020053)
                    ·
                      rfl

theorem cell22_2252145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2252145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252145 prefixEnd_2252145 := by exact prefixLift 2252145
  have htrace : WordTrace (prefixWord ++ tailWord_2252145) baseStart_2252145 baseEnd_2252145 := by
    simpa [prefixWord, tailWord_2252145, baseEnd_2252145] using wordTrace_append hprefix tailTrace_2252145
  have hstable : (prefixWord ++ tailWord_2252145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252145).length < 2 ^ (prefixWord ++ tailWord_2252145).sum := by decide
  have hdescent : baseEnd_2252145 < baseStart_2252145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252213 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2252213 : Nat := 118140960795 + 2252213 * 2 ^ 59
def prefixEnd_2252213 : Nat := 4983230072969 + 3 ^ 40 * 2252213 * 2
def baseEnd_2252213 : Nat := 770978536869801293319845

theorem tailTrace_2252213 : CollatzResearch.WordTrace tailWord_2252213 prefixEnd_2252213 770978536869801293319845 := by
  unfold tailWord_2252213
  simp only [CollatzResearch.WordTrace]
  refine ⟨82144956589624423202169293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54763304393082948801446195 82144956589624423202169293)
  ·
    refine ⟨30804358721109158700813485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82144956589624423202169293 30804358721109158700813485)
    ·
      refine ⟨11551634520415934512805057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30804358721109158700813485 11551634520415934512805057)
      ·
        refine ⟨8663725890311950884603793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11551634520415934512805057 8663725890311950884603793)
        ·
          refine ⟨6497794417733963163452845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8663725890311950884603793 6497794417733963163452845)
          ·
            refine ⟨2436672906650236186294817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6497794417733963163452845 2436672906650236186294817)
            ·
              refine ⟨1827504679987677139721113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436672906650236186294817 1827504679987677139721113)
              ·
                refine ⟨1370628509990757854790835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827504679987677139721113 1370628509990757854790835)
                ·
                  refine ⟨2055942764986136782186253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370628509990757854790835 2055942764986136782186253)
                  ·
                    refine ⟨770978536869801293319845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055942764986136782186253 770978536869801293319845)
                    ·
                      rfl

theorem cell22_2252213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2252213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252213 prefixEnd_2252213 := by exact prefixLift 2252213
  have htrace : WordTrace (prefixWord ++ tailWord_2252213) baseStart_2252213 baseEnd_2252213 := by
    simpa [prefixWord, tailWord_2252213, baseEnd_2252213] using wordTrace_append hprefix tailTrace_2252213
  have hstable : (prefixWord ++ tailWord_2252213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252213).length < 2 ^ (prefixWord ++ tailWord_2252213).sum := by decide
  have hdescent : baseEnd_2252213 < baseStart_2252213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252235 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_2252235 : Nat := 118140960795 + 2252235 * 2 ^ 59
def prefixEnd_2252235 : Nat := 4983230072969 + 3 ^ 40 * 2252235 * 2
def baseEnd_2252235 : Nat := 770986067919400569269777

theorem tailTrace_2252235 : CollatzResearch.WordTrace tailWord_2252235 prefixEnd_2252235 770986067919400569269777 := by
  unfold tailWord_2252235
  simp only [CollatzResearch.WordTrace]
  refine ⟨82145758995544720959470159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54763839330363147306313439 82145758995544720959470159)
  ·
    refine ⟨123218638493317081439205239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82145758995544720959470159 123218638493317081439205239)
    ·
      refine ⟨184827957739975622158807859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123218638493317081439205239 184827957739975622158807859)
      ·
        refine ⟨277241936609963433238211789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184827957739975622158807859 277241936609963433238211789)
        ·
          refine ⟨103965726228736287464329421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277241936609963433238211789 103965726228736287464329421)
          ·
            refine ⟨38987147335776107799123533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103965726228736287464329421 38987147335776107799123533)
            ·
              refine ⟨14620180250916040424671325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38987147335776107799123533 14620180250916040424671325)
              ·
                refine ⟨5482567594093515159251747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14620180250916040424671325 5482567594093515159251747)
                ·
                  refine ⟨8223851391140272738877621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482567594093515159251747 8223851391140272738877621)
                  ·
                    refine ⟨770986067919400569269777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8223851391140272738877621 770986067919400569269777)
                    ·
                      rfl

theorem cell22_2252235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_2252235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252235 prefixEnd_2252235 := by exact prefixLift 2252235
  have htrace : WordTrace (prefixWord ++ tailWord_2252235) baseStart_2252235 baseEnd_2252235 := by
    simpa [prefixWord, tailWord_2252235, baseEnd_2252235] using wordTrace_append hprefix tailTrace_2252235
  have hstable : (prefixWord ++ tailWord_2252235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252235).length < 2 ^ (prefixWord ++ tailWord_2252235).sum := by decide
  have hdescent : baseEnd_2252235 < baseStart_2252235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252297 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_2252297 : Nat := 118140960795 + 2252297 * 2 ^ 59
def prefixEnd_2252297 : Nat := 4983230072969 + 3 ^ 40 * 2252297 * 2
def baseEnd_2252297 : Nat := 771007291786453074219587

theorem tailTrace_2252297 : CollatzResearch.WordTrace tailWord_2252297 prefixEnd_2252297 771007291786453074219587 := by
  unfold tailWord_2252297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82148020321320105548227145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54765346880880070365484763 82148020321320105548227145)
  ·
    refine ⟨61611015240990079161170359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82148020321320105548227145 61611015240990079161170359)
    ·
      refine ⟨92416522861485118741755539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61611015240990079161170359 92416522861485118741755539)
      ·
        refine ⟨138624784292227678112633309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92416522861485118741755539 138624784292227678112633309)
        ·
          refine ⟨51984294109585379292237491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138624784292227678112633309 51984294109585379292237491)
          ·
            refine ⟨77976441164378068938356237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51984294109585379292237491 77976441164378068938356237)
            ·
              refine ⟨29241165436641775851883589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77976441164378068938356237 29241165436641775851883589)
              ·
                refine ⟨5482718519370332972228173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29241165436641775851883589 5482718519370332972228173)
                ·
                  refine ⟨2056019444763874864585565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5482718519370332972228173 2056019444763874864585565)
                  ·
                    refine ⟨771007291786453074219587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056019444763874864585565 771007291786453074219587)
                    ·
                      rfl

theorem cell22_2252297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_2252297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252297 prefixEnd_2252297 := by exact prefixLift 2252297
  have htrace : WordTrace (prefixWord ++ tailWord_2252297) baseStart_2252297 baseEnd_2252297 := by
    simpa [prefixWord, tailWord_2252297, baseEnd_2252297] using wordTrace_append hprefix tailTrace_2252297
  have hstable : (prefixWord ++ tailWord_2252297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252297).length < 2 ^ (prefixWord ++ tailWord_2252297).sum := by decide
  have hdescent : baseEnd_2252297 < baseStart_2252297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252299 : List Nat := [1, 1, 1, 1, 8, 2, 2, 6]
def baseStart_2252299 : Nat := 118140960795 + 2252299 * 2 ^ 59
def prefixEnd_2252299 : Nat := 4983230072969 + 3 ^ 40 * 2252299 * 2
def baseEnd_2252299 : Nat := 85667552936369526185509

theorem tailTrace_2252299 : CollatzResearch.WordTrace tailWord_2252299 prefixEnd_2252299 85667552936369526185509 := by
  unfold tailWord_2252299
  simp only [CollatzResearch.WordTrace]
  refine ⟨82148093267312859889799951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54765395511541906593199967 82148093267312859889799951)
  ·
    refine ⟨123222139900969289834699927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82148093267312859889799951 123222139900969289834699927)
    ·
      refine ⟨184833209851453934752049891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123222139900969289834699927 184833209851453934752049891)
      ·
        refine ⟨277249814777180902128074837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184833209851453934752049891 277249814777180902128074837)
        ·
          refine ⟨3249021266920088696813377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 277249814777180902128074837 3249021266920088696813377)
          ·
            refine ⟨2436765950190066522610033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249021266920088696813377 2436765950190066522610033)
            ·
              refine ⟨1827574462642549891957525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436765950190066522610033 1827574462642549891957525)
              ·
                refine ⟨85667552936369526185509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1827574462642549891957525 85667552936369526185509)
                ·
                  rfl

theorem cell22_2252299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 6].length) (baseStart_2252299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252299 prefixEnd_2252299 := by exact prefixLift 2252299
  have htrace : WordTrace (prefixWord ++ tailWord_2252299) baseStart_2252299 baseEnd_2252299 := by
    simpa [prefixWord, tailWord_2252299, baseEnd_2252299] using wordTrace_append hprefix tailTrace_2252299
  have hstable : (prefixWord ++ tailWord_2252299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252299).length < 2 ^ (prefixWord ++ tailWord_2252299).sum := by decide
  have hdescent : baseEnd_2252299 < baseStart_2252299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252344 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_2252344 : Nat := 118140960795 + 2252344 * 2 ^ 59
def prefixEnd_2252344 : Nat := 4983230072969 + 3 ^ 40 * 2252344 * 2
def baseEnd_2252344 : Nat := 257007793615653539431481

theorem tailTrace_2252344 : CollatzResearch.WordTrace tailWord_2252344 prefixEnd_2252344 257007793615653539431481 := by
  unfold tailWord_2252344
  simp only [CollatzResearch.WordTrace]
  refine ⟨41074867276074916287594043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54766489701433221716792057 41074867276074916287594043)
  ·
    refine ⟨61612300914112374431391065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41074867276074916287594043 61612300914112374431391065)
    ·
      refine ⟨46209225685584280823543299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61612300914112374431391065 46209225685584280823543299)
      ·
        refine ⟨69313838528376421235314949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46209225685584280823543299 69313838528376421235314949)
        ·
          refine ⟨12996344724070578981621553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69313838528376421235314949 12996344724070578981621553)
          ·
            refine ⟨9747258543052934236216165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12996344724070578981621553 9747258543052934236216165)
            ·
              refine ⟨1827610976822425169290531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9747258543052934236216165 1827610976822425169290531)
              ·
                refine ⟨2741416465233637753935797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827610976822425169290531 2741416465233637753935797)
                ·
                  refine ⟨257007793615653539431481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2741416465233637753935797 257007793615653539431481)
                  ·
                    rfl

theorem cell22_2252344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_2252344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252344 prefixEnd_2252344 := by exact prefixLift 2252344
  have htrace : WordTrace (prefixWord ++ tailWord_2252344) baseStart_2252344 baseEnd_2252344 := by
    simpa [prefixWord, tailWord_2252344, baseEnd_2252344] using wordTrace_append hprefix tailTrace_2252344
  have hstable : (prefixWord ++ tailWord_2252344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252344).length < 2 ^ (prefixWord ++ tailWord_2252344).sum := by decide
  have hdescent : baseEnd_2252344 < baseStart_2252344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252357 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_2252357 : Nat := 118140960795 + 2252357 * 2 ^ 59
def prefixEnd_2252357 : Nat := 4983230072969 + 3 ^ 40 * 2252357 * 2
def baseEnd_2252357 : Nat := 771027831012632917719403

theorem tailTrace_2252357 : CollatzResearch.WordTrace tailWord_2252357 prefixEnd_2252357 771027831012632917719403 := by
  unfold tailWord_2252357
  simp only [CollatzResearch.WordTrace]
  refine ⟨82150208701102735795411325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54766805800735157196940883 82150208701102735795411325)
  ·
    refine ⟨30806328262913525923279247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82150208701102735795411325 30806328262913525923279247)
    ·
      refine ⟨46209492394370288884918871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30806328262913525923279247 46209492394370288884918871)
      ·
        refine ⟨69314238591555433327378307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46209492394370288884918871 69314238591555433327378307)
        ·
          refine ⟨103971357887333149991067461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69314238591555433327378307 103971357887333149991067461)
          ·
            refine ⟨19494629603874965623325149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103971357887333149991067461 19494629603874965623325149)
            ·
              refine ⟨7310486101453112108746931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19494629603874965623325149 7310486101453112108746931)
              ·
                refine ⟨10965729152179668163120397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7310486101453112108746931 10965729152179668163120397)
                ·
                  refine ⟨4112148432067375561170149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10965729152179668163120397 4112148432067375561170149)
                  ·
                    refine ⟨771027831012632917719403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4112148432067375561170149 771027831012632917719403)
                    ·
                      rfl

theorem cell22_2252357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_2252357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252357 prefixEnd_2252357 := by exact prefixLift 2252357
  have htrace : WordTrace (prefixWord ++ tailWord_2252357) baseStart_2252357 baseEnd_2252357 := by
    simpa [prefixWord, tailWord_2252357, baseEnd_2252357] using wordTrace_append hprefix tailTrace_2252357
  have hstable : (prefixWord ++ tailWord_2252357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252357).length < 2 ^ (prefixWord ++ tailWord_2252357).sum := by decide
  have hdescent : baseEnd_2252357 < baseStart_2252357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252434 : List Nat := [3, 2, 3, 1, 3, 1, 9]
def baseStart_2252434 : Nat := 118140960795 + 2252434 * 2 ^ 59
def prefixEnd_2252434 : Nat := 4983230072969 + 3 ^ 40 * 2252434 * 2
def baseEnd_2252434 : Nat := 28557562580971495686821

theorem tailTrace_2252434 : CollatzResearch.WordTrace tailWord_2252434 prefixEnd_2252434 28557562580971495686821 := by
  unfold tailWord_2252434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20538254280455944486491089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54768678081215851963976237 20538254280455944486491089)
  ·
    refine ⟨15403690710341958364868317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20538254280455944486491089 15403690710341958364868317)
    ·
      refine ⟨5776384016378234386825619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15403690710341958364868317 5776384016378234386825619)
      ·
        refine ⟨8664576024567351580238429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776384016378234386825619 8664576024567351580238429)
        ·
          refine ⟨3249216009212756842589411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8664576024567351580238429 3249216009212756842589411)
          ·
            refine ⟨4873824013819135263884117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249216009212756842589411 4873824013819135263884117)
            ·
              refine ⟨28557562580971495686821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4873824013819135263884117 28557562580971495686821)
              ·
                rfl

theorem cell22_2252434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 9].length) (baseStart_2252434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252434 prefixEnd_2252434 := by exact prefixLift 2252434
  have htrace : WordTrace (prefixWord ++ tailWord_2252434) baseStart_2252434 baseEnd_2252434 := by
    simpa [prefixWord, tailWord_2252434, baseEnd_2252434] using wordTrace_append hprefix tailTrace_2252434
  have hstable : (prefixWord ++ tailWord_2252434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252434).length < 2 ^ (prefixWord ++ tailWord_2252434).sum := by decide
  have hdescent : baseEnd_2252434 < baseStart_2252434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252513 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 5]
def baseStart_2252513 : Nat := 118140960795 + 2252513 * 2 ^ 59
def prefixEnd_2252513 : Nat := 4983230072969 + 3 ^ 40 * 2252513 * 2
def baseEnd_2252513 : Nat := 257027077666900170272975

theorem tailTrace_2252513 : CollatzResearch.WordTrace tailWord_2252513 prefixEnd_2252513 257027077666900170272975 := by
  unfold tailWord_2252513
  simp only [CollatzResearch.WordTrace]
  refine ⟨82155898488537574438090193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54770598992358382958726795 82155898488537574438090193)
  ·
    refine ⟨61616923866403180828567645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82155898488537574438090193 61616923866403180828567645)
    ·
      refine ⟨23106346449901192810712867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61616923866403180828567645 23106346449901192810712867)
      ·
        refine ⟨34659519674851789216069301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23106346449901192810712867 34659519674851789216069301)
        ·
          refine ⟨3249329969517355239006497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34659519674851789216069301 3249329969517355239006497)
          ·
            refine ⟨2436997477138016429254873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249329969517355239006497 2436997477138016429254873)
            ·
              refine ⟨1827748107853512321941155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436997477138016429254873 1827748107853512321941155)
              ·
                refine ⟨2741622161780268482911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827748107853512321941155 2741622161780268482911733)
                ·
                  refine ⟨257027077666900170272975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2741622161780268482911733 257027077666900170272975)
                  ·
                    rfl

theorem cell22_2252513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_2252513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252513 prefixEnd_2252513 := by exact prefixLift 2252513
  have htrace : WordTrace (prefixWord ++ tailWord_2252513) baseStart_2252513 baseEnd_2252513 := by
    simpa [prefixWord, tailWord_2252513, baseEnd_2252513] using wordTrace_append hprefix tailTrace_2252513
  have hstable : (prefixWord ++ tailWord_2252513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252513).length < 2 ^ (prefixWord ++ tailWord_2252513).sum := by decide
  have hdescent : baseEnd_2252513 < baseStart_2252513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252539 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 4, 3]
def baseStart_2252539 : Nat := 118140960795 + 2252539 * 2 ^ 59
def prefixEnd_2252539 : Nat := 4983230072969 + 3 ^ 40 * 2252539 * 2
def baseEnd_2252539 : Nat := 771090133332045109668845

theorem tailTrace_2252539 : CollatzResearch.WordTrace tailWord_2252539 prefixEnd_2252539 771090133332045109668845 := by
  unfold tailWord_2252539
  simp only [CollatzResearch.WordTrace]
  refine ⟨82156846786443380878536671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54771231190962253919024447 82156846786443380878536671)
  ·
    refine ⟨123235270179665071317805007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82156846786443380878536671 123235270179665071317805007)
    ·
      refine ⟨184852905269497606976707511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123235270179665071317805007 184852905269497606976707511)
      ·
        refine ⟨277279357904246410465061267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184852905269497606976707511 277279357904246410465061267)
        ·
          refine ⟨415919036856369615697591901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277279357904246410465061267 415919036856369615697591901)
          ·
            refine ⟨155969638821138605886596963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415919036856369615697591901 155969638821138605886596963)
            ·
              refine ⟨233954458231707908829895445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155969638821138605886596963 233954458231707908829895445)
              ·
                refine ⟨10966615229611308226401349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233954458231707908829895445 10966615229611308226401349)
                ·
                  refine ⟨2056240355552120292450253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10966615229611308226401349 2056240355552120292450253)
                  ·
                    refine ⟨771090133332045109668845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056240355552120292450253 771090133332045109668845)
                    ·
                      rfl

theorem cell22_2252539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].length) (baseStart_2252539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252539 prefixEnd_2252539 := by exact prefixLift 2252539
  have htrace : WordTrace (prefixWord ++ tailWord_2252539) baseStart_2252539 baseEnd_2252539 := by
    simpa [prefixWord, tailWord_2252539, baseEnd_2252539] using wordTrace_append hprefix tailTrace_2252539
  have hstable : (prefixWord ++ tailWord_2252539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252539).length < 2 ^ (prefixWord ++ tailWord_2252539).sum := by decide
  have hdescent : baseEnd_2252539 < baseStart_2252539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252556 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_2252556 : Nat := 118140960795 + 2252556 * 2 ^ 59
def prefixEnd_2252556 : Nat := 4983230072969 + 3 ^ 40 * 2252556 * 2
def baseEnd_2252556 : Nat := 771095952779462731993793

theorem tailTrace_2252556 : CollatzResearch.WordTrace tailWord_2252556 prefixEnd_2252556 771095952779462731993793 := by
  unfold tailWord_2252556
  simp only [CollatzResearch.WordTrace]
  refine ⟨41078733413690896390952761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54771644551587861854603681 41078733413690896390952761)
  ·
    refine ⟨30809050060268172293214571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41078733413690896390952761 30809050060268172293214571)
    ·
      refine ⟨46213575090402258439821857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30809050060268172293214571 46213575090402258439821857)
      ·
        refine ⟨34660181317801693829866393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46213575090402258439821857 34660181317801693829866393)
        ·
          refine ⟨25995135988351270372399795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34660181317801693829866393 25995135988351270372399795)
          ·
            refine ⟨38992703982526905558599693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25995135988351270372399795 38992703982526905558599693)
            ·
              refine ⟨14622263993447589584474885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38992703982526905558599693 14622263993447589584474885)
              ·
                refine ⟨2741674498771423047089041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14622263993447589584474885 2741674498771423047089041)
                ·
                  refine ⟨2056255874078567285316781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741674498771423047089041 2056255874078567285316781)
                  ·
                    refine ⟨771095952779462731993793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056255874078567285316781 771095952779462731993793)
                    ·
                      rfl

theorem cell22_2252556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_2252556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252556 prefixEnd_2252556 := by exact prefixLift 2252556
  have htrace : WordTrace (prefixWord ++ tailWord_2252556) baseStart_2252556 baseEnd_2252556 := by
    simpa [prefixWord, tailWord_2252556, baseEnd_2252556] using wordTrace_append hprefix tailTrace_2252556
  have hstable : (prefixWord ++ tailWord_2252556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252556).length < 2 ^ (prefixWord ++ tailWord_2252556).sum := by decide
  have hdescent : baseEnd_2252556 < baseStart_2252556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252558 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_2252558 : Nat := 118140960795 + 2252558 * 2 ^ 59
def prefixEnd_2252558 : Nat := 4983230072969 + 3 ^ 40 * 2252558 * 2
def baseEnd_2252558 : Nat := 257032212473445131147929

theorem tailTrace_2252558 : CollatzResearch.WordTrace tailWord_2252558 prefixEnd_2252558 257032212473445131147929 := by
  unfold tailWord_2252558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269692471671818390434791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54771693182249698082318885 10269692471671818390434791)
  ·
    refine ⟨15404538707507727585652187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10269692471671818390434791 15404538707507727585652187)
    ·
      refine ⟨23106808061261591378478281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15404538707507727585652187 23106808061261591378478281)
      ·
        refine ⟨17330106045946193533858711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23106808061261591378478281 17330106045946193533858711)
        ·
          refine ⟨25995159068919290300788067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17330106045946193533858711 25995159068919290300788067)
          ·
            refine ⟨38992738603378935451182101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25995159068919290300788067 38992738603378935451182101)
            ·
              refine ⟨1827784622033387599274161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38992738603378935451182101 1827784622033387599274161)
              ·
                refine ⟨1370838466525040699455621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827784622033387599274161 1370838466525040699455621)
                ·
                  refine ⟨257032212473445131147929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370838466525040699455621 257032212473445131147929)
                  ·
                    rfl

theorem cell22_2252558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_2252558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252558 prefixEnd_2252558 := by exact prefixLift 2252558
  have htrace : WordTrace (prefixWord ++ tailWord_2252558) baseStart_2252558 baseEnd_2252558 := by
    simpa [prefixWord, tailWord_2252558, baseEnd_2252558] using wordTrace_append hprefix tailTrace_2252558
  have hstable : (prefixWord ++ tailWord_2252558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252558).length < 2 ^ (prefixWord ++ tailWord_2252558).sum := by decide
  have hdescent : baseEnd_2252558 < baseStart_2252558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252618 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_2252618 : Nat := 118140960795 + 2252618 * 2 ^ 59
def prefixEnd_2252618 : Nat := 4983230072969 + 3 ^ 40 * 2252618 * 2
def baseEnd_2252618 : Nat := 771117176646515236943603

theorem tailTrace_2252618 : CollatzResearch.WordTrace tailWord_2252618 prefixEnd_2252618 771117176646515236943603 := by
  unfold tailWord_2252618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539932038289294342665627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54773152102104784913775005 20539932038289294342665627)
  ·
    refine ⟨30809898057433941513998441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539932038289294342665627 30809898057433941513998441)
    ·
      refine ⟨23107423543075456135498831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30809898057433941513998441 23107423543075456135498831)
      ·
        refine ⟨34661135314613184203248247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23107423543075456135498831 34661135314613184203248247)
        ·
          refine ⟨51991702971919776304872371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34661135314613184203248247 51991702971919776304872371)
          ·
            refine ⟨77987554457879664457308557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51991702971919776304872371 77987554457879664457308557)
            ·
              refine ⟨29245332921704874171490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77987554457879664457308557 29245332921704874171490709)
              ·
                refine ⟨1370874980704915976788627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29245332921704874171490709 1370874980704915976788627)
                ·
                  refine ⟨2056312471057373965182941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370874980704915976788627 2056312471057373965182941)
                  ·
                    refine ⟨771117176646515236943603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056312471057373965182941 771117176646515236943603)
                    ·
                      rfl

theorem cell22_2252618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_2252618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252618 prefixEnd_2252618 := by exact prefixLift 2252618
  have htrace : WordTrace (prefixWord ++ tailWord_2252618) baseStart_2252618 baseEnd_2252618 := by
    simpa [prefixWord, tailWord_2252618, baseEnd_2252618] using wordTrace_append hprefix tailTrace_2252618
  have hstable : (prefixWord ++ tailWord_2252618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252618).length < 2 ^ (prefixWord ++ tailWord_2252618).sum := by decide
  have hdescent : baseEnd_2252618 < baseStart_2252618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252676 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_2252676 : Nat := 118140960795 + 2252676 * 2 ^ 59
def prefixEnd_2252676 : Nat := 4983230072969 + 3 ^ 40 * 2252676 * 2
def baseEnd_2252676 : Nat := 257045677077274139664475

theorem tailTrace_2252676 : CollatzResearch.WordTrace tailWord_2252676 prefixEnd_2252676 257045677077274139664475 := by
  unfold tailWord_2252676
  simp only [CollatzResearch.WordTrace]
  refine ⟨41080921793473526638136941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54774562391298035517515921 41080921793473526638136941)
  ·
    refine ⟨15405345672552572489301353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41080921793473526638136941 15405345672552572489301353)
    ·
      refine ⟨11554009254414429366976015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15405345672552572489301353 11554009254414429366976015)
      ·
        refine ⟨17331013881621644050464023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554009254414429366976015 17331013881621644050464023)
        ·
          refine ⟨25996520822432466075696035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17331013881621644050464023 25996520822432466075696035)
          ·
            refine ⟨38994781233648699113544053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25996520822432466075696035 38994781233648699113544053)
            ·
              refine ⟨3655760740654565541894755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38994781233648699113544053 3655760740654565541894755)
              ·
                refine ⟨5483641110981848312842133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655760740654565541894755 5483641110981848312842133)
                ·
                  refine ⟨257045677077274139664475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5483641110981848312842133 257045677077274139664475)
                  ·
                    rfl

theorem cell22_2252676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_2252676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252676 prefixEnd_2252676 := by exact prefixLift 2252676
  have htrace : WordTrace (prefixWord ++ tailWord_2252676) baseStart_2252676 baseEnd_2252676 := by
    simpa [prefixWord, tailWord_2252676, baseEnd_2252676] using wordTrace_append hprefix tailTrace_2252676
  have hstable : (prefixWord ++ tailWord_2252676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252676).length < 2 ^ (prefixWord ++ tailWord_2252676).sum := by decide
  have hdescent : baseEnd_2252676 < baseStart_2252676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252682 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_2252682 : Nat := 118140960795 + 2252682 * 2 ^ 59
def prefixEnd_2252682 : Nat := 4983230072969 + 3 ^ 40 * 2252682 * 2
def baseEnd_2252682 : Nat := 257046361718146801114469

theorem tailTrace_2252682 : CollatzResearch.WordTrace tailWord_2252682 prefixEnd_2252682 257046361718146801114469 := by
  unfold tailWord_2252682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20540515606231329075248075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54774708283283544200661533 20540515606231329075248075)
  ·
    refine ⟨30810773409346993612872113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20540515606231329075248075 30810773409346993612872113)
    ·
      refine ⟨23108080057010245209654085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30810773409346993612872113 23108080057010245209654085)
      ·
        refine ⟨4332765010689420976810141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23108080057010245209654085 4332765010689420976810141)
        ·
          refine ⟨1624786879008532866303803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4332765010689420976810141 1624786879008532866303803)
          ·
            refine ⟨2437180318512799299455705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624786879008532866303803 2437180318512799299455705)
            ·
              refine ⟨1827885238884599474591779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437180318512799299455705 1827885238884599474591779)
              ·
                refine ⟨2741827858326899211887669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827885238884599474591779 2741827858326899211887669)
                ·
                  refine ⟨257046361718146801114469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2741827858326899211887669 257046361718146801114469)
                  ·
                    rfl

theorem cell22_2252682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_2252682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252682 prefixEnd_2252682 := by exact prefixLift 2252682
  have htrace : WordTrace (prefixWord ++ tailWord_2252682) baseStart_2252682 baseEnd_2252682 := by
    simpa [prefixWord, tailWord_2252682, baseEnd_2252682] using wordTrace_append hprefix tailTrace_2252682
  have hstable : (prefixWord ++ tailWord_2252682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252682).length < 2 ^ (prefixWord ++ tailWord_2252682).sum := by decide
  have hdescent : baseEnd_2252682 < baseStart_2252682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252689 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_2252689 : Nat := 118140960795 + 2252689 * 2 ^ 59
def prefixEnd_2252689 : Nat := 4983230072969 + 3 ^ 40 * 2252689 * 2
def baseEnd_2252689 : Nat := 771141481397494718418385

theorem tailTrace_2252689 : CollatzResearch.WordTrace tailWord_2252689 prefixEnd_2252689 771141481397494718418385 := by
  unfold tailWord_2252689
  simp only [CollatzResearch.WordTrace]
  refine ⟨82162317735899956496497121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54774878490599970997664747 82162317735899956496497121)
  ·
    refine ⟨61621738301924967372372841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82162317735899956496497121 61621738301924967372372841)
    ·
      refine ⟨46216303726443725529279631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61621738301924967372372841 46216303726443725529279631)
      ·
        refine ⟨69324455589665588293919447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46216303726443725529279631 69324455589665588293919447)
        ·
          refine ⟨103986683384498382440879171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69324455589665588293919447 103986683384498382440879171)
          ·
            refine ⟨155980025076747573661318757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103986683384498382440879171 155980025076747573661318757)
            ·
              refine ⟨29246254701890170061497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155980025076747573661318757 29246254701890170061497267)
              ·
                refine ⟨43869382052835255092245901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29246254701890170061497267 43869382052835255092245901)
                ·
                  refine ⟨16451018269813220659592213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43869382052835255092245901 16451018269813220659592213)
                  ·
                    refine ⟨771141481397494718418385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16451018269813220659592213 771141481397494718418385)
                    ·
                      rfl

theorem cell22_2252689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_2252689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252689 prefixEnd_2252689 := by exact prefixLift 2252689
  have htrace : WordTrace (prefixWord ++ tailWord_2252689) baseStart_2252689 baseEnd_2252689 := by
    simpa [prefixWord, tailWord_2252689, baseEnd_2252689] using wordTrace_append hprefix tailTrace_2252689
  have hstable : (prefixWord ++ tailWord_2252689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252689).length < 2 ^ (prefixWord ++ tailWord_2252689).sum := by decide
  have hdescent : baseEnd_2252689 < baseStart_2252689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252725 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2252725 : Nat := 118140960795 + 2252725 * 2 ^ 59
def prefixEnd_2252725 : Nat := 4983230072969 + 3 ^ 40 * 2252725 * 2
def baseEnd_2252725 : Nat := 771153804933202624518275

theorem tailTrace_2252725 : CollatzResearch.WordTrace tailWord_2252725 prefixEnd_2252725 771153804933202624518275 := by
  unfold tailWord_2252725
  simp only [CollatzResearch.WordTrace]
  refine ⟨82163630763769534644807629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54775753842513023096538419 82163630763769534644807629)
  ·
    refine ⟨30811361536413575491802861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82163630763769534644807629 30811361536413575491802861)
    ·
      refine ⟨11554260576155090809426073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30811361536413575491802861 11554260576155090809426073)
      ·
        refine ⟨8665695432116318107069555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11554260576155090809426073 8665695432116318107069555)
        ·
          refine ⟨12998543148174477160604333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8665695432116318107069555 12998543148174477160604333)
          ·
            refine ⟨4874453680565428935226625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12998543148174477160604333 4874453680565428935226625)
            ·
              refine ⟨3655840260424071701419969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4874453680565428935226625 3655840260424071701419969)
              ·
                refine ⟨2741880195318053776064977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655840260424071701419969 2741880195318053776064977)
                ·
                  refine ⟨2056410146488540332048733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741880195318053776064977 2056410146488540332048733)
                  ·
                    refine ⟨771153804933202624518275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056410146488540332048733 771153804933202624518275)
                    ·
                      rfl

theorem cell22_2252725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2252725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252725 prefixEnd_2252725 := by exact prefixLift 2252725
  have htrace : WordTrace (prefixWord ++ tailWord_2252725) baseStart_2252725 baseEnd_2252725 := by
    simpa [prefixWord, tailWord_2252725, baseEnd_2252725] using wordTrace_append hprefix tailTrace_2252725
  have hstable : (prefixWord ++ tailWord_2252725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252725).length < 2 ^ (prefixWord ++ tailWord_2252725).sum := by decide
  have hdescent : baseEnd_2252725 < baseStart_2252725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252806 : List Nat := [6, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2252806 : Nat := 118140960795 + 2252806 * 2 ^ 59
def prefixEnd_2252806 : Nat := 4983230072969 + 3 ^ 40 * 2252806 * 2
def baseEnd_2252806 : Nat := 85686836987616157027003

theorem tailTrace_2252806 : CollatzResearch.WordTrace tailWord_2252806 prefixEnd_2252806 85686836987616157027003 := by
  unfold tailWord_2252806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567705783639877671203321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54777723384317390319004181 2567705783639877671203321)
  ·
    refine ⟨1925779337729908253402491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2567705783639877671203321 1925779337729908253402491)
    ·
      refine ⟨2888669006594862380103737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925779337729908253402491 2888669006594862380103737)
      ·
        refine ⟨2166501754946146785077803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888669006594862380103737 2166501754946146785077803)
        ·
          refine ⟨3249752632419220177616705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166501754946146785077803 3249752632419220177616705)
          ·
            refine ⟨2437314474314415133212529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249752632419220177616705 2437314474314415133212529)
            ·
              refine ⟨1827985855735811349909397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437314474314415133212529 1827985855735811349909397)
              ·
                refine ⟨85686836987616157027003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1827985855735811349909397 85686836987616157027003)
                ·
                  rfl

theorem cell22_2252806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2252806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252806 prefixEnd_2252806 := by exact prefixLift 2252806
  have htrace : WordTrace (prefixWord ++ tailWord_2252806) baseStart_2252806 baseEnd_2252806 := by
    simpa [prefixWord, tailWord_2252806, baseEnd_2252806] using wordTrace_append hprefix tailTrace_2252806
  have hstable : (prefixWord ++ tailWord_2252806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252806).length < 2 ^ (prefixWord ++ tailWord_2252806).sum := by decide
  have hdescent : baseEnd_2252806 < baseStart_2252806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252811 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 6]
def baseStart_2252811 : Nat := 118140960795 + 2252811 * 2 ^ 59
def prefixEnd_2252811 : Nat := 4983230072969 + 3 ^ 40 * 2252811 * 2
def baseEnd_2252811 : Nat := 257061081496909022289337

theorem tailTrace_2252811 : CollatzResearch.WordTrace tailWord_2252811 prefixEnd_2252811 257061081496909022289337 := by
  unfold tailWord_2252811
  simp only [CollatzResearch.WordTrace]
  refine ⟨82166767441457971332438287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54777844960971980888292191 82166767441457971332438287)
  ·
    refine ⟨123250151162186956998657431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82166767441457971332438287 123250151162186956998657431)
    ·
      refine ⟨184875226743280435497986147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123250151162186956998657431 184875226743280435497986147)
      ·
        refine ⟨277312840114920653246979221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184875226743280435497986147 277312840114920653246979221)
        ·
          refine ⟨12999039380386905620952151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 277312840114920653246979221 12999039380386905620952151)
          ·
            refine ⟨19498559070580358431428227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12999039380386905620952151 19498559070580358431428227)
            ·
              refine ⟨29247838605870537647142341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19498559070580358431428227 29247838605870537647142341)
              ·
                refine ⟨5483969738600725808839189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29247838605870537647142341 5483969738600725808839189)
                ·
                  refine ⟨257061081496909022289337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5483969738600725808839189 257061081496909022289337)
                  ·
                    rfl

theorem cell22_2252811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_2252811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252811 prefixEnd_2252811 := by exact prefixLift 2252811
  have htrace : WordTrace (prefixWord ++ tailWord_2252811) baseStart_2252811 baseEnd_2252811 := by
    simpa [prefixWord, tailWord_2252811, baseEnd_2252811] using wordTrace_append hprefix tailTrace_2252811
  have hstable : (prefixWord ++ tailWord_2252811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252811).length < 2 ^ (prefixWord ++ tailWord_2252811).sum := by decide
  have hdescent : baseEnd_2252811 < baseStart_2252811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252860 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2252860 : Nat := 118140960795 + 2252860 * 2 ^ 59
def prefixEnd_2252860 : Nat := 4983230072969 + 3 ^ 40 * 2252860 * 2
def baseEnd_2252860 : Nat := 771200018192107272392861

theorem tailTrace_2252860 : CollatzResearch.WordTrace tailWord_2252860 prefixEnd_2252860 771200018192107272392861 := by
  unfold tailWord_2252860
  simp only [CollatzResearch.WordTrace]
  refine ⟨41084277309140226350486017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54779036412186968467314689 41084277309140226350486017)
  ·
    refine ⟨30813207981855169762864513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41084277309140226350486017 30813207981855169762864513)
    ·
      refine ⟨23109905986391377322148385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30813207981855169762864513 23109905986391377322148385)
      ·
        refine ⟨17332429489793532991611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23109905986391377322148385 17332429489793532991611289)
        ·
          refine ⟨12999322117345149743708467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17332429489793532991611289 12999322117345149743708467)
          ·
            refine ⟨19498983176017724615562701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12999322117345149743708467 19498983176017724615562701)
            ·
              refine ⟨7312118691006646730836013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19498983176017724615562701 7312118691006646730836013)
              ·
                refine ⟨2742044509127492524063505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7312118691006646730836013 2742044509127492524063505)
                ·
                  refine ⟨2056533381845619393047629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742044509127492524063505 2056533381845619393047629)
                  ·
                    refine ⟨771200018192107272392861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056533381845619393047629 771200018192107272392861)
                    ·
                      rfl

theorem cell22_2252860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2252860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252860 prefixEnd_2252860 := by exact prefixLift 2252860
  have htrace : WordTrace (prefixWord ++ tailWord_2252860) baseStart_2252860 baseEnd_2252860 := by
    simpa [prefixWord, tailWord_2252860, baseEnd_2252860] using wordTrace_append hprefix tailTrace_2252860
  have hstable : (prefixWord ++ tailWord_2252860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252860).length < 2 ^ (prefixWord ++ tailWord_2252860).sum := by decide
  have hdescent : baseEnd_2252860 < baseStart_2252860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252952 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_2252952 : Nat := 118140960795 + 2252952 * 2 ^ 59
def prefixEnd_2252952 : Nat := 4983230072969 + 3 ^ 40 * 2252952 * 2
def baseEnd_2252952 : Nat := 257077170557416566364193

theorem tailTrace_2252952 : CollatzResearch.WordTrace tailWord_2252952 prefixEnd_2252952 257077170557416566364193 := by
  unfold tailWord_2252952
  simp only [CollatzResearch.WordTrace]
  refine ⟨41085955066973576206660555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54781273422631434942214073 41085955066973576206660555)
  ·
    refine ⟨61628932600460364309990833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41085955066973576206660555 61628932600460364309990833)
    ·
      refine ⟨46221699450345273232493125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61628932600460364309990833 46221699450345273232493125)
      ·
        refine ⟨8666568646939738731092461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46221699450345273232493125 8666568646939738731092461)
        ·
          refine ⟨3249963242602402024159673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8666568646939738731092461 3249963242602402024159673)
          ·
            refine ⟨2437472431951801518119755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249963242602402024159673 2437472431951801518119755)
            ·
              refine ⟨3656208647927702277179633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437472431951801518119755 3656208647927702277179633)
              ·
                refine ⟨2742156485945776707884725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656208647927702277179633 2742156485945776707884725)
                ·
                  refine ⟨257077170557416566364193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742156485945776707884725 257077170557416566364193)
                  ·
                    rfl

theorem cell22_2252952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_2252952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2252952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2252952 prefixEnd_2252952 := by exact prefixLift 2252952
  have htrace : WordTrace (prefixWord ++ tailWord_2252952) baseStart_2252952 baseEnd_2252952 := by
    simpa [prefixWord, tailWord_2252952, baseEnd_2252952] using wordTrace_append hprefix tailTrace_2252952
  have hstable : (prefixWord ++ tailWord_2252952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252952).length < 2 ^ (prefixWord ++ tailWord_2252952).sum := by decide
  have hdescent : baseEnd_2252952 < baseStart_2252952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253010 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2253010 : Nat := 118140960795 + 2253010 * 2 ^ 59
def prefixEnd_2253010 : Nat := 4983230072969 + 3 ^ 40 * 2253010 * 2
def baseEnd_2253010 : Nat := 771251366257556881142401

theorem tailTrace_2253010 : CollatzResearch.WordTrace tailWord_2253010 prefixEnd_2253010 771251366257556881142401 := by
  unfold tailWord_2253010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20543506391934257079733121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54782683711824685545954989 20543506391934257079733121)
  ·
    refine ⟨15407629793950692809799841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20543506391934257079733121 15407629793950692809799841)
    ·
      refine ⟨11555722345463019607349881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15407629793950692809799841 11555722345463019607349881)
      ·
        refine ⟨8666791759097264705512411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11555722345463019607349881 8666791759097264705512411)
        ·
          refine ⟨13000187638645897058268617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666791759097264705512411 13000187638645897058268617)
          ·
            refine ⟨9750140728984422793701463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000187638645897058268617 9750140728984422793701463)
            ·
              refine ⟨14625211093476634190552195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9750140728984422793701463 14625211093476634190552195)
              ·
                refine ⟨21937816640214951285828293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14625211093476634190552195 21937816640214951285828293)
                ·
                  refine ⟨4113340620040303366092805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21937816640214951285828293 4113340620040303366092805)
                  ·
                    refine ⟨771251366257556881142401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4113340620040303366092805 771251366257556881142401)
                    ·
                      rfl

theorem cell22_2253010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2253010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253010 prefixEnd_2253010 := by exact prefixLift 2253010
  have htrace : WordTrace (prefixWord ++ tailWord_2253010) baseStart_2253010 baseEnd_2253010 := by
    simpa [prefixWord, tailWord_2253010, baseEnd_2253010] using wordTrace_append hprefix tailTrace_2253010
  have hstable : (prefixWord ++ tailWord_2253010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253010).length < 2 ^ (prefixWord ++ tailWord_2253010).sum := by decide
  have hdescent : baseEnd_2253010 < baseStart_2253010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253014 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2253014 : Nat := 118140960795 + 2253014 * 2 ^ 59
def prefixEnd_2253014 : Nat := 4983230072969 + 3 ^ 40 * 2253014 * 2
def baseEnd_2253014 : Nat := 257084245179767401347463

theorem tailTrace_2253014 : CollatzResearch.WordTrace tailWord_2253014 prefixEnd_2253014 257084245179767401347463 := by
  unfold tailWord_2253014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135885716232658562629881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54782780973148358001385397 5135885716232658562629881)
  ·
    refine ⟨3851914287174493921972411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5135885716232658562629881 3851914287174493921972411)
    ·
      refine ⟨5777871430761740882958617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3851914287174493921972411 5777871430761740882958617)
      ·
        refine ⟨4333403573071305662218963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5777871430761740882958617 4333403573071305662218963)
        ·
          refine ⟨6500105359606958493328445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333403573071305662218963 6500105359606958493328445)
          ·
            refine ⟨2437539509852609434998167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500105359606958493328445 2437539509852609434998167)
            ·
              refine ⟨3656309264778914152497251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437539509852609434998167 3656309264778914152497251)
              ·
                refine ⟨5484463897168371228745877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656309264778914152497251 5484463897168371228745877)
                ·
                  refine ⟨257084245179767401347463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5484463897168371228745877 257084245179767401347463)
                  ·
                    rfl

theorem cell22_2253014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2253014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253014 prefixEnd_2253014 := by exact prefixLift 2253014
  have htrace : WordTrace (prefixWord ++ tailWord_2253014) baseStart_2253014 baseEnd_2253014 := by
    simpa [prefixWord, tailWord_2253014, baseEnd_2253014] using wordTrace_append hprefix tailTrace_2253014
  have hstable : (prefixWord ++ tailWord_2253014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253014).length < 2 ^ (prefixWord ++ tailWord_2253014).sum := by decide
  have hdescent : baseEnd_2253014 < baseStart_2253014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253029 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_2253029 : Nat := 118140960795 + 2253029 * 2 ^ 59
def prefixEnd_2253029 : Nat := 4983230072969 + 3 ^ 40 * 2253029 * 2
def baseEnd_2253029 : Nat := 771257870345847164917343

theorem tailTrace_2253029 : CollatzResearch.WordTrace tailWord_2253029 prefixEnd_2253029 771257870345847164917343 := by
  unfold tailWord_2253029
  simp only [CollatzResearch.WordTrace]
  refine ⟨82174718554668194563874141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54783145703112129709249427 82174718554668194563874141)
  ·
    refine ⟨30815519458000572961452803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82174718554668194563874141 30815519458000572961452803)
    ·
      refine ⟨46223279187000859442179205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30815519458000572961452803 46223279187000859442179205)
      ·
        refine ⟨8666864847562661145408601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46223279187000859442179205 8666864847562661145408601)
        ·
          refine ⟨6500148635671995859056451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8666864847562661145408601 6500148635671995859056451)
          ·
            refine ⟨9750222953507993788584677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500148635671995859056451 9750222953507993788584677)
            ·
              refine ⟨1828166803782748835359627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9750222953507993788584677 1828166803782748835359627)
              ·
                refine ⟨2742250205674123253039441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828166803782748835359627 2742250205674123253039441)
                ·
                  refine ⟨2056687654255592439779581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742250205674123253039441 2056687654255592439779581)
                  ·
                    refine ⟨771257870345847164917343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056687654255592439779581 771257870345847164917343)
                    ·
                      rfl

theorem cell22_2253029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_2253029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253029 prefixEnd_2253029 := by exact prefixLift 2253029
  have htrace : WordTrace (prefixWord ++ tailWord_2253029) baseStart_2253029 baseEnd_2253029 := by
    simpa [prefixWord, tailWord_2253029, baseEnd_2253029] using wordTrace_append hprefix tailTrace_2253029
  have hstable : (prefixWord ++ tailWord_2253029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253029).length < 2 ^ (prefixWord ++ tailWord_2253029).sum := by decide
  have hdescent : baseEnd_2253029 < baseStart_2253029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253040 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_2253040 : Nat := 118140960795 + 2253040 * 2 ^ 59
def prefixEnd_2253040 : Nat := 4983230072969 + 3 ^ 40 * 2253040 * 2
def baseEnd_2253040 : Nat := 771261635870646802892309

theorem tailTrace_2253040 : CollatzResearch.WordTrace tailWord_2253040 prefixEnd_2253040 771261635870646802892309 := by
  unfold tailWord_2253040
  simp only [CollatzResearch.WordTrace]
  refine ⟨41087559878814171721262287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54783413171752228961683049 41087559878814171721262287)
  ·
    refine ⟨61631339818221257581893431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41087559878814171721262287 61631339818221257581893431)
    ·
      refine ⟨92447009727331886372840147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61631339818221257581893431 92447009727331886372840147)
      ·
        refine ⟨138670514590997829559260221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92447009727331886372840147 138670514590997829559260221)
        ·
          refine ⟨52001442971624186084722583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138670514590997829559260221 52001442971624186084722583)
          ·
            refine ⟨78002164457436279127083875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52001442971624186084722583 78002164457436279127083875)
            ·
              refine ⟨117003246686154418690625813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78002164457436279127083875 117003246686154418690625813)
              ·
                refine ⟨5484527188413488376123085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117003246686154418690625813 5484527188413488376123085)
                ·
                  refine ⟨2056697695655058141046157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5484527188413488376123085 2056697695655058141046157)
                  ·
                    refine ⟨771261635870646802892309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056697695655058141046157 771261635870646802892309)
                    ·
                      rfl

theorem cell22_2253040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_2253040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253040 prefixEnd_2253040 := by exact prefixLift 2253040
  have htrace : WordTrace (prefixWord ++ tailWord_2253040) baseStart_2253040 baseEnd_2253040 := by
    simpa [prefixWord, tailWord_2253040, baseEnd_2253040] using wordTrace_append hprefix tailTrace_2253040
  have hstable : (prefixWord ++ tailWord_2253040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253040).length < 2 ^ (prefixWord ++ tailWord_2253040).sum := by decide
  have hdescent : baseEnd_2253040 < baseStart_2253040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253053 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 9]
def baseStart_2253053 : Nat := 118140960795 + 2253053 * 2 ^ 59
def prefixEnd_2253053 : Nat := 4983230072969 + 3 ^ 40 * 2253053 * 2
def baseEnd_2253053 : Nat := 257088695345439700772423

theorem tailTrace_2253053 : CollatzResearch.WordTrace tailWord_2253053 prefixEnd_2253053 257088695345439700772423 := by
  unfold tailWord_2253053
  simp only [CollatzResearch.WordTrace]
  refine ⟨82175593906581246662747813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54783729271054164441831875 82175593906581246662747813)
  ·
    refine ⟨15407923857483983749265215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82175593906581246662747813 15407923857483983749265215)
    ·
      refine ⟨23111885786225975623897823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15407923857483983749265215 23111885786225975623897823)
      ·
        refine ⟨34667828679338963435846735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23111885786225975623897823 34667828679338963435846735)
        ·
          refine ⟨52001743019008445153770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34667828679338963435846735 52001743019008445153770103)
          ·
            refine ⟨78002614528512667730655155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52001743019008445153770103 78002614528512667730655155)
            ·
              refine ⟨117003921792769001595982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78002614528512667730655155 117003921792769001595982733)
              ·
                refine ⟨43876470672288375598493525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117003921792769001595982733 43876470672288375598493525)
                ·
                  refine ⟨257088695345439700772423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43876470672288375598493525 257088695345439700772423)
                  ·
                    rfl

theorem cell22_2253053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_2253053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253053 prefixEnd_2253053 := by exact prefixLift 2253053
  have htrace : WordTrace (prefixWord ++ tailWord_2253053) baseStart_2253053 baseEnd_2253053 := by
    simpa [prefixWord, tailWord_2253053, baseEnd_2253053] using wordTrace_append hprefix tailTrace_2253053
  have hstable : (prefixWord ++ tailWord_2253053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253053).length < 2 ^ (prefixWord ++ tailWord_2253053).sum := by decide
  have hdescent : baseEnd_2253053 < baseStart_2253053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253100 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_2253100 : Nat := 118140960795 + 2253100 * 2 ^ 59
def prefixEnd_2253100 : Nat := 4983230072969 + 3 ^ 40 * 2253100 * 2
def baseEnd_2253100 : Nat := 771282175096826646392125

theorem tailTrace_2253100 : CollatzResearch.WordTrace tailWord_2253100 prefixEnd_2253100 771282175096826646392125 := by
  unfold tailWord_2253100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41088654068705486844854377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54784872091607315793139169 41088654068705486844854377)
  ·
    refine ⟨30816490551529115133640783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41088654068705486844854377 30816490551529115133640783)
    ·
      refine ⟨46224735827293672700461175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30816490551529115133640783 46224735827293672700461175)
      ·
        refine ⟨69337103740940509050691763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46224735827293672700461175 69337103740940509050691763)
        ·
          refine ⟨104005655611410763576037645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69337103740940509050691763 104005655611410763576037645)
          ·
            refine ⟨39002120854279036341014117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104005655611410763576037645 39002120854279036341014117)
            ·
              refine ⟨7312897660177319313940147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39002120854279036341014117 7312897660177319313940147)
              ·
                refine ⟨10969346490265978970910221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312897660177319313940147 10969346490265978970910221)
                ·
                  refine ⟨4113504933849742114091333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10969346490265978970910221 4113504933849742114091333)
                  ·
                    refine ⟨771282175096826646392125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4113504933849742114091333 771282175096826646392125)
                    ·
                      rfl

theorem cell22_2253100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_2253100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253100 prefixEnd_2253100 := by exact prefixLift 2253100
  have htrace : WordTrace (prefixWord ++ tailWord_2253100) baseStart_2253100 baseEnd_2253100 := by
    simpa [prefixWord, tailWord_2253100, baseEnd_2253100] using wordTrace_append hprefix tailTrace_2253100
  have hstable : (prefixWord ++ tailWord_2253100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253100).length < 2 ^ (prefixWord ++ tailWord_2253100).sum := by decide
  have hdescent : baseEnd_2253100 < baseStart_2253100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253121 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 5]
def baseStart_2253121 : Nat := 118140960795 + 2253121 * 2 ^ 59
def prefixEnd_2253121 : Nat := 4983230072969 + 3 ^ 40 * 2253121 * 2
def baseEnd_2253121 : Nat := 257096454608663197205687

theorem tailTrace_2253121 : CollatzResearch.WordTrace tailWord_2253121 prefixEnd_2253121 257096454608663197205687 := by
  unfold tailWord_2253121
  simp only [CollatzResearch.WordTrace]
  refine ⟨82178074070334894276223217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54785382713556596184148811 82178074070334894276223217)
  ·
    refine ⟨61633555552751170707167413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82178074070334894276223217 61633555552751170707167413)
    ·
      refine ⟨5778145833070422253796945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61633555552751170707167413 5778145833070422253796945)
      ·
        refine ⟨4333609374802816690347709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778145833070422253796945 4333609374802816690347709)
        ·
          refine ⟨1625103515551056258880391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4333609374802816690347709 1625103515551056258880391)
          ·
            refine ⟨2437655273326584388320587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625103515551056258880391 2437655273326584388320587)
            ·
              refine ⟨3656482909989876582480881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437655273326584388320587 3656482909989876582480881)
              ·
                refine ⟨2742362182492407436860661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656482909989876582480881 2742362182492407436860661)
                ·
                  refine ⟨257096454608663197205687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742362182492407436860661 257096454608663197205687)
                  ·
                    rfl

theorem cell22_2253121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_2253121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253121 prefixEnd_2253121 := by exact prefixLift 2253121
  have htrace : WordTrace (prefixWord ++ tailWord_2253121) baseStart_2253121 baseEnd_2253121 := by
    simpa [prefixWord, tailWord_2253121, baseEnd_2253121] using wordTrace_append hprefix tailTrace_2253121
  have hstable : (prefixWord ++ tailWord_2253121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253121).length < 2 ^ (prefixWord ++ tailWord_2253121).sum := by decide
  have hdescent : baseEnd_2253121 < baseStart_2253121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253132 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_2253132 : Nat := 118140960795 + 2253132 * 2 ^ 59
def prefixEnd_2253132 : Nat := 4983230072969 + 3 ^ 40 * 2253132 * 2
def baseEnd_2253132 : Nat := 257097709783596409864009

theorem tailTrace_2253132 : CollatzResearch.WordTrace tailWord_2253132 prefixEnd_2253132 257097709783596409864009 := by
  unfold tailWord_2253132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089237636647521577436825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54785650182196695436582433 41089237636647521577436825)
  ·
    refine ⟨30816928227485641183077619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41089237636647521577436825 30816928227485641183077619)
    ·
      refine ⟨46225392341228461774616429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30816928227485641183077619 46225392341228461774616429)
      ·
        refine ⟨17334522127960673165481161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46225392341228461774616429 17334522127960673165481161)
        ·
          refine ⟨13000891595970504874110871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17334522127960673165481161 13000891595970504874110871)
          ·
            refine ⟨19501337393955757311166307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13000891595970504874110871 19501337393955757311166307)
            ·
              refine ⟨29252006090933635966749461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19501337393955757311166307 29252006090933635966749461)
              ·
                refine ⟨1371187785512514185941381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29252006090933635966749461 1371187785512514185941381)
                ·
                  refine ⟨257097709783596409864009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371187785512514185941381 257097709783596409864009)
                  ·
                    rfl

theorem cell22_2253132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_2253132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253132 prefixEnd_2253132 := by exact prefixLift 2253132
  have htrace : WordTrace (prefixWord ++ tailWord_2253132) baseStart_2253132 baseEnd_2253132 := by
    simpa [prefixWord, tailWord_2253132, baseEnd_2253132] using wordTrace_append hprefix tailTrace_2253132
  have hstable : (prefixWord ++ tailWord_2253132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253132).length < 2 ^ (prefixWord ++ tailWord_2253132).sum := by decide
  have hdescent : baseEnd_2253132 < baseStart_2253132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253162 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2253162 : Nat := 118140960795 + 2253162 * 2 ^ 59
def prefixEnd_2253162 : Nat := 4983230072969 + 3 ^ 40 * 2253162 * 2
def baseEnd_2253162 : Nat := 771303398963879151341935

theorem tailTrace_2253162 : CollatzResearch.WordTrace tailWord_2253162 prefixEnd_2253162 771303398963879151341935 := by
  unfold tailWord_2253162
  simp only [CollatzResearch.WordTrace]
  refine ⟨20544892365796589569616435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54786379642124238852310493 20544892365796589569616435)
  ·
    refine ⟨30817338548694884354424653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20544892365796589569616435 30817338548694884354424653)
    ·
      refine ⟨11556501955760581632909245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30817338548694884354424653 11556501955760581632909245)
      ·
        refine ⟨4333688233410218112340967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11556501955760581632909245 4333688233410218112340967)
        ·
          refine ⟨6500532350115327168511451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333688233410218112340967 6500532350115327168511451)
          ·
            refine ⟨9750798525172990752767177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500532350115327168511451 9750798525172990752767177)
            ·
              refine ⟨7313098893879743064575383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750798525172990752767177 7313098893879743064575383)
              ·
                refine ⟨10969648340819614596863075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7313098893879743064575383 10969648340819614596863075)
                ·
                  refine ⟨16454472511229421895294613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10969648340819614596863075 16454472511229421895294613)
                  ·
                    refine ⟨771303398963879151341935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16454472511229421895294613 771303398963879151341935)
                    ·
                      rfl

theorem cell22_2253162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2253162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253162 prefixEnd_2253162 := by exact prefixLift 2253162
  have htrace : WordTrace (prefixWord ++ tailWord_2253162) baseStart_2253162 baseEnd_2253162 := by
    simpa [prefixWord, tailWord_2253162, baseEnd_2253162] using wordTrace_append hprefix tailTrace_2253162
  have hstable : (prefixWord ++ tailWord_2253162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253162).length < 2 ^ (prefixWord ++ tailWord_2253162).sum := by decide
  have hdescent : baseEnd_2253162 < baseStart_2253162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253194 : List Nat := [3, 1, 2, 5, 1, 1, 2, 7]
def baseStart_2253194 : Nat := 118140960795 + 2253194 * 2 ^ 59
def prefixEnd_2253194 : Nat := 4983230072969 + 3 ^ 40 * 2253194 * 2
def baseEnd_2253194 : Nat := 85701594801982414949093

theorem tailTrace_2253194 : CollatzResearch.WordTrace tailWord_2253194 prefixEnd_2253194 85701594801982414949093 := by
  unfold tailWord_2253194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545184149767606935907659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54787157732713618495753757 20545184149767606935907659)
  ·
    refine ⟨30817776224651410403861489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20545184149767606935907659 30817776224651410403861489)
    ·
      refine ⟨23113332168488557802896117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30817776224651410403861489 23113332168488557802896117)
      ·
        refine ⟨2166874890795802294021511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23113332168488557802896117 2166874890795802294021511)
        ·
          refine ⟨3250312336193703441032267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166874890795802294021511 3250312336193703441032267)
          ·
            refine ⟨4875468504290555161548401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250312336193703441032267 4875468504290555161548401)
            ·
              refine ⟨3656601378217916371161301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875468504290555161548401 3656601378217916371161301)
              ·
                refine ⟨85701594801982414949093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3656601378217916371161301 85701594801982414949093)
                ·
                  rfl

theorem cell22_2253194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_2253194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253194 prefixEnd_2253194 := by exact prefixLift 2253194
  have htrace : WordTrace (prefixWord ++ tailWord_2253194) baseStart_2253194 baseEnd_2253194 := by
    simpa [prefixWord, tailWord_2253194, baseEnd_2253194] using wordTrace_append hprefix tailTrace_2253194
  have hstable : (prefixWord ++ tailWord_2253194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253194).length < 2 ^ (prefixWord ++ tailWord_2253194).sum := by decide
  have hdescent : baseEnd_2253194 < baseStart_2253194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253198 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_2253198 : Nat := 118140960795 + 2253198 * 2 ^ 59
def prefixEnd_2253198 : Nat := 4983230072969 + 3 ^ 40 * 2253198 * 2
def baseEnd_2253198 : Nat := 771315722499587057441825

theorem tailTrace_2253198 : CollatzResearch.WordTrace tailWord_2253198 prefixEnd_2253198 771315722499587057441825 := by
  unfold tailWord_2253198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272610311381992053347031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54787254994037290951184165 10272610311381992053347031)
  ·
    refine ⟨15408915467072988080020547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10272610311381992053347031 15408915467072988080020547)
    ·
      refine ⟨23113373200609482120030821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15408915467072988080020547 23113373200609482120030821)
      ·
        refine ⟨4333757475114277897505779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23113373200609482120030821 4333757475114277897505779)
        ·
          refine ⟨6500636212671416846258669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333757475114277897505779 6500636212671416846258669)
          ·
            refine ⟨2437738579751781317347001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500636212671416846258669 2437738579751781317347001)
            ·
              refine ⟨1828303934813835988010251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437738579751781317347001 1828303934813835988010251)
              ·
                refine ⟨2742455902220753982015377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828303934813835988010251 2742455902220753982015377)
                ·
                  refine ⟨2056841926665565486511533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742455902220753982015377 2056841926665565486511533)
                  ·
                    refine ⟨771315722499587057441825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056841926665565486511533 771315722499587057441825)
                    ·
                      rfl

theorem cell22_2253198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_2253198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253198 prefixEnd_2253198 := by exact prefixLift 2253198
  have htrace : WordTrace (prefixWord ++ tailWord_2253198) baseStart_2253198 baseEnd_2253198 := by
    simpa [prefixWord, tailWord_2253198, baseEnd_2253198] using wordTrace_append hprefix tailTrace_2253198
  have hstable : (prefixWord ++ tailWord_2253198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253198).length < 2 ^ (prefixWord ++ tailWord_2253198).sum := by decide
  have hdescent : baseEnd_2253198 < baseStart_2253198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253297 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2253297 : Nat := 118140960795 + 2253297 * 2 ^ 59
def prefixEnd_2253297 : Nat := 4983230072969 + 3 ^ 40 * 2253297 * 2
def baseEnd_2253297 : Nat := 771349612222783799216521

theorem tailTrace_2253297 : CollatzResearch.WordTrace tailWord_2253297 prefixEnd_2253297 771349612222783799216521 := by
  unfold tailWord_2253297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82184493317697276334630145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54789662211798184223086763 82184493317697276334630145)
  ·
    refine ⟨61638369988272957250972609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82184493317697276334630145 61638369988272957250972609)
    ·
      refine ⟨46228777491204717938229457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61638369988272957250972609 46228777491204717938229457)
      ·
        refine ⟨34671583118403538453672093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46228777491204717938229457 34671583118403538453672093)
        ·
          refine ⟨13001843669401326920127035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34671583118403538453672093 13001843669401326920127035)
          ·
            refine ⟨19502765504101990380190553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001843669401326920127035 19502765504101990380190553)
            ·
              refine ⟨14627074128076492785142915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19502765504101990380190553 14627074128076492785142915)
              ·
                refine ⟨21940611192114739177714373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14627074128076492785142915 21940611192114739177714373)
                ·
                  refine ⟨4113864598521513595821445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21940611192114739177714373 4113864598521513595821445)
                  ·
                    refine ⟨771349612222783799216521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4113864598521513595821445 771349612222783799216521)
                    ·
                      rfl

theorem cell22_2253297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2253297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253297 prefixEnd_2253297 := by exact prefixLift 2253297
  have htrace : WordTrace (prefixWord ++ tailWord_2253297) baseStart_2253297 baseEnd_2253297 := by
    simpa [prefixWord, tailWord_2253297, baseEnd_2253297] using wordTrace_append hprefix tailTrace_2253297
  have hstable : (prefixWord ++ tailWord_2253297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253297).length < 2 ^ (prefixWord ++ tailWord_2253297).sum := by decide
  have hdescent : baseEnd_2253297 < baseStart_2253297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253301 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 6]
def baseStart_2253301 : Nat := 118140960795 + 2253301 * 2 ^ 59
def prefixEnd_2253301 : Nat := 4983230072969 + 3 ^ 40 * 2253301 * 2
def baseEnd_2253301 : Nat := 257116993834843040705503

theorem tailTrace_2253301 : CollatzResearch.WordTrace tailWord_2253301 prefixEnd_2253301 257116993834843040705503 := by
  unfold tailWord_2253301
  simp only [CollatzResearch.WordTrace]
  refine ⟨82184639209682785017775757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54789759473121856678517171 82184639209682785017775757)
  ·
    refine ⟨30819239703631044381665909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82184639209682785017775757 30819239703631044381665909)
    ·
      refine ⟨2889303722215410410781179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30819239703631044381665909 2889303722215410410781179)
      ·
        refine ⟨4333955583323115616171769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889303722215410410781179 4333955583323115616171769)
        ·
          refine ⟨3250466687492336712128827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333955583323115616171769 3250466687492336712128827)
          ·
            refine ⟨4875700031238505068193241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250466687492336712128827 4875700031238505068193241)
            ·
              refine ⟨3656775023428878801144931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875700031238505068193241 3656775023428878801144931)
              ·
                refine ⟨5485162535143318201717397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656775023428878801144931 5485162535143318201717397)
                ·
                  refine ⟨257116993834843040705503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5485162535143318201717397 257116993834843040705503)
                  ·
                    rfl

theorem cell22_2253301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_2253301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253301 prefixEnd_2253301 := by exact prefixLift 2253301
  have htrace : WordTrace (prefixWord ++ tailWord_2253301) baseStart_2253301 baseEnd_2253301 := by
    simpa [prefixWord, tailWord_2253301, baseEnd_2253301] using wordTrace_append hprefix tailTrace_2253301
  have hstable : (prefixWord ++ tailWord_2253301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253301).length < 2 ^ (prefixWord ++ tailWord_2253301).sum := by decide
  have hdescent : baseEnd_2253301 < baseStart_2253301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253316 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2253316 : Nat := 118140960795 + 2253316 * 2 ^ 59
def prefixEnd_2253316 : Nat := 4983230072969 + 3 ^ 40 * 2253316 * 2
def baseEnd_2253316 : Nat := 771356116311074082991463

theorem tailTrace_2253316 : CollatzResearch.WordTrace tailWord_2253316 prefixEnd_2253316 771356116311074082991463 := by
  unfold tailWord_2253316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41092593152314221289785901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54790124203085628386381201 41092593152314221289785901)
  ·
    refine ⟨15409722432117832983669713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41092593152314221289785901 15409722432117832983669713)
    ·
      refine ⟨11557291824088374737752285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15409722432117832983669713 11557291824088374737752285)
      ·
        refine ⟨4333984434033140526657107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11557291824088374737752285 4333984434033140526657107)
        ·
          refine ⟨6500976651049710789985661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333984434033140526657107 6500976651049710789985661)
          ·
            refine ⟨2437866244143641546244623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500976651049710789985661 2437866244143641546244623)
            ·
              refine ⟨3656799366215462319366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437866244143641546244623 3656799366215462319366935)
              ·
                refine ⟨5485199049323193479050403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656799366215462319366935 5485199049323193479050403)
                ·
                  refine ⟨8227798573984790218575605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5485199049323193479050403 8227798573984790218575605)
                  ·
                    refine ⟨771356116311074082991463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8227798573984790218575605 771356116311074082991463)
                    ·
                      rfl

theorem cell22_2253316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2253316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253316 prefixEnd_2253316 := by exact prefixLift 2253316
  have htrace : WordTrace (prefixWord ++ tailWord_2253316) baseStart_2253316 baseEnd_2253316 := by
    simpa [prefixWord, tailWord_2253316, baseEnd_2253316] using wordTrace_append hprefix tailTrace_2253316
  have hstable : (prefixWord ++ tailWord_2253316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253316).length < 2 ^ (prefixWord ++ tailWord_2253316).sum := by decide
  have hdescent : baseEnd_2253316 < baseStart_2253316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253318 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2253318 : Nat := 118140960795 + 2253318 * 2 ^ 59
def prefixEnd_2253318 : Nat := 4983230072969 + 3 ^ 40 * 2253318 * 2
def baseEnd_2253318 : Nat := 257118933650648914813819

theorem tailTrace_2253318 : CollatzResearch.WordTrace tailWord_2253318 prefixEnd_2253318 257118933650648914813819 := by
  unfold tailWord_2253318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568289351581912403785769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54790172833747464614096405 2568289351581912403785769)
  ·
    refine ⟨1926217013686434302839327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568289351581912403785769 1926217013686434302839327)
    ·
      refine ⟨2889325520529651454258991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926217013686434302839327 2889325520529651454258991)
      ·
        refine ⟨4333988280794477181388487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889325520529651454258991 4333988280794477181388487)
        ·
          refine ⟨6500982421191715772082731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333988280794477181388487 6500982421191715772082731)
          ·
            refine ⟨9751473631787573658124097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500982421191715772082731 9751473631787573658124097)
            ·
              refine ⟨7313605223840680243593073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9751473631787573658124097 7313605223840680243593073)
              ·
                refine ⟨5485203917880510182694805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7313605223840680243593073 5485203917880510182694805)
                ·
                  refine ⟨257118933650648914813819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5485203917880510182694805 257118933650648914813819)
                  ·
                    rfl

theorem cell22_2253318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2253318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253318 prefixEnd_2253318 := by exact prefixLift 2253318
  have htrace : WordTrace (prefixWord ++ tailWord_2253318) baseStart_2253318 baseEnd_2253318 := by
    simpa [prefixWord, tailWord_2253318, baseEnd_2253318] using wordTrace_append hprefix tailTrace_2253318
  have hstable : (prefixWord ++ tailWord_2253318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253318).length < 2 ^ (prefixWord ++ tailWord_2253318).sum := by decide
  have hdescent : baseEnd_2253318 < baseStart_2253318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253335 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 4]
def baseStart_2253335 : Nat := 118140960795 + 2253335 * 2 ^ 59
def prefixEnd_2253335 : Nat := 4983230072969 + 3 ^ 40 * 2253335 * 2
def baseEnd_2253335 : Nat := 257120873466454788922135

theorem tailTrace_2253335 : CollatzResearch.WordTrace tailWord_2253335 prefixEnd_2253335 257120873466454788922135 := by
  unfold tailWord_2253335
  simp only [CollatzResearch.WordTrace]
  refine ⟨82185879291559608824513459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54790586194373072549675639 82185879291559608824513459)
  ·
    refine ⟨123278818937339413236770189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82185879291559608824513459 123278818937339413236770189)
    ·
      refine ⟨46229557101502279963788821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123278818937339413236770189 46229557101502279963788821)
      ·
        refine ⟨2167010489132919373302601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46229557101502279963788821 2167010489132919373302601)
        ·
          refine ⟨1625257866849689529976951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167010489132919373302601 1625257866849689529976951)
          ·
            refine ⟨2437886800274534294965427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625257866849689529976951 2437886800274534294965427)
            ·
              refine ⟨3656830200411801442448141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437886800274534294965427 3656830200411801442448141)
              ·
                refine ⟨1371311325154425540918053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3656830200411801442448141 1371311325154425540918053)
                ·
                  refine ⟨257120873466454788922135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371311325154425540918053 257120873466454788922135)
                  ·
                    rfl

theorem cell22_2253335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 4].length) (baseStart_2253335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253335 prefixEnd_2253335 := by exact prefixLift 2253335
  have htrace : WordTrace (prefixWord ++ tailWord_2253335) baseStart_2253335 baseEnd_2253335 := by
    simpa [prefixWord, tailWord_2253335, baseEnd_2253335] using wordTrace_append hprefix tailTrace_2253335
  have hstable : (prefixWord ++ tailWord_2253335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253335).length < 2 ^ (prefixWord ++ tailWord_2253335).sum := by decide
  have hdescent : baseEnd_2253335 < baseStart_2253335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253361 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_2253361 : Nat := 118140960795 + 2253361 * 2 ^ 59
def prefixEnd_2253361 : Nat := 4983230072969 + 3 ^ 40 * 2253361 * 2
def baseEnd_2253361 : Nat := 771371520730708965616325

theorem tailTrace_2253361 : CollatzResearch.WordTrace tailWord_2253361 prefixEnd_2253361 771371520730708965616325 := by
  unfold tailWord_2253361
  simp only [CollatzResearch.WordTrace]
  refine ⟨82186827589465415264959937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54791218392976943509973291 82186827589465415264959937)
  ·
    refine ⟨61640120692099061448719953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82186827589465415264959937 61640120692099061448719953)
    ·
      refine ⟨46230090519074296086539965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61640120692099061448719953 46230090519074296086539965)
      ·
        refine ⟨17336283944652861032452487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46230090519074296086539965 17336283944652861032452487)
        ·
          refine ⟨26004425916979291548678731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17336283944652861032452487 26004425916979291548678731)
          ·
            refine ⟨39006638875468937323018097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26004425916979291548678731 39006638875468937323018097)
            ·
              refine ⟨29254979156601702992263573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39006638875468937323018097 29254979156601702992263573)
              ·
                refine ⟨1371327147965704827762355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29254979156601702992263573 1371327147965704827762355)
                ·
                  refine ⟨2056990721948557241643533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371327147965704827762355 2056990721948557241643533)
                  ·
                    refine ⟨771371520730708965616325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056990721948557241643533 771371520730708965616325)
                    ·
                      rfl

theorem cell22_2253361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_2253361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253361 prefixEnd_2253361 := by exact prefixLift 2253361
  have htrace : WordTrace (prefixWord ++ tailWord_2253361) baseStart_2253361 baseEnd_2253361 := by
    simpa [prefixWord, tailWord_2253361, baseEnd_2253361] using wordTrace_append hprefix tailTrace_2253361
  have hstable : (prefixWord ++ tailWord_2253361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253361).length < 2 ^ (prefixWord ++ tailWord_2253361).sum := by decide
  have hdescent : baseEnd_2253361 < baseStart_2253361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253417 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_2253417 : Nat := 118140960795 + 2253417 * 2 ^ 59
def prefixEnd_2253417 : Nat := 4983230072969 + 3 ^ 40 * 2253417 * 2
def baseEnd_2253417 : Nat := 771390690675143486216153

theorem tailTrace_2253417 : CollatzResearch.WordTrace tailWord_2253417 prefixEnd_2253417 771390690675143486216153 := by
  unfold tailWord_2253417
  simp only [CollatzResearch.WordTrace]
  refine ⟨82188870077262536828998505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54792580051508357885999003 82188870077262536828998505)
  ·
    refine ⟨61641652557946902621748879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82188870077262536828998505 61641652557946902621748879)
    ·
      refine ⟨92462478836920353932623319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61641652557946902621748879 92462478836920353932623319)
      ·
        refine ⟨138693718255380530898934979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92462478836920353932623319 138693718255380530898934979)
        ·
          refine ⟨208040577383070796348402469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138693718255380530898934979 208040577383070796348402469)
          ·
            refine ⟨39007608259325774315325463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208040577383070796348402469 39007608259325774315325463)
            ·
              refine ⟨58511412388988661472988195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39007608259325774315325463 58511412388988661472988195)
              ·
                refine ⟨87767118583482992209482293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58511412388988661472988195 87767118583482992209482293)
                ·
                  refine ⟨8228167367201530519638965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87767118583482992209482293 8228167367201530519638965)
                  ·
                    refine ⟨771390690675143486216153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8228167367201530519638965 771390690675143486216153)
                    ·
                      rfl

theorem cell22_2253417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_2253417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253417 prefixEnd_2253417 := by exact prefixLift 2253417
  have htrace : WordTrace (prefixWord ++ tailWord_2253417) baseStart_2253417 baseEnd_2253417 := by
    simpa [prefixWord, tailWord_2253417, baseEnd_2253417] using wordTrace_append hprefix tailTrace_2253417
  have hstable : (prefixWord ++ tailWord_2253417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253417).length < 2 ^ (prefixWord ++ tailWord_2253417).sum := by decide
  have hdescent : baseEnd_2253417 < baseStart_2253417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253432 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2253432 : Nat := 118140960795 + 2253432 * 2 ^ 59
def prefixEnd_2253432 : Nat := 4983230072969 + 3 ^ 40 * 2253432 * 2
def baseEnd_2253432 : Nat := 771395825481688447091107

theorem tailTrace_2253432 : CollatzResearch.WordTrace tailWord_2253432 prefixEnd_2253432 771395825481688447091107 := by
  unfold tailWord_2253432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41094708586104097195397275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54792944781472129593863033 41094708586104097195397275)
  ·
    refine ⟨61642062879156145793095913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41094708586104097195397275 61642062879156145793095913)
    ·
      refine ⟨46231547159367109344821935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61642062879156145793095913 46231547159367109344821935)
      ·
        refine ⟨69347320739050664017232903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46231547159367109344821935 69347320739050664017232903)
        ·
          refine ⟨104020981108575996025849355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69347320739050664017232903 104020981108575996025849355)
          ·
            refine ⟨156031471662863994038774033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104020981108575996025849355 156031471662863994038774033)
            ·
              refine ⟨117023603747147995529080525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156031471662863994038774033 117023603747147995529080525)
              ·
                refine ⟨43883851405180498323405197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117023603747147995529080525 43883851405180498323405197)
                ·
                  refine ⟨16456444276942686871276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43883851405180498323405197 16456444276942686871276949)
                  ·
                    refine ⟨771395825481688447091107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16456444276942686871276949 771395825481688447091107)
                    ·
                      rfl

theorem cell22_2253432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2253432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253432 prefixEnd_2253432 := by exact prefixLift 2253432
  have htrace : WordTrace (prefixWord ++ tailWord_2253432) baseStart_2253432 baseEnd_2253432 := by
    simpa [prefixWord, tailWord_2253432, baseEnd_2253432] using wordTrace_append hprefix tailTrace_2253432
  have hstable : (prefixWord ++ tailWord_2253432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253432).length < 2 ^ (prefixWord ++ tailWord_2253432).sum := by decide
  have hdescent : baseEnd_2253432 < baseStart_2253432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253468 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2253468 : Nat := 118140960795 + 2253468 * 2 ^ 59
def prefixEnd_2253468 : Nat := 4983230072969 + 3 ^ 40 * 2253468 * 2
def baseEnd_2253468 : Nat := 771408149017396353190997

theorem tailTrace_2253468 : CollatzResearch.WordTrace tailWord_2253468 prefixEnd_2253468 771408149017396353190997 := by
  unfold tailWord_2253468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41095365100038886269552529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54793820133385181692736705 41095365100038886269552529)
  ·
    refine ⟨30821523825029164702164397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41095365100038886269552529 30821523825029164702164397)
    ·
      refine ⟨11558071434385936763311649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30821523825029164702164397 11558071434385936763311649)
      ·
        refine ⟨8668553575789452572483737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11558071434385936763311649 8668553575789452572483737)
        ·
          refine ⟨6501415181842089429362803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8668553575789452572483737 6501415181842089429362803)
          ·
            refine ⟨9752122772763134144044205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6501415181842089429362803 9752122772763134144044205)
            ·
              refine ⟨3657046039786175304016577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9752122772763134144044205 3657046039786175304016577)
              ·
                refine ⟨2742784529839631478012433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657046039786175304016577 2742784529839631478012433)
                ·
                  refine ⟨2057088397379723608509325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742784529839631478012433 2057088397379723608509325)
                  ·
                    refine ⟨771408149017396353190997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057088397379723608509325 771408149017396353190997)
                    ·
                      rfl

theorem cell22_2253468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2253468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253468 prefixEnd_2253468 := by exact prefixLift 2253468
  have htrace : WordTrace (prefixWord ++ tailWord_2253468) baseStart_2253468 baseEnd_2253468 := by
    simpa [prefixWord, tailWord_2253468, baseEnd_2253468] using wordTrace_append hprefix tailTrace_2253468
  have hstable : (prefixWord ++ tailWord_2253468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253468).length < 2 ^ (prefixWord ++ tailWord_2253468).sum := by decide
  have hdescent : baseEnd_2253468 < baseStart_2253468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253485 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2253485 : Nat := 118140960795 + 2253485 * 2 ^ 59
def prefixEnd_2253485 : Nat := 4983230072969 + 3 ^ 40 * 2253485 * 2
def baseEnd_2253485 : Nat := 771413968464813975515945

theorem tailTrace_2253485 : CollatzResearch.WordTrace tailWord_2253485 prefixEnd_2253485 771413968464813975515945 := by
  unfold tailWord_2253485
  simp only [CollatzResearch.WordTrace]
  refine ⟨82191350241016184442473909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54794233494010789628315939 82191350241016184442473909)
  ·
    refine ⟨7705439085095267291481929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82191350241016184442473909 7705439085095267291481929)
    ·
      refine ⟨5779079313821450468611447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7705439085095267291481929 5779079313821450468611447)
      ·
        refine ⟨8668618970732175702917171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779079313821450468611447 8668618970732175702917171)
        ·
          refine ⟨13002928456098263554375757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8668618970732175702917171 13002928456098263554375757)
          ·
            refine ⟨4876098171036848832890909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13002928456098263554375757 4876098171036848832890909)
            ·
              refine ⟨1828536814138818312334091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4876098171036848832890909 1828536814138818312334091)
              ·
                refine ⟨2742805221208227468501137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828536814138818312334091 2742805221208227468501137)
                ·
                  refine ⟨2057103915906170601375853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742805221208227468501137 2057103915906170601375853)
                  ·
                    refine ⟨771413968464813975515945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057103915906170601375853 771413968464813975515945)
                    ·
                      rfl

theorem cell22_2253485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2253485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253485 prefixEnd_2253485 := by exact prefixLift 2253485
  have htrace : WordTrace (prefixWord ++ tailWord_2253485) baseStart_2253485 baseEnd_2253485 := by
    simpa [prefixWord, tailWord_2253485, baseEnd_2253485] using wordTrace_append hprefix tailTrace_2253485
  have hstable : (prefixWord ++ tailWord_2253485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253485).length < 2 ^ (prefixWord ++ tailWord_2253485).sum := by decide
  have hdescent : baseEnd_2253485 < baseStart_2253485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253530 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_2253530 : Nat := 118140960795 + 2253530 * 2 ^ 59
def prefixEnd_2253530 : Nat := 4983230072969 + 3 ^ 40 * 2253530 * 2
def baseEnd_2253530 : Nat := 771429372884448858140807

theorem tailTrace_2253530 : CollatzResearch.WordTrace tailWord_2253530 prefixEnd_2253530 771429372884448858140807 := by
  unfold tailWord_2253530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20548247881463289281965511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54795327683902104751908029 20548247881463289281965511)
  ·
    refine ⟨30822371822194933922948267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20548247881463289281965511 30822371822194933922948267)
    ·
      refine ⟨46233557733292400884422401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30822371822194933922948267 46233557733292400884422401)
      ·
        refine ⟨34675168299969300663316801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46233557733292400884422401 34675168299969300663316801)
        ·
          refine ⟨26006376224976975497487601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34675168299969300663316801 26006376224976975497487601)
          ·
            refine ⟨19504782168732731623115701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26006376224976975497487601 19504782168732731623115701)
            ·
              refine ⟨1828573328318693589667097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19504782168732731623115701 1828573328318693589667097)
              ·
                refine ⟨1371429996239020192250323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828573328318693589667097 1371429996239020192250323)
                ·
                  refine ⟨2057144994358530288375485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371429996239020192250323 2057144994358530288375485)
                  ·
                    refine ⟨771429372884448858140807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057144994358530288375485 771429372884448858140807)
                    ·
                      rfl

theorem cell22_2253530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_2253530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253530 prefixEnd_2253530 := by exact prefixLift 2253530
  have htrace : WordTrace (prefixWord ++ tailWord_2253530) baseStart_2253530 baseEnd_2253530 := by
    simpa [prefixWord, tailWord_2253530, baseEnd_2253530] using wordTrace_append hprefix tailTrace_2253530
  have hstable : (prefixWord ++ tailWord_2253530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253530).length < 2 ^ (prefixWord ++ tailWord_2253530).sum := by decide
  have hdescent : baseEnd_2253530 < baseStart_2253530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253571 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 4]
def baseStart_2253571 : Nat := 118140960795 + 2253571 * 2 ^ 59
def prefixEnd_2253571 : Nat := 4983230072969 + 3 ^ 40 * 2253571 * 2
def baseEnd_2253571 : Nat := 257147802674112805955227

theorem tailTrace_2253571 : CollatzResearch.WordTrace tailWord_2253571 prefixEnd_2253571 257147802674112805955227 := by
  unfold tailWord_2253571
  simp only [CollatzResearch.WordTrace]
  refine ⟨82194486918704621130104567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54796324612469747420069711 82194486918704621130104567)
  ·
    refine ⟨123291730378056931695156851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82194486918704621130104567 123291730378056931695156851)
    ·
      refine ⟨184937595567085397542735277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123291730378056931695156851 184937595567085397542735277)
      ·
        refine ⟨69351598337657024078525729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184937595567085397542735277 69351598337657024078525729)
        ·
          refine ⟨52013698753242768058894297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69351598337657024078525729 52013698753242768058894297)
          ·
            refine ⟨39010274064932076044170723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52013698753242768058894297 39010274064932076044170723)
            ·
              refine ⟨58515411097398114066256085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39010274064932076044170723 58515411097398114066256085)
              ·
                refine ⟨1371454947595268298427877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58515411097398114066256085 1371454947595268298427877)
                ·
                  refine ⟨257147802674112805955227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371454947595268298427877 257147802674112805955227)
                  ·
                    rfl

theorem cell22_2253571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 4].length) (baseStart_2253571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253571 prefixEnd_2253571 := by exact prefixLift 2253571
  have htrace : WordTrace (prefixWord ++ tailWord_2253571) baseStart_2253571 baseEnd_2253571 := by
    simpa [prefixWord, tailWord_2253571, baseEnd_2253571] using wordTrace_append hprefix tailTrace_2253571
  have hstable : (prefixWord ++ tailWord_2253571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253571).length < 2 ^ (prefixWord ++ tailWord_2253571).sum := by decide
  have hdescent : baseEnd_2253571 < baseStart_2253571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253622 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2253622 : Nat := 118140960795 + 2253622 * 2 ^ 59
def prefixEnd_2253622 : Nat := 4983230072969 + 3 ^ 40 * 2253622 * 2
def baseEnd_2253622 : Nat := 257153622121530428280175

theorem tailTrace_2253622 : CollatzResearch.WordTrace tailWord_2253622 prefixEnd_2253622 257153622121530428280175 := by
  unfold tailWord_2253622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137271690094991052513195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54797564694346571226807413 5137271690094991052513195)
  ·
    refine ⟨7705907535142486578769793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137271690094991052513195 7705907535142486578769793)
    ·
      refine ⟨5779430651356864934077345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7705907535142486578769793 5779430651356864934077345)
      ·
        refine ⟨4334572988517648700558009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5779430651356864934077345 4334572988517648700558009)
        ·
          refine ⟨3250929741388236525418507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4334572988517648700558009 3250929741388236525418507)
          ·
            refine ⟨4876394612082354788127761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250929741388236525418507 4876394612082354788127761)
            ·
              refine ⟨3657295959061766091095821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4876394612082354788127761 3657295959061766091095821)
              ·
                refine ⟨1371485984648162284160933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657295959061766091095821 1371485984648162284160933)
                ·
                  refine ⟨257153622121530428280175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371485984648162284160933 257153622121530428280175)
                  ·
                    rfl

theorem cell22_2253622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2253622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253622 prefixEnd_2253622 := by exact prefixLift 2253622
  have htrace : WordTrace (prefixWord ++ tailWord_2253622) baseStart_2253622 baseEnd_2253622 := by
    simpa [prefixWord, tailWord_2253622, baseEnd_2253622] using wordTrace_append hprefix tailTrace_2253622
  have hstable : (prefixWord ++ tailWord_2253622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253622).length < 2 ^ (prefixWord ++ tailWord_2253622).sum := by decide
  have hdescent : baseEnd_2253622 < baseStart_2253622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253633 : List Nat := [1, 2, 5, 3, 1, 1, 9]
def baseStart_2253633 : Nat := 118140960795 + 2253633 * 2 ^ 59
def prefixEnd_2253633 : Nat := 4983230072969 + 3 ^ 40 * 2253633 * 2
def baseEnd_2253633 : Nat := 28572764144051515659833

theorem tailTrace_2253633 : CollatzResearch.WordTrace tailWord_2253633 prefixEnd_2253633 28572764144051515659833 := by
  unfold tailWord_2253633
  simp only [CollatzResearch.WordTrace]
  refine ⟨82196748244480005718861553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54797832162986670479241035 82196748244480005718861553)
  ·
    refine ⟨61647561183360004289146165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82196748244480005718861553 61647561183360004289146165)
    ·
      refine ⟨5779458860940000402107453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61647561183360004289146165 5779458860940000402107453)
      ·
        refine ⟨2167297072852500150790295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5779458860940000402107453 2167297072852500150790295)
        ·
          refine ⟨3250945609278750226185443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167297072852500150790295 3250945609278750226185443)
          ·
            refine ⟨4876418413918125339278165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250945609278750226185443 4876418413918125339278165)
            ·
              refine ⟨28572764144051515659833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4876418413918125339278165 28572764144051515659833)
              ·
                rfl

theorem cell22_2253633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 9].length) (baseStart_2253633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253633 prefixEnd_2253633 := by exact prefixLift 2253633
  have htrace : WordTrace (prefixWord ++ tailWord_2253633) baseStart_2253633 baseEnd_2253633 := by
    simpa [prefixWord, tailWord_2253633, baseEnd_2253633] using wordTrace_append hprefix tailTrace_2253633
  have hstable : (prefixWord ++ tailWord_2253633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253633).length < 2 ^ (prefixWord ++ tailWord_2253633).sum := by decide
  have hdescent : baseEnd_2253633 < baseStart_2253633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253659 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_2253659 : Nat := 118140960795 + 2253659 * 2 ^ 59
def prefixEnd_2253659 : Nat := 4983230072969 + 3 ^ 40 * 2253659 * 2
def baseEnd_2253659 : Nat := 771473532220735521665411

theorem tailTrace_2253659 : CollatzResearch.WordTrace tailWord_2253659 prefixEnd_2253659 771473532220735521665411 := by
  unfold tailWord_2253659
  simp only [CollatzResearch.WordTrace]
  refine ⟨82197696542385812159308031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54798464361590541439538687 82197696542385812159308031)
  ·
    refine ⟨123296544813578718238962047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82197696542385812159308031 123296544813578718238962047)
    ·
      refine ⟨184944817220368077358443071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123296544813578718238962047 184944817220368077358443071)
      ·
        refine ⟨277417225830552116037664607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184944817220368077358443071 277417225830552116037664607)
        ·
          refine ⟨416125838745828174056496911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277417225830552116037664607 416125838745828174056496911)
          ·
            refine ⟨624188758118742261084745367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416125838745828174056496911 624188758118742261084745367)
            ·
              refine ⟨936283137178113391627118051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624188758118742261084745367 936283137178113391627118051)
              ·
                refine ⟨1404424705767170087440677077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936283137178113391627118051 1404424705767170087440677077)
                ·
                  refine ⟨32916204041418048924390869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1404424705767170087440677077 32916204041418048924390869)
                  ·
                    refine ⟨771473532220735521665411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32916204041418048924390869 771473532220735521665411)
                    ·
                      rfl

theorem cell22_2253659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_2253659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253659 prefixEnd_2253659 := by exact prefixLift 2253659
  have htrace : WordTrace (prefixWord ++ tailWord_2253659) baseStart_2253659 baseEnd_2253659 := by
    simpa [prefixWord, tailWord_2253659, baseEnd_2253659] using wordTrace_append hprefix tailTrace_2253659
  have hstable : (prefixWord ++ tailWord_2253659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253659).length < 2 ^ (prefixWord ++ tailWord_2253659).sum := by decide
  have hdescent : baseEnd_2253659 < baseStart_2253659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253721 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_2253721 : Nat := 118140960795 + 2253721 * 2 ^ 59
def prefixEnd_2253721 : Nat := 4983230072969 + 3 ^ 40 * 2253721 * 2
def baseEnd_2253721 : Nat := 771494756087788026615221

theorem tailTrace_2253721 : CollatzResearch.WordTrace tailWord_2253721 prefixEnd_2253721 771494756087788026615221 := by
  unfold tailWord_2253721
  simp only [CollatzResearch.WordTrace]
  refine ⟨82199957868161196748065017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54799971912107464498710011 82199957868161196748065017)
  ·
    refine ⟨61649968401120897561048763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82199957868161196748065017 61649968401120897561048763)
    ·
      refine ⟨92474952601681346341573145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61649968401120897561048763 92474952601681346341573145)
      ·
        refine ⟨69356214451261009756179859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92474952601681346341573145 69356214451261009756179859)
        ·
          refine ⟨104034321676891514634269789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69356214451261009756179859 104034321676891514634269789)
          ·
            refine ⟨39012870628834317987851171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104034321676891514634269789 39012870628834317987851171)
            ·
              refine ⟨58519305943251476981776757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39012870628834317987851171 58519305943251476981776757)
              ·
                refine ⟨5486184932179825967041571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58519305943251476981776757 5486184932179825967041571)
                ·
                  refine ⟨8229277398269738950562357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486184932179825967041571 8229277398269738950562357)
                  ·
                    refine ⟨771494756087788026615221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8229277398269738950562357 771494756087788026615221)
                    ·
                      rfl

theorem cell22_2253721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_2253721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253721 prefixEnd_2253721 := by exact prefixLift 2253721
  have htrace : WordTrace (prefixWord ++ tailWord_2253721) baseStart_2253721 baseEnd_2253721 := by
    simpa [prefixWord, tailWord_2253721, baseEnd_2253721] using wordTrace_append hprefix tailTrace_2253721
  have hstable : (prefixWord ++ tailWord_2253721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253721).length < 2 ^ (prefixWord ++ tailWord_2253721).sum := by decide
  have hdescent : baseEnd_2253721 < baseStart_2253721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253750 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2253750 : Nat := 118140960795 + 2253750 * 2 ^ 59
def prefixEnd_2253750 : Nat := 4983230072969 + 3 ^ 40 * 2253750 * 2
def baseEnd_2253750 : Nat := 771504683380441617640133

theorem tailTrace_2253750 : CollatzResearch.WordTrace tailWord_2253750 prefixEnd_2253750 771504683380441617640133 := by
  unfold tailWord_2253750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137563474066008418804419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54800677056704089800580469 5137563474066008418804419)
  ·
    refine ⟨7706345211099012628206629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137563474066008418804419 7706345211099012628206629)
    ·
      refine ⟨1444939727081064867788743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7706345211099012628206629 1444939727081064867788743)
      ·
        refine ⟨2167409590621597301683115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444939727081064867788743 2167409590621597301683115)
        ·
          refine ⟨3251114385932395952524673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167409590621597301683115 3251114385932395952524673)
          ·
            refine ⟨2438335789449296964393505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251114385932395952524673 2438335789449296964393505)
            ·
              refine ⟨1828751842086972723295129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438335789449296964393505 1828751842086972723295129)
              ·
                refine ⟨1371563881565229542471347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828751842086972723295129 1371563881565229542471347)
                ·
                  refine ⟨2057345822347844313707021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371563881565229542471347 2057345822347844313707021)
                  ·
                    refine ⟨771504683380441617640133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057345822347844313707021 771504683380441617640133)
                    ·
                      rfl

theorem cell22_2253750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2253750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253750 prefixEnd_2253750 := by exact prefixLift 2253750
  have htrace : WordTrace (prefixWord ++ tailWord_2253750) baseStart_2253750 baseEnd_2253750 := by
    simpa [prefixWord, tailWord_2253750, baseEnd_2253750] using wordTrace_append hprefix tailTrace_2253750
  have hstable : (prefixWord ++ tailWord_2253750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253750).length < 2 ^ (prefixWord ++ tailWord_2253750).sum := by decide
  have hdescent : baseEnd_2253750 < baseStart_2253750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253753 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_2253753 : Nat := 118140960795 + 2253753 * 2 ^ 59
def prefixEnd_2253753 : Nat := 4983230072969 + 3 ^ 40 * 2253753 * 2
def baseEnd_2253753 : Nat := 771505710341750609815123

theorem tailTrace_2253753 : CollatzResearch.WordTrace tailWord_2253753 prefixEnd_2253753 771505710341750609815123 := by
  unfold tailWord_2253753
  simp only [CollatzResearch.WordTrace]
  refine ⟨82201125004045266213229913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54800750002696844142153275 82201125004045266213229913)
  ·
    refine ⟨61650843753033949659922435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82201125004045266213229913 61650843753033949659922435)
    ·
      refine ⟨92476265629550924489883653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61650843753033949659922435 92476265629550924489883653)
      ·
        refine ⟨17339299805540798341853185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92476265629550924489883653 17339299805540798341853185)
        ·
          refine ⟨13004474854155598756389889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17339299805540798341853185 13004474854155598756389889)
          ·
            refine ⟨9753356140616699067292417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004474854155598756389889 9753356140616699067292417)
            ·
              refine ⟨7315017105462524300469313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9753356140616699067292417 7315017105462524300469313)
              ·
                refine ⟨5486262829096893225351985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7315017105462524300469313 5486262829096893225351985)
                ·
                  refine ⟨4114697121822669919013989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5486262829096893225351985 4114697121822669919013989)
                  ·
                    refine ⟨771505710341750609815123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4114697121822669919013989 771505710341750609815123)
                    ·
                      rfl

theorem cell22_2253753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_2253753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253753 prefixEnd_2253753 := by exact prefixLift 2253753
  have htrace : WordTrace (prefixWord ++ tailWord_2253753) baseStart_2253753 baseEnd_2253753 := by
    simpa [prefixWord, tailWord_2253753, baseEnd_2253753] using wordTrace_append hprefix tailTrace_2253753
  have hstable : (prefixWord ++ tailWord_2253753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253753).length < 2 ^ (prefixWord ++ tailWord_2253753).sum := by decide
  have hdescent : baseEnd_2253753 < baseStart_2253753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253888 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_2253888 : Nat := 118140960795 + 2253888 * 2 ^ 59
def prefixEnd_2253888 : Nat := 4983230072969 + 3 ^ 40 * 2253888 * 2
def baseEnd_2253888 : Nat := 771551923600655257689709

theorem tailTrace_2253888 : CollatzResearch.WordTrace tailWord_2253888 prefixEnd_2253888 771551923600655257689709 := by
  unfold tailWord_2253888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41103024429278092134697159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54804032572370789512929545 41103024429278092134697159)
  ·
    refine ⟨61654536643917138202045739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41103024429278092134697159 61654536643917138202045739)
    ·
      refine ⟨92481804965875707303068609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61654536643917138202045739 92481804965875707303068609)
      ·
        refine ⟨69361353724406780477301457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92481804965875707303068609 69361353724406780477301457)
        ·
          refine ⟨52021015293305085357976093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69361353724406780477301457 52021015293305085357976093)
          ·
            refine ⟨19507880734989407009241035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52021015293305085357976093 19507880734989407009241035)
            ·
              refine ⟨29261821102484110513861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19507880734989407009241035 29261821102484110513861553)
              ·
                refine ⟨21946365826863082885396165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29261821102484110513861553 21946365826863082885396165)
                ·
                  refine ⟨4114943592536828041011781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21946365826863082885396165 4114943592536828041011781)
                  ·
                    refine ⟨771551923600655257689709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4114943592536828041011781 771551923600655257689709)
                    ·
                      rfl

theorem cell22_2253888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_2253888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253888 prefixEnd_2253888 := by exact prefixLift 2253888
  have htrace : WordTrace (prefixWord ++ tailWord_2253888) baseStart_2253888 baseEnd_2253888 := by
    simpa [prefixWord, tailWord_2253888, baseEnd_2253888] using wordTrace_append hprefix tailTrace_2253888
  have hstable : (prefixWord ++ tailWord_2253888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253888).length < 2 ^ (prefixWord ++ tailWord_2253888).sum := by decide
  have hdescent : baseEnd_2253888 < baseStart_2253888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253894 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2253894 : Nat := 118140960795 + 2253894 * 2 ^ 59
def prefixEnd_2253894 : Nat := 4983230072969 + 3 ^ 40 * 2253894 * 2
def baseEnd_2253894 : Nat := 771553977523273242039691

theorem tailTrace_2253894 : CollatzResearch.WordTrace tailWord_2253894 prefixEnd_2253894 771553977523273242039691 := by
  unfold tailWord_2253894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568945865516701477941023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54804178464356298196075157 2568945865516701477941023)
  ·
    refine ⟨3853418798275052216911535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568945865516701477941023 3853418798275052216911535)
    ·
      refine ⟨5780128197412578325367303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853418798275052216911535 5780128197412578325367303)
      ·
        refine ⟨8670192296118867488050955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780128197412578325367303 8670192296118867488050955)
        ·
          refine ⟨13005288444178301232076433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670192296118867488050955 13005288444178301232076433)
          ·
            refine ⟨9753966333133725924057325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13005288444178301232076433 9753966333133725924057325)
            ·
              refine ⟨3657737374925147221521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9753966333133725924057325 3657737374925147221521497)
              ·
                refine ⟨2743303031193860416141123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657737374925147221521497 2743303031193860416141123)
                ·
                  refine ⟨4114954546790790624211685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743303031193860416141123 4114954546790790624211685)
                  ·
                    refine ⟨771553977523273242039691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4114954546790790624211685 771553977523273242039691)
                    ·
                      rfl

theorem cell22_2253894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2253894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253894 prefixEnd_2253894 := by exact prefixLift 2253894
  have htrace : WordTrace (prefixWord ++ tailWord_2253894) baseStart_2253894 baseEnd_2253894 := by
    simpa [prefixWord, tailWord_2253894, baseEnd_2253894] using wordTrace_append hprefix tailTrace_2253894
  have hstable : (prefixWord ++ tailWord_2253894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253894).length < 2 ^ (prefixWord ++ tailWord_2253894).sum := by decide
  have hdescent : baseEnd_2253894 < baseStart_2253894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253922 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2253922 : Nat := 118140960795 + 2253922 * 2 ^ 59
def prefixEnd_2253922 : Nat := 4983230072969 + 3 ^ 40 * 2253922 * 2
def baseEnd_2253922 : Nat := 771563562495490502339605

theorem tailTrace_2253922 : CollatzResearch.WordTrace tailWord_2253922 prefixEnd_2253922 771563562495490502339605 := by
  unfold tailWord_2253922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20551822235108252019033005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54804859293622005384088013 20551822235108252019033005)
  ·
    refine ⟨7706933338165594507137377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20551822235108252019033005 7706933338165594507137377)
    ·
      refine ⟨5780200003624195880353033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706933338165594507137377 5780200003624195880353033)
      ·
        refine ⟨4335150002718146910264775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5780200003624195880353033 4335150002718146910264775)
        ·
          refine ⟨6502725004077220365397163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335150002718146910264775 6502725004077220365397163)
          ·
            refine ⟨9754087506115830548095745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502725004077220365397163 9754087506115830548095745)
            ·
              refine ⟨7315565629586872911071809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754087506115830548095745 7315565629586872911071809)
              ·
                refine ⟨5486674222190154683303857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7315565629586872911071809 5486674222190154683303857)
                ·
                  refine ⟨4115005666642616012477893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5486674222190154683303857 4115005666642616012477893)
                  ·
                    refine ⟨771563562495490502339605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115005666642616012477893 771563562495490502339605)
                    ·
                      rfl

theorem cell22_2253922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2253922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253922 prefixEnd_2253922 := by exact prefixLift 2253922
  have htrace : WordTrace (prefixWord ++ tailWord_2253922) baseStart_2253922 baseEnd_2253922 := by
    simpa [prefixWord, tailWord_2253922, baseEnd_2253922] using wordTrace_append hprefix tailTrace_2253922
  have hstable : (prefixWord ++ tailWord_2253922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253922).length < 2 ^ (prefixWord ++ tailWord_2253922).sum := by decide
  have hdescent : baseEnd_2253922 < baseStart_2253922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253935 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 3, 3]
def baseStart_2253935 : Nat := 118140960795 + 2253935 * 2 ^ 59
def prefixEnd_2253935 : Nat := 4983230072969 + 3 ^ 40 * 2253935 * 2
def baseEnd_2253935 : Nat := 771568012661162801764565

theorem tailTrace_2253935 : CollatzResearch.WordTrace tailWord_2253935 prefixEnd_2253935 771568012661162801764565 := by
  unfold tailWord_2253935
  simp only [CollatzResearch.WordTrace]
  refine ⟨82207763089385911296355259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54805175392923940864236839 82207763089385911296355259)
  ·
    refine ⟨123311644634078866944532889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82207763089385911296355259 123311644634078866944532889)
    ·
      refine ⟨92483733475559150208399667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123311644634078866944532889 92483733475559150208399667)
      ·
        refine ⟨138725600213338725312599501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92483733475559150208399667 138725600213338725312599501)
        ·
          refine ⟨52022100080002021992224813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138725600213338725312599501 52022100080002021992224813)
          ·
            refine ⟨19508287530000758247084305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52022100080002021992224813 19508287530000758247084305)
            ·
              refine ⟨14631215647500568685313229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19508287530000758247084305 14631215647500568685313229)
              ·
                refine ⟨5486705867812713256992461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14631215647500568685313229 5486705867812713256992461)
                ·
                  refine ⟨2057514700429767471372173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5486705867812713256992461 2057514700429767471372173)
                  ·
                    refine ⟨771568012661162801764565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057514700429767471372173 771568012661162801764565)
                    ·
                      rfl

theorem cell22_2253935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_2253935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253935 prefixEnd_2253935 := by exact prefixLift 2253935
  have htrace : WordTrace (prefixWord ++ tailWord_2253935) baseStart_2253935 baseEnd_2253935 := by
    simpa [prefixWord, tailWord_2253935, baseEnd_2253935] using wordTrace_append hprefix tailTrace_2253935
  have hstable : (prefixWord ++ tailWord_2253935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253935).length < 2 ^ (prefixWord ++ tailWord_2253935).sum := by decide
  have hdescent : baseEnd_2253935 < baseStart_2253935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253980 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2253980 : Nat := 118140960795 + 2253980 * 2 ^ 59
def prefixEnd_2253980 : Nat := 4983230072969 + 3 ^ 40 * 2253980 * 2
def baseEnd_2253980 : Nat := 771583417080797684389427

theorem tailTrace_2253980 : CollatzResearch.WordTrace tailWord_2253980 prefixEnd_2253980 771583417080797684389427 := by
  unfold tailWord_2253980
  simp only [CollatzResearch.WordTrace]
  refine ⟨41104702187111441990871697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54806269582815255987828929 41104702187111441990871697)
  ·
    refine ⟨30828526640333581493153773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41104702187111441990871697 30828526640333581493153773)
    ·
      refine ⟨11560697490125093059932665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30828526640333581493153773 11560697490125093059932665)
      ·
        refine ⟨8670523117593819794949499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11560697490125093059932665 8670523117593819794949499)
        ·
          refine ⟨13005784676390729692424249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670523117593819794949499 13005784676390729692424249)
          ·
            refine ⟨9754338507293047269318187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13005784676390729692424249 9754338507293047269318187)
            ·
              refine ⟨14631507760939570903977281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9754338507293047269318187 14631507760939570903977281)
              ·
                refine ⟨10973630820704678177982961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14631507760939570903977281 10973630820704678177982961)
                ·
                  refine ⟨8230223115528508633487221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10973630820704678177982961 8230223115528508633487221)
                  ·
                    refine ⟨771583417080797684389427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8230223115528508633487221 771583417080797684389427)
                    ·
                      rfl

theorem cell22_2253980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2253980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253980 prefixEnd_2253980 := by exact prefixLift 2253980
  have htrace : WordTrace (prefixWord ++ tailWord_2253980) baseStart_2253980 baseEnd_2253980 := by
    simpa [prefixWord, tailWord_2253980, baseEnd_2253980] using wordTrace_append hprefix tailTrace_2253980
  have hstable : (prefixWord ++ tailWord_2253980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253980).length < 2 ^ (prefixWord ++ tailWord_2253980).sum := by decide
  have hdescent : baseEnd_2253980 < baseStart_2253980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253982 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2253982 : Nat := 118140960795 + 2253982 * 2 ^ 59
def prefixEnd_2253982 : Nat := 4983230072969 + 3 ^ 40 * 2253982 * 2
def baseEnd_2253982 : Nat := 257194700573890115279807

theorem tailTrace_2253982 : CollatzResearch.WordTrace tailWord_2253982 prefixEnd_2253982 257194700573890115279807 := by
  unfold tailWord_2253982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276184665026954790414525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54806318213477092215544133 10276184665026954790414525)
  ·
    refine ⟨3853569249385108046405447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10276184665026954790414525 3853569249385108046405447)
    ·
      refine ⟨5780353874077662069608171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853569249385108046405447 5780353874077662069608171)
      ·
        refine ⟨8670530811116493104412257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780353874077662069608171 8670530811116493104412257)
        ·
          refine ⟨6502898108337369828309193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8670530811116493104412257 6502898108337369828309193)
          ·
            refine ⟨4877173581253027371231895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6502898108337369828309193 4877173581253027371231895)
            ·
              refine ⟨7315760371879541056847843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877173581253027371231895 7315760371879541056847843)
              ·
                refine ⟨10973640557819311585271765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315760371879541056847843 10973640557819311585271765)
                ·
                  refine ⟨257194700573890115279807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10973640557819311585271765 257194700573890115279807)
                  ·
                    rfl

theorem cell22_2253982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2253982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2253982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2253982 prefixEnd_2253982 := by exact prefixLift 2253982
  have htrace : WordTrace (prefixWord ++ tailWord_2253982) baseStart_2253982 baseEnd_2253982 := by
    simpa [prefixWord, tailWord_2253982, baseEnd_2253982] using wordTrace_append hprefix tailTrace_2253982
  have hstable : (prefixWord ++ tailWord_2253982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253982).length < 2 ^ (prefixWord ++ tailWord_2253982).sum := by decide
  have hdescent : baseEnd_2253982 < baseStart_2253982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254012 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2254012 : Nat := 118140960795 + 2254012 * 2 ^ 59
def prefixEnd_2254012 : Nat := 4983230072969 + 3 ^ 40 * 2254012 * 2
def baseEnd_2254012 : Nat := 771594371334760267589329

theorem tailTrace_2254012 : CollatzResearch.WordTrace tailWord_2254012 prefixEnd_2254012 771594371334760267589329 := by
  unfold tailWord_2254012
  simp only [CollatzResearch.WordTrace]
  refine ⟨41105285755053476723454145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54807047673404635631272193 41105285755053476723454145)
  ·
    refine ⟨30828964316290107542590609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41105285755053476723454145 30828964316290107542590609)
    ·
      refine ⟨23121723237217580656942957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30828964316290107542590609 23121723237217580656942957)
      ·
        refine ⟨8670646213956592746353609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23121723237217580656942957 8670646213956592746353609)
        ·
          refine ⟨6502984660467444559765207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8670646213956592746353609 6502984660467444559765207)
          ·
            refine ⟨9754476990701166839647811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502984660467444559765207 9754476990701166839647811)
            ·
              refine ⟨14631715486051750259471717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9754476990701166839647811 14631715486051750259471717)
              ·
                refine ⟨2743446653634703173650947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14631715486051750259471717 2743446653634703173650947)
                ·
                  refine ⟨4115169980452054760476421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743446653634703173650947 4115169980452054760476421)
                  ·
                    refine ⟨771594371334760267589329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115169980452054760476421 771594371334760267589329)
                    ·
                      rfl

theorem cell22_2254012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2254012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254012 prefixEnd_2254012 := by exact prefixLift 2254012
  have htrace : WordTrace (prefixWord ++ tailWord_2254012) baseStart_2254012 baseEnd_2254012 := by
    simpa [prefixWord, tailWord_2254012, baseEnd_2254012] using wordTrace_append hprefix tailTrace_2254012
  have hstable : (prefixWord ++ tailWord_2254012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254012).length < 2 ^ (prefixWord ++ tailWord_2254012).sum := by decide
  have hdescent : baseEnd_2254012 < baseStart_2254012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254042 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_2254042 : Nat := 118140960795 + 2254042 * 2 ^ 59
def prefixEnd_2254042 : Nat := 4983230072969 + 3 ^ 40 * 2254042 * 2
def baseEnd_2254042 : Nat := 771604640947850189339237

theorem tailTrace_2254042 : CollatzResearch.WordTrace tailWord_2254042 prefixEnd_2254042 771604640947850189339237 := by
  unfold tailWord_2254042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552916424999567142625095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54807777133332179047000253 20552916424999567142625095)
  ·
    refine ⟨30829374637499350713937643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20552916424999567142625095 30829374637499350713937643)
    ·
      refine ⟨46244061956249026070906465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30829374637499350713937643 46244061956249026070906465)
      ·
        refine ⟨34683046467186769553179849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46244061956249026070906465 34683046467186769553179849)
        ·
          refine ⟨26012284850390077164884887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34683046467186769553179849 26012284850390077164884887)
          ·
            refine ⟨39018427275585115747327331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26012284850390077164884887 39018427275585115747327331)
            ·
              refine ⟨58527640913377673620990997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39018427275585115747327331 58527640913377673620990997)
              ·
                refine ⟨2743483167814578450983953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58527640913377673620990997 2743483167814578450983953)
                ·
                  refine ⟨2057612375860933838237965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2743483167814578450983953 2057612375860933838237965)
                  ·
                    refine ⟨771604640947850189339237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057612375860933838237965 771604640947850189339237)
                    ·
                      rfl

theorem cell22_2254042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_2254042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254042 prefixEnd_2254042 := by exact prefixLift 2254042
  have htrace : WordTrace (prefixWord ++ tailWord_2254042) baseStart_2254042 baseEnd_2254042 := by
    simpa [prefixWord, tailWord_2254042, baseEnd_2254042] using wordTrace_append hprefix tailTrace_2254042
  have hstable : (prefixWord ++ tailWord_2254042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254042).length < 2 ^ (prefixWord ++ tailWord_2254042).sum := by decide
  have hdescent : baseEnd_2254042 < baseStart_2254042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254059 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 2, 3]
def baseStart_2254059 : Nat := 118140960795 + 2254059 * 2 ^ 59
def prefixEnd_2254059 : Nat := 4983230072969 + 3 ^ 40 * 2254059 * 2
def baseEnd_2254059 : Nat := 771610460395267811664185

theorem tailTrace_2254059 : CollatzResearch.WordTrace tailWord_2254059 prefixEnd_2254059 771610460395267811664185 := by
  unfold tailWord_2254059
  simp only [CollatzResearch.WordTrace]
  refine ⟨82212285740936680473869231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54808190493957786982579487 82212285740936680473869231)
  ·
    refine ⟨123318428611405020710803847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82212285740936680473869231 123318428611405020710803847)
    ·
      refine ⟨184977642917107531066205771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123318428611405020710803847 184977642917107531066205771)
      ·
        refine ⟨277466464375661296599308657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184977642917107531066205771 277466464375661296599308657)
        ·
          refine ⟨208099848281745972449481493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277466464375661296599308657 208099848281745972449481493)
          ·
            refine ⟨9754680388206842458569445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 208099848281745972449481493 9754680388206842458569445)
            ·
              refine ⟨1829002572788782960981771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9754680388206842458569445 1829002572788782960981771)
              ·
                refine ⟨2743503859183174441472657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829002572788782960981771 2743503859183174441472657)
                ·
                  refine ⟨2057627894387380831104493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2743503859183174441472657 2057627894387380831104493)
                  ·
                    refine ⟨771610460395267811664185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057627894387380831104493 771610460395267811664185)
                    ·
                      rfl

theorem cell22_2254059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 3].length) (baseStart_2254059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254059 prefixEnd_2254059 := by exact prefixLift 2254059
  have htrace : WordTrace (prefixWord ++ tailWord_2254059) baseStart_2254059 baseEnd_2254059 := by
    simpa [prefixWord, tailWord_2254059, baseEnd_2254059] using wordTrace_append hprefix tailTrace_2254059
  have hstable : (prefixWord ++ tailWord_2254059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254059).length < 2 ^ (prefixWord ++ tailWord_2254059).sum := by decide
  have hdescent : baseEnd_2254059 < baseStart_2254059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254115 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_2254115 : Nat := 118140960795 + 2254115 * 2 ^ 59
def prefixEnd_2254115 : Nat := 4983230072969 + 3 ^ 40 * 2254115 * 2
def baseEnd_2254115 : Nat := 771629630339702332264013

theorem tailTrace_2254115 : CollatzResearch.WordTrace tailWord_2254115 prefixEnd_2254115 771629630339702332264013 := by
  unfold tailWord_2254115
  simp only [CollatzResearch.WordTrace]
  refine ⟨82214328228733802037907799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54809552152489201358605199 82214328228733802037907799)
  ·
    refine ⟨123321492343100703056861699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82214328228733802037907799 123321492343100703056861699)
    ·
      refine ⟨184982238514651054585292549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123321492343100703056861699 184982238514651054585292549)
      ·
        refine ⟨34684169721497072734742353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184982238514651054585292549 34684169721497072734742353)
        ·
          refine ⟨26013127291122804551056765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34684169721497072734742353 26013127291122804551056765)
          ·
            refine ⟨9754922734171051706646287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26013127291122804551056765 9754922734171051706646287)
            ·
              refine ⟨14632384101256577559969431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9754922734171051706646287 14632384101256577559969431)
              ·
                refine ⟨21948576151884866339954147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14632384101256577559969431 21948576151884866339954147)
                ·
                  refine ⟨32922864227827299509931221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21948576151884866339954147 32922864227827299509931221)
                  ·
                    refine ⟨771629630339702332264013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32922864227827299509931221 771629630339702332264013)
                    ·
                      rfl

theorem cell22_2254115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_2254115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254115 prefixEnd_2254115 := by exact prefixLift 2254115
  have htrace : WordTrace (prefixWord ++ tailWord_2254115) baseStart_2254115 baseEnd_2254115 := by
    simpa [prefixWord, tailWord_2254115, baseEnd_2254115] using wordTrace_append hprefix tailTrace_2254115
  have hstable : (prefixWord ++ tailWord_2254115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254115).length < 2 ^ (prefixWord ++ tailWord_2254115).sum := by decide
  have hdescent : baseEnd_2254115 < baseStart_2254115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254117 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 5]
def baseStart_2254117 : Nat := 118140960795 + 2254117 * 2 ^ 59
def prefixEnd_2254117 : Nat := 4983230072969 + 3 ^ 40 * 2254117 * 2
def baseEnd_2254117 : Nat := 257210104993524997904669

theorem tailTrace_2254117 : CollatzResearch.WordTrace tailWord_2254117 prefixEnd_2254117 257210104993524997904669 := by
  unfold tailWord_2254117
  simp only [CollatzResearch.WordTrace]
  refine ⟨82214401174726556379480605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54809600783151037586320403 82214401174726556379480605)
  ·
    refine ⟨30830400440522458642305227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82214401174726556379480605 30830400440522458642305227)
    ·
      refine ⟨46245600660783687963457841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30830400440522458642305227 46245600660783687963457841)
      ·
        refine ⟨34684200495587765972593381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46245600660783687963457841 34684200495587765972593381)
        ·
          refine ⟨6503287592922706119861259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34684200495587765972593381 6503287592922706119861259)
          ·
            refine ⟨9754931389384059179791889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6503287592922706119861259 9754931389384059179791889)
            ·
              refine ⟨7316198542038044384843917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754931389384059179791889 7316198542038044384843917)
              ·
                refine ⟨2743574453264266644316469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7316198542038044384843917 2743574453264266644316469)
                ·
                  refine ⟨257210104993524997904669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2743574453264266644316469 257210104993524997904669)
                  ·
                    rfl

theorem cell22_2254117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_2254117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254117 prefixEnd_2254117 := by exact prefixLift 2254117
  have htrace : WordTrace (prefixWord ++ tailWord_2254117) baseStart_2254117 baseEnd_2254117 := by
    simpa [prefixWord, tailWord_2254117, baseEnd_2254117] using wordTrace_append hprefix tailTrace_2254117
  have hstable : (prefixWord ++ tailWord_2254117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254117).length < 2 ^ (prefixWord ++ tailWord_2254117).sum := by decide
  have hdescent : baseEnd_2254117 < baseStart_2254117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254132 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2254132 : Nat := 118140960795 + 2254132 * 2 ^ 59
def prefixEnd_2254132 : Nat := 4983230072969 + 3 ^ 40 * 2254132 * 2
def baseEnd_2254132 : Nat := 771635449787119954588961

theorem tailTrace_2254132 : CollatzResearch.WordTrace tailWord_2254132 prefixEnd_2254132 771635449787119954588961 := by
  unfold tailWord_2254132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41107474134836106970638325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54809965513114809294184433 41107474134836106970638325)
  ·
    refine ⟨3853825700140885028497343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41107474134836106970638325 3853825700140885028497343)
    ·
      refine ⟨5780738550211327542746015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853825700140885028497343 5780738550211327542746015)
      ·
        refine ⟨8671107825316991314119023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780738550211327542746015 8671107825316991314119023)
        ·
          refine ⟨13006661737975486971178535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671107825316991314119023 13006661737975486971178535)
          ·
            refine ⟨19509992606963230456767803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13006661737975486971178535 19509992606963230456767803)
            ·
              refine ⟨29264988910444845685151705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19509992606963230456767803 29264988910444845685151705)
              ·
                refine ⟨21948741682833634263863779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29264988910444845685151705 21948741682833634263863779)
                ·
                  refine ⟨32923112524250451395795669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21948741682833634263863779 32923112524250451395795669)
                  ·
                    refine ⟨771635449787119954588961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32923112524250451395795669 771635449787119954588961)
                    ·
                      rfl

theorem cell22_2254132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2254132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254132 prefixEnd_2254132 := by exact prefixLift 2254132
  have htrace : WordTrace (prefixWord ++ tailWord_2254132) baseStart_2254132 baseEnd_2254132 := by
    simpa [prefixWord, tailWord_2254132, baseEnd_2254132] using wordTrace_append hprefix tailTrace_2254132
  have hstable : (prefixWord ++ tailWord_2254132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254132).length < 2 ^ (prefixWord ++ tailWord_2254132).sum := by decide
  have hdescent : baseEnd_2254132 < baseStart_2254132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254192 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_2254192 : Nat := 118140960795 + 2254192 * 2 ^ 59
def prefixEnd_2254192 : Nat := 4983230072969 + 3 ^ 40 * 2254192 * 2
def baseEnd_2254192 : Nat := 771655989013299798088777

theorem tailTrace_2254192 : CollatzResearch.WordTrace tailWord_2254192 prefixEnd_2254192 771655989013299798088777 := by
  unfold tailWord_2254192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41108568324727422094230415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54811424432969896125640553 41108568324727422094230415)
  ·
    refine ⟨61662852487091133141345623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41108568324727422094230415 61662852487091133141345623)
    ·
      refine ⟨92494278730636699712018435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61662852487091133141345623 92494278730636699712018435)
      ·
        refine ⟨138741418095955049568027653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92494278730636699712018435 138741418095955049568027653)
        ·
          refine ⟨26014015892991571794005185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138741418095955049568027653 26014015892991571794005185)
          ·
            refine ⟨19510511919743678845503889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26014015892991571794005185 19510511919743678845503889)
            ·
              refine ⟨14632883939807759134127917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19510511919743678845503889 14632883939807759134127917)
              ·
                refine ⟨5487331477427909675297969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14632883939807759134127917 5487331477427909675297969)
                ·
                  refine ⟨4115498608070932256473477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5487331477427909675297969 4115498608070932256473477)
                  ·
                    refine ⟨771655989013299798088777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115498608070932256473477 771655989013299798088777)
                    ·
                      rfl

theorem cell22_2254192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_2254192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254192 prefixEnd_2254192 := by exact prefixLift 2254192
  have htrace : WordTrace (prefixWord ++ tailWord_2254192) baseStart_2254192 baseEnd_2254192 := by
    simpa [prefixWord, tailWord_2254192, baseEnd_2254192] using wordTrace_append hprefix tailTrace_2254192
  have hstable : (prefixWord ++ tailWord_2254192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254192).length < 2 ^ (prefixWord ++ tailWord_2254192).sum := by decide
  have hdescent : baseEnd_2254192 < baseStart_2254192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254228 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2254228 : Nat := 118140960795 + 2254228 * 2 ^ 59
def prefixEnd_2254228 : Nat := 4983230072969 + 3 ^ 40 * 2254228 * 2
def baseEnd_2254228 : Nat := 771668312549007704188667

theorem tailTrace_2254228 : CollatzResearch.WordTrace tailWord_2254228 prefixEnd_2254228 771668312549007704188667 := by
  unfold tailWord_2254228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41109224838662211168385669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54812299784882948224514225 41109224838662211168385669)
  ·
    refine ⟨7707979657249164594072313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41109224838662211168385669 7707979657249164594072313)
    ·
      refine ⟨5780984742936873445554235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7707979657249164594072313 5780984742936873445554235)
      ·
        refine ⟨8671477114405310168331353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780984742936873445554235 8671477114405310168331353)
        ·
          refine ⟨6503607835803982626248515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8671477114405310168331353 6503607835803982626248515)
          ·
            refine ⟨9755411753705973939372773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6503607835803982626248515 9755411753705973939372773)
            ·
              refine ⟨1829139703819870113632395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9755411753705973939372773 1829139703819870113632395)
              ·
                refine ⟨2743709555729805170448593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829139703819870113632395 2743709555729805170448593)
                ·
                  refine ⟨2057782166797353877836445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2743709555729805170448593 2057782166797353877836445)
                  ·
                    refine ⟨771668312549007704188667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057782166797353877836445 771668312549007704188667)
                    ·
                      rfl

theorem cell22_2254228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2254228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254228 prefixEnd_2254228 := by exact prefixLift 2254228
  have htrace : WordTrace (prefixWord ++ tailWord_2254228) baseStart_2254228 baseEnd_2254228 := by
    simpa [prefixWord, tailWord_2254228, baseEnd_2254228] using wordTrace_append hprefix tailTrace_2254228
  have hstable : (prefixWord ++ tailWord_2254228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254228).length < 2 ^ (prefixWord ++ tailWord_2254228).sum := by decide
  have hdescent : baseEnd_2254228 < baseStart_2254228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254269 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2254269 : Nat := 118140960795 + 2254269 * 2 ^ 59
def prefixEnd_2254269 : Nat := 4983230072969 + 3 ^ 40 * 2254269 * 2
def baseEnd_2254269 : Nat := 257227449228965754637847

theorem tailTrace_2254269 : CollatzResearch.WordTrace tailWord_2254269 prefixEnd_2254269 257227449228965754637847 := by
  unfold tailWord_2254269
  simp only [CollatzResearch.WordTrace]
  refine ⟨82219945070175886339013861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54813296713450590892675907 82219945070175886339013861)
  ·
    refine ⟨15416239700657978688565099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82219945070175886339013861 15416239700657978688565099)
    ·
      refine ⟨23124359550986968032847649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15416239700657978688565099 23124359550986968032847649)
      ·
        refine ⟨17343269663240226024635737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23124359550986968032847649 17343269663240226024635737)
        ·
          refine ⟨13007452247430169518476803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17343269663240226024635737 13007452247430169518476803)
          ·
            refine ⟨19511178371145254277715205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13007452247430169518476803 19511178371145254277715205)
            ·
              refine ⟨3658345944589735177071601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19511178371145254277715205 3658345944589735177071601)
              ·
                refine ⟨2743759458442301382803701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658345944589735177071601 2743759458442301382803701)
                ·
                  refine ⟨257227449228965754637847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2743759458442301382803701 257227449228965754637847)
                  ·
                    rfl

theorem cell22_2254269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2254269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254269 prefixEnd_2254269 := by exact prefixLift 2254269
  have htrace : WordTrace (prefixWord ++ tailWord_2254269) baseStart_2254269 baseEnd_2254269 := by
    simpa [prefixWord, tailWord_2254269, baseEnd_2254269] using wordTrace_append hprefix tailTrace_2254269
  have hstable : (prefixWord ++ tailWord_2254269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254269).length < 2 ^ (prefixWord ++ tailWord_2254269).sum := by decide
  have hdescent : baseEnd_2254269 < baseStart_2254269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254284 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_2254284 : Nat := 118140960795 + 2254284 * 2 ^ 59
def prefixEnd_2254284 : Nat := 4983230072969 + 3 ^ 40 * 2254284 * 2
def baseEnd_2254284 : Nat := 771687482493442224788495

theorem tailTrace_2254284 : CollatzResearch.WordTrace tailWord_2254284 prefixEnd_2254284 771687482493442224788495 := by
  unfold tailWord_2254284
  simp only [CollatzResearch.WordTrace]
  refine ⟨41110246082560771950404953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54813661443414362600539937 41110246082560771950404953)
  ·
    refine ⟨30832684561920578962803715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41110246082560771950404953 30832684561920578962803715)
    ·
      refine ⟨46249026842880868444205573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30832684561920578962803715 46249026842880868444205573)
      ·
        refine ⟨8671692533040162833288545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46249026842880868444205573 8671692533040162833288545)
        ·
          refine ⟨6503769399780122124966409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8671692533040162833288545 6503769399780122124966409)
          ·
            refine ⟨4877827049835091593724807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503769399780122124966409 4877827049835091593724807)
            ·
              refine ⟨7316740574752637390587211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877827049835091593724807 7316740574752637390587211)
              ·
                refine ⟨10975110862128956085880817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316740574752637390587211 10975110862128956085880817)
                ·
                  refine ⟨8231333146596717064410613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10975110862128956085880817 8231333146596717064410613)
                  ·
                    refine ⟨771687482493442224788495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8231333146596717064410613 771687482493442224788495)
                    ·
                      rfl

theorem cell22_2254284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_2254284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254284 prefixEnd_2254284 := by exact prefixLift 2254284
  have htrace : WordTrace (prefixWord ++ tailWord_2254284) baseStart_2254284 baseEnd_2254284 := by
    simpa [prefixWord, tailWord_2254284, baseEnd_2254284] using wordTrace_append hprefix tailTrace_2254284
  have hstable : (prefixWord ++ tailWord_2254284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254284).length < 2 ^ (prefixWord ++ tailWord_2254284).sum := by decide
  have hdescent : baseEnd_2254284 < baseStart_2254284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254297 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 8]
def baseStart_2254297 : Nat := 118140960795 + 2254297 * 2 ^ 59
def prefixEnd_2254297 : Nat := 4983230072969 + 3 ^ 40 * 2254297 * 2
def baseEnd_2254297 : Nat := 257230644219704841404485

theorem tailTrace_2254297 : CollatzResearch.WordTrace tailWord_2254297 prefixEnd_2254297 257230644219704841404485 := by
  unfold tailWord_2254297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82220966314074447121033145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54813977542716298080688763 82220966314074447121033145)
  ·
    refine ⟨61665724735555835340774859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82220966314074447121033145 61665724735555835340774859)
    ·
      refine ⟨92498587103333753011162289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61665724735555835340774859 92498587103333753011162289)
      ·
        refine ⟨69373940327500314758371717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92498587103333753011162289 69373940327500314758371717)
        ·
          refine ⟨13007613811406309017194697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69373940327500314758371717 13007613811406309017194697)
          ·
            refine ⟨9755710358554731762896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007613811406309017194697 9755710358554731762896023)
            ·
              refine ⟨14633565537832097644344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9755710358554731762896023 14633565537832097644344035)
              ·
                refine ⟨21950348306748146466516053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14633565537832097644344035 21950348306748146466516053)
                ·
                  refine ⟨257230644219704841404485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21950348306748146466516053 257230644219704841404485)
                  ·
                    rfl

theorem cell22_2254297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_2254297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254297 prefixEnd_2254297 := by exact prefixLift 2254297
  have htrace : WordTrace (prefixWord ++ tailWord_2254297) baseStart_2254297 baseEnd_2254297 := by
    simpa [prefixWord, tailWord_2254297, baseEnd_2254297] using wordTrace_append hprefix tailTrace_2254297
  have hstable : (prefixWord ++ tailWord_2254297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254297).length < 2 ^ (prefixWord ++ tailWord_2254297).sum := by decide
  have hdescent : baseEnd_2254297 < baseStart_2254297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254346 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_2254346 : Nat := 118140960795 + 2254346 * 2 ^ 59
def prefixEnd_2254346 : Nat := 4983230072969 + 3 ^ 40 * 2254346 * 2
def baseEnd_2254346 : Nat := 771708706360494729738305

theorem tailTrace_2254346 : CollatzResearch.WordTrace tailWord_2254346 prefixEnd_2254346 771708706360494729738305 := by
  unfold tailWord_2254346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20555688372724232122391723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54815168993931285659711261 20555688372724232122391723)
  ·
    refine ⟨30833532559086348183587585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20555688372724232122391723 30833532559086348183587585)
    ·
      refine ⟨23125149419314761137690689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30833532559086348183587585 23125149419314761137690689)
      ·
        refine ⟨17343862064486070853268017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23125149419314761137690689 17343862064486070853268017)
        ·
          refine ⟨13007896548364553139951013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17343862064486070853268017 13007896548364553139951013)
          ·
            refine ⟨2438980602818353713740815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13007896548364553139951013 2438980602818353713740815)
            ·
              refine ⟨3658470904227530570611223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438980602818353713740815 3658470904227530570611223)
              ·
                refine ⟨5487706356341295855916835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658470904227530570611223 5487706356341295855916835)
                ·
                  refine ⟨8231559534511943783875253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487706356341295855916835 8231559534511943783875253)
                  ·
                    refine ⟨771708706360494729738305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8231559534511943783875253 771708706360494729738305)
                    ·
                      rfl

theorem cell22_2254346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_2254346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254346 prefixEnd_2254346 := by exact prefixLift 2254346
  have htrace : WordTrace (prefixWord ++ tailWord_2254346) baseStart_2254346 baseEnd_2254346 := by
    simpa [prefixWord, tailWord_2254346, baseEnd_2254346] using wordTrace_append hprefix tailTrace_2254346
  have hstable : (prefixWord ++ tailWord_2254346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254346).length < 2 ^ (prefixWord ++ tailWord_2254346).sum := by decide
  have hdescent : baseEnd_2254346 < baseStart_2254346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254376 : List Nat := [2, 1, 5, 2, 2, 2, 8]
def baseStart_2254376 : Nat := 118140960795 + 2254376 * 2 ^ 59
def prefixEnd_2254376 : Nat := 4983230072969 + 3 ^ 40 * 2254376 * 2
def baseEnd_2254376 : Nat := 28582184295317950055119

theorem tailTrace_2254376 : CollatzResearch.WordTrace tailWord_2254376 prefixEnd_2254376 28582184295317950055119 := by
  unfold tailWord_2254376
  simp only [CollatzResearch.WordTrace]
  refine ⟨41111923840394121806579491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54815898453858829075439321 41111923840394121806579491)
  ·
    refine ⟨61667885760591182709869237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41111923840394121806579491 61667885760591182709869237)
    ·
      refine ⟨5781364290055423379050241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61667885760591182709869237 5781364290055423379050241)
      ·
        refine ⟨4336023217541567534287681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5781364290055423379050241 4336023217541567534287681)
        ·
          refine ⟨3252017413156175650715761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336023217541567534287681 3252017413156175650715761)
          ·
            refine ⟨2439013059867131738036821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252017413156175650715761 2439013059867131738036821)
            ·
              refine ⟨28582184295317950055119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2439013059867131738036821 28582184295317950055119)
              ·
                rfl

theorem cell22_2254376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 8].length) (baseStart_2254376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254376 prefixEnd_2254376 := by exact prefixLift 2254376
  have htrace : WordTrace (prefixWord ++ tailWord_2254376) baseStart_2254376 baseEnd_2254376 := by
    simpa [prefixWord, tailWord_2254376, baseEnd_2254376] using wordTrace_append hprefix tailTrace_2254376
  have hstable : (prefixWord ++ tailWord_2254376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254376).length < 2 ^ (prefixWord ++ tailWord_2254376).sum := by decide
  have hdescent : baseEnd_2254376 < baseStart_2254376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254391 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 3, 3]
def baseStart_2254391 : Nat := 118140960795 + 2254391 * 2 ^ 59
def prefixEnd_2254391 : Nat := 4983230072969 + 3 ^ 40 * 2254391 * 2
def baseEnd_2254391 : Nat := 771724110780129612363167

theorem tailTrace_2254391 : CollatzResearch.WordTrace tailWord_2254391 prefixEnd_2254391 771724110780129612363167 := by
  unfold tailWord_2254391
  simp only [CollatzResearch.WordTrace]
  refine ⟨82224394775733901174955027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54816263183822600783303351 82224394775733901174955027)
  ·
    refine ⟨123336592163600851762432541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82224394775733901174955027 123336592163600851762432541)
    ·
      refine ⟨46251222061350319410912203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123336592163600851762432541 46251222061350319410912203)
      ·
        refine ⟨69376833092025479116368305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46251222061350319410912203 69376833092025479116368305)
        ·
          refine ⟨52032624819019109337276229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69376833092025479116368305 52032624819019109337276229)
          ·
            refine ⟨9756117153566083000739293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52032624819019109337276229 9756117153566083000739293)
            ·
              refine ⟨3658543932587281125277235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9756117153566083000739293 3658543932587281125277235)
              ·
                refine ⟨5487815898880921687915853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658543932587281125277235 5487815898880921687915853)
                ·
                  refine ⟨2057930962080345632968445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5487815898880921687915853 2057930962080345632968445)
                  ·
                    refine ⟨771724110780129612363167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057930962080345632968445 771724110780129612363167)
                    ·
                      rfl

theorem cell22_2254391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_2254391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254391 prefixEnd_2254391 := by exact prefixLift 2254391
  have htrace : WordTrace (prefixWord ++ tailWord_2254391) baseStart_2254391 baseEnd_2254391 := by
    simpa [prefixWord, tailWord_2254391, baseEnd_2254391] using wordTrace_append hprefix tailTrace_2254391
  have hstable : (prefixWord ++ tailWord_2254391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254391).length < 2 ^ (prefixWord ++ tailWord_2254391).sum := by decide
  have hdescent : baseEnd_2254391 < baseStart_2254391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254397 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_2254397 : Nat := 118140960795 + 2254397 * 2 ^ 59
def prefixEnd_2254397 : Nat := 4983230072969 + 3 ^ 40 * 2254397 * 2
def baseEnd_2254397 : Nat := 771726164702747596713149

theorem tailTrace_2254397 : CollatzResearch.WordTrace tailWord_2254397 prefixEnd_2254397 771726164702747596713149 := by
  unfold tailWord_2254397
  simp only [CollatzResearch.WordTrace]
  refine ⟨82224613613712164199673445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54816409075808109466448963 82224613613712164199673445)
  ·
    refine ⟨15417115052571030787438771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82224613613712164199673445 15417115052571030787438771)
    ·
      refine ⟨23125672578856546181158157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15417115052571030787438771 23125672578856546181158157)
      ·
        refine ⟨8672127217071204817934309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23125672578856546181158157 8672127217071204817934309)
        ·
          refine ⟨1626023853200850903362683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8672127217071204817934309 1626023853200850903362683)
          ·
            refine ⟨2439035779801276355044025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626023853200850903362683 2439035779801276355044025)
            ·
              refine ⟨1829276834850957266283019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439035779801276355044025 1829276834850957266283019)
              ·
                refine ⟨2743915252276435899424529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829276834850957266283019 2743915252276435899424529)
                ·
                  refine ⟨2057936439207326924568397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2743915252276435899424529 2057936439207326924568397)
                  ·
                    refine ⟨771726164702747596713149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057936439207326924568397 771726164702747596713149)
                    ·
                      rfl

theorem cell22_2254397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_2254397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254397 prefixEnd_2254397 := by exact prefixLift 2254397
  have htrace : WordTrace (prefixWord ++ tailWord_2254397) baseStart_2254397 baseEnd_2254397 := by
    simpa [prefixWord, tailWord_2254397, baseEnd_2254397] using wordTrace_append hprefix tailTrace_2254397
  have hstable : (prefixWord ++ tailWord_2254397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254397).length < 2 ^ (prefixWord ++ tailWord_2254397).sum := by decide
  have hdescent : baseEnd_2254397 < baseStart_2254397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254442 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2254442 : Nat := 118140960795 + 2254442 * 2 ^ 59
def prefixEnd_2254442 : Nat := 4983230072969 + 3 ^ 40 * 2254442 * 2
def baseEnd_2254442 : Nat := 771741569122382479338011

theorem tailTrace_2254442 : CollatzResearch.WordTrace tailWord_2254442 prefixEnd_2254442 771741569122382479338011 := by
  unfold tailWord_2254442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20556563724637284221265395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54817503265699424590041053 20556563724637284221265395)
  ·
    refine ⟨30834845586955926331898093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20556563724637284221265395 30834845586955926331898093)
    ·
      refine ⟨11563067095108472374461785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30834845586955926331898093 11563067095108472374461785)
      ·
        refine ⟨8672300321331354280846339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11563067095108472374461785 8672300321331354280846339)
        ·
          refine ⟨13008450481997031421269509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672300321331354280846339 13008450481997031421269509)
          ·
            refine ⟨2439084465374443391488033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13008450481997031421269509 2439084465374443391488033)
            ·
              refine ⟨1829313349030832543616025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439084465374443391488033 1829313349030832543616025)
              ·
                refine ⟨1371985011773124407712019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829313349030832543616025 1371985011773124407712019)
                ·
                  refine ⟨2057977517659686611568029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371985011773124407712019 2057977517659686611568029)
                  ·
                    refine ⟨771741569122382479338011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057977517659686611568029 771741569122382479338011)
                    ·
                      rfl

theorem cell22_2254442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2254442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254442 prefixEnd_2254442 := by exact prefixLift 2254442
  have htrace : WordTrace (prefixWord ++ tailWord_2254442) baseStart_2254442 baseEnd_2254442 := by
    simpa [prefixWord, tailWord_2254442, baseEnd_2254442] using wordTrace_append hprefix tailTrace_2254442
  have hstable : (prefixWord ++ tailWord_2254442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254442).length < 2 ^ (prefixWord ++ tailWord_2254442).sum := by decide
  have hdescent : baseEnd_2254442 < baseStart_2254442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254534 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2254534 : Nat := 118140960795 + 2254534 * 2 ^ 59
def prefixEnd_2254534 : Nat := 4983230072969 + 3 ^ 40 * 2254534 * 2
def baseEnd_2254534 : Nat := 257257687534174968679243

theorem tailTrace_2254534 : CollatzResearch.WordTrace tailWord_2254534 prefixEnd_2254534 257257687534174968679243 := by
  unfold tailWord_2254534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569675325444244893669083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54819740276143891064940437 2569675325444244893669083)
  ·
    refine ⟨3854512988166367340503625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569675325444244893669083 3854512988166367340503625)
    ·
      refine ⟨2890884741124775505377719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854512988166367340503625 2890884741124775505377719)
      ·
        refine ⟨4336327111687163258066579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890884741124775505377719 4336327111687163258066579)
        ·
          refine ⟨6504490667530744887099869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4336327111687163258066579 6504490667530744887099869)
          ·
            refine ⟨2439184000324029332662451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6504490667530744887099869 2439184000324029332662451)
            ·
              refine ⟨3658776000486043998993677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439184000324029332662451 3658776000486043998993677)
              ·
                refine ⟨1372041000182266499622629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658776000486043998993677 1372041000182266499622629)
                ·
                  refine ⟨257257687534174968679243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372041000182266499622629 257257687534174968679243)
                  ·
                    rfl

theorem cell22_2254534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2254534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254534 prefixEnd_2254534 := by exact prefixLift 2254534
  have htrace : WordTrace (prefixWord ++ tailWord_2254534) baseStart_2254534 baseEnd_2254534 := by
    simpa [prefixWord, tailWord_2254534, baseEnd_2254534] using wordTrace_append hprefix tailTrace_2254534
  have hstable : (prefixWord ++ tailWord_2254534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254534).length < 2 ^ (prefixWord ++ tailWord_2254534).sum := by decide
  have hdescent : baseEnd_2254534 < baseStart_2254534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254569 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_2254569 : Nat := 118140960795 + 2254569 * 2 ^ 59
def prefixEnd_2254569 : Nat := 4983230072969 + 3 ^ 40 * 2254569 * 2
def baseEnd_2254569 : Nat := 771785043817796481412621

theorem tailTrace_2254569 : CollatzResearch.WordTrace tailWord_2254569 prefixEnd_2254569 771785043817796481412621 := by
  unfold tailWord_2254569
  simp only [CollatzResearch.WordTrace]
  refine ⟨82230886969089037574934761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54820591312726025049956507 82230886969089037574934761)
  ·
    refine ⟨61673165226816778181201071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82230886969089037574934761 61673165226816778181201071)
    ·
      refine ⟨92509747840225167271801607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61673165226816778181201071 92509747840225167271801607)
      ·
        refine ⟨138764621760337750907702411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92509747840225167271801607 138764621760337750907702411)
        ·
          refine ⟨208146932640506626361553617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138764621760337750907702411 208146932640506626361553617)
          ·
            refine ⟨156110199480379969771165213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208146932640506626361553617 156110199480379969771165213)
            ·
              refine ⟨58541324805142488664186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156110199480379969771165213 58541324805142488664186955)
              ·
                refine ⟨87811987207713732996280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58541324805142488664186955 87811987207713732996280433)
                ·
                  refine ⟨65858990405785299747210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87811987207713732996280433 65858990405785299747210325)
                  ·
                    refine ⟨771785043817796481412621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65858990405785299747210325 771785043817796481412621)
                    ·
                      rfl

theorem cell22_2254569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_2254569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254569 prefixEnd_2254569 := by exact prefixLift 2254569
  have htrace : WordTrace (prefixWord ++ tailWord_2254569) baseStart_2254569 baseEnd_2254569 := by
    simpa [prefixWord, tailWord_2254569, baseEnd_2254569] using wordTrace_append hprefix tailTrace_2254569
  have hstable : (prefixWord ++ tailWord_2254569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254569).length < 2 ^ (prefixWord ++ tailWord_2254569).sum := by decide
  have hdescent : baseEnd_2254569 < baseStart_2254569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254573 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2254573 : Nat := 118140960795 + 2254573 * 2 ^ 59
def prefixEnd_2254573 : Nat := 4983230072969 + 3 ^ 40 * 2254573 * 2
def baseEnd_2254573 : Nat := 257262137699847268104203

theorem tailTrace_2254573 : CollatzResearch.WordTrace tailWord_2254573 prefixEnd_2254573 257262137699847268104203 := by
  unfold tailWord_2254573
  simp only [CollatzResearch.WordTrace]
  refine ⟨82231032861074546258080373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54820688574049697505386915 82231032861074546258080373)
  ·
    refine ⟨7709159330725738711695035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82231032861074546258080373 7709159330725738711695035)
    ·
      refine ⟨11563738996088608067542553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7709159330725738711695035 11563738996088608067542553)
      ·
        refine ⟨8672804247066456050656915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11563738996088608067542553 8672804247066456050656915)
        ·
          refine ⟨13009206370599684075985373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672804247066456050656915 13009206370599684075985373)
          ·
            refine ⟨4878452388974881528494515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13009206370599684075985373 4878452388974881528494515)
            ·
              refine ⟨7317678583462322292741773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878452388974881528494515 7317678583462322292741773)
              ·
                refine ⟨2744129468798370859778165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7317678583462322292741773 2744129468798370859778165)
                ·
                  refine ⟨257262137699847268104203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2744129468798370859778165 257262137699847268104203)
                  ·
                    rfl

theorem cell22_2254573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2254573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254573 prefixEnd_2254573 := by exact prefixLift 2254573
  have htrace : WordTrace (prefixWord ++ tailWord_2254573) baseStart_2254573 baseEnd_2254573 := by
    simpa [prefixWord, tailWord_2254573, baseEnd_2254573] using wordTrace_append hprefix tailTrace_2254573
  have hstable : (prefixWord ++ tailWord_2254573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254573).length < 2 ^ (prefixWord ++ tailWord_2254573).sum := by decide
  have hdescent : baseEnd_2254573 < baseStart_2254573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254622 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2254622 : Nat := 118140960795 + 2254622 * 2 ^ 59
def prefixEnd_2254622 : Nat := 4983230072969 + 3 ^ 40 * 2254622 * 2
def baseEnd_2254622 : Nat := 771803186800922009837459

theorem tailTrace_2254622 : CollatzResearch.WordTrace tailWord_2254622 prefixEnd_2254622 771803186800922009837459 := by
  unfold tailWord_2254622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10279102504737128453326765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54821880025264685084409413 10279102504737128453326765)
  ·
    refine ⟨3854663439276423169997537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10279102504737128453326765 3854663439276423169997537)
    ·
      refine ⟨2890997579457317377498153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854663439276423169997537 2890997579457317377498153)
      ·
        refine ⟨2168248184592988033123615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890997579457317377498153 2168248184592988033123615)
        ·
          refine ⟨3252372276889482049685423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168248184592988033123615 3252372276889482049685423)
          ·
            refine ⟨4878558415334223074528135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252372276889482049685423 4878558415334223074528135)
            ·
              refine ⟨7317837623001334611792203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878558415334223074528135 7317837623001334611792203)
              ·
                refine ⟨10976756434502001917688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7317837623001334611792203 10976756434502001917688305)
                ·
                  refine ⟨8232567325876501438266229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10976756434502001917688305 8232567325876501438266229)
                  ·
                    refine ⟨771803186800922009837459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8232567325876501438266229 771803186800922009837459)
                    ·
                      rfl

theorem cell22_2254622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2254622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254622 prefixEnd_2254622 := by exact prefixLift 2254622
  have htrace : WordTrace (prefixWord ++ tailWord_2254622) baseStart_2254622 baseEnd_2254622 := by
    simpa [prefixWord, tailWord_2254622, baseEnd_2254622] using wordTrace_append hprefix tailTrace_2254622
  have hstable : (prefixWord ++ tailWord_2254622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254622).length < 2 ^ (prefixWord ++ tailWord_2254622).sum := by decide
  have hdescent : baseEnd_2254622 < baseStart_2254622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254648 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_2254648 : Nat := 118140960795 + 2254648 * 2 ^ 59
def prefixEnd_2254648 : Nat := 4983230072969 + 3 ^ 40 * 2254648 * 2
def baseEnd_2254648 : Nat := 771812087132266608687379

theorem tailTrace_2254648 : CollatzResearch.WordTrace tailWord_2254648 prefixEnd_2254648 771812087132266608687379 := by
  unfold tailWord_2254648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116884167901417033530299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54822512223868556044707065 41116884167901417033530299)
  ·
    refine ⟨61675326251852125550295449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41116884167901417033530299 61675326251852125550295449)
    ·
      refine ⟨46256494688889094162721587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61675326251852125550295449 46256494688889094162721587)
      ·
        refine ⟨69384742033333641244082381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46256494688889094162721587 69384742033333641244082381)
        ·
          refine ⟨26019278262500115466530893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69384742033333641244082381 26019278262500115466530893)
          ·
            refine ⟨9757229348437543299949085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26019278262500115466530893 9757229348437543299949085)
            ·
              refine ⟨3658961005664078737480907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9757229348437543299949085 3658961005664078737480907)
              ·
                refine ⟨5488441508496118106221361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658961005664078737480907 5488441508496118106221361)
                ·
                  refine ⟨4116331131372088579666021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488441508496118106221361 4116331131372088579666021)
                  ·
                    refine ⟨771812087132266608687379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116331131372088579666021 771812087132266608687379)
                    ·
                      rfl

theorem cell22_2254648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_2254648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254648 prefixEnd_2254648 := by exact prefixLift 2254648
  have htrace : WordTrace (prefixWord ++ tailWord_2254648) baseStart_2254648 baseEnd_2254648 := by
    simpa [prefixWord, tailWord_2254648, baseEnd_2254648] using wordTrace_append hprefix tailTrace_2254648
  have hstable : (prefixWord ++ tailWord_2254648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254648).length < 2 ^ (prefixWord ++ tailWord_2254648).sum := by decide
  have hdescent : baseEnd_2254648 < baseStart_2254648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254684 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2254684 : Nat := 118140960795 + 2254684 * 2 ^ 59
def prefixEnd_2254684 : Nat := 4983230072969 + 3 ^ 40 * 2254684 * 2
def baseEnd_2254684 : Nat := 771824410667974514787269

theorem tailTrace_2254684 : CollatzResearch.WordTrace tailWord_2254684 prefixEnd_2254684 771824410667974514787269 := by
  unfold tailWord_2254684
  simp only [CollatzResearch.WordTrace]
  refine ⟨41117540681836206107685553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54823387575781608143580737 41117540681836206107685553)
  ·
    refine ⟨30838155511377154580764165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41117540681836206107685553 30838155511377154580764165)
    ·
      refine ⟨5782154158383216483893281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30838155511377154580764165 5782154158383216483893281)
      ·
        refine ⟨4336615618787412362919961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5782154158383216483893281 4336615618787412362919961)
        ·
          refine ⟨3252461714090559272189971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336615618787412362919961 3252461714090559272189971)
          ·
            refine ⟨4878692571135838908284957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252461714090559272189971 4878692571135838908284957)
            ·
              refine ⟨1829509714175939590606859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4878692571135838908284957 1829509714175939590606859)
              ·
                refine ⟨2744264571263909385910289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829509714175939590606859 2744264571263909385910289)
                ·
                  refine ⟨2058198428447932039432717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2744264571263909385910289 2058198428447932039432717)
                  ·
                    refine ⟨771824410667974514787269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058198428447932039432717 771824410667974514787269)
                    ·
                      rfl

theorem cell22_2254684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2254684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254684 prefixEnd_2254684 := by exact prefixLift 2254684
  have htrace : WordTrace (prefixWord ++ tailWord_2254684) baseStart_2254684 baseEnd_2254684 := by
    simpa [prefixWord, tailWord_2254684, baseEnd_2254684] using wordTrace_append hprefix tailTrace_2254684
  have hstable : (prefixWord ++ tailWord_2254684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254684).length < 2 ^ (prefixWord ++ tailWord_2254684).sum := by decide
  have hdescent : baseEnd_2254684 < baseStart_2254684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254783 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_2254783 : Nat := 118140960795 + 2254783 * 2 ^ 59
def prefixEnd_2254783 : Nat := 4983230072969 + 3 ^ 40 * 2254783 * 2
def baseEnd_2254783 : Nat := 771858300391171256561965

theorem tailTrace_2254783 : CollatzResearch.WordTrace tailWord_2254783 prefixEnd_2254783 771858300391171256561965 := by
  unfold tailWord_2254783
  simp only [CollatzResearch.WordTrace]
  refine ⟨82238692190313752123225003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54825794793542501415483335 82238692190313752123225003)
  ·
    refine ⟨123358038285470628184837505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82238692190313752123225003 123358038285470628184837505)
    ·
      refine ⟨92518528714102971138628129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123358038285470628184837505 92518528714102971138628129)
      ·
        refine ⟨69388896535577228353971097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92518528714102971138628129 69388896535577228353971097)
        ·
          refine ⟨52041672401682921265478323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69388896535577228353971097 52041672401682921265478323)
          ·
            refine ⟨78062508602524381898217485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52041672401682921265478323 78062508602524381898217485)
            ·
              refine ⟨29273440725946643211831557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78062508602524381898217485 29273440725946643211831557)
              ·
                refine ⟨5488770136114995602218417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29273440725946643211831557 5488770136114995602218417)
                ·
                  refine ⟨4116577602086246701663813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488770136114995602218417 4116577602086246701663813)
                  ·
                    refine ⟨771858300391171256561965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116577602086246701663813 771858300391171256561965)
                    ·
                      rfl

theorem cell22_2254783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_2254783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254783 prefixEnd_2254783 := by exact prefixLift 2254783
  have htrace : WordTrace (prefixWord ++ tailWord_2254783) baseStart_2254783 baseEnd_2254783 := by
    simpa [prefixWord, tailWord_2254783, baseEnd_2254783] using wordTrace_append hprefix tailTrace_2254783
  have hstable : (prefixWord ++ tailWord_2254783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254783).length < 2 ^ (prefixWord ++ tailWord_2254783).sum := by decide
  have hdescent : baseEnd_2254783 < baseStart_2254783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254802 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2254802 : Nat := 118140960795 + 2254802 * 2 ^ 59
def prefixEnd_2254802 : Nat := 4983230072969 + 3 ^ 40 * 2254802 * 2
def baseEnd_2254802 : Nat := 771864804479461540336907

theorem tailTrace_2254802 : CollatzResearch.WordTrace tailWord_2254802 prefixEnd_2254802 771864804479461540336907 := by
  unfold tailWord_2254802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20559846294311229592041665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54826256784829945578777773 20559846294311229592041665)
  ·
    refine ⟨15419884720733422194031249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20559846294311229592041665 15419884720733422194031249)
    ·
      refine ⟨11564913540550066645523437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15419884720733422194031249 11564913540550066645523437)
      ·
        refine ⟨4336842577706274992071289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11564913540550066645523437 4336842577706274992071289)
        ·
          refine ⟨3252631933279706244053467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336842577706274992071289 3252631933279706244053467)
          ·
            refine ⟨4878947899919559366080201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252631933279706244053467 4878947899919559366080201)
            ·
              refine ⟨3659210924939669524560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4878947899919559366080201 3659210924939669524560151)
              ·
                refine ⟨5488816387409504286840227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659210924939669524560151 5488816387409504286840227)
                ·
                  refine ⟨8233224581114256430260341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5488816387409504286840227 8233224581114256430260341)
                  ·
                    refine ⟨771864804479461540336907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8233224581114256430260341 771864804479461540336907)
                    ·
                      rfl

theorem cell22_2254802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2254802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254802 prefixEnd_2254802 := by exact prefixLift 2254802
  have htrace : WordTrace (prefixWord ++ tailWord_2254802) baseStart_2254802 baseEnd_2254802 := by
    simpa [prefixWord, tailWord_2254802, baseEnd_2254802] using wordTrace_append hprefix tailTrace_2254802
  have hstable : (prefixWord ++ tailWord_2254802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254802).length < 2 ^ (prefixWord ++ tailWord_2254802).sum := by decide
  have hdescent : baseEnd_2254802 < baseStart_2254802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254815 : List Nat := [1, 1, 2, 3, 4, 2, 3, 6]
def baseStart_2254815 : Nat := 118140960795 + 2254815 * 2 ^ 59
def prefixEnd_2254815 : Nat := 4983230072969 + 3 ^ 40 * 2254815 * 2
def baseEnd_2254815 : Nat := 85763250516125982195763

theorem tailTrace_2254815 : CollatzResearch.WordTrace tailWord_2254815 prefixEnd_2254815 85763250516125982195763 := by
  unfold tailWord_2254815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82239859326197821588389899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54826572884131881058926599 82239859326197821588389899)
  ·
    refine ⟨123359788989296732382584849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82239859326197821588389899 123359788989296732382584849)
    ·
      refine ⟨92519841741972549286938637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123359788989296732382584849 92519841741972549286938637)
      ·
        refine ⟨34694940653239705982601989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92519841741972549286938637 34694940653239705982601989)
        ·
          refine ⟨6505301372482444871737873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34694940653239705982601989 6505301372482444871737873)
          ·
            refine ⟨4878976029361833653803405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505301372482444871737873 4878976029361833653803405)
            ·
              refine ⟨1829616011010687620176277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4878976029361833653803405 1829616011010687620176277)
              ·
                refine ⟨85763250516125982195763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1829616011010687620176277 85763250516125982195763)
                ·
                  rfl

theorem cell22_2254815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 6].length) (baseStart_2254815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254815 prefixEnd_2254815 := by exact prefixLift 2254815
  have htrace : WordTrace (prefixWord ++ tailWord_2254815) baseStart_2254815 baseEnd_2254815 := by
    simpa [prefixWord, tailWord_2254815, baseEnd_2254815] using wordTrace_append hprefix tailTrace_2254815
  have hstable : (prefixWord ++ tailWord_2254815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254815).length < 2 ^ (prefixWord ++ tailWord_2254815).sum := by decide
  have hdescent : baseEnd_2254815 < baseStart_2254815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254881 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2254881 : Nat := 118140960795 + 2254881 * 2 ^ 59
def prefixEnd_2254881 : Nat := 4983230072969 + 3 ^ 40 * 2254881 * 2
def baseEnd_2254881 : Nat := 771891847793931667611665

theorem tailTrace_2254881 : CollatzResearch.WordTrace tailWord_2254881 prefixEnd_2254881 771891847793931667611665 := by
  unfold tailWord_2254881
  simp only [CollatzResearch.WordTrace]
  refine ⟨82242266543958714860292497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54828177695972476573528331 82242266543958714860292497)
  ·
    refine ⟨61681699907969036145219373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82242266543958714860292497 61681699907969036145219373)
    ·
      refine ⟨23130637465488388554457265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61681699907969036145219373 23130637465488388554457265)
      ·
        refine ⟨17347978099116291415842949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23130637465488388554457265 17347978099116291415842949)
        ·
          refine ⟨3252745893584304640470553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17347978099116291415842949 3252745893584304640470553)
          ·
            refine ⟨2439559420188228480352915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252745893584304640470553 2439559420188228480352915)
            ·
              refine ⟨3659339130282342720529373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439559420188228480352915 3659339130282342720529373)
              ·
                refine ⟨1372252173855878520198515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3659339130282342720529373 1372252173855878520198515)
                ·
                  refine ⟨2058378260783817780297773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372252173855878520198515 2058378260783817780297773)
                  ·
                    refine ⟨771891847793931667611665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058378260783817780297773 771891847793931667611665)
                    ·
                      rfl

theorem cell22_2254881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2254881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254881 prefixEnd_2254881 := by exact prefixLift 2254881
  have htrace : WordTrace (prefixWord ++ tailWord_2254881) baseStart_2254881 baseEnd_2254881 := by
    simpa [prefixWord, tailWord_2254881, baseEnd_2254881] using wordTrace_append hprefix tailTrace_2254881
  have hstable : (prefixWord ++ tailWord_2254881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254881).length < 2 ^ (prefixWord ++ tailWord_2254881).sum := by decide
  have hdescent : baseEnd_2254881 < baseStart_2254881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254920 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2254920 : Nat := 118140960795 + 2254920 * 2 ^ 59
def prefixEnd_2254920 : Nat := 4983230072969 + 3 ^ 40 * 2254920 * 2
def baseEnd_2254920 : Nat := 771905198290948565886545

theorem tailTrace_2254920 : CollatzResearch.WordTrace tailWord_2254920 prefixEnd_2254920 771905198290948565886545 := by
  unfold tailWord_2254920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41121844495408712260481107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54829125993878283013974809 41121844495408712260481107)
  ·
    refine ⟨61682766743113068390721661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41121844495408712260481107 61682766743113068390721661)
    ·
      refine ⟨23131037528667400646520623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61682766743113068390721661 23131037528667400646520623)
      ·
        refine ⟨34696556293001100969780935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23131037528667400646520623 34696556293001100969780935)
        ·
          refine ⟨52044834439501651454671403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34696556293001100969780935 52044834439501651454671403)
          ·
            refine ⟨78067251659252477182007105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52044834439501651454671403 78067251659252477182007105)
            ·
              refine ⟨58550438744439357886505329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78067251659252477182007105 58550438744439357886505329)
              ·
                refine ⟨43912829058329518414878997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58550438744439357886505329 43912829058329518414878997)
                ·
                  refine ⟨2058413862109196175697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43912829058329518414878997 2058413862109196175697453)
                  ·
                    refine ⟨771905198290948565886545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058413862109196175697453 771905198290948565886545)
                    ·
                      rfl

theorem cell22_2254920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2254920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254920 prefixEnd_2254920 := by exact prefixLift 2254920
  have htrace : WordTrace (prefixWord ++ tailWord_2254920) baseStart_2254920 baseEnd_2254920 := by
    simpa [prefixWord, tailWord_2254920, baseEnd_2254920] using wordTrace_append hprefix tailTrace_2254920
  have hstable : (prefixWord ++ tailWord_2254920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254920).length < 2 ^ (prefixWord ++ tailWord_2254920).sum := by decide
  have hdescent : baseEnd_2254920 < baseStart_2254920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254935 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2254935 : Nat := 118140960795 + 2254935 * 2 ^ 59
def prefixEnd_2254935 : Nat := 4983230072969 + 3 ^ 40 * 2254935 * 2
def baseEnd_2254935 : Nat := 771910333097493526761499

theorem tailTrace_2254935 : CollatzResearch.WordTrace tailWord_2254935 prefixEnd_2254935 771910333097493526761499 := by
  unfold tailWord_2254935
  simp only [CollatzResearch.WordTrace]
  refine ⟨82244236085763082082758259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54829490723842054721838839 82244236085763082082758259)
  ·
    refine ⟨123366354128644623124137389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82244236085763082082758259 123366354128644623124137389)
    ·
      refine ⟨46262382798241733671551521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123366354128644623124137389 46262382798241733671551521)
      ·
        refine ⟨34696787098681300253663641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46262382798241733671551521 34696787098681300253663641)
        ·
          refine ⟨26022590324010975190247731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34696787098681300253663641 26022590324010975190247731)
          ·
            refine ⟨39033885486016462785371597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26022590324010975190247731 39033885486016462785371597)
            ·
              refine ⟨14637707057256173544514349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39033885486016462785371597 14637707057256173544514349)
              ·
                refine ⟨5489140146471065079192881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14637707057256173544514349 5489140146471065079192881)
                ·
                  refine ⟨4116855109853298809394661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5489140146471065079192881 4116855109853298809394661)
                  ·
                    refine ⟨771910333097493526761499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116855109853298809394661 771910333097493526761499)
                    ·
                      rfl

theorem cell22_2254935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2254935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254935 prefixEnd_2254935 := by exact prefixLift 2254935
  have htrace : WordTrace (prefixWord ++ tailWord_2254935) baseStart_2254935 baseEnd_2254935 := by
    simpa [prefixWord, tailWord_2254935, baseEnd_2254935] using wordTrace_append hprefix tailTrace_2254935
  have hstable : (prefixWord ++ tailWord_2254935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254935).length < 2 ^ (prefixWord ++ tailWord_2254935).sum := by decide
  have hdescent : baseEnd_2254935 < baseStart_2254935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254941 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2254941 : Nat := 118140960795 + 2254941 * 2 ^ 59
def prefixEnd_2254941 : Nat := 4983230072969 + 3 ^ 40 * 2254941 * 2
def baseEnd_2254941 : Nat := 771912387020111511111481

theorem tailTrace_2254941 : CollatzResearch.WordTrace tailWord_2254941 prefixEnd_2254941 771912387020111511111481 := by
  unfold tailWord_2254941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82244454923741345107476677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54829636615827563404984451 82244454923741345107476677)
  ·
    refine ⟨15420835298201502207651877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82244454923741345107476677 15420835298201502207651877)
    ·
      refine ⟨2891406618412781663934727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15420835298201502207651877 2891406618412781663934727)
      ·
        refine ⟨4337109927619172495902091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891406618412781663934727 4337109927619172495902091)
        ·
          refine ⟨6505664891428758743853137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337109927619172495902091 6505664891428758743853137)
          ·
            refine ⟨4879248668571569057889853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505664891428758743853137 4879248668571569057889853)
            ·
              refine ⟨1829718250714338396708695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4879248668571569057889853 1829718250714338396708695)
              ·
                refine ⟨2744577376071507595063043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829718250714338396708695 2744577376071507595063043)
                ·
                  refine ⟨4116866064107261392594565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744577376071507595063043 4116866064107261392594565)
                  ·
                    refine ⟨771912387020111511111481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116866064107261392594565 771912387020111511111481)
                    ·
                      rfl

theorem cell22_2254941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2254941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254941 prefixEnd_2254941 := by exact prefixLift 2254941
  have htrace : WordTrace (prefixWord ++ tailWord_2254941) baseStart_2254941 baseEnd_2254941 := by
    simpa [prefixWord, tailWord_2254941, baseEnd_2254941] using wordTrace_append hprefix tailTrace_2254941
  have hstable : (prefixWord ++ tailWord_2254941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254941).length < 2 ^ (prefixWord ++ tailWord_2254941).sum := by decide
  have hdescent : baseEnd_2254941 < baseStart_2254941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254980 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2254980 : Nat := 118140960795 + 2254980 * 2 ^ 59
def prefixEnd_2254980 : Nat := 4983230072969 + 3 ^ 40 * 2254980 * 2
def baseEnd_2254980 : Nat := 771925737517128409386361

theorem tailTrace_2254980 : CollatzResearch.WordTrace tailWord_2254980 prefixEnd_2254980 771925737517128409386361 := by
  unfold tailWord_2254980
  simp only [CollatzResearch.WordTrace]
  refine ⟨41122938685300027384073197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54830584913733369845430929 41122938685300027384073197)
  ·
    refine ⟨15421102006987510269027449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41122938685300027384073197 15421102006987510269027449)
    ·
      refine ⟨11565826505240632701770587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15421102006987510269027449 11565826505240632701770587)
      ·
        refine ⟨17348739757860949052655881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11565826505240632701770587 17348739757860949052655881)
        ·
          refine ⟨13011554818395711789491911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17348739757860949052655881 13011554818395711789491911)
          ·
            refine ⟨19517332227593567684237867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011554818395711789491911 19517332227593567684237867)
            ·
              refine ⟨29275998341390351526356801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19517332227593567684237867 29275998341390351526356801)
              ·
                refine ⟨21956998756042763644767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29275998341390351526356801 21956998756042763644767601)
                ·
                  refine ⟨16467749067032072733575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21956998756042763644767601 16467749067032072733575701)
                  ·
                    refine ⟨771925737517128409386361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16467749067032072733575701 771925737517128409386361)
                    ·
                      rfl

theorem cell22_2254980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2254980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2254980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2254980 prefixEnd_2254980 := by exact prefixLift 2254980
  have htrace : WordTrace (prefixWord ++ tailWord_2254980) baseStart_2254980 baseEnd_2254980 := by
    simpa [prefixWord, tailWord_2254980, baseEnd_2254980] using wordTrace_append hprefix tailTrace_2254980
  have hstable : (prefixWord ++ tailWord_2254980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254980).length < 2 ^ (prefixWord ++ tailWord_2254980).sum := by decide
  have hdescent : baseEnd_2254980 < baseStart_2254980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255012 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_2255012 : Nat := 118140960795 + 2255012 * 2 ^ 59
def prefixEnd_2255012 : Nat := 4983230072969 + 3 ^ 40 * 2255012 * 2
def baseEnd_2255012 : Nat := 257312230590363664195421

theorem tailTrace_2255012 : CollatzResearch.WordTrace tailWord_2255012 prefixEnd_2255012 257312230590363664195421 := by
  unfold tailWord_2255012
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123522253242062116655645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54831363004322749488874193 41123522253242062116655645)
  ·
    refine ⟨15421320844965773293745867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41123522253242062116655645 15421320844965773293745867)
    ·
      refine ⟨23131981267448659940618801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15421320844965773293745867 23131981267448659940618801)
      ·
        refine ⟨17348985950586494955464101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23131981267448659940618801 17348985950586494955464101)
        ·
          refine ⟨3252934865734967804149519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17348985950586494955464101 3252934865734967804149519)
          ·
            refine ⟨4879402298602451706224279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252934865734967804149519 4879402298602451706224279)
            ·
              refine ⟨7319103447903677559336419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879402298602451706224279 7319103447903677559336419)
              ·
                refine ⟨10978655171855516339004629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319103447903677559336419 10978655171855516339004629)
                ·
                  refine ⟨257312230590363664195421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10978655171855516339004629 257312230590363664195421)
                  ·
                    rfl

theorem cell22_2255012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_2255012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255012 prefixEnd_2255012 := by exact prefixLift 2255012
  have htrace : WordTrace (prefixWord ++ tailWord_2255012) baseStart_2255012 baseEnd_2255012 := by
    simpa [prefixWord, tailWord_2255012, baseEnd_2255012] using wordTrace_append hprefix tailTrace_2255012
  have hstable : (prefixWord ++ tailWord_2255012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255012).length < 2 ^ (prefixWord ++ tailWord_2255012).sum := by decide
  have hdescent : baseEnd_2255012 < baseStart_2255012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255055 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_2255055 : Nat := 118140960795 + 2255055 * 2 ^ 59
def prefixEnd_2255055 : Nat := 4983230072969 + 3 ^ 40 * 2255055 * 2
def baseEnd_2255055 : Nat := 771951411549853213761131

theorem tailTrace_2255055 : CollatzResearch.WordTrace tailWord_2255055 prefixEnd_2255055 771951411549853213761131 := by
  unfold tailWord_2255055
  simp only [CollatzResearch.WordTrace]
  refine ⟨82248612845328342577126619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54832408563552228384751079 82248612845328342577126619)
  ·
    refine ⟨123372919267992513865689929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82248612845328342577126619 123372919267992513865689929)
    ·
      refine ⟨92529689450994385399267447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123372919267992513865689929 92529689450994385399267447)
      ·
        refine ⟨138794534176491578098901171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92529689450994385399267447 138794534176491578098901171)
        ·
          refine ⟨208191801264737367148351757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138794534176491578098901171 208191801264737367148351757)
          ·
            refine ⟨78071925474276512680631909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208191801264737367148351757 78071925474276512680631909)
            ·
              refine ⟨14638486026426846127618483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78071925474276512680631909 14638486026426846127618483)
              ·
                refine ⟨21957729039640269191427725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14638486026426846127618483 21957729039640269191427725)
                ·
                  refine ⟨8234148389865100946785397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21957729039640269191427725 8234148389865100946785397)
                  ·
                    refine ⟨771951411549853213761131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8234148389865100946785397 771951411549853213761131)
                    ·
                      rfl

theorem cell22_2255055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_2255055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255055 prefixEnd_2255055 := by exact prefixLift 2255055
  have htrace : WordTrace (prefixWord ++ tailWord_2255055) baseStart_2255055 baseEnd_2255055 := by
    simpa [prefixWord, tailWord_2255055, baseEnd_2255055] using wordTrace_append hprefix tailTrace_2255055
  have hstable : (prefixWord ++ tailWord_2255055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255055).length < 2 ^ (prefixWord ++ tailWord_2255055).sum := by decide
  have hdescent : baseEnd_2255055 < baseStart_2255055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255072 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_2255072 : Nat := 118140960795 + 2255072 * 2 ^ 59
def prefixEnd_2255072 : Nat := 4983230072969 + 3 ^ 40 * 2255072 * 2
def baseEnd_2255072 : Nat := 771957230997270836086079

theorem tailTrace_2255072 : CollatzResearch.WordTrace tailWord_2255072 prefixEnd_2255072 771957230997270836086079 := by
  unfold tailWord_2255072
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124616443133377240247735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54832821924177836320330313 41124616443133377240247735)
  ·
    refine ⟨61686924664700065860371603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41124616443133377240247735 61686924664700065860371603)
    ·
      refine ⟨92530386997050098790557405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61686924664700065860371603 92530386997050098790557405)
      ·
        refine ⟨34698895123893787046459027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92530386997050098790557405 34698895123893787046459027)
        ·
          refine ⟨52048342685840680569688541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34698895123893787046459027 52048342685840680569688541)
          ·
            refine ⟨19518128507190255213633203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52048342685840680569688541 19518128507190255213633203)
            ·
              refine ⟨29277192760785382820449805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19518128507190255213633203 29277192760785382820449805)
              ·
                refine ⟨10978947285294518557668677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29277192760785382820449805 10978947285294518557668677)
                ·
                  refine ⟨2058552615992722229562877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10978947285294518557668677 2058552615992722229562877)
                  ·
                    refine ⟨771957230997270836086079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058552615992722229562877 771957230997270836086079)
                    ·
                      rfl

theorem cell22_2255072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_2255072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255072 prefixEnd_2255072 := by exact prefixLift 2255072
  have htrace : WordTrace (prefixWord ++ tailWord_2255072) baseStart_2255072 baseEnd_2255072 := by
    simpa [prefixWord, tailWord_2255072, baseEnd_2255072] using wordTrace_append hprefix tailTrace_2255072
  have hstable : (prefixWord ++ tailWord_2255072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255072).length < 2 ^ (prefixWord ++ tailWord_2255072).sum := by decide
  have hdescent : baseEnd_2255072 < baseStart_2255072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255102 : List Nat := [4, 2, 2, 1, 1, 1, 1, 10]
def baseStart_2255102 : Nat := 118140960795 + 2255102 * 2 ^ 59
def prefixEnd_2255102 : Nat := 4983230072969 + 3 ^ 40 * 2255102 * 2
def baseEnd_2255102 : Nat := 85774166734484528648443

theorem tailTrace_2255102 : CollatzResearch.WordTrace tailWord_2255102 prefixEnd_2255102 85774166734484528648443 := by
  unfold tailWord_2255102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281290884519758700510945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54833551384105379736058373 10281290884519758700510945)
  ·
    refine ⟨7710968163389819025383209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10281290884519758700510945 7710968163389819025383209)
    ·
      refine ⟨5783226122542364269037407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7710968163389819025383209 5783226122542364269037407)
      ·
        refine ⟨8674839183813546403556111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783226122542364269037407 8674839183813546403556111)
        ·
          refine ⟨13012258775720319605334167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674839183813546403556111 13012258775720319605334167)
          ·
            refine ⟨19518388163580479408001251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012258775720319605334167 19518388163580479408001251)
            ·
              refine ⟨29277582245370719112001877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19518388163580479408001251 29277582245370719112001877)
              ·
                refine ⟨85774166734484528648443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29277582245370719112001877 85774166734484528648443)
                ·
                  rfl

theorem cell22_2255102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_2255102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255102 prefixEnd_2255102 := by exact prefixLift 2255102
  have htrace : WordTrace (prefixWord ++ tailWord_2255102) baseStart_2255102 baseEnd_2255102 := by
    simpa [prefixWord, tailWord_2255102, baseEnd_2255102] using wordTrace_append hprefix tailTrace_2255102
  have hstable : (prefixWord ++ tailWord_2255102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255102).length < 2 ^ (prefixWord ++ tailWord_2255102).sum := by decide
  have hdescent : baseEnd_2255102 < baseStart_2255102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255239 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2255239 : Nat := 118140960795 + 2255239 * 2 ^ 59
def prefixEnd_2255239 : Nat := 4983230072969 + 3 ^ 40 * 2255239 * 2
def baseEnd_2255239 : Nat := 772014398510138067160567

theorem tailTrace_2255239 : CollatzResearch.WordTrace tailWord_2255239 prefixEnd_2255239 772014398510138067160567 := by
  unfold tailWord_2255239
  simp only [CollatzResearch.WordTrace]
  refine ⟨82255323876661742001824771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54836882584441161334549847 82255323876661742001824771)
  ·
    refine ⟨123382985814992613002737157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82255323876661742001824771 123382985814992613002737157)
    ·
      refine ⟨23134309840311114938013217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123382985814992613002737157 23134309840311114938013217)
      ·
        refine ⟨17350732380233336203509913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23134309840311114938013217 17350732380233336203509913)
        ·
          refine ⟨13013049285175002152632435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17350732380233336203509913 13013049285175002152632435)
          ·
            refine ⟨19519573927762503228948653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013049285175002152632435 19519573927762503228948653)
            ·
              refine ⟨7319840222910938710855745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19519573927762503228948653 7319840222910938710855745)
              ·
                refine ⟨5489880167183204033141809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319840222910938710855745 5489880167183204033141809)
                ·
                  refine ⟨4117410125387403024856357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5489880167183204033141809 4117410125387403024856357)
                  ·
                    refine ⟨772014398510138067160567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117410125387403024856357 772014398510138067160567)
                    ·
                      rfl

theorem cell22_2255239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2255239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255239 prefixEnd_2255239 := by exact prefixLift 2255239
  have htrace : WordTrace (prefixWord ++ tailWord_2255239) baseStart_2255239 baseEnd_2255239 := by
    simpa [prefixWord, tailWord_2255239, baseEnd_2255239] using wordTrace_append hprefix tailTrace_2255239
  have hstable : (prefixWord ++ tailWord_2255239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255239).length < 2 ^ (prefixWord ++ tailWord_2255239).sum := by decide
  have hdescent : baseEnd_2255239 < baseStart_2255239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255258 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_2255258 : Nat := 118140960795 + 2255258 * 2 ^ 59
def prefixEnd_2255258 : Nat := 4983230072969 + 3 ^ 40 * 2255258 * 2
def baseEnd_2255258 : Nat := 772020902598428350935509

theorem tailTrace_2255258 : CollatzResearch.WordTrace tailWord_2255258 prefixEnd_2255258 772020902598428350935509 := by
  unfold tailWord_2255258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20564004215898227061691607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54837344575728605497844285 20564004215898227061691607)
  ·
    refine ⟨30846006323847340592537411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20564004215898227061691607 30846006323847340592537411)
    ·
      refine ⟨46269009485771010888806117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30846006323847340592537411 46269009485771010888806117)
      ·
        refine ⟨8675439278582064541651147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46269009485771010888806117 8675439278582064541651147)
        ·
          refine ⟨13013158917873096812476721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675439278582064541651147 13013158917873096812476721)
          ·
            refine ⟨9759869188404822609357541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13013158917873096812476721 9759869188404822609357541)
            ·
              refine ⟨1829975472825904239254539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9759869188404822609357541 1829975472825904239254539)
              ·
                refine ⟨2744963209238856358881809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829975472825904239254539 2744963209238856358881809)
                ·
                  refine ⟨2058722406929142269161357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2744963209238856358881809 2058722406929142269161357)
                  ·
                    refine ⟨772020902598428350935509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058722406929142269161357 772020902598428350935509)
                    ·
                      rfl

theorem cell22_2255258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_2255258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255258 prefixEnd_2255258 := by exact prefixLift 2255258
  have htrace : WordTrace (prefixWord ++ tailWord_2255258) baseStart_2255258 baseEnd_2255258 := by
    simpa [prefixWord, tailWord_2255258, baseEnd_2255258] using wordTrace_append hprefix tailTrace_2255258
  have hstable : (prefixWord ++ tailWord_2255258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255258).length < 2 ^ (prefixWord ++ tailWord_2255258).sum := by decide
  have hdescent : baseEnd_2255258 < baseStart_2255258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255269 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_2255269 : Nat := 118140960795 + 2255269 * 2 ^ 59
def prefixEnd_2255269 : Nat := 4983230072969 + 3 ^ 40 * 2255269 * 2
def baseEnd_2255269 : Nat := 772024668123227988910475

theorem tailTrace_2255269 : CollatzResearch.WordTrace tailWord_2255269 prefixEnd_2255269 772024668123227988910475 := by
  unfold tailWord_2255269
  simp only [CollatzResearch.WordTrace]
  refine ⟨82256418066553057125416861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54837612044368704750277907 82256418066553057125416861)
  ·
    refine ⟨30846156774957396422031323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82256418066553057125416861 30846156774957396422031323)
    ·
      refine ⟨46269235162436094633046985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30846156774957396422031323 46269235162436094633046985)
      ·
        refine ⟨34701926371827070974785239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46269235162436094633046985 34701926371827070974785239)
        ·
          refine ⟨52052889557740606462177859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34701926371827070974785239 52052889557740606462177859)
          ·
            refine ⟨78079334336610909693266789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52052889557740606462177859 78079334336610909693266789)
            ·
              refine ⟨14639875188114545567487523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78079334336610909693266789 14639875188114545567487523)
              ·
                refine ⟨21959812782171818351231285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14639875188114545567487523 21959812782171818351231285)
                ·
                  refine ⟨2058732448328607970427933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21959812782171818351231285 2058732448328607970427933)
                  ·
                    refine ⟨772024668123227988910475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058732448328607970427933 772024668123227988910475)
                    ·
                      rfl

theorem cell22_2255269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_2255269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255269 prefixEnd_2255269 := by exact prefixLift 2255269
  have htrace : WordTrace (prefixWord ++ tailWord_2255269) baseStart_2255269 baseEnd_2255269 := by
    simpa [prefixWord, tailWord_2255269, baseEnd_2255269] using wordTrace_append hprefix tailTrace_2255269
  have hstable : (prefixWord ++ tailWord_2255269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255269).length < 2 ^ (prefixWord ++ tailWord_2255269).sum := by decide
  have hdescent : baseEnd_2255269 < baseStart_2255269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255303 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2255303 : Nat := 118140960795 + 2255303 * 2 ^ 59
def prefixEnd_2255303 : Nat := 4983230072969 + 3 ^ 40 * 2255303 * 2
def baseEnd_2255303 : Nat := 772036307018063233560371

theorem tailTrace_2255303 : CollatzResearch.WordTrace tailWord_2255303 prefixEnd_2255303 772036307018063233560371 := by
  unfold tailWord_2255303
  simp only [CollatzResearch.WordTrace]
  refine ⟨82257658148429880932154563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54838438765619920621436375 82257658148429880932154563)
  ·
    refine ⟨123386487222644821398231845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82257658148429880932154563 123386487222644821398231845)
    ·
      refine ⟨23134966354245904012168471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123386487222644821398231845 23134966354245904012168471)
      ·
        refine ⟨34702449531368856018252707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23134966354245904012168471 34702449531368856018252707)
        ·
          refine ⟨52053674297053284027379061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34702449531368856018252707 52053674297053284027379061)
          ·
            refine ⟨4880031965348745377566787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52053674297053284027379061 4880031965348745377566787)
            ·
              refine ⟨7320047948023118066350181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880031965348745377566787 7320047948023118066350181)
              ·
                refine ⟨1372508990254334637440659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7320047948023118066350181 1372508990254334637440659)
                ·
                  refine ⟨2058763485381501956160989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372508990254334637440659 2058763485381501956160989)
                  ·
                    refine ⟨772036307018063233560371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058763485381501956160989 772036307018063233560371)
                    ·
                      rfl

theorem cell22_2255303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2255303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255303 prefixEnd_2255303 := by exact prefixLift 2255303
  have htrace : WordTrace (prefixWord ++ tailWord_2255303) baseStart_2255303 baseEnd_2255303 := by
    simpa [prefixWord, tailWord_2255303, baseEnd_2255303] using wordTrace_append hprefix tailTrace_2255303
  have hstable : (prefixWord ++ tailWord_2255303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255303).length < 2 ^ (prefixWord ++ tailWord_2255303).sum := by decide
  have hdescent : baseEnd_2255303 < baseStart_2255303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255312 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_2255312 : Nat := 118140960795 + 2255312 * 2 ^ 59
def prefixEnd_2255312 : Nat := 4983230072969 + 3 ^ 40 * 2255312 * 2
def baseEnd_2255312 : Nat := 772039387901990210085343

theorem tailTrace_2255312 : CollatzResearch.WordTrace tailWord_2255312 prefixEnd_2255312 772039387901990210085343 := by
  unfold tailWord_2255312
  simp only [CollatzResearch.WordTrace]
  refine ⟨41128993202698637734616095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54838657603598183646154793 41128993202698637734616095)
  ·
    refine ⟨61693489804047956601924143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41128993202698637734616095 61693489804047956601924143)
    ·
      refine ⟨92540234706071934902886215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61693489804047956601924143 92540234706071934902886215)
      ·
        refine ⟨138810352059107902354329323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92540234706071934902886215 138810352059107902354329323)
        ·
          refine ⟨208215528088661853531493985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138810352059107902354329323 208215528088661853531493985)
          ·
            refine ⟨156161646066496390148620489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208215528088661853531493985 156161646066496390148620489)
            ·
              refine ⟨117121234549872292611465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156161646066496390148620489 117121234549872292611465367)
              ·
                refine ⟨175681851824808438917198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117121234549872292611465367 175681851824808438917198051)
                ·
                  refine ⟨263522777737212658375797077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175681851824808438917198051 263522777737212658375797077)
                  ·
                    refine ⟨772039387901990210085343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 263522777737212658375797077 772039387901990210085343)
                    ·
                      rfl

theorem cell22_2255312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_2255312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255312 prefixEnd_2255312 := by exact prefixLift 2255312
  have htrace : WordTrace (prefixWord ++ tailWord_2255312) baseStart_2255312 baseEnd_2255312 := by
    simpa [prefixWord, tailWord_2255312, baseEnd_2255312] using wordTrace_append hprefix tailTrace_2255312
  have hstable : (prefixWord ++ tailWord_2255312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255312).length < 2 ^ (prefixWord ++ tailWord_2255312).sum := by decide
  have hdescent : baseEnd_2255312 < baseStart_2255312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255316 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_2255316 : Nat := 118140960795 + 2255316 * 2 ^ 59
def prefixEnd_2255316 : Nat := 4983230072969 + 3 ^ 40 * 2255316 * 2
def baseEnd_2255316 : Nat := 257346919061245177661777

theorem tailTrace_2255316 : CollatzResearch.WordTrace tailWord_2255316 prefixEnd_2255316 257346919061245177661777 := by
  unfold tailWord_2255316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41129066148691392076188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54838754864921856101585201 41129066148691392076188901)
  ·
    refine ⟨7711699902879636014285419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41129066148691392076188901 7711699902879636014285419)
    ·
      refine ⟨11567549854319454021428129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711699902879636014285419 11567549854319454021428129)
      ·
        refine ⟨8675662390739590516071097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11567549854319454021428129 8675662390739590516071097)
        ·
          refine ⟨6506746793054692887053323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8675662390739590516071097 6506746793054692887053323)
          ·
            refine ⟨9760120189582039330579985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6506746793054692887053323 9760120189582039330579985)
            ·
              refine ⟨7320090142186529497934989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9760120189582039330579985 7320090142186529497934989)
              ·
                refine ⟨2745033803319948561725621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7320090142186529497934989 2745033803319948561725621)
                ·
                  refine ⟨257346919061245177661777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2745033803319948561725621 257346919061245177661777)
                  ·
                    rfl

theorem cell22_2255316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_2255316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255316 prefixEnd_2255316 := by exact prefixLift 2255316
  have htrace : WordTrace (prefixWord ++ tailWord_2255316) baseStart_2255316 baseEnd_2255316 := by
    simpa [prefixWord, tailWord_2255316, baseEnd_2255316] using wordTrace_append hprefix tailTrace_2255316
  have hstable : (prefixWord ++ tailWord_2255316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255316).length < 2 ^ (prefixWord ++ tailWord_2255316).sum := by decide
  have hdescent : baseEnd_2255316 < baseStart_2255316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255329 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2255329 : Nat := 118140960795 + 2255329 * 2 ^ 59
def prefixEnd_2255329 : Nat := 4983230072969 + 3 ^ 40 * 2255329 * 2
def baseEnd_2255329 : Nat := 772045207349407832410291

theorem tailTrace_2255329 : CollatzResearch.WordTrace tailWord_2255329 prefixEnd_2255329 772045207349407832410291 := by
  unfold tailWord_2255329
  simp only [CollatzResearch.WordTrace]
  refine ⟨82258606446335687372601041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54839070964223791581734027 82258606446335687372601041)
  ·
    refine ⟨61693954834751765529450781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82258606446335687372601041 61693954834751765529450781)
    ·
      refine ⟨23135233063031912073544043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61693954834751765529450781 23135233063031912073544043)
      ·
        refine ⟨34702849594547868110316065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23135233063031912073544043 34702849594547868110316065)
        ·
          refine ⟨26027137195910901082737049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34702849594547868110316065 26027137195910901082737049)
          ·
            refine ⟨19520352896933175812052787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26027137195910901082737049 19520352896933175812052787)
            ·
              refine ⟨29280529345399763718079181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19520352896933175812052787 29280529345399763718079181)
              ·
                refine ⟨10980198504524911394279693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29280529345399763718079181 10980198504524911394279693)
                ·
                  refine ⟨4117574439196841772854885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10980198504524911394279693 4117574439196841772854885)
                  ·
                    refine ⟨772045207349407832410291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117574439196841772854885 772045207349407832410291)
                    ·
                      rfl

theorem cell22_2255329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2255329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255329 prefixEnd_2255329 := by exact prefixLift 2255329
  have htrace : WordTrace (prefixWord ++ tailWord_2255329) baseStart_2255329 baseEnd_2255329 := by
    simpa [prefixWord, tailWord_2255329, baseEnd_2255329] using wordTrace_append hprefix tailTrace_2255329
  have hstable : (prefixWord ++ tailWord_2255329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255329).length < 2 ^ (prefixWord ++ tailWord_2255329).sum := by decide
  have hdescent : baseEnd_2255329 < baseStart_2255329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255361 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 6]
def baseStart_2255361 : Nat := 118140960795 + 2255361 * 2 ^ 59
def prefixEnd_2255361 : Nat := 4983230072969 + 3 ^ 40 * 2255361 * 2
def baseEnd_2255361 : Nat := 257352053867790138536731

theorem tailTrace_2255361 : CollatzResearch.WordTrace tailWord_2255361 prefixEnd_2255361 257352053867790138536731 := by
  unfold tailWord_2255361
  simp only [CollatzResearch.WordTrace]
  refine ⟨82259773582219756837765937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54839849054813171225177291 82259773582219756837765937)
  ·
    refine ⟨61694830186664817628324453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82259773582219756837765937 61694830186664817628324453)
    ·
      refine ⟨11567780659999653305310835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61694830186664817628324453 11567780659999653305310835)
      ·
        refine ⟨17351670989999479957966253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567780659999653305310835 17351670989999479957966253)
        ·
          refine ⟨6506876621249804984237345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17351670989999479957966253 6506876621249804984237345)
          ·
            refine ⟨4880157465937353738178009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506876621249804984237345 4880157465937353738178009)
            ·
              refine ⟨3660118099453015303633507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880157465937353738178009 3660118099453015303633507)
              ·
                refine ⟨5490177149179522955450261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660118099453015303633507 5490177149179522955450261)
                ·
                  refine ⟨257352053867790138536731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5490177149179522955450261 257352053867790138536731)
                  ·
                    rfl

theorem cell22_2255361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_2255361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255361 prefixEnd_2255361 := by exact prefixLift 2255361
  have htrace : WordTrace (prefixWord ++ tailWord_2255361) baseStart_2255361 baseEnd_2255361 := by
    simpa [prefixWord, tailWord_2255361, baseEnd_2255361] using wordTrace_append hprefix tailTrace_2255361
  have hstable : (prefixWord ++ tailWord_2255361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255361).length < 2 ^ (prefixWord ++ tailWord_2255361).sum := by decide
  have hdescent : baseEnd_2255361 < baseStart_2255361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255380 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2255380 : Nat := 118140960795 + 2255380 * 2 ^ 59
def prefixEnd_2255380 : Nat := 4983230072969 + 3 ^ 40 * 2255380 * 2
def baseEnd_2255380 : Nat := 772062665691660699385135

theorem tailTrace_2255380 : CollatzResearch.WordTrace tailWord_2255380 prefixEnd_2255380 772062665691660699385135 := by
  unfold tailWord_2255380
  simp only [CollatzResearch.WordTrace]
  refine ⟨41130233284575461541353797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54840311046100615388471729 41130233284575461541353797)
  ·
    refine ⟨7711918740857899039003837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41130233284575461541353797 7711918740857899039003837)
    ·
      refine ⟨2891969527821712139626439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7711918740857899039003837 2891969527821712139626439)
      ·
        refine ⟨4337954291732568209439659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891969527821712139626439 4337954291732568209439659)
        ·
          refine ⟨6506931437598852314159489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337954291732568209439659 6506931437598852314159489)
          ·
            refine ⟨4880198578199139235619617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506931437598852314159489 4880198578199139235619617)
            ·
              refine ⟨3660148933649354426714713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880198578199139235619617 3660148933649354426714713)
              ·
                refine ⟨2745111700237015820036035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660148933649354426714713 2745111700237015820036035)
                ·
                  refine ⟨4117667550355523730054053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745111700237015820036035 4117667550355523730054053)
                  ·
                    refine ⟨772062665691660699385135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117667550355523730054053 772062665691660699385135)
                    ·
                      rfl

theorem cell22_2255380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2255380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255380 prefixEnd_2255380 := by exact prefixLift 2255380
  have htrace : WordTrace (prefixWord ++ tailWord_2255380) baseStart_2255380 baseEnd_2255380 := by
    simpa [prefixWord, tailWord_2255380, baseEnd_2255380] using wordTrace_append hprefix tailTrace_2255380
  have hstable : (prefixWord ++ tailWord_2255380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255380).length < 2 ^ (prefixWord ++ tailWord_2255380).sum := by decide
  have hdescent : baseEnd_2255380 < baseStart_2255380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255412 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2255412 : Nat := 118140960795 + 2255412 * 2 ^ 59
def prefixEnd_2255412 : Nat := 4983230072969 + 3 ^ 40 * 2255412 * 2
def baseEnd_2255412 : Nat := 257357873315207760861679

theorem tailTrace_2255412 : CollatzResearch.WordTrace tailWord_2255412 prefixEnd_2255412 257357873315207760861679 := by
  unfold tailWord_2255412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41130816852517496273936245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54841089136689995031914993 41130816852517496273936245)
  ·
    refine ⟨3856014079923515275681523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41130816852517496273936245 3856014079923515275681523)
    ·
      refine ⟨5784021119885272913522285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856014079923515275681523 5784021119885272913522285)
      ·
        refine ⟨2169007919956977342570857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5784021119885272913522285 2169007919956977342570857)
        ·
          refine ⟨1626755939967733006928143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2169007919956977342570857 1626755939967733006928143)
          ·
            refine ⟨2440133909951599510392215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626755939967733006928143 2440133909951599510392215)
            ·
              refine ⟨3660200864927399265588323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440133909951599510392215 3660200864927399265588323)
              ·
                refine ⟨5490301297391098898382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660200864927399265588323 5490301297391098898382485)
                ·
                  refine ⟨257357873315207760861679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5490301297391098898382485 257357873315207760861679)
                  ·
                    rfl

theorem cell22_2255412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2255412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255412 prefixEnd_2255412 := by exact prefixLift 2255412
  have htrace : WordTrace (prefixWord ++ tailWord_2255412) baseStart_2255412 baseEnd_2255412 := by
    simpa [prefixWord, tailWord_2255412, baseEnd_2255412] using wordTrace_append hprefix tailTrace_2255412
  have hstable : (prefixWord ++ tailWord_2255412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255412).length < 2 ^ (prefixWord ++ tailWord_2255412).sum := by decide
  have hdescent : baseEnd_2255412 < baseStart_2255412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255449 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_2255449 : Nat := 118140960795 + 2255449 * 2 ^ 59
def prefixEnd_2255449 : Nat := 4983230072969 + 3 ^ 40 * 2255449 * 2
def baseEnd_2255449 : Nat := 772086285801767519409923

theorem tailTrace_2255449 : CollatzResearch.WordTrace tailWord_2255449 prefixEnd_2255449 772086285801767519409923 := by
  unfold tailWord_2255449
  simp only [CollatzResearch.WordTrace]
  refine ⟨82262983205900947866969401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54841988803933965244646267 82262983205900947866969401)
  ·
    refine ⟨61697237404425710900227051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82262983205900947866969401 61697237404425710900227051)
    ·
      refine ⟨92545856106638566350340577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61697237404425710900227051 92545856106638566350340577)
      ·
        refine ⟨69409392079978924762755433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92545856106638566350340577 69409392079978924762755433)
        ·
          refine ⟨52057044059984193572066575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69409392079978924762755433 52057044059984193572066575)
          ·
            refine ⟨78085566089976290358099863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52057044059984193572066575 78085566089976290358099863)
            ·
              refine ⟨117128349134964435537149795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78085566089976290358099863 117128349134964435537149795)
              ·
                refine ⟨175692523702446653305724693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117128349134964435537149795 175692523702446653305724693)
                ·
                  refine ⟨8235587048552186873705845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175692523702446653305724693 8235587048552186873705845)
                  ·
                    refine ⟨772086285801767519409923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8235587048552186873705845 772086285801767519409923)
                    ·
                      rfl

theorem cell22_2255449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_2255449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255449 prefixEnd_2255449 := by exact prefixLift 2255449
  have htrace : WordTrace (prefixWord ++ tailWord_2255449) baseStart_2255449 baseEnd_2255449 := by
    simpa [prefixWord, tailWord_2255449, baseEnd_2255449] using wordTrace_append hprefix tailTrace_2255449
  have hstable : (prefixWord ++ tailWord_2255449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255449).length < 2 ^ (prefixWord ++ tailWord_2255449).sum := by decide
  have hdescent : baseEnd_2255449 < baseStart_2255449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255466 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2255466 : Nat := 118140960795 + 2255466 * 2 ^ 59
def prefixEnd_2255466 : Nat := 4983230072969 + 3 ^ 40 * 2255466 * 2
def baseEnd_2255466 : Nat := 772092105249185141734871

theorem tailTrace_2255466 : CollatzResearch.WordTrace tailWord_2255466 prefixEnd_2255466 772092105249185141734871 := by
  unfold tailWord_2255466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565900811709839942584563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54842402164559573180225501 20565900811709839942584563)
  ·
    refine ⟨30848851217564759913876845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20565900811709839942584563 30848851217564759913876845)
    ·
      refine ⟨11568319206586784967703817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30848851217564759913876845 11568319206586784967703817)
      ·
        refine ⟨8676239404940088725777863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11568319206586784967703817 8676239404940088725777863)
        ·
          refine ⟨13014359107410133088666795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676239404940088725777863 13014359107410133088666795)
          ·
            refine ⟨19521538661115199633000193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13014359107410133088666795 19521538661115199633000193)
            ·
              refine ⟨14641153995836399724750145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19521538661115199633000193 14641153995836399724750145)
              ·
                refine ⟨10980865496877299793562609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14641153995836399724750145 10980865496877299793562609)
                ·
                  refine ⟨8235649122657974845171957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10980865496877299793562609 8235649122657974845171957)
                  ·
                    refine ⟨772092105249185141734871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8235649122657974845171957 772092105249185141734871)
                    ·
                      rfl

theorem cell22_2255466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2255466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255466 prefixEnd_2255466 := by exact prefixLift 2255466
  have htrace : WordTrace (prefixWord ++ tailWord_2255466) baseStart_2255466 baseEnd_2255466 := by
    simpa [prefixWord, tailWord_2255466, baseEnd_2255466] using wordTrace_append hprefix tailTrace_2255466
  have hstable : (prefixWord ++ tailWord_2255466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255466).length < 2 ^ (prefixWord ++ tailWord_2255466).sum := by decide
  have hdescent : baseEnd_2255466 < baseStart_2255466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255481 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_2255481 : Nat := 118140960795 + 2255481 * 2 ^ 59
def prefixEnd_2255481 : Nat := 4983230072969 + 3 ^ 40 * 2255481 * 2
def baseEnd_2255481 : Nat := 772097240055730102609825

theorem tailTrace_2255481 : CollatzResearch.WordTrace tailWord_2255481 prefixEnd_2255481 772097240055730102609825 := by
  unfold tailWord_2255481
  simp only [CollatzResearch.WordTrace]
  refine ⟨82264150341785017332134297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54842766894523344888089531 82264150341785017332134297)
  ·
    refine ⟨61698112756338762999100723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82264150341785017332134297 61698112756338762999100723)
    ·
      refine ⟨92547169134508144498651085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61698112756338762999100723 92547169134508144498651085)
      ·
        refine ⟨34705188425440554186994157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92547169134508144498651085 34705188425440554186994157)
        ·
          refine ⟨13014445659540207820122809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34705188425440554186994157 13014445659540207820122809)
          ·
            refine ⟨9760834244655155865092107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13014445659540207820122809 9760834244655155865092107)
            ·
              refine ⟨14641251366982733797638161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9760834244655155865092107 14641251366982733797638161)
              ·
                refine ⟨10980938525237050348228621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14641251366982733797638161 10980938525237050348228621)
                ·
                  refine ⟨4117851946963893880585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10980938525237050348228621 4117851946963893880585733)
                  ·
                    refine ⟨772097240055730102609825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117851946963893880585733 772097240055730102609825)
                    ·
                      rfl

theorem cell22_2255481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_2255481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255481 prefixEnd_2255481 := by exact prefixLift 2255481
  have htrace : WordTrace (prefixWord ++ tailWord_2255481) baseStart_2255481 baseEnd_2255481 := by
    simpa [prefixWord, tailWord_2255481, baseEnd_2255481] using wordTrace_append hprefix tailTrace_2255481
  have hstable : (prefixWord ++ tailWord_2255481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255481).length < 2 ^ (prefixWord ++ tailWord_2255481).sum := by decide
  have hdescent : baseEnd_2255481 < baseStart_2255481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255511 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2255511 : Nat := 118140960795 + 2255511 * 2 ^ 59
def prefixEnd_2255511 : Nat := 4983230072969 + 3 ^ 40 * 2255511 * 2
def baseEnd_2255511 : Nat := 772107509668820024359733

theorem tailTrace_2255511 : CollatzResearch.WordTrace tailWord_2255511 prefixEnd_2255511 772107509668820024359733 := by
  unfold tailWord_2255511
  simp only [CollatzResearch.WordTrace]
  refine ⟨82265244531676332455726387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54843496354450888303817591 82265244531676332455726387)
  ·
    refine ⟨123397866797514498683589581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82265244531676332455726387 123397866797514498683589581)
    ·
      refine ⟨46274200049067937006346093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123397866797514498683589581 46274200049067937006346093)
      ·
        refine ⟨17352825018400476377379785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46274200049067937006346093 17352825018400476377379785)
        ·
          refine ⟨13014618763800357283034839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17352825018400476377379785 13014618763800357283034839)
          ·
            refine ⟨19521928145700535924552259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13014618763800357283034839 19521928145700535924552259)
            ·
              refine ⟨29282892218550803886828389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19521928145700535924552259 29282892218550803886828389)
              ·
                refine ⟨5490542290978275728780323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29282892218550803886828389 5490542290978275728780323)
                ·
                  refine ⟨8235813436467413593170485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5490542290978275728780323 8235813436467413593170485)
                  ·
                    refine ⟨772107509668820024359733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8235813436467413593170485 772107509668820024359733)
                    ·
                      rfl

theorem cell22_2255511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2255511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255511 prefixEnd_2255511 := by exact prefixLift 2255511
  have htrace : WordTrace (prefixWord ++ tailWord_2255511) baseStart_2255511 baseEnd_2255511 := by
    simpa [prefixWord, tailWord_2255511, baseEnd_2255511] using wordTrace_append hprefix tailTrace_2255511
  have hstable : (prefixWord ++ tailWord_2255511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255511).length < 2 ^ (prefixWord ++ tailWord_2255511).sum := by decide
  have hdescent : baseEnd_2255511 < baseStart_2255511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255513 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 4]
def baseStart_2255513 : Nat := 118140960795 + 2255513 * 2 ^ 59
def prefixEnd_2255513 : Nat := 4983230072969 + 3 ^ 40 * 2255513 * 2
def baseEnd_2255513 : Nat := 257369398103230895269909

theorem tailTrace_2255513 : CollatzResearch.WordTrace tailWord_2255513 prefixEnd_2255513 257369398103230895269909 := by
  unfold tailWord_2255513
  simp only [CollatzResearch.WordTrace]
  refine ⟨82265317477669086797299193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54843544985112724531532795 82265317477669086797299193)
  ·
    refine ⟨61698988108251815097974395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82265317477669086797299193 61698988108251815097974395)
    ·
      refine ⟨92548482162377722646961593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61698988108251815097974395 92548482162377722646961593)
      ·
        refine ⟨69411361621783291985221195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92548482162377722646961593 69411361621783291985221195)
        ·
          refine ⟨104117042432674937977831793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69411361621783291985221195 104117042432674937977831793)
          ·
            refine ⟨78087781824506203483373845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104117042432674937977831793 78087781824506203483373845)
            ·
              refine ⟨3660364773023728288283149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78087781824506203483373845 3660364773023728288283149)
              ·
                refine ⟨1372636789883898108106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3660364773023728288283149 1372636789883898108106181)
                ·
                  refine ⟨257369398103230895269909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372636789883898108106181 257369398103230895269909)
                  ·
                    rfl

theorem cell22_2255513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_2255513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255513 prefixEnd_2255513 := by exact prefixLift 2255513
  have htrace : WordTrace (prefixWord ++ tailWord_2255513) baseStart_2255513 baseEnd_2255513 := by
    simpa [prefixWord, tailWord_2255513, baseEnd_2255513] using wordTrace_append hprefix tailTrace_2255513
  have hstable : (prefixWord ++ tailWord_2255513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255513).length < 2 ^ (prefixWord ++ tailWord_2255513).sum := by decide
  have hdescent : baseEnd_2255513 < baseStart_2255513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255601 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2255601 : Nat := 118140960795 + 2255601 * 2 ^ 59
def prefixEnd_2255601 : Nat := 4983230072969 + 3 ^ 40 * 2255601 * 2
def baseEnd_2255601 : Nat := 772138318508089789609457

theorem tailTrace_2255601 : CollatzResearch.WordTrace tailWord_2255601 prefixEnd_2255601 772138318508089789609457 := by
  unfold tailWord_2255601
  simp only [CollatzResearch.WordTrace]
  refine ⟨82268527101350277826502657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54845684734233518551001771 82268527101350277826502657)
  ·
    refine ⟨61701395326012708369876993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82268527101350277826502657 61701395326012708369876993)
    ·
      refine ⟨46276046494509531277407745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61701395326012708369876993 46276046494509531277407745)
      ·
        refine ⟨34707034870882148458055809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46276046494509531277407745 34707034870882148458055809)
        ·
          refine ⟨26030276153161611343541857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34707034870882148458055809 26030276153161611343541857)
          ·
            refine ⟨19522707114871208507656393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26030276153161611343541857 19522707114871208507656393)
            ·
              refine ⟨14642030336153406380742295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19522707114871208507656393 14642030336153406380742295)
              ·
                refine ⟨21963045504230109571113443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14642030336153406380742295 21963045504230109571113443)
                ·
                  refine ⟨32944568256345164356670165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21963045504230109571113443 32944568256345164356670165)
                  ·
                    refine ⟨772138318508089789609457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32944568256345164356670165 772138318508089789609457)
                    ·
                      rfl

theorem cell22_2255601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2255601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255601 prefixEnd_2255601 := by exact prefixLift 2255601
  have htrace : WordTrace (prefixWord ++ tailWord_2255601) baseStart_2255601 baseEnd_2255601 := by
    simpa [prefixWord, tailWord_2255601, baseEnd_2255601] using wordTrace_append hprefix tailTrace_2255601
  have hstable : (prefixWord ++ tailWord_2255601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255601).length < 2 ^ (prefixWord ++ tailWord_2255601).sum := by decide
  have hdescent : baseEnd_2255601 < baseStart_2255601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255633 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2255633 : Nat := 118140960795 + 2255633 * 2 ^ 59
def prefixEnd_2255633 : Nat := 4983230072969 + 3 ^ 40 * 2255633 * 2
def baseEnd_2255633 : Nat := 772149272762052372809359

theorem tailTrace_2255633 : CollatzResearch.WordTrace tailWord_2255633 prefixEnd_2255633 772149272762052372809359 := by
  unfold tailWord_2255633
  simp only [CollatzResearch.WordTrace]
  refine ⟨82269694237234347291667553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54846462824822898194445035 82269694237234347291667553)
  ·
    refine ⟨61702270677925760468750665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82269694237234347291667553 61702270677925760468750665)
    ·
      refine ⟨46276703008444320351562999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61702270677925760468750665 46276703008444320351562999)
      ·
        refine ⟨69415054512666480527344499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46276703008444320351562999 69415054512666480527344499)
        ·
          refine ⟨104122581768999720791016749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69415054512666480527344499 104122581768999720791016749)
          ·
            refine ⟨39045968163374895296631281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104122581768999720791016749 39045968163374895296631281)
            ·
              refine ⟨29284476122531171472473461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39045968163374895296631281 29284476122531171472473461)
              ·
                refine ⟨2745419636487297325544387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29284476122531171472473461 2745419636487297325544387)
                ·
                  refine ⟨4118129454730945988316581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745419636487297325544387 4118129454730945988316581)
                  ·
                    refine ⟨772149272762052372809359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118129454730945988316581 772149272762052372809359)
                    ·
                      rfl

theorem cell22_2255633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2255633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255633 prefixEnd_2255633 := by exact prefixLift 2255633
  have htrace : WordTrace (prefixWord ++ tailWord_2255633) baseStart_2255633 baseEnd_2255633 := by
    simpa [prefixWord, tailWord_2255633, baseEnd_2255633] using wordTrace_append hprefix tailTrace_2255633
  have hstable : (prefixWord ++ tailWord_2255633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255633).length < 2 ^ (prefixWord ++ tailWord_2255633).sum := by decide
  have hdescent : baseEnd_2255633 < baseStart_2255633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255684 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2255684 : Nat := 118140960795 + 2255684 * 2 ^ 59
def prefixEnd_2255684 : Nat := 4983230072969 + 3 ^ 40 * 2255684 * 2
def baseEnd_2255684 : Nat := 772166731104305239784203

theorem tailTrace_2255684 : CollatzResearch.WordTrace tailWord_2255684 prefixEnd_2255684 772166731104305239784203 := by
  unfold tailWord_2255684
  simp only [CollatzResearch.WordTrace]
  refine ⟨41135777180024791500887053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54847702906699722001182737 41135777180024791500887053)
  ·
    refine ⟨15425916442509296812832645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41135777180024791500887053 15425916442509296812832645)
    ·
      refine ⟨2892359332970493152406121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15425916442509296812832645 2892359332970493152406121)
      ·
        refine ⟨2169269499727869864304591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2892359332970493152406121 2169269499727869864304591)
        ·
          refine ⟨3253904249591804796456887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169269499727869864304591 3253904249591804796456887)
          ·
            refine ⟨4880856374387707194685331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253904249591804796456887 4880856374387707194685331)
            ·
              refine ⟨7321284561581560792027997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880856374387707194685331 7321284561581560792027997)
              ·
                refine ⟨2745481710593085297010499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7321284561581560792027997 2745481710593085297010499)
                ·
                  refine ⟨4118222565889627945515749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745481710593085297010499 4118222565889627945515749)
                  ·
                    refine ⟨772166731104305239784203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118222565889627945515749 772166731104305239784203)
                    ·
                      rfl

theorem cell22_2255684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2255684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255684 prefixEnd_2255684 := by exact prefixLift 2255684
  have htrace : WordTrace (prefixWord ++ tailWord_2255684) baseStart_2255684 baseEnd_2255684 := by
    simpa [prefixWord, tailWord_2255684, baseEnd_2255684] using wordTrace_append hprefix tailTrace_2255684
  have hstable : (prefixWord ++ tailWord_2255684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255684).length < 2 ^ (prefixWord ++ tailWord_2255684).sum := by decide
  have hdescent : baseEnd_2255684 < baseStart_2255684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255691 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_2255691 : Nat := 118140960795 + 2255691 * 2 ^ 59
def prefixEnd_2255691 : Nat := 4983230072969 + 3 ^ 40 * 2255691 * 2
def baseEnd_2255691 : Nat := 772169127347359554859181

theorem tailTrace_2255691 : CollatzResearch.WordTrace tailWord_2255691 prefixEnd_2255691 772169127347359554859181 := by
  unfold tailWord_2255691
  simp only [CollatzResearch.WordTrace]
  refine ⟨82271809671024223197278927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54847873114016148798185951 82271809671024223197278927)
  ·
    refine ⟨123407714506536334795918391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82271809671024223197278927 123407714506536334795918391)
    ·
      refine ⟨185111571759804502193877587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123407714506536334795918391 185111571759804502193877587)
      ·
        refine ⟨277667357639706753290816381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185111571759804502193877587 277667357639706753290816381)
        ·
          refine ⟨104125259114890032484056143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277667357639706753290816381 104125259114890032484056143)
          ·
            refine ⟨156187888672335048726084215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104125259114890032484056143 156187888672335048726084215)
            ·
              refine ⟨234281833008502573089126323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156187888672335048726084215 234281833008502573089126323)
              ·
                refine ⟨351422749512753859633689485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234281833008502573089126323 351422749512753859633689485)
                ·
                  refine ⟨131783531067282697362633557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351422749512753859633689485 131783531067282697362633557)
                  ·
                    refine ⟨772169127347359554859181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131783531067282697362633557 772169127347359554859181)
                    ·
                      rfl

theorem cell22_2255691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_2255691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255691 prefixEnd_2255691 := by exact prefixLift 2255691
  have htrace : WordTrace (prefixWord ++ tailWord_2255691) baseStart_2255691 baseEnd_2255691 := by
    simpa [prefixWord, tailWord_2255691, baseEnd_2255691] using wordTrace_append hprefix tailTrace_2255691
  have hstable : (prefixWord ++ tailWord_2255691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255691).length < 2 ^ (prefixWord ++ tailWord_2255691).sum := by decide
  have hdescent : baseEnd_2255691 < baseStart_2255691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255714 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2255714 : Nat := 118140960795 + 2255714 * 2 ^ 59
def prefixEnd_2255714 : Nat := 4983230072969 + 3 ^ 40 * 2255714 * 2
def baseEnd_2255714 : Nat := 772177000717395161534111

theorem tailTrace_2255714 : CollatzResearch.WordTrace tailWord_2255714 prefixEnd_2255714 772177000717395161534111 := by
  unfold tailWord_2255714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568162137485224531341549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54848432366627265416910797 20568162137485224531341549)
  ·
    refine ⟨7713060801556959199253081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20568162137485224531341549 7713060801556959199253081)
    ·
      refine ⟨5784795601167719399439811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713060801556959199253081 5784795601167719399439811)
      ·
        refine ⟨8677193401751579099159717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784795601167719399439811 8677193401751579099159717)
        ·
          refine ⟨1626973762828421081092447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8677193401751579099159717 1626973762828421081092447)
          ·
            refine ⟨2440460644242631621638671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626973762828421081092447 2440460644242631621638671)
            ·
              refine ⟨3660690966363947432458007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440460644242631621638671 3660690966363947432458007)
              ·
                refine ⟨5491036449545921148687011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660690966363947432458007 5491036449545921148687011)
                ·
                  refine ⟨8236554674318881723030517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491036449545921148687011 8236554674318881723030517)
                  ·
                    refine ⟨772177000717395161534111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8236554674318881723030517 772177000717395161534111)
                    ·
                      rfl

theorem cell22_2255714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2255714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255714 prefixEnd_2255714 := by exact prefixLift 2255714
  have htrace : WordTrace (prefixWord ++ tailWord_2255714) baseStart_2255714 baseEnd_2255714 := by
    simpa [prefixWord, tailWord_2255714, baseEnd_2255714] using wordTrace_append hprefix tailTrace_2255714
  have hstable : (prefixWord ++ tailWord_2255714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255714).length < 2 ^ (prefixWord ++ tailWord_2255714).sum := by decide
  have hdescent : baseEnd_2255714 < baseStart_2255714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
