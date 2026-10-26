import V185TrunkScan22Chunk257

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2301842 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2301842 : Nat := 118140960795 + 2301842 * 2 ^ 59
def prefixEnd_2301842 : Nat := 4983230072969 + 3 ^ 40 * 2301842 * 2
def baseEnd_2301842 : Nat := 787967557804458844192685

theorem tailTrace_2301842 : CollatzResearch.WordTrace tailWord_2301842 prefixEnd_2301842 787967557804458844192685 := by
  unfold tailWord_2301842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20988768731706758040140945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55970049951218021440375853 20988768731706758040140945)
  ·
    refine ⟨15741576548780068530105709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20988768731706758040140945 15741576548780068530105709)
    ·
      refine ⟨5903091205792525698789641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15741576548780068530105709 5903091205792525698789641)
      ·
        refine ⟨4427318404344394274092231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5903091205792525698789641 4427318404344394274092231)
        ·
          refine ⟨6640977606516591411138347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427318404344394274092231 6640977606516591411138347)
          ·
            refine ⟨9961466409774887116707521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640977606516591411138347 9961466409774887116707521)
            ·
              refine ⟨7471099807331165337530641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9961466409774887116707521 7471099807331165337530641)
              ·
                refine ⟨5603324855498374003147981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7471099807331165337530641 5603324855498374003147981)
                ·
                  refine ⟨2101246820811890251180493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603324855498374003147981 2101246820811890251180493)
                  ·
                    refine ⟨787967557804458844192685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101246820811890251180493 787967557804458844192685)
                    ·
                      rfl

theorem cell22_2301842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2301842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301842 prefixEnd_2301842 := by exact prefixLift 2301842
  have htrace : WordTrace (prefixWord ++ tailWord_2301842) baseStart_2301842 baseEnd_2301842 := by
    simpa [prefixWord, tailWord_2301842, baseEnd_2301842] using wordTrace_append hprefix tailTrace_2301842
  have hstable : (prefixWord ++ tailWord_2301842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301842).length < 2 ^ (prefixWord ++ tailWord_2301842).sum := by decide
  have hdescent : baseEnd_2301842 < baseStart_2301842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301876 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2301876 : Nat := 118140960795 + 2301876 * 2 ^ 59
def prefixEnd_2301876 : Nat := 4983230072969 + 3 ^ 40 * 2301876 * 2
def baseEnd_2301876 : Nat := 787979196699294088842581

theorem tailTrace_2301876 : CollatzResearch.WordTrace tailWord_2301876 prefixEnd_2301876 787979196699294088842581 := by
  unfold tailWord_2301876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41978157504351927983650741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55970876672469237311534321 41978157504351927983650741)
  ·
    refine ⟨3935452266032993248467257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41978157504351927983650741 3935452266032993248467257)
    ·
      refine ⟨2951589199524744936350443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3935452266032993248467257 2951589199524744936350443)
      ·
        refine ⟨4427383799287117404525665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951589199524744936350443 4427383799287117404525665)
        ·
          refine ⟨3320537849465338053394249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4427383799287117404525665 3320537849465338053394249)
          ·
            refine ⟨2490403387099003540045687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320537849465338053394249 2490403387099003540045687)
            ·
              refine ⟨3735605080648505310068531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490403387099003540045687 3735605080648505310068531)
              ·
                refine ⟨5603407620972757965102797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735605080648505310068531 5603407620972757965102797)
                ·
                  refine ⟨2101277857864784236913549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603407620972757965102797 2101277857864784236913549)
                  ·
                    refine ⟨787979196699294088842581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101277857864784236913549 787979196699294088842581)
                    ·
                      rfl

theorem cell22_2301876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2301876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301876 prefixEnd_2301876 := by exact prefixLift 2301876
  have htrace : WordTrace (prefixWord ++ tailWord_2301876) baseStart_2301876 baseEnd_2301876 := by
    simpa [prefixWord, tailWord_2301876, baseEnd_2301876] using wordTrace_append hprefix tailTrace_2301876
  have hstable : (prefixWord ++ tailWord_2301876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301876).length < 2 ^ (prefixWord ++ tailWord_2301876).sum := by decide
  have hdescent : baseEnd_2301876 < baseStart_2301876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301930 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2301930 : Nat := 118140960795 + 2301930 * 2 ^ 59
def prefixEnd_2301930 : Nat := 4983230072969 + 3 ^ 40 * 2301930 * 2
def baseEnd_2301930 : Nat := 787997682002855947992415

theorem tailTrace_2301930 : CollatzResearch.WordTrace tailWord_2301930 prefixEnd_2301930 787997682002855947992415 := by
  unfold tailWord_2301930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20989571137627055797441811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55972189700338815459844829 20989571137627055797441811)
  ·
    refine ⟨31484356706440583696162717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20989571137627055797441811 31484356706440583696162717)
    ·
      refine ⟨11806633764915218886061019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31484356706440583696162717 11806633764915218886061019)
      ·
        refine ⟨17709950647372828329091529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806633764915218886061019 17709950647372828329091529)
        ·
          refine ⟨13282462985529621246818647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17709950647372828329091529 13282462985529621246818647)
          ·
            refine ⟨19923694478294431870227971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13282462985529621246818647 19923694478294431870227971)
            ·
              refine ⟨29885541717441647805341957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19923694478294431870227971 29885541717441647805341957)
              ·
                refine ⟨5603539072020308963501617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29885541717441647805341957 5603539072020308963501617)
                ·
                  refine ⟨4202654304015231722626213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5603539072020308963501617 4202654304015231722626213)
                  ·
                    refine ⟨787997682002855947992415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202654304015231722626213 787997682002855947992415)
                    ·
                      rfl

theorem cell22_2301930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2301930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301930 prefixEnd_2301930 := by exact prefixLift 2301930
  have htrace : WordTrace (prefixWord ++ tailWord_2301930) baseStart_2301930 baseEnd_2301930 := by
    simpa [prefixWord, tailWord_2301930, baseEnd_2301930] using wordTrace_append hprefix tailTrace_2301930
  have hstable : (prefixWord ++ tailWord_2301930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301930).length < 2 ^ (prefixWord ++ tailWord_2301930).sum := by decide
  have hdescent : baseEnd_2301930 < baseStart_2301930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301934 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2301934 : Nat := 118140960795 + 2301934 * 2 ^ 59
def prefixEnd_2301934 : Nat := 4983230072969 + 3 ^ 40 * 2301934 * 2
def baseEnd_2301934 : Nat := 262666350428200423630801

theorem tailTrace_2301934 : CollatzResearch.WordTrace tailWord_2301934 prefixEnd_2301934 262666350428200423630801 := by
  unfold tailWord_2301934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10494803805311716484114107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55972286961662487915275237 10494803805311716484114107)
  ·
    refine ⟨15742205707967574726171161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10494803805311716484114107 15742205707967574726171161)
    ·
      refine ⟨11806654280975681044628371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15742205707967574726171161 11806654280975681044628371)
      ·
        refine ⟨17709981421463521566942557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806654280975681044628371 17709981421463521566942557)
        ·
          refine ⟨6641243033048820587603459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17709981421463521566942557 6641243033048820587603459)
          ·
            refine ⟨9961864549573230881405189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641243033048820587603459 9961864549573230881405189)
            ·
              refine ⟨1867849603044980790263473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9961864549573230881405189 1867849603044980790263473)
              ·
                refine ⟨1400887202283735592697605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867849603044980790263473 1400887202283735592697605)
                ·
                  refine ⟨262666350428200423630801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400887202283735592697605 262666350428200423630801)
                  ·
                    rfl

theorem cell22_2301934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2301934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301934 prefixEnd_2301934 := by exact prefixLift 2301934
  have htrace : WordTrace (prefixWord ++ tailWord_2301934) baseStart_2301934 baseEnd_2301934 := by
    simpa [prefixWord, tailWord_2301934, baseEnd_2301934] using wordTrace_append hprefix tailTrace_2301934
  have hstable : (prefixWord ++ tailWord_2301934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301934).length < 2 ^ (prefixWord ++ tailWord_2301934).sum := by decide
  have hdescent : baseEnd_2301934 < baseStart_2301934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301945 : List Nat := [1, 2, 1, 3, 1, 6, 1, 7]
def baseStart_2301945 : Nat := 118140960795 + 2301945 * 2 ^ 59
def prefixEnd_2301945 : Nat := 4983230072969 + 3 ^ 40 * 2301945 * 2
def baseEnd_2301945 : Nat := 87555868534377878763041

theorem tailTrace_2301945 : CollatzResearch.WordTrace tailWord_2301945 prefixEnd_2301945 87555868534377878763041 := by
  unfold tailWord_2301945
  simp only [CollatzResearch.WordTrace]
  refine ⟨83958831645453880751563289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55972554430302587167708859 83958831645453880751563289)
  ·
    refine ⟨62969123734090410563672467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83958831645453880751563289 62969123734090410563672467)
    ·
      refine ⟨94453685601135615845508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62969123734090410563672467 94453685601135615845508701)
      ·
        refine ⟨35420132100425855942065763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94453685601135615845508701 35420132100425855942065763)
        ·
          refine ⟨53130198150638783913098645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35420132100425855942065763 53130198150638783913098645)
          ·
            refine ⟨2490478038311192995926499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53130198150638783913098645 2490478038311192995926499)
            ·
              refine ⟨3735717057466789493889749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490478038311192995926499 3735717057466789493889749)
              ·
                refine ⟨87555868534377878763041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3735717057466789493889749 87555868534377878763041)
                ·
                  rfl

theorem cell22_2301945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 7].length) (baseStart_2301945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301945 prefixEnd_2301945 := by exact prefixLift 2301945
  have htrace : WordTrace (prefixWord ++ tailWord_2301945) baseStart_2301945 baseEnd_2301945 := by
    simpa [prefixWord, tailWord_2301945, baseEnd_2301945] using wordTrace_append hprefix tailTrace_2301945
  have hstable : (prefixWord ++ tailWord_2301945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301945).length < 2 ^ (prefixWord ++ tailWord_2301945).sum := by decide
  have hdescent : baseEnd_2301945 < baseStart_2301945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301962 : List Nat := [3, 1, 2, 2, 4, 1, 3, 6]
def baseStart_2301962 : Nat := 118140960795 + 2301962 * 2 ^ 59
def prefixEnd_2301962 : Nat := 4983230072969 + 3 ^ 40 * 2301962 * 2
def baseEnd_2301962 : Nat := 87556515139646503465813

theorem tailTrace_2301962 : CollatzResearch.WordTrace tailWord_2301962 prefixEnd_2301962 87556515139646503465813 := by
  unfold tailWord_2301962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20989862921598073163733035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55972967790928195103288093 20989862921598073163733035)
  ·
    refine ⟨31484794382397109745599553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20989862921598073163733035 31484794382397109745599553)
    ·
      refine ⟨23613595786797832309199665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31484794382397109745599553 23613595786797832309199665)
      ·
        refine ⟨17710196840098374231899749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23613595786797832309199665 17710196840098374231899749)
        ·
          refine ⟨3320661907518445168481203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17710196840098374231899749 3320661907518445168481203)
          ·
            refine ⟨4980992861277667752721805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320661907518445168481203 4980992861277667752721805)
            ·
              refine ⟨1867872322979125407270677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4980992861277667752721805 1867872322979125407270677)
              ·
                refine ⟨87556515139646503465813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867872322979125407270677 87556515139646503465813)
                ·
                  rfl

theorem cell22_2301962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_2301962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301962 prefixEnd_2301962 := by exact prefixLift 2301962
  have htrace : WordTrace (prefixWord ++ tailWord_2301962) baseStart_2301962 baseEnd_2301962 := by
    simpa [prefixWord, tailWord_2301962, baseEnd_2301962] using wordTrace_append hprefix tailTrace_2301962
  have hstable : (prefixWord ++ tailWord_2301962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301962).length < 2 ^ (prefixWord ++ tailWord_2301962).sum := by decide
  have hdescent : baseEnd_2301962 < baseStart_2301962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301994 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2301994 : Nat := 118140960795 + 2301994 * 2 ^ 59
def prefixEnd_2301994 : Nat := 4983230072969 + 3 ^ 40 * 2301994 * 2
def baseEnd_2301994 : Nat := 788019590510781114392219

theorem tailTrace_2301994 : CollatzResearch.WordTrace tailWord_2301994 prefixEnd_2301994 788019590510781114392219 := by
  unfold tailWord_2301994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990154705569090530024259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55973745881517574746731357 20990154705569090530024259)
  ·
    refine ⟨31485232058353635795036389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20990154705569090530024259 31485232058353635795036389)
    ·
      refine ⟨5903481010941306711569323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31485232058353635795036389 5903481010941306711569323)
      ·
        refine ⟨8855221516411960067353985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5903481010941306711569323 8855221516411960067353985)
        ·
          refine ⟨6641416137308970050515489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8855221516411960067353985 6641416137308970050515489)
          ·
            refine ⟨4981062102981727537886617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6641416137308970050515489 4981062102981727537886617)
            ·
              refine ⟨3735796577236295653414963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981062102981727537886617 3735796577236295653414963)
              ·
                refine ⟨5603694865854443480122445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735796577236295653414963 5603694865854443480122445)
                ·
                  refine ⟨2101385574695416305045917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603694865854443480122445 2101385574695416305045917)
                  ·
                    refine ⟨788019590510781114392219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101385574695416305045917 788019590510781114392219)
                    ·
                      rfl

theorem cell22_2301994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2301994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301994 prefixEnd_2301994 := by exact prefixLift 2301994
  have htrace : WordTrace (prefixWord ++ tailWord_2301994) baseStart_2301994 baseEnd_2301994 := by
    simpa [prefixWord, tailWord_2301994, baseEnd_2301994] using wordTrace_append hprefix tailTrace_2301994
  have hstable : (prefixWord ++ tailWord_2301994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301994).length < 2 ^ (prefixWord ++ tailWord_2301994).sum := by decide
  have hdescent : baseEnd_2301994 < baseStart_2301994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302005 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2302005 : Nat := 118140960795 + 2302005 * 2 ^ 59
def prefixEnd_2302005 : Nat := 4983230072969 + 3 ^ 40 * 2302005 * 2
def baseEnd_2302005 : Nat := 788023356035580752367185

theorem tailTrace_2302005 : CollatzResearch.WordTrace tailWord_2302005 prefixEnd_2302005 788023356035580752367185 := by
  unfold tailWord_2302005
  simp only [CollatzResearch.WordTrace]
  refine ⟨83961020025236510998747469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55974013350157673999164979 83961020025236510998747469)
  ·
    refine ⟨31485382509463691624530301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83961020025236510998747469 31485382509463691624530301)
    ·
      refine ⟨11807018441048884359198863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31485382509463691624530301 11807018441048884359198863)
      ·
        refine ⟨17710527661573326538798295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11807018441048884359198863 17710527661573326538798295)
        ·
          refine ⟨26565791492359989808197443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17710527661573326538798295 26565791492359989808197443)
          ·
            refine ⟨39848687238539984712296165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26565791492359989808197443 39848687238539984712296165)
            ·
              refine ⟨7471628857226247133555531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39848687238539984712296165 7471628857226247133555531)
              ·
                refine ⟨11207443285839370700333297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7471628857226247133555531 11207443285839370700333297)
                ·
                  refine ⟨8405582464379528025249973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11207443285839370700333297 8405582464379528025249973)
                  ·
                    refine ⟨788023356035580752367185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8405582464379528025249973 788023356035580752367185)
                    ·
                      rfl

theorem cell22_2302005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2302005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302005 prefixEnd_2302005 := by exact prefixLift 2302005
  have htrace : WordTrace (prefixWord ++ tailWord_2302005) baseStart_2302005 baseEnd_2302005 := by
    simpa [prefixWord, tailWord_2302005, baseEnd_2302005] using wordTrace_append hprefix tailTrace_2302005
  have hstable : (prefixWord ++ tailWord_2302005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302005).length < 2 ^ (prefixWord ++ tailWord_2302005).sum := by decide
  have hdescent : baseEnd_2302005 < baseStart_2302005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302037 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2302037 : Nat := 118140960795 + 2302037 * 2 ^ 59
def prefixEnd_2302037 : Nat := 4983230072969 + 3 ^ 40 * 2302037 * 2
def baseEnd_2302037 : Nat := 788034310289543335567087

theorem tailTrace_2302037 : CollatzResearch.WordTrace tailWord_2302037 prefixEnd_2302037 788034310289543335567087 := by
  unfold tailWord_2302037
  simp only [CollatzResearch.WordTrace]
  refine ⟨83962187161120580463912365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55974791440747053642608243 83962187161120580463912365)
  ·
    refine ⟨31485820185420217673967137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83962187161120580463912365 31485820185420217673967137)
    ·
      refine ⟨23614365139065163255475353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31485820185420217673967137 23614365139065163255475353)
      ·
        refine ⟨17710773854298872441606515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23614365139065163255475353 17710773854298872441606515)
        ·
          refine ⟨26566160781448308662409773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17710773854298872441606515 26566160781448308662409773)
          ·
            refine ⟨9962310293043115748403665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26566160781448308662409773 9962310293043115748403665)
            ·
              refine ⟨7471732719782336811302749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9962310293043115748403665 7471732719782336811302749)
              ·
                refine ⟨2801899769918376304238531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7471732719782336811302749 2801899769918376304238531)
                ·
                  refine ⟨4202849654877564456357797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801899769918376304238531 4202849654877564456357797)
                  ·
                    refine ⟨788034310289543335567087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202849654877564456357797 788034310289543335567087)
                    ·
                      rfl

theorem cell22_2302037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2302037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302037 prefixEnd_2302037 := by exact prefixLift 2302037
  have htrace : WordTrace (prefixWord ++ tailWord_2302037) baseStart_2302037 baseEnd_2302037 := by
    simpa [prefixWord, tailWord_2302037, baseEnd_2302037] using wordTrace_append hprefix tailTrace_2302037
  have hstable : (prefixWord ++ tailWord_2302037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302037).length < 2 ^ (prefixWord ++ tailWord_2302037).sum := by decide
  have hdescent : baseEnd_2302037 < baseStart_2302037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302052 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_2302052 : Nat := 118140960795 + 2302052 * 2 ^ 59
def prefixEnd_2302052 : Nat := 4983230072969 + 3 ^ 40 * 2302052 * 2
def baseEnd_2302052 : Nat := 262679815032029432147347

theorem tailTrace_2302052 : CollatzResearch.WordTrace tailWord_2302052 prefixEnd_2302052 262679815032029432147347 := by
  unfold tailWord_2302052
  simp only [CollatzResearch.WordTrace]
  refine ⟨41981367128033119012854205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55975156170710825350472273 41981367128033119012854205)
  ·
    refine ⟨15743012673012419629820327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41981367128033119012854205 15743012673012419629820327)
    ·
      refine ⟨23614519009518629444730491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15743012673012419629820327 23614519009518629444730491)
      ·
        refine ⟨35421778514277944167095737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23614519009518629444730491 35421778514277944167095737)
        ·
          refine ⟨26566333885708458125321803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35421778514277944167095737 26566333885708458125321803)
          ·
            refine ⟨39849500828562687187982705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26566333885708458125321803 39849500828562687187982705)
            ·
              refine ⟨29887125621422015390987029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39849500828562687187982705 29887125621422015390987029)
              ·
                refine ⟨1400959013504156971452517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29887125621422015390987029 1400959013504156971452517)
                ·
                  refine ⟨262679815032029432147347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400959013504156971452517 262679815032029432147347)
                  ·
                    rfl

theorem cell22_2302052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_2302052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302052 prefixEnd_2302052 := by exact prefixLift 2302052
  have htrace : WordTrace (prefixWord ++ tailWord_2302052) baseStart_2302052 baseEnd_2302052 := by
    simpa [prefixWord, tailWord_2302052, baseEnd_2302052] using wordTrace_append hprefix tailTrace_2302052
  have hstable : (prefixWord ++ tailWord_2302052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302052).length < 2 ^ (prefixWord ++ tailWord_2302052).sum := by decide
  have hdescent : baseEnd_2302052 < baseStart_2302052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302065 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2302065 : Nat := 118140960795 + 2302065 * 2 ^ 59
def prefixEnd_2302065 : Nat := 4983230072969 + 3 ^ 40 * 2302065 * 2
def baseEnd_2302065 : Nat := 788043895261760595867001

theorem tailTrace_2302065 : CollatzResearch.WordTrace tailWord_2302065 prefixEnd_2302065 788043895261760595867001 := by
  unfold tailWord_2302065
  simp only [CollatzResearch.WordTrace]
  refine ⟨83963208405019141245931649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55975472270012760830621099 83963208405019141245931649)
  ·
    refine ⟨62972406303764355934448737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83963208405019141245931649 62972406303764355934448737)
    ·
      refine ⟨47229304727823266950836553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62972406303764355934448737 47229304727823266950836553)
      ·
        refine ⟨35421978545867450213127415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47229304727823266950836553 35421978545867450213127415)
        ·
          refine ⟨53132967818801175319691123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35421978545867450213127415 53132967818801175319691123)
          ·
            refine ⟨79699451728201762979536685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53132967818801175319691123 79699451728201762979536685)
            ·
              refine ⟨29887294398075661117326257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79699451728201762979536685 29887294398075661117326257)
              ·
                refine ⟨22415470798556745837994693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29887294398075661117326257 22415470798556745837994693)
                ·
                  refine ⟨4202900774729389844624005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22415470798556745837994693 4202900774729389844624005)
                  ·
                    refine ⟨788043895261760595867001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202900774729389844624005 788043895261760595867001)
                    ·
                      rfl

theorem cell22_2302065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2302065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302065 prefixEnd_2302065 := by exact prefixLift 2302065
  have htrace : WordTrace (prefixWord ++ tailWord_2302065) baseStart_2302065 baseEnd_2302065 := by
    simpa [prefixWord, tailWord_2302065, baseEnd_2302065] using wordTrace_append hprefix tailTrace_2302065
  have hstable : (prefixWord ++ tailWord_2302065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302065).length < 2 ^ (prefixWord ++ tailWord_2302065).sum := by decide
  have hdescent : baseEnd_2302065 < baseStart_2302065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302103 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 4]
def baseStart_2302103 : Nat := 118140960795 + 2302103 * 2 ^ 59
def prefixEnd_2302103 : Nat := 4983230072969 + 3 ^ 40 * 2302103 * 2
def baseEnd_2302103 : Nat := 262685634479447054472295

theorem tailTrace_2302103 : CollatzResearch.WordTrace tailWord_2302103 prefixEnd_2302103 262685634479447054472295 := by
  unfold tailWord_2302103
  simp only [CollatzResearch.WordTrace]
  refine ⟨83964594378881473735814963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55976396252587649157209975 83964594378881473735814963)
  ·
    refine ⟨125946891568322210603722445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83964594378881473735814963 125946891568322210603722445)
    ·
      refine ⟨47230084338120828976395917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125946891568322210603722445 47230084338120828976395917)
      ·
        refine ⟨17711281626795310866148469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47230084338120828976395917 17711281626795310866148469)
        ·
          refine ⟨1660432652512060393701419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17711281626795310866148469 1660432652512060393701419)
          ·
            refine ⟨2490648978768090590552129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660432652512060393701419 2490648978768090590552129)
            ·
              refine ⟨1867986734076067942914097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490648978768090590552129 1867986734076067942914097)
              ·
                refine ⟨1400990050557050957185573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867986734076067942914097 1400990050557050957185573)
                ·
                  refine ⟨262685634479447054472295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400990050557050957185573 262685634479447054472295)
                  ·
                    rfl

theorem cell22_2302103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 4].length) (baseStart_2302103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302103 prefixEnd_2302103 := by exact prefixLift 2302103
  have htrace : WordTrace (prefixWord ++ tailWord_2302103) baseStart_2302103 baseEnd_2302103 := by
    simpa [prefixWord, tailWord_2302103, baseEnd_2302103] using wordTrace_append hprefix tailTrace_2302103
  have hstable : (prefixWord ++ tailWord_2302103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302103).length < 2 ^ (prefixWord ++ tailWord_2302103).sum := by decide
  have hdescent : baseEnd_2302103 < baseStart_2302103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302114 : List Nat := [3, 3, 1, 3, 1, 3, 1, 7]
def baseStart_2302114 : Nat := 118140960795 + 2302114 * 2 ^ 59
def prefixEnd_2302114 : Nat := 4983230072969 + 3 ^ 40 * 2302114 * 2
def baseEnd_2302114 : Nat := 87562296551460089043539

theorem tailTrace_2302114 : CollatzResearch.WordTrace tailWord_2302114 prefixEnd_2302114 87562296551460089043539 := by
  unfold tailWord_2302114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20991248895460405653616349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55976663721227748409643597 20991248895460405653616349)
  ·
    refine ⟨7871718335797652120106131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20991248895460405653616349 7871718335797652120106131)
    ·
      refine ⟨11807577503696478180159197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871718335797652120106131 11807577503696478180159197)
      ·
        refine ⟨4427841563886179317559699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11807577503696478180159197 4427841563886179317559699)
        ·
          refine ⟨6641762345829268976339549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427841563886179317559699 6641762345829268976339549)
          ·
            refine ⟨2490660879685975866127331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6641762345829268976339549 2490660879685975866127331)
            ·
              refine ⟨3735991319528963799190997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490660879685975866127331 3735991319528963799190997)
              ·
                refine ⟨87562296551460089043539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3735991319528963799190997 87562296551460089043539)
                ·
                  rfl

theorem cell22_2302114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_2302114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302114 prefixEnd_2302114 := by exact prefixLift 2302114
  have htrace : WordTrace (prefixWord ++ tailWord_2302114) baseStart_2302114 baseEnd_2302114 := by
    simpa [prefixWord, tailWord_2302114, baseEnd_2302114] using wordTrace_append hprefix tailTrace_2302114
  have hstable : (prefixWord ++ tailWord_2302114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302114).length < 2 ^ (prefixWord ++ tailWord_2302114).sum := by decide
  have hdescent : baseEnd_2302114 < baseStart_2302114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302133 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2302133 : Nat := 118140960795 + 2302133 * 2 ^ 59
def prefixEnd_2302133 : Nat := 4983230072969 + 3 ^ 40 * 2302133 * 2
def baseEnd_2302133 : Nat := 788067173051431085166793

theorem tailTrace_2302133 : CollatzResearch.WordTrace tailWord_2302133 prefixEnd_2302133 788067173051431085166793 := by
  unfold tailWord_2302133
  simp only [CollatzResearch.WordTrace]
  refine ⟨83965688568772788859407053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55977125712515192572938035 83965688568772788859407053)
  ·
    refine ⟨31487133213289795822277645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83965688568772788859407053 31487133213289795822277645)
    ·
      refine ⟨11807674954983673433354117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31487133213289795822277645 11807674954983673433354117)
      ·
        refine ⟨2213939054059438768753897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11807674954983673433354117 2213939054059438768753897)
        ·
          refine ⟨1660454290544579076565423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213939054059438768753897 1660454290544579076565423)
          ·
            refine ⟨2490681435816868614848135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660454290544579076565423 2490681435816868614848135)
            ·
              refine ⟨3736022153725302922272203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490681435816868614848135 3736022153725302922272203)
              ·
                refine ⟨5604033230587954383408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736022153725302922272203 5604033230587954383408305)
                ·
                  refine ⟨4203024922940965787556229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5604033230587954383408305 4203024922940965787556229)
                  ·
                    refine ⟨788067173051431085166793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203024922940965787556229 788067173051431085166793)
                    ·
                      rfl

theorem cell22_2302133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2302133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302133 prefixEnd_2302133 := by exact prefixLift 2302133
  have htrace : WordTrace (prefixWord ++ tailWord_2302133) baseStart_2302133 baseEnd_2302133 := by
    simpa [prefixWord, tailWord_2302133, baseEnd_2302133] using wordTrace_append hprefix tailTrace_2302133
  have hstable : (prefixWord ++ tailWord_2302133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302133).length < 2 ^ (prefixWord ++ tailWord_2302133).sum := by decide
  have hdescent : baseEnd_2302133 < baseStart_2302133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302217 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_2302217 : Nat := 118140960795 + 2302217 * 2 ^ 59
def prefixEnd_2302217 : Nat := 4983230072969 + 3 ^ 40 * 2302217 * 2
def baseEnd_2302217 : Nat := 788095927968082866066535

theorem tailTrace_2302217 : CollatzResearch.WordTrace tailWord_2302217 prefixEnd_2302217 788095927968082866066535 := by
  unfold tailWord_2302217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83968752300468471205464905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55979168200312314136976603 83968752300468471205464905)
  ·
    refine ⟨62976564225351353404098679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83968752300468471205464905 62976564225351353404098679)
    ·
      refine ⟨94464846338027030106148019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62976564225351353404098679 94464846338027030106148019)
      ·
        refine ⟨141697269507040545159222029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94464846338027030106148019 141697269507040545159222029)
        ·
          refine ⟨53136476065140204434708261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141697269507040545159222029 53136476065140204434708261)
          ·
            refine ⟨9963089262213788331507799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53136476065140204434708261 9963089262213788331507799)
            ·
              refine ⟨14944633893320682497261699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9963089262213788331507799 14944633893320682497261699)
              ·
                refine ⟨22416950839981023745892549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14944633893320682497261699 22416950839981023745892549)
                ·
                  refine ⟨4203178282496441952354853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22416950839981023745892549 4203178282496441952354853)
                  ·
                    refine ⟨788095927968082866066535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203178282496441952354853 788095927968082866066535)
                    ·
                      rfl

theorem cell22_2302217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_2302217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302217 prefixEnd_2302217 := by exact prefixLift 2302217
  have htrace : WordTrace (prefixWord ++ tailWord_2302217) baseStart_2302217 baseEnd_2302217 := by
    simpa [prefixWord, tailWord_2302217, baseEnd_2302217] using wordTrace_append hprefix tailTrace_2302217
  have hstable : (prefixWord ++ tailWord_2302217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302217).length < 2 ^ (prefixWord ++ tailWord_2302217).sum := by decide
  have hdescent : baseEnd_2302217 < baseStart_2302217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302219 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 2, 3]
def baseStart_2302219 : Nat := 118140960795 + 2302219 * 2 ^ 59
def prefixEnd_2302219 : Nat := 4983230072969 + 3 ^ 40 * 2302219 * 2
def baseEnd_2302219 : Nat := 788096612608955527516529

theorem tailTrace_2302219 : CollatzResearch.WordTrace tailWord_2302219 prefixEnd_2302219 788096612608955527516529 := by
  unfold tailWord_2302219
  simp only [CollatzResearch.WordTrace]
  refine ⟨83968825246461225547037711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55979216830974150364691807 83968825246461225547037711)
  ·
    refine ⟨125953237869691838320556567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83968825246461225547037711 125953237869691838320556567)
    ·
      refine ⟨188929856804537757480834851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125953237869691838320556567 188929856804537757480834851)
      ·
        refine ⟨283394785206806636221252277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188929856804537757480834851 283394785206806636221252277)
        ·
          refine ⟨26568261113138122145742401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283394785206806636221252277 26568261113138122145742401)
          ·
            refine ⟨19926195834853591609306801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26568261113138122145742401 19926195834853591609306801)
            ·
              refine ⟨14944646876140193706980101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19926195834853591609306801 14944646876140193706980101)
              ·
                refine ⟨2802121289276286320058769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14944646876140193706980101 2802121289276286320058769)
                ·
                  refine ⟨2101590966957214740044077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802121289276286320058769 2101590966957214740044077)
                  ·
                    refine ⟨788096612608955527516529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101590966957214740044077 788096612608955527516529)
                    ·
                      rfl

theorem cell22_2302219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].length) (baseStart_2302219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302219 prefixEnd_2302219 := by exact prefixLift 2302219
  have htrace : WordTrace (prefixWord ++ tailWord_2302219) baseStart_2302219 baseEnd_2302219 := by
    simpa [prefixWord, tailWord_2302219, baseEnd_2302219] using wordTrace_append hprefix tailTrace_2302219
  have hstable : (prefixWord ++ tailWord_2302219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302219).length < 2 ^ (prefixWord ++ tailWord_2302219).sum := by decide
  have hdescent : baseEnd_2302219 < baseStart_2302219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302232 : List Nat := [2, 1, 2, 3, 1, 2, 4, 7]
def baseStart_2302232 : Nat := 118140960795 + 2302232 * 2 ^ 59
def prefixEnd_2302232 : Nat := 4983230072969 + 3 ^ 40 * 2302232 * 2
def baseEnd_2302232 : Nat := 87566784752736425215721

theorem tailTrace_2302232 : CollatzResearch.WordTrace tailWord_2302232 prefixEnd_2302232 87566784752736425215721 := by
  unfold tailWord_2302232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41984649697707064383630475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55979532930276085844840633 41984649697707064383630475)
  ·
    refine ⟨62976974546560596575445713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41984649697707064383630475 62976974546560596575445713)
    ·
      refine ⟨47232730909920447431584285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62976974546560596575445713 47232730909920447431584285)
      ·
        refine ⟨17712274091220167786844107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47232730909920447431584285 17712274091220167786844107)
        ·
          refine ⟨26568411136830251680266161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17712274091220167786844107 26568411136830251680266161)
          ·
            refine ⟨19926308352622688760199621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26568411136830251680266161 19926308352622688760199621)
            ·
              refine ⟨3736182816116754142537429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19926308352622688760199621 3736182816116754142537429)
              ·
                refine ⟨87566784752736425215721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3736182816116754142537429 87566784752736425215721)
                ·
                  rfl

theorem cell22_2302232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_2302232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302232 prefixEnd_2302232 := by exact prefixLift 2302232
  have htrace : WordTrace (prefixWord ++ tailWord_2302232) baseStart_2302232 baseEnd_2302232 := by
    simpa [prefixWord, tailWord_2302232, baseEnd_2302232] using wordTrace_append hprefix tailTrace_2302232
  have hstable : (prefixWord ++ tailWord_2302232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302232).length < 2 ^ (prefixWord ++ tailWord_2302232).sum := by decide
  have hdescent : baseEnd_2302232 < baseStart_2302232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302433 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2302433 : Nat := 118140960795 + 2302433 * 2 ^ 59
def prefixEnd_2302433 : Nat := 4983230072969 + 3 ^ 40 * 2302433 * 2
def baseEnd_2302433 : Nat := 788169869182330302665873

theorem tailTrace_2302433 : CollatzResearch.WordTrace tailWord_2302433 prefixEnd_2302433 788169869182330302665873 := by
  unfold tailWord_2302433
  simp only [CollatzResearch.WordTrace]
  refine ⟨83976630467685940095327953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55984420311790626730218635 83976630467685940095327953)
  ·
    refine ⟨62982472850764455071495965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83976630467685940095327953 62982472850764455071495965)
    ·
      refine ⟨23618427319036670651810987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62982472850764455071495965 23618427319036670651810987)
      ·
        refine ⟨35427640978555005977716481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23618427319036670651810987 35427640978555005977716481)
        ·
          refine ⟨26570730733916254483287361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35427640978555005977716481 26570730733916254483287361)
          ·
            refine ⟨19928048050437190862465521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26570730733916254483287361 19928048050437190862465521)
            ·
              refine ⟨14946036037827893146849141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19928048050437190862465521 14946036037827893146849141)
              ·
                refine ⟨1401190878546364982517107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14946036037827893146849141 1401190878546364982517107)
                ·
                  refine ⟨2101786317819547473775661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401190878546364982517107 2101786317819547473775661)
                  ·
                    refine ⟨788169869182330302665873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101786317819547473775661 788169869182330302665873)
                    ·
                      rfl

theorem cell22_2302433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2302433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302433 prefixEnd_2302433 := by exact prefixLift 2302433
  have htrace : WordTrace (prefixWord ++ tailWord_2302433) baseStart_2302433 baseEnd_2302433 := by
    simpa [prefixWord, tailWord_2302433, baseEnd_2302433] using wordTrace_append hprefix tailTrace_2302433
  have hstable : (prefixWord ++ tailWord_2302433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302433).length < 2 ^ (prefixWord ++ tailWord_2302433).sum := by decide
  have hdescent : baseEnd_2302433 < baseStart_2302433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302444 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_2302444 : Nat := 118140960795 + 2302444 * 2 ^ 59
def prefixEnd_2302444 : Nat := 4983230072969 + 3 ^ 40 * 2302444 * 2
def baseEnd_2302444 : Nat := 788173634707129940640839

theorem tailTrace_2302444 : CollatzResearch.WordTrace tailWord_2302444 prefixEnd_2302444 788173634707129940640839 := by
  unfold tailWord_2302444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41988515835323044486989193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55984687780430725982652257 41988515835323044486989193)
  ·
    refine ⟨31491386876492283365241895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41988515835323044486989193 31491386876492283365241895)
    ·
      refine ⟨47237080314738425047862843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31491386876492283365241895 47237080314738425047862843)
      ·
        refine ⟨70855620472107637571794265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47237080314738425047862843 70855620472107637571794265)
        ·
          refine ⟨53141715354080728178845699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70855620472107637571794265 53141715354080728178845699)
          ·
            refine ⟨79712573031121092268268549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53141715354080728178845699 79712573031121092268268549)
            ·
              refine ⟨14946107443335204800300353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79712573031121092268268549 14946107443335204800300353)
              ·
                refine ⟨11209580582501403600225265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14946107443335204800300353 11209580582501403600225265)
                ·
                  refine ⟨8407185436876052700168949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11209580582501403600225265 8407185436876052700168949)
                  ·
                    refine ⟨788173634707129940640839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8407185436876052700168949 788173634707129940640839)
                    ·
                      rfl

theorem cell22_2302444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_2302444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302444 prefixEnd_2302444 := by exact prefixLift 2302444
  have htrace : WordTrace (prefixWord ++ tailWord_2302444) baseStart_2302444 baseEnd_2302444 := by
    simpa [prefixWord, tailWord_2302444, baseEnd_2302444] using wordTrace_append hprefix tailTrace_2302444
  have hstable : (prefixWord ++ tailWord_2302444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302444).length < 2 ^ (prefixWord ++ tailWord_2302444).sum := by decide
  have hdescent : baseEnd_2302444 < baseStart_2302444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302446 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2302446 : Nat := 118140960795 + 2302446 * 2 ^ 59
def prefixEnd_2302446 : Nat := 4983230072969 + 3 ^ 40 * 2302446 * 2
def baseEnd_2302446 : Nat := 262724773116000867363611

theorem tailTrace_2302446 : CollatzResearch.WordTrace tailWord_2302446 prefixEnd_2302446 262724773116000867363611 := by
  unfold tailWord_2302446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497138077079855414443899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55984736411092562210367461 10497138077079855414443899)
  ·
    refine ⟨15745707115619783121665849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10497138077079855414443899 15745707115619783121665849)
    ·
      refine ⟨11809280336714837341249387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15745707115619783121665849 11809280336714837341249387)
      ·
        refine ⟨17713920505072256011874081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11809280336714837341249387 17713920505072256011874081)
        ·
          refine ⟨13285440378804192008905561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17713920505072256011874081 13285440378804192008905561)
          ·
            refine ⟨9964080284103144006679171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13285440378804192008905561 9964080284103144006679171)
            ·
              refine ⟨14946120426154716010018757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9964080284103144006679171 14946120426154716010018757)
              ·
                refine ⟨2802397579904009251878517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14946120426154716010018757 2802397579904009251878517)
                ·
                  refine ⟨262724773116000867363611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802397579904009251878517 262724773116000867363611)
                  ·
                    rfl

theorem cell22_2302446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2302446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302446 prefixEnd_2302446 := by exact prefixLift 2302446
  have htrace : WordTrace (prefixWord ++ tailWord_2302446) baseStart_2302446 baseEnd_2302446 := by
    simpa [prefixWord, tailWord_2302446, baseEnd_2302446] using wordTrace_append hprefix tailTrace_2302446
  have hstable : (prefixWord ++ tailWord_2302446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302446).length < 2 ^ (prefixWord ++ tailWord_2302446).sum := by decide
  have hdescent : baseEnd_2302446 < baseStart_2302446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302476 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2302476 : Nat := 118140960795 + 2302476 * 2 ^ 59
def prefixEnd_2302476 : Nat := 4983230072969 + 3 ^ 40 * 2302476 * 2
def baseEnd_2302476 : Nat := 788184588961092523840741

theorem tailTrace_2302476 : CollatzResearch.WordTrace tailWord_2302476 prefixEnd_2302476 788184588961092523840741 := by
  unfold tailWord_2302476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989099403265079219571641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55985465871020105626095521 41989099403265079219571641)
  ·
    refine ⟨31491824552448809414678731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41989099403265079219571641 31491824552448809414678731)
    ·
      refine ⟨47237736828673214122018097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31491824552448809414678731 47237736828673214122018097)
      ·
        refine ⟨35428302621504910591513573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47237736828673214122018097 35428302621504910591513573)
        ·
          refine ⟨6642806741532170735908795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35428302621504910591513573 6642806741532170735908795)
          ·
            refine ⟨9964210112298256103863193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642806741532170735908795 9964210112298256103863193)
            ·
              refine ⟨7473157584223692077897395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9964210112298256103863193 7473157584223692077897395)
              ·
                refine ⟨11209736376335538116846093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7473157584223692077897395 11209736376335538116846093)
                ·
                  refine ⟨4203651141125826793817285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11209736376335538116846093 4203651141125826793817285)
                  ·
                    refine ⟨788184588961092523840741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203651141125826793817285 788184588961092523840741)
                    ·
                      rfl

theorem cell22_2302476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2302476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302476 prefixEnd_2302476 := by exact prefixLift 2302476
  have htrace : WordTrace (prefixWord ++ tailWord_2302476) baseStart_2302476 baseEnd_2302476 := by
    simpa [prefixWord, tailWord_2302476, baseEnd_2302476] using wordTrace_append hprefix tailTrace_2302476
  have hstable : (prefixWord ++ tailWord_2302476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302476).length < 2 ^ (prefixWord ++ tailWord_2302476).sum := by decide
  have hdescent : baseEnd_2302476 < baseStart_2302476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302493 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2302493 : Nat := 118140960795 + 2302493 * 2 ^ 59
def prefixEnd_2302493 : Nat := 4983230072969 + 3 ^ 40 * 2302493 * 2
def baseEnd_2302493 : Nat := 788190408408510146165689

theorem tailTrace_2302493 : CollatzResearch.WordTrace tailWord_2302493 prefixEnd_2302493 788190408408510146165689 := by
  unfold tailWord_2302493
  simp only [CollatzResearch.WordTrace]
  refine ⟨83978818847468570342512133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55985879231645713561674755 83978818847468570342512133)
  ·
    refine ⟨15746028533900356939221025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83978818847468570342512133 15746028533900356939221025)
    ·
      refine ⟨11809521400425267704415769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15746028533900356939221025 11809521400425267704415769)
      ·
        refine ⟨8857141050318950778311827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11809521400425267704415769 8857141050318950778311827)
        ·
          refine ⟨13285711575478426167467741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8857141050318950778311827 13285711575478426167467741)
          ·
            refine ⟨4982141840804409812800403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13285711575478426167467741 4982141840804409812800403)
            ·
              refine ⟨7473212761206614719200605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982141840804409812800403 7473212761206614719200605)
              ·
                refine ⟨2802454785452480519700227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7473212761206614719200605 2802454785452480519700227)
                ·
                  refine ⟨4203682178178720779550341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802454785452480519700227 4203682178178720779550341)
                  ·
                    refine ⟨788190408408510146165689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203682178178720779550341 788190408408510146165689)
                    ·
                      rfl

theorem cell22_2302493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2302493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302493 prefixEnd_2302493 := by exact prefixLift 2302493
  have htrace : WordTrace (prefixWord ++ tailWord_2302493) baseStart_2302493 baseEnd_2302493 := by
    simpa [prefixWord, tailWord_2302493, baseEnd_2302493] using wordTrace_append hprefix tailTrace_2302493
  have hstable : (prefixWord ++ tailWord_2302493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302493).length < 2 ^ (prefixWord ++ tailWord_2302493).sum := by decide
  have hdescent : baseEnd_2302493 < baseStart_2302493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302519 : List Nat := [1, 1, 3, 1, 2, 3, 2, 9]
def baseStart_2302519 : Nat := 118140960795 + 2302519 * 2 ^ 59
def prefixEnd_2302519 : Nat := 4983230072969 + 3 ^ 40 * 2302519 * 2
def baseEnd_2302519 : Nat := 87577700971094971668401

theorem tailTrace_2302519 : CollatzResearch.WordTrace tailWord_2302519 prefixEnd_2302519 87577700971094971668401 := by
  unfold tailWord_2302519
  simp only [CollatzResearch.WordTrace]
  refine ⟨83979767145374376782958611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55986511430249584521972407 83979767145374376782958611)
  ·
    refine ⟨125969650718061565174437917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83979767145374376782958611 125969650718061565174437917)
    ·
      refine ⟨47238619019273086940414219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125969650718061565174437917 47238619019273086940414219)
      ·
        refine ⟨70857928528909630410621329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47238619019273086940414219 70857928528909630410621329)
        ·
          refine ⟨53143446396682222807965997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70857928528909630410621329 53143446396682222807965997)
          ·
            refine ⟨19928792398755833552987249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53143446396682222807965997 19928792398755833552987249)
            ·
              refine ⟨14946594299066875164740437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19928792398755833552987249 14946594299066875164740437)
              ·
                refine ⟨87577700971094971668401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14946594299066875164740437 87577700971094971668401)
                ·
                  rfl

theorem cell22_2302519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 9].length) (baseStart_2302519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302519 prefixEnd_2302519 := by exact prefixLift 2302519
  have htrace : WordTrace (prefixWord ++ tailWord_2302519) baseStart_2302519 baseEnd_2302519 := by
    simpa [prefixWord, tailWord_2302519, baseEnd_2302519] using wordTrace_append hprefix tailTrace_2302519
  have hstable : (prefixWord ++ tailWord_2302519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302519).length < 2 ^ (prefixWord ++ tailWord_2302519).sum := by decide
  have hdescent : baseEnd_2302519 < baseStart_2302519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302660 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_2302660 : Nat := 118140960795 + 2302660 * 2 ^ 59
def prefixEnd_2302660 : Nat := 4983230072969 + 3 ^ 40 * 2302660 * 2
def baseEnd_2302660 : Nat := 262749191973792459080059

theorem tailTrace_2302660 : CollatzResearch.WordTrace tailWord_2302660 prefixEnd_2302660 262749191973792459080059 := by
  unfold tailWord_2302660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41992454918931778931920717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55989939891909038575894289 41992454918931778931920717)
  ·
    refine ⟨15747170594599417099470269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41992454918931778931920717 15747170594599417099470269)
    ·
      refine ⟨5905188972974781412301351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15747170594599417099470269 5905188972974781412301351)
      ·
        refine ⟨8857783459462172118452027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5905188972974781412301351 8857783459462172118452027)
        ·
          refine ⟨13286675189193258177678041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8857783459462172118452027 13286675189193258177678041)
          ·
            refine ⟨9965006391894943633258531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13286675189193258177678041 9965006391894943633258531)
            ·
              refine ⟨14947509587842415449887797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9965006391894943633258531 14947509587842415449887797)
              ·
                refine ⟨1401329023860226448426981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14947509587842415449887797 1401329023860226448426981)
                ·
                  refine ⟨262749191973792459080059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401329023860226448426981 262749191973792459080059)
                  ·
                    rfl

theorem cell22_2302660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_2302660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302660 prefixEnd_2302660 := by exact prefixLift 2302660
  have htrace : WordTrace (prefixWord ++ tailWord_2302660) baseStart_2302660 baseEnd_2302660 := by
    simpa [prefixWord, tailWord_2302660, baseEnd_2302660] using wordTrace_append hprefix tailTrace_2302660
  have hstable : (prefixWord ++ tailWord_2302660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302660).length < 2 ^ (prefixWord ++ tailWord_2302660).sum := by decide
  have hdescent : baseEnd_2302660 < baseStart_2302660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302692 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_2302692 : Nat := 118140960795 + 2302692 * 2 ^ 59
def prefixEnd_2302692 : Nat := 4983230072969 + 3 ^ 40 * 2302692 * 2
def baseEnd_2302692 : Nat := 788258530175339960440079

theorem tailTrace_2302692 : CollatzResearch.WordTrace tailWord_2302692 prefixEnd_2302692 788258530175339960440079 := by
  unfold tailWord_2302692
  simp only [CollatzResearch.WordTrace]
  refine ⟨41993038486873813664503165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55990717982498418219337553 41993038486873813664503165)
  ·
    refine ⟨15747389432577680124188687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41993038486873813664503165 15747389432577680124188687)
    ·
      refine ⟨23621084148866520186283031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15747389432577680124188687 23621084148866520186283031)
      ·
        refine ⟨35431626223299780279424547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23621084148866520186283031 35431626223299780279424547)
        ·
          refine ⟨53147439334949670419136821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35431626223299780279424547 53147439334949670419136821)
          ·
            refine ⟨4982572437651531601794077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53147439334949670419136821 4982572437651531601794077)
            ·
              refine ⟨1868464664119324350672779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4982572437651531601794077 1868464664119324350672779)
              ·
                refine ⟨2802696996178986526009169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868464664119324350672779 2802696996178986526009169)
                ·
                  refine ⟨2102022747134239894506877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802696996178986526009169 2102022747134239894506877)
                  ·
                    refine ⟨788258530175339960440079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102022747134239894506877 788258530175339960440079)
                    ·
                      rfl

theorem cell22_2302692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_2302692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302692 prefixEnd_2302692 := by exact prefixLift 2302692
  have htrace : WordTrace (prefixWord ++ tailWord_2302692) baseStart_2302692 baseEnd_2302692 := by
    simpa [prefixWord, tailWord_2302692, baseEnd_2302692] using wordTrace_append hprefix tailTrace_2302692
  have hstable : (prefixWord ++ tailWord_2302692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302692).length < 2 ^ (prefixWord ++ tailWord_2302692).sum := by decide
  have hdescent : baseEnd_2302692 < baseStart_2302692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302808 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2302808 : Nat := 118140960795 + 2302808 * 2 ^ 59
def prefixEnd_2302808 : Nat := 4983230072969 + 3 ^ 40 * 2302808 * 2
def baseEnd_2302808 : Nat := 788298239345954324539723

theorem tailTrace_2302808 : CollatzResearch.WordTrace tailWord_2302808 prefixEnd_2302808 788298239345954324539723 := by
  unfold tailWord_2302808
  simp only [CollatzResearch.WordTrace]
  refine ⟨41995153920663689570114539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55993538560884919426819385 41995153920663689570114539)
  ·
    refine ⟨62992730880995534355171809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41995153920663689570114539 62992730880995534355171809)
    ·
      refine ⟨47244548160746650766378857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62992730880995534355171809 47244548160746650766378857)
      ·
        refine ⟨35433411120559988074784143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47244548160746650766378857 35433411120559988074784143)
        ·
          refine ⟨53150116680839982112176215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35433411120559988074784143 53150116680839982112176215)
          ·
            refine ⟨79725175021259973168264323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53150116680839982112176215 79725175021259973168264323)
            ·
              refine ⟨119587762531889959752396485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79725175021259973168264323 119587762531889959752396485)
              ·
                refine ⟨22422705474729367453574341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119587762531889959752396485 22422705474729367453574341)
                ·
                  refine ⟨4204257276511756397545189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22422705474729367453574341 4204257276511756397545189)
                  ·
                    refine ⟨788298239345954324539723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4204257276511756397545189 788298239345954324539723)
                    ·
                      rfl

theorem cell22_2302808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2302808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302808 prefixEnd_2302808 := by exact prefixLift 2302808
  have htrace : WordTrace (prefixWord ++ tailWord_2302808) baseStart_2302808 baseEnd_2302808 := by
    simpa [prefixWord, tailWord_2302808, baseEnd_2302808] using wordTrace_append hprefix tailTrace_2302808
  have hstable : (prefixWord ++ tailWord_2302808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302808).length < 2 ^ (prefixWord ++ tailWord_2302808).sum := by decide
  have hdescent : baseEnd_2302808 < baseStart_2302808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302810 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_2302810 : Nat := 118140960795 + 2302810 * 2 ^ 59
def prefixEnd_2302810 : Nat := 4983230072969 + 3 ^ 40 * 2302810 * 2
def baseEnd_2302810 : Nat := 788298923986826985989717

theorem tailTrace_2302810 : CollatzResearch.WordTrace tailWord_2302810 prefixEnd_2302810 788298923986826985989717 := by
  unfold tailWord_2302810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997595196830033370450471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55993587191546755654534589 20997595196830033370450471)
  ·
    refine ⟨31496392795245050055675707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20997595196830033370450471 31496392795245050055675707)
    ·
      refine ⟨47244589192867575083513561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31496392795245050055675707 47244589192867575083513561)
      ·
        refine ⟨35433441894650681312635171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47244589192867575083513561 35433441894650681312635171)
        ·
          refine ⟨53150162841976021968952757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35433441894650681312635171 53150162841976021968952757)
          ·
            refine ⟨4982827766435252059589321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53150162841976021968952757 4982827766435252059589321)
            ·
              refine ⟨3737120824826439044691991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4982827766435252059589321 3737120824826439044691991)
              ·
                refine ⟨5605681237239658567037987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737120824826439044691991 5605681237239658567037987)
                ·
                  refine ⟨8408521855859487850556981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605681237239658567037987 8408521855859487850556981)
                  ·
                    refine ⟨788298923986826985989717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8408521855859487850556981 788298923986826985989717)
                    ·
                      rfl

theorem cell22_2302810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_2302810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302810 prefixEnd_2302810 := by exact prefixLift 2302810
  have htrace : WordTrace (prefixWord ++ tailWord_2302810) baseStart_2302810 baseEnd_2302810 := by
    simpa [prefixWord, tailWord_2302810, baseEnd_2302810] using wordTrace_append hprefix tailTrace_2302810
  have hstable : (prefixWord ++ tailWord_2302810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302810).length < 2 ^ (prefixWord ++ tailWord_2302810).sum := by decide
  have hdescent : baseEnd_2302810 < baseStart_2302810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302874 : List Nat := [3, 1, 1, 4, 4, 1, 2, 6]
def baseStart_2302874 : Nat := 118140960795 + 2302874 * 2 ^ 59
def prefixEnd_2302874 : Nat := 4983230072969 + 3 ^ 40 * 2302874 * 2
def baseEnd_2302874 : Nat := 87591203610528016932169

theorem tailTrace_2302874 : CollatzResearch.WordTrace tailWord_2302874 prefixEnd_2302874 87591203610528016932169 := by
  unfold tailWord_2302874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20998178764772068103032919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55995143372725514941421117 20998178764772068103032919)
  ·
    refine ⟨31497268147158102154549379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20998178764772068103032919 31497268147158102154549379)
    ·
      refine ⟨47245902220737153231824069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31497268147158102154549379 47245902220737153231824069)
      ·
        refine ⟨8858606666388216230967013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47245902220737153231824069 8858606666388216230967013)
        ·
          refine ⟨1660988749947790543306315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8858606666388216230967013 1660988749947790543306315)
          ·
            refine ⟨2491483124921685814959473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660988749947790543306315 2491483124921685814959473)
            ·
              refine ⟨1868612343691264361219605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491483124921685814959473 1868612343691264361219605)
              ·
                refine ⟨87591203610528016932169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1868612343691264361219605 87591203610528016932169)
                ·
                  rfl

theorem cell22_2302874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_2302874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302874 prefixEnd_2302874 := by exact prefixLift 2302874
  have htrace : WordTrace (prefixWord ++ tailWord_2302874) baseStart_2302874 baseEnd_2302874 := by
    simpa [prefixWord, tailWord_2302874, baseEnd_2302874] using wordTrace_append hprefix tailTrace_2302874
  have hstable : (prefixWord ++ tailWord_2302874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302874).length < 2 ^ (prefixWord ++ tailWord_2302874).sum := by decide
  have hdescent : baseEnd_2302874 < baseStart_2302874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302883 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_2302883 : Nat := 118140960795 + 2302883 * 2 ^ 59
def prefixEnd_2302883 : Nat := 4983230072969 + 3 ^ 40 * 2302883 * 2
def baseEnd_2302883 : Nat := 788323913378679128914493

theorem tailTrace_2302883 : CollatzResearch.WordTrace tailWord_2302883 prefixEnd_2302883 788323913378679128914493 := by
  unfold tailWord_2302883
  simp only [CollatzResearch.WordTrace]
  refine ⟨83993043316055666949209303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55995362210703777966139535 83993043316055666949209303)
  ·
    refine ⟨125989564974083500423813955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83993043316055666949209303 125989564974083500423813955)
    ·
      refine ⟨188984347461125250635720933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125989564974083500423813955 188984347461125250635720933)
      ·
        refine ⟨35434565148960984494197675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188984347461125250635720933 35434565148960984494197675)
        ·
          refine ⟨53151847723441476741296513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35434565148960984494197675 53151847723441476741296513)
          ·
            refine ⟨39863885792581107555972385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53151847723441476741296513 39863885792581107555972385)
            ·
              refine ⟨29897914344435830666979289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39863885792581107555972385 29897914344435830666979289)
              ·
                refine ⟨22423435758326873000234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29897914344435830666979289 22423435758326873000234467)
                ·
                  refine ⟨33635153637490309500351701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22423435758326873000234467 33635153637490309500351701)
                  ·
                    refine ⟨788323913378679128914493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33635153637490309500351701 788323913378679128914493)
                    ·
                      rfl

theorem cell22_2302883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_2302883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302883 prefixEnd_2302883 := by exact prefixLift 2302883
  have htrace : WordTrace (prefixWord ++ tailWord_2302883) baseStart_2302883 baseEnd_2302883 := by
    simpa [prefixWord, tailWord_2302883, baseEnd_2302883] using wordTrace_append hprefix tailTrace_2302883
  have hstable : (prefixWord ++ tailWord_2302883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302883).length < 2 ^ (prefixWord ++ tailWord_2302883).sum := by decide
  have hdescent : baseEnd_2302883 < baseStart_2302883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302932 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2302932 : Nat := 118140960795 + 2302932 * 2 ^ 59
def prefixEnd_2302932 : Nat := 4983230072969 + 3 ^ 40 * 2302932 * 2
def baseEnd_2302932 : Nat := 788340687080059334439343

theorem tailTrace_2302932 : CollatzResearch.WordTrace tailWord_2302932 prefixEnd_2302932 788340687080059334439343 := by
  unfold tailWord_2302932
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997415246439074158871525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55996553661918765545162033 41997415246439074158871525)
  ·
    refine ⟨7874515358707326404788411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41997415246439074158871525 7874515358707326404788411)
    ·
      refine ⟨11811773038060989607182617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874515358707326404788411 11811773038060989607182617)
      ·
        refine ⟨8858829778545742205386963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11811773038060989607182617 8858829778545742205386963)
        ·
          refine ⟨13288244667818613308080445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8858829778545742205386963 13288244667818613308080445)
          ·
            refine ⟨4983091750431979990530167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13288244667818613308080445 4983091750431979990530167)
            ·
              refine ⟨7474637625647969985795251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983091750431979990530167 7474637625647969985795251)
              ·
                refine ⟨11211956438471954978692877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474637625647969985795251 11211956438471954978692877)
                ·
                  refine ⟨4204483664426983117009829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11211956438471954978692877 4204483664426983117009829)
                  ·
                    refine ⟨788340687080059334439343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4204483664426983117009829 788340687080059334439343)
                    ·
                      rfl

theorem cell22_2302932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2302932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302932 prefixEnd_2302932 := by exact prefixLift 2302932
  have htrace : WordTrace (prefixWord ++ tailWord_2302932) baseStart_2302932 baseEnd_2302932 := by
    simpa [prefixWord, tailWord_2302932, baseEnd_2302932] using wordTrace_append hprefix tailTrace_2302932
  have hstable : (prefixWord ++ tailWord_2302932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302932).length < 2 ^ (prefixWord ++ tailWord_2302932).sum := by decide
  have hdescent : baseEnd_2302932 < baseStart_2302932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302947 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 4]
def baseStart_2302947 : Nat := 118140960795 + 2302947 * 2 ^ 59
def prefixEnd_2302947 : Nat := 4983230072969 + 3 ^ 40 * 2302947 * 2
def baseEnd_2302947 : Nat := 262781940628868098438099

theorem tailTrace_2302947 : CollatzResearch.WordTrace tailWord_2302947 prefixEnd_2302947 262781940628868098438099 := by
  unfold tailWord_2302947
  simp only [CollatzResearch.WordTrace]
  refine ⟨83995377587823805879539095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55996918391882537253026063 83995377587823805879539095)
  ·
    refine ⟨125993066381735708819308643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83995377587823805879539095 125993066381735708819308643)
    ·
      refine ⟨188989599572603563228962965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125993066381735708819308643 188989599572603563228962965)
      ·
        refine ⟨8858887479965792026357639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188989599572603563228962965 8858887479965792026357639)
        ·
          refine ⟨13288331219948688039536459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8858887479965792026357639 13288331219948688039536459)
          ·
            refine ⟨19932496829923032059304689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13288331219948688039536459 19932496829923032059304689)
            ·
              refine ⟨14949372622442274044478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19932496829923032059304689 14949372622442274044478517)
              ·
                refine ⟨1401503683353963191669861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14949372622442274044478517 1401503683353963191669861)
                ·
                  refine ⟨262781940628868098438099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401503683353963191669861 262781940628868098438099)
                  ·
                    rfl

theorem cell22_2302947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 4].length) (baseStart_2302947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2302947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2302947 prefixEnd_2302947 := by exact prefixLift 2302947
  have htrace : WordTrace (prefixWord ++ tailWord_2302947) baseStart_2302947 baseEnd_2302947 := by
    simpa [prefixWord, tailWord_2302947, baseEnd_2302947] using wordTrace_append hprefix tailTrace_2302947
  have hstable : (prefixWord ++ tailWord_2302947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302947).length < 2 ^ (prefixWord ++ tailWord_2302947).sum := by decide
  have hdescent : baseEnd_2302947 < baseStart_2302947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303020 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_2303020 : Nat := 118140960795 + 2303020 * 2 ^ 59
def prefixEnd_2303020 : Nat := 4983230072969 + 3 ^ 40 * 2303020 * 2
def baseEnd_2303020 : Nat := 262790270426152146079691

theorem tailTrace_2303020 : CollatzResearch.WordTrace tailWord_2303020 prefixEnd_2303020 262790270426152146079691 := by
  unfold tailWord_2303020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41999020058279669673473257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55998693411039559564631009 41999020058279669673473257)
  ·
    refine ⟨31499265043709752255104943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41999020058279669673473257 31499265043709752255104943)
    ·
      refine ⟨47248897565564628382657415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31499265043709752255104943 47248897565564628382657415)
      ·
        refine ⟨70873346348346942573986123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47248897565564628382657415 70873346348346942573986123)
        ·
          refine ⟨106310019522520413860979185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70873346348346942573986123 106310019522520413860979185)
          ·
            refine ⟨79732514641890310395734389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106310019522520413860979185 79732514641890310395734389)
            ·
              refine ⟨7474923247677216599600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79732514641890310395734389 7474923247677216599600099)
              ·
                refine ⟨11212384871515824899400149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474923247677216599600099 11212384871515824899400149)
                ·
                  refine ⟨262790270426152146079691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11212384871515824899400149 262790270426152146079691)
                  ·
                    rfl

theorem cell22_2303020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_2303020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303020 prefixEnd_2303020 := by exact prefixLift 2303020
  have htrace : WordTrace (prefixWord ++ tailWord_2303020) baseStart_2303020 baseEnd_2303020 := by
    simpa [prefixWord, tailWord_2303020, baseEnd_2303020] using wordTrace_append hprefix tailTrace_2303020
  have hstable : (prefixWord ++ tailWord_2303020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303020).length < 2 ^ (prefixWord ++ tailWord_2303020).sum := by decide
  have hdescent : baseEnd_2303020 < baseStart_2303020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303024 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_2303024 : Nat := 118140960795 + 2303024 * 2 ^ 59
def prefixEnd_2303024 : Nat := 4983230072969 + 3 ^ 40 * 2303024 * 2
def baseEnd_2303024 : Nat := 788372180560201761139061

theorem tailTrace_2303024 : CollatzResearch.WordTrace tailWord_2303024 prefixEnd_2303024 788372180560201761139061 := by
  unfold tailWord_2303024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41999093004272424015046063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55998790672363232020061417 41999093004272424015046063)
  ·
    refine ⟨62998639506408636022569095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41999093004272424015046063 62998639506408636022569095)
    ·
      refine ⟨94497959259612954033853643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62998639506408636022569095 94497959259612954033853643)
      ·
        refine ⟨141746938889419431050780465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94497959259612954033853643 141746938889419431050780465)
        ·
          refine ⟨106310204167064573288085349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141746938889419431050780465 106310204167064573288085349)
          ·
            refine ⟨19933163281324607491516003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106310204167064573288085349 19933163281324607491516003)
            ·
              refine ⟨29899744921986911237274005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19933163281324607491516003 29899744921986911237274005)
              ·
                refine ⟨1401550543218136464247219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29899744921986911237274005 1401550543218136464247219)
                ·
                  refine ⟨2102325814827204696370829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401550543218136464247219 2102325814827204696370829)
                  ·
                    refine ⟨788372180560201761139061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102325814827204696370829 788372180560201761139061)
                    ·
                      rfl

theorem cell22_2303024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_2303024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303024 prefixEnd_2303024 := by exact prefixLift 2303024
  have htrace : WordTrace (prefixWord ++ tailWord_2303024) baseStart_2303024 baseEnd_2303024 := by
    simpa [prefixWord, tailWord_2303024, baseEnd_2303024] using wordTrace_append hprefix tailTrace_2303024
  have hstable : (prefixWord ++ tailWord_2303024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303024).length < 2 ^ (prefixWord ++ tailWord_2303024).sum := by decide
  have hdescent : baseEnd_2303024 < baseStart_2303024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303058 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2303058 : Nat := 118140960795 + 2303058 * 2 ^ 59
def prefixEnd_2303058 : Nat := 4983230072969 + 3 ^ 40 * 2303058 * 2
def baseEnd_2303058 : Nat := 788383819455037005788957

theorem tailTrace_2303058 : CollatzResearch.WordTrace tailWord_2303058 prefixEnd_2303058 788383819455037005788957 := by
  unfold tailWord_2303058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20999856522605417959207457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55999617393614447891219885 20999856522605417959207457)
  ·
    refine ⟨15749892391954063469405593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20999856522605417959207457 15749892391954063469405593)
    ·
      refine ⟨11812419293965547602054195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15749892391954063469405593 11812419293965547602054195)
      ·
        refine ⟨17718628940948321403081293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812419293965547602054195 17718628940948321403081293)
        ·
          refine ⟨6644485852855620526155485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17718628940948321403081293 6644485852855620526155485)
          ·
            refine ⟨2491682194820857697308307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6644485852855620526155485 2491682194820857697308307)
            ·
              refine ⟨3737523292231286545962461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491682194820857697308307 3737523292231286545962461)
              ·
                refine ⟨1401571234586732454735923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3737523292231286545962461 1401571234586732454735923)
                ·
                  refine ⟨2102356851880098682103885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401571234586732454735923 2102356851880098682103885)
                  ·
                    refine ⟨788383819455037005788957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102356851880098682103885 788383819455037005788957)
                    ·
                      rfl

theorem cell22_2303058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2303058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303058 prefixEnd_2303058 := by exact prefixLift 2303058
  have htrace : WordTrace (prefixWord ++ tailWord_2303058) baseStart_2303058 baseEnd_2303058 := by
    simpa [prefixWord, tailWord_2303058, baseEnd_2303058] using wordTrace_append hprefix tailTrace_2303058
  have hstable : (prefixWord ++ tailWord_2303058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303058).length < 2 ^ (prefixWord ++ tailWord_2303058).sum := by decide
  have hdescent : baseEnd_2303058 < baseStart_2303058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303159 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 3, 3]
def baseStart_2303159 : Nat := 118140960795 + 2303159 * 2 ^ 59
def prefixEnd_2303159 : Nat := 4983230072969 + 3 ^ 40 * 2303159 * 2
def baseEnd_2303159 : Nat := 788418393819106409013647

theorem tailTrace_2303159 : CollatzResearch.WordTrace tailWord_2303159 prefixEnd_2303159 788418393819106409013647 := by
  unfold tailWord_2303159
  simp only [CollatzResearch.WordTrace]
  refine ⟨84003109863055766086256531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56002073242037177390837687 84003109863055766086256531)
  ·
    refine ⟨126004664794583649129384797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84003109863055766086256531 126004664794583649129384797)
    ·
      refine ⟨47251749297968868423519299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126004664794583649129384797 47251749297968868423519299)
      ·
        refine ⟨70877623946953302635278949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47251749297968868423519299 70877623946953302635278949)
        ·
          refine ⟨13289554490053744244114803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70877623946953302635278949 13289554490053744244114803)
          ·
            refine ⟨19934331735080616366172205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13289554490053744244114803 19934331735080616366172205)
            ·
              refine ⟨7475374400655231137314577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19934331735080616366172205 7475374400655231137314577)
              ·
                refine ⟨5606530800491423352985933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475374400655231137314577 5606530800491423352985933)
                ·
                  refine ⟨2102449050184283757369725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5606530800491423352985933 2102449050184283757369725)
                  ·
                    refine ⟨788418393819106409013647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102449050184283757369725 788418393819106409013647)
                    ·
                      rfl

theorem cell22_2303159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_2303159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303159 prefixEnd_2303159 := by exact prefixLift 2303159
  have htrace : WordTrace (prefixWord ++ tailWord_2303159) baseStart_2303159 baseEnd_2303159 := by
    simpa [prefixWord, tailWord_2303159, baseEnd_2303159] using wordTrace_append hprefix tailTrace_2303159
  have hstable : (prefixWord ++ tailWord_2303159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303159).length < 2 ^ (prefixWord ++ tailWord_2303159).sum := by decide
  have hdescent : baseEnd_2303159 < baseStart_2303159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303176 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_2303176 : Nat := 118140960795 + 2303176 * 2 ^ 59
def prefixEnd_2303176 : Nat := 4983230072969 + 3 ^ 40 * 2303176 * 2
def baseEnd_2303176 : Nat := 788424213266524031338595

theorem tailTrace_2303176 : CollatzResearch.WordTrace tailWord_2303176 prefixEnd_2303176 788424213266524031338595 := by
  unfold tailWord_2303176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42001864951997088994812691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56002486602662785326416921 42001864951997088994812691)
  ·
    refine ⟨63002797427995633492219037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42001864951997088994812691 63002797427995633492219037)
    ·
      refine ⟨23626049035498362559582139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63002797427995633492219037 23626049035498362559582139)
      ·
        refine ⟨35439073553247543839373209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23626049035498362559582139 35439073553247543839373209)
        ·
          refine ⟨26579305164935657879529907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35439073553247543839373209 26579305164935657879529907)
          ·
            refine ⟨39868957747403486819294861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26579305164935657879529907 39868957747403486819294861)
            ·
              refine ⟨14950859155276307557235573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39868957747403486819294861 14950859155276307557235573)
              ·
                refine ⟨1401643045807153833490835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14950859155276307557235573 1401643045807153833490835)
                ·
                  refine ⟨2102464568710730750236253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401643045807153833490835 2102464568710730750236253)
                  ·
                    refine ⟨788424213266524031338595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102464568710730750236253 788424213266524031338595)
                    ·
                      rfl

theorem cell22_2303176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_2303176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303176 prefixEnd_2303176 := by exact prefixLift 2303176
  have htrace : WordTrace (prefixWord ++ tailWord_2303176) baseStart_2303176 baseEnd_2303176 := by
    simpa [prefixWord, tailWord_2303176, baseEnd_2303176] using wordTrace_append hprefix tailTrace_2303176
  have hstable : (prefixWord ++ tailWord_2303176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303176).length < 2 ^ (prefixWord ++ tailWord_2303176).sum := by decide
  have hdescent : baseEnd_2303176 < baseStart_2303176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303189 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 7]
def baseStart_2303189 : Nat := 118140960795 + 2303189 * 2 ^ 59
def prefixEnd_2303189 : Nat := 4983230072969 + 3 ^ 40 * 2303189 * 2
def baseEnd_2303189 : Nat := 262809554477398776921185

theorem tailTrace_2303189 : CollatzResearch.WordTrace tailWord_2303189 prefixEnd_2303189 262809554477398776921185 := by
  unfold tailWord_2303189
  simp only [CollatzResearch.WordTrace]
  refine ⟨84004204052947081209848621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56002802701964720806565747 84004204052947081209848621)
  ·
    refine ⟨31501576519855155453693233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84004204052947081209848621 31501576519855155453693233)
    ·
      refine ⟨23626182389891366590269925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31501576519855155453693233 23626182389891366590269925)
      ·
        refine ⟨4429909198104631235675611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23626182389891366590269925 4429909198104631235675611)
        ·
          refine ⟨6644863797156946853513417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429909198104631235675611 6644863797156946853513417)
          ·
            refine ⟨4983647847867710140135063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6644863797156946853513417 4983647847867710140135063)
            ·
              refine ⟨7475471771801565210202595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983647847867710140135063 7475471771801565210202595)
              ·
                refine ⟨11213207657702347815303893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7475471771801565210202595 11213207657702347815303893)
                ·
                  refine ⟨262809554477398776921185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11213207657702347815303893 262809554477398776921185)
                  ·
                    rfl

theorem cell22_2303189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_2303189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303189 prefixEnd_2303189 := by exact prefixLift 2303189
  have htrace : WordTrace (prefixWord ++ tailWord_2303189) baseStart_2303189 baseEnd_2303189 := by
    simpa [prefixWord, tailWord_2303189, baseEnd_2303189] using wordTrace_append hprefix tailTrace_2303189
  have hstable : (prefixWord ++ tailWord_2303189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303189).length < 2 ^ (prefixWord ++ tailWord_2303189).sum := by decide
  have hdescent : baseEnd_2303189 < baseStart_2303189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303219 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 1, 4]
def baseStart_2303219 : Nat := 118140960795 + 2303219 * 2 ^ 59
def prefixEnd_2303219 : Nat := 4983230072969 + 3 ^ 40 * 2303219 * 2
def baseEnd_2303219 : Nat := 788438933045286252513463

theorem tailTrace_2303219 : CollatzResearch.WordTrace tailWord_2303219 prefixEnd_2303219 788438933045286252513463 := by
  unfold tailWord_2303219
  simp only [CollatzResearch.WordTrace]
  refine ⟨84005298242838396333440711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56003532161892264222293807 84005298242838396333440711)
  ·
    refine ⟨126007947364257594500161067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84005298242838396333440711 126007947364257594500161067)
    ·
      refine ⟨189011921046386391750241601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126007947364257594500161067 189011921046386391750241601)
      ·
        refine ⟨141758940784789793812681201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189011921046386391750241601 141758940784789793812681201)
        ·
          refine ⟨106319205588592345359510901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141758940784789793812681201 106319205588592345359510901)
          ·
            refine ⟨9967425523930532377454147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106319205588592345359510901 9967425523930532377454147)
            ·
              refine ⟨14951138285895798566181221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967425523930532377454147 14951138285895798566181221)
              ·
                refine ⟨2803338428605462231158979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14951138285895798566181221 2803338428605462231158979)
                ·
                  refine ⟨4205007642908193346738469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803338428605462231158979 4205007642908193346738469)
                  ·
                    refine ⟨788438933045286252513463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205007642908193346738469 788438933045286252513463)
                    ·
                      rfl

theorem cell22_2303219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_2303219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303219 prefixEnd_2303219 := by exact prefixLift 2303219
  have htrace : WordTrace (prefixWord ++ tailWord_2303219) baseStart_2303219 baseEnd_2303219 := by
    simpa [prefixWord, tailWord_2303219, baseEnd_2303219] using wordTrace_append hprefix tailTrace_2303219
  have hstable : (prefixWord ++ tailWord_2303219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303219).length < 2 ^ (prefixWord ++ tailWord_2303219).sum := by decide
  have hdescent : baseEnd_2303219 < baseStart_2303219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303232 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_2303232 : Nat := 118140960795 + 2303232 * 2 ^ 59
def prefixEnd_2303232 : Nat := 4983230072969 + 3 ^ 40 * 2303232 * 2
def baseEnd_2303232 : Nat := 788443383210958551938423

theorem tailTrace_2303232 : CollatzResearch.WordTrace tailWord_2303232 prefixEnd_2303232 788443383210958551938423 := by
  unfold tailWord_2303232
  simp only [CollatzResearch.WordTrace]
  refine ⟨42002886195895649776831975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56003848261194199702442633 42002886195895649776831975)
  ·
    refine ⟨63004329293843474665247963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42002886195895649776831975 63004329293843474665247963)
    ·
      refine ⟨94506493940765211997871945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63004329293843474665247963 94506493940765211997871945)
      ·
        refine ⟨70879870455573908998403959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94506493940765211997871945 70879870455573908998403959)
        ·
          refine ⟨106319805683360863497605939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70879870455573908998403959 106319805683360863497605939)
          ·
            refine ⟨159479708525041295246408909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106319805683360863497605939 159479708525041295246408909)
            ·
              refine ⟨59804890696890485717403341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159479708525041295246408909 59804890696890485717403341)
              ·
                refine ⟨22426834011333932144026253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59804890696890485717403341 22426834011333932144026253)
                ·
                  refine ⟨8410062754250224554009845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22426834011333932144026253 8410062754250224554009845)
                  ·
                    refine ⟨788443383210958551938423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8410062754250224554009845 788443383210958551938423)
                    ·
                      rfl

theorem cell22_2303232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_2303232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303232 prefixEnd_2303232 := by exact prefixLift 2303232
  have htrace : WordTrace (prefixWord ++ tailWord_2303232) baseStart_2303232 baseEnd_2303232 := by
    simpa [prefixWord, tailWord_2303232, baseEnd_2303232] using wordTrace_append hprefix tailTrace_2303232
  have hstable : (prefixWord ++ tailWord_2303232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303232).length < 2 ^ (prefixWord ++ tailWord_2303232).sum := by decide
  have hdescent : baseEnd_2303232 < baseStart_2303232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303236 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2303236 : Nat := 118140960795 + 2303236 * 2 ^ 59
def prefixEnd_2303236 : Nat := 4983230072969 + 3 ^ 40 * 2303236 * 2
def baseEnd_2303236 : Nat := 788444752492703874838411

theorem tailTrace_2303236 : CollatzResearch.WordTrace tailWord_2303236 prefixEnd_2303236 788444752492703874838411 := by
  unfold tailWord_2303236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42002959141888404118404781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56003945522517872157873041 42002959141888404118404781)
  ·
    refine ⟨15751109678208151544401793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42002959141888404118404781 15751109678208151544401793)
    ·
      refine ⟨11813332258656113658301345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15751109678208151544401793 11813332258656113658301345)
      ·
        refine ⟨8859999193992085243726009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11813332258656113658301345 8859999193992085243726009)
        ·
          refine ⟨6644999395494063932794507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8859999193992085243726009 6644999395494063932794507)
          ·
            refine ⟨9967499093241095899191761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644999395494063932794507 9967499093241095899191761)
            ·
              refine ⟨7475624319930821924393821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9967499093241095899191761 7475624319930821924393821)
              ·
                refine ⟨2803359119974058221647683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7475624319930821924393821 2803359119974058221647683)
                ·
                  refine ⟨4205038679961087332471525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803359119974058221647683 4205038679961087332471525)
                  ·
                    refine ⟨788444752492703874838411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205038679961087332471525 788444752492703874838411)
                    ·
                      rfl

theorem cell22_2303236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2303236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303236 prefixEnd_2303236 := by exact prefixLift 2303236
  have htrace : WordTrace (prefixWord ++ tailWord_2303236) baseStart_2303236 baseEnd_2303236 := by
    simpa [prefixWord, tailWord_2303236, baseEnd_2303236] using wordTrace_append hprefix tailTrace_2303236
  have hstable : (prefixWord ++ tailWord_2303236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303236).length < 2 ^ (prefixWord ++ tailWord_2303236).sum := by decide
  have hdescent : baseEnd_2303236 < baseStart_2303236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303249 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_2303249 : Nat := 118140960795 + 2303249 * 2 ^ 59
def prefixEnd_2303249 : Nat := 4983230072969 + 3 ^ 40 * 2303249 * 2
def baseEnd_2303249 : Nat := 788449202658376174263371

theorem tailTrace_2303249 : CollatzResearch.WordTrace tailWord_2303249 prefixEnd_2303249 788449202658376174263371 := by
  unfold tailWord_2303249
  simp only [CollatzResearch.WordTrace]
  refine ⟨84006392432729711457032801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56004261621819807638021867 84006392432729711457032801)
  ·
    refine ⟨63004794324547283592774601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84006392432729711457032801 63004794324547283592774601)
    ·
      refine ⟨47253595743410462694580951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63004794324547283592774601 47253595743410462694580951)
      ·
        refine ⟨70880393615115694041871427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47253595743410462694580951 70880393615115694041871427)
        ·
          refine ⟨106320590422673541062807141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70880393615115694041871427 106320590422673541062807141)
          ·
            refine ⟨19935110704251288949276339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106320590422673541062807141 19935110704251288949276339)
            ·
              refine ⟨29902666056376933423914509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19935110704251288949276339 29902666056376933423914509)
              ·
                refine ⟨11213499771141350033967941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29902666056376933423914509 11213499771141350033967941)
                ·
                  refine ⟨2102531207089003131368989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11213499771141350033967941 2102531207089003131368989)
                  ·
                    refine ⟨788449202658376174263371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102531207089003131368989 788449202658376174263371)
                    ·
                      rfl

theorem cell22_2303249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_2303249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303249 prefixEnd_2303249 := by exact prefixLift 2303249
  have htrace : WordTrace (prefixWord ++ tailWord_2303249) baseStart_2303249 baseEnd_2303249 := by
    simpa [prefixWord, tailWord_2303249, baseEnd_2303249] using wordTrace_append hprefix tailTrace_2303249
  have hstable : (prefixWord ++ tailWord_2303249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303249).length < 2 ^ (prefixWord ++ tailWord_2303249).sum := by decide
  have hdescent : baseEnd_2303249 < baseStart_2303249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303281 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_2303281 : Nat := 118140960795 + 2303281 * 2 ^ 59
def prefixEnd_2303281 : Nat := 4983230072969 + 3 ^ 40 * 2303281 * 2
def baseEnd_2303281 : Nat := 788460156912338757463273

theorem tailTrace_2303281 : CollatzResearch.WordTrace tailWord_2303281 prefixEnd_2303281 788460156912338757463273 := by
  unfold tailWord_2303281
  simp only [CollatzResearch.WordTrace]
  refine ⟨84007559568613780922197697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56005039712409187281465131 84007559568613780922197697)
  ·
    refine ⟨63005669676460335691648273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84007559568613780922197697 63005669676460335691648273)
    ·
      refine ⟨47254252257345251768736205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63005669676460335691648273 47254252257345251768736205)
      ·
        refine ⟨17720344596504469413276077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47254252257345251768736205 17720344596504469413276077)
        ·
          refine ⟨6645129223689176029978529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17720344596504469413276077 6645129223689176029978529)
          ·
            refine ⟨4983846917766882022483897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645129223689176029978529 4983846917766882022483897)
            ·
              refine ⟨3737885188325161516862923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4983846917766882022483897 3737885188325161516862923)
              ·
                refine ⟨5606827782487742275294385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737885188325161516862923 5606827782487742275294385)
                ·
                  refine ⟨4205120836865806706470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5606827782487742275294385 4205120836865806706470789)
                  ·
                    refine ⟨788460156912338757463273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205120836865806706470789 788460156912338757463273)
                    ·
                      rfl

theorem cell22_2303281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_2303281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303281 prefixEnd_2303281 := by exact prefixLift 2303281
  have htrace : WordTrace (prefixWord ++ tailWord_2303281) baseStart_2303281 baseEnd_2303281 := by
    simpa [prefixWord, tailWord_2303281, baseEnd_2303281] using wordTrace_append hprefix tailTrace_2303281
  have hstable : (prefixWord ++ tailWord_2303281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303281).length < 2 ^ (prefixWord ++ tailWord_2303281).sum := by decide
  have hdescent : baseEnd_2303281 < baseStart_2303281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303300 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2303300 : Nat := 118140960795 + 2303300 * 2 ^ 59
def prefixEnd_2303300 : Nat := 4983230072969 + 3 ^ 40 * 2303300 * 2
def baseEnd_2303300 : Nat := 788466661000629041238215

theorem tailTrace_2303300 : CollatzResearch.WordTrace tailWord_2303300 prefixEnd_2303300 788466661000629041238215 := by
  unfold tailWord_2303300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42004126277772473583569677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56005501703696631444759569 42004126277772473583569677)
  ·
    refine ⟨15751547354164677593838629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42004126277772473583569677 15751547354164677593838629)
    ·
      refine ⟨2953415128905877048844743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15751547354164677593838629 2953415128905877048844743)
      ·
        refine ⟨4430122693358815573267115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953415128905877048844743 4430122693358815573267115)
        ·
          refine ⟨6645184040038223359900673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430122693358815573267115 6645184040038223359900673)
          ·
            refine ⟨4983888030028667519925505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645184040038223359900673 4983888030028667519925505)
            ·
              refine ⟨3737916022521500639944129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4983888030028667519925505 3737916022521500639944129)
              ·
                refine ⟨2803437016891125479958097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3737916022521500639944129 2803437016891125479958097)
                ·
                  refine ⟨2102577762668344109968573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2803437016891125479958097 2102577762668344109968573)
                  ·
                    refine ⟨788466661000629041238215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102577762668344109968573 788466661000629041238215)
                    ·
                      rfl

theorem cell22_2303300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2303300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303300 prefixEnd_2303300 := by exact prefixLift 2303300
  have htrace : WordTrace (prefixWord ++ tailWord_2303300) baseStart_2303300 baseEnd_2303300 := by
    simpa [prefixWord, tailWord_2303300, baseEnd_2303300] using wordTrace_append hprefix tailTrace_2303300
  have hstable : (prefixWord ++ tailWord_2303300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303300).length < 2 ^ (prefixWord ++ tailWord_2303300).sum := by decide
  have hdescent : baseEnd_2303300 < baseStart_2303300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303302 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2303302 : Nat := 118140960795 + 2303302 * 2 ^ 59
def prefixEnd_2303302 : Nat := 4983230072969 + 3 ^ 40 * 2303302 * 2
def baseEnd_2303302 : Nat := 262822448547167234229403

theorem tailTrace_2303302 : CollatzResearch.WordTrace tailWord_2303302 prefixEnd_2303302 262822448547167234229403 := by
  unfold tailWord_2303302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625260171923053172147255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56005550334358467672474773 2625260171923053172147255)
  ·
    refine ⟨3937890257884579758220883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2625260171923053172147255 3937890257884579758220883)
    ·
      refine ⟨5906835386826869637331325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937890257884579758220883 5906835386826869637331325)
      ·
        refine ⟨2215063270060076113999247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5906835386826869637331325 2215063270060076113999247)
        ·
          refine ⟨3322594905090114170998871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215063270060076113999247 3322594905090114170998871)
          ·
            refine ⟨4983892357635171256498307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322594905090114170998871 4983892357635171256498307)
            ·
              refine ⟨7475838536452756884747461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983892357635171256498307 7475838536452756884747461)
              ·
                refine ⟨1401719725584891915890149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7475838536452756884747461 1401719725584891915890149)
                ·
                  refine ⟨262822448547167234229403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401719725584891915890149 262822448547167234229403)
                  ·
                    rfl

theorem cell22_2303302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2303302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303302 prefixEnd_2303302 := by exact prefixLift 2303302
  have htrace : WordTrace (prefixWord ++ tailWord_2303302) baseStart_2303302 baseEnd_2303302 := by
    simpa [prefixWord, tailWord_2303302, baseEnd_2303302] using wordTrace_append hprefix tailTrace_2303302
  have hstable : (prefixWord ++ tailWord_2303302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303302).length < 2 ^ (prefixWord ++ tailWord_2303302).sum := by decide
  have hdescent : baseEnd_2303302 < baseStart_2303302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303307 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 11]
def baseStart_2303307 : Nat := 118140960795 + 2303307 * 2 ^ 59
def prefixEnd_2303307 : Nat := 4983230072969 + 3 ^ 40 * 2303307 * 2
def baseEnd_2303307 : Nat := 262823019081227785437731

theorem tailTrace_2303307 : CollatzResearch.WordTrace tailWord_2303307 prefixEnd_2303307 262823019081227785437731 := by
  unfold tailWord_2303307
  simp only [CollatzResearch.WordTrace]
  refine ⟨84008507866519587362644175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56005671911013058241762783 84008507866519587362644175)
  ·
    refine ⟨126012761799779381043966263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84008507866519587362644175 126012761799779381043966263)
    ·
      refine ⟨189019142699669071565949395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126012761799779381043966263 189019142699669071565949395)
      ·
        refine ⟨283528714049503607348924093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189019142699669071565949395 283528714049503607348924093)
        ·
          refine ⟨106323267768563852755846535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283528714049503607348924093 106323267768563852755846535)
          ·
            refine ⟨159484901652845779133769803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106323267768563852755846535 159484901652845779133769803)
            ·
              refine ⟨239227352479268668700654705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159484901652845779133769803 239227352479268668700654705)
              ·
                refine ⟨179420514359451501525491029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239227352479268668700654705 179420514359451501525491029)
                ·
                  refine ⟨262823019081227785437731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 179420514359451501525491029 262823019081227785437731)
                  ·
                    rfl

theorem cell22_2303307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_2303307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303307 prefixEnd_2303307 := by exact prefixLift 2303307
  have htrace : WordTrace (prefixWord ++ tailWord_2303307) baseStart_2303307 baseEnd_2303307 := by
    simpa [prefixWord, tailWord_2303307, baseEnd_2303307] using wordTrace_append hprefix tailTrace_2303307
  have hstable : (prefixWord ++ tailWord_2303307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303307).length < 2 ^ (prefixWord ++ tailWord_2303307).sum := by decide
  have hdescent : baseEnd_2303307 < baseStart_2303307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303362 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2303362 : Nat := 118140960795 + 2303362 * 2 ^ 59
def prefixEnd_2303362 : Nat := 4983230072969 + 3 ^ 40 * 2303362 * 2
def baseEnd_2303362 : Nat := 788487884867681546188025

theorem tailTrace_2303362 : CollatzResearch.WordTrace tailWord_2303362 prefixEnd_2303362 788487884867681546188025 := by
  unfold tailWord_2303362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21002628470330082938974085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56007009254213554503930893 21002628470330082938974085)
  ·
    refine ⟨3937992838186890551057641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21002628470330082938974085 3937992838186890551057641)
    ·
      refine ⟨2953494628640167913293231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3937992838186890551057641 2953494628640167913293231)
      ·
        refine ⟨4430241942960251869939847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953494628640167913293231 4430241942960251869939847)
        ·
          refine ⟨6645362914440377804909771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430241942960251869939847 6645362914440377804909771)
          ·
            refine ⟨9968044371660566707364657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6645362914440377804909771 9968044371660566707364657)
            ·
              refine ⟨7476033278745425030523493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9968044371660566707364657 7476033278745425030523493)
              ·
                refine ⟨1401756239764767193223155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7476033278745425030523493 1401756239764767193223155)
                ·
                  refine ⟨2102634359647150789834733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401756239764767193223155 2102634359647150789834733)
                  ·
                    refine ⟨788487884867681546188025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102634359647150789834733 788487884867681546188025)
                    ·
                      rfl

theorem cell22_2303362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2303362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303362 prefixEnd_2303362 := by exact prefixLift 2303362
  have htrace : WordTrace (prefixWord ++ tailWord_2303362) baseStart_2303362 baseEnd_2303362 := by
    simpa [prefixWord, tailWord_2303362, baseEnd_2303362] using wordTrace_append hprefix tailTrace_2303362
  have hstable : (prefixWord ++ tailWord_2303362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303362).length < 2 ^ (prefixWord ++ tailWord_2303362).sum := by decide
  have hdescent : baseEnd_2303362 < baseStart_2303362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303420 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_2303420 : Nat := 118140960795 + 2303420 * 2 ^ 59
def prefixEnd_2303420 : Nat := 4983230072969 + 3 ^ 40 * 2303420 * 2
def baseEnd_2303420 : Nat := 262835913150996242745949

theorem tailTrace_2303420 : CollatzResearch.WordTrace tailWord_2303420 prefixEnd_2303420 262835913150996242745949 := by
  unfold tailWord_2303420
  simp only [CollatzResearch.WordTrace]
  refine ⟨42006314657555103830753857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56008419543406805107671809 42006314657555103830753857)
  ·
    refine ⟨31504735993166327873065393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42006314657555103830753857 31504735993166327873065393)
    ·
      refine ⟨23628551994874745904799045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31504735993166327873065393 23628551994874745904799045)
      ·
        refine ⟨4430353499039014857149821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23628551994874745904799045 4430353499039014857149821)
        ·
          refine ⟨1661382562139630571431183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4430353499039014857149821 1661382562139630571431183)
          ·
            refine ⟨2492073843209445857146775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661382562139630571431183 2492073843209445857146775)
            ·
              refine ⟨3738110764814168785720163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492073843209445857146775 3738110764814168785720163)
              ·
                refine ⟨5607166147221253178580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738110764814168785720163 5607166147221253178580245)
                ·
                  refine ⟨262835913150996242745949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5607166147221253178580245 262835913150996242745949)
                  ·
                    rfl

theorem cell22_2303420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_2303420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303420 prefixEnd_2303420 := by exact prefixLift 2303420
  have htrace : WordTrace (prefixWord ++ tailWord_2303420) baseStart_2303420 baseEnd_2303420 := by
    simpa [prefixWord, tailWord_2303420, baseEnd_2303420] using wordTrace_append hprefix tailTrace_2303420
  have hstable : (prefixWord ++ tailWord_2303420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303420).length < 2 ^ (prefixWord ++ tailWord_2303420).sum := by decide
  have hdescent : baseEnd_2303420 < baseStart_2303420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303426 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2303426 : Nat := 118140960795 + 2303426 * 2 ^ 59
def prefixEnd_2303426 : Nat := 4983230072969 + 3 ^ 40 * 2303426 * 2
def baseEnd_2303426 : Nat := 262836597791868904195943

theorem tailTrace_2303426 : CollatzResearch.WordTrace tailWord_2303426 prefixEnd_2303426 262836597791868904195943 := by
  unfold tailWord_2303426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003212038272117671556533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56008565435392313790817421 21003212038272117671556533)
  ·
    refine ⟨1969051128588011031708425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21003212038272117671556533 1969051128588011031708425)
    ·
      refine ⟨1476788346441008273781319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1969051128588011031708425 1476788346441008273781319)
      ·
        refine ⟨2215182519661512410671979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476788346441008273781319 2215182519661512410671979)
        ·
          refine ⟨3322773779492268616007969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215182519661512410671979 3322773779492268616007969)
          ·
            refine ⟨2492080334619201462005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3322773779492268616007969 2492080334619201462005977)
            ·
              refine ⟨1869060250964401096504483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492080334619201462005977 1869060250964401096504483)
              ·
                refine ⟨2803590376446601644756725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869060250964401096504483 2803590376446601644756725)
                ·
                  refine ⟨262836597791868904195943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2803590376446601644756725 262836597791868904195943)
                  ·
                    rfl

theorem cell22_2303426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2303426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303426 prefixEnd_2303426 := by exact prefixLift 2303426
  have htrace : WordTrace (prefixWord ++ tailWord_2303426) baseStart_2303426 baseEnd_2303426 := by
    simpa [prefixWord, tailWord_2303426, baseEnd_2303426] using wordTrace_append hprefix tailTrace_2303426
  have hstable : (prefixWord ++ tailWord_2303426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303426).length < 2 ^ (prefixWord ++ tailWord_2303426).sum := by decide
  have hdescent : baseEnd_2303426 < baseStart_2303426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303480 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_2303480 : Nat := 118140960795 + 2303480 * 2 ^ 59
def prefixEnd_2303480 : Nat := 4983230072969 + 3 ^ 40 * 2303480 * 2
def baseEnd_2303480 : Nat := 788528278679168571737663

theorem tailTrace_2303480 : CollatzResearch.WordTrace tailWord_2303480 prefixEnd_2303480 788528278679168571737663 := by
  unfold tailWord_2303480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42007408847446418954345947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56009878463261891939127929 42007408847446418954345947)
  ·
    refine ⟨63011113271169628431518921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42007408847446418954345947 63011113271169628431518921)
    ·
      refine ⟨47258334953377221323639191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63011113271169628431518921 47258334953377221323639191)
      ·
        refine ⟨70887502430065831985458787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47258334953377221323639191 70887502430065831985458787)
        ·
          refine ⟨106331253645098747978188181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70887502430065831985458787 106331253645098747978188181)
          ·
            refine ⟨4984277514614003811477571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106331253645098747978188181 4984277514614003811477571)
            ·
              refine ⟨7476416271921005717216357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984277514614003811477571 7476416271921005717216357)
              ·
                refine ⟨1401828050985188571978067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7476416271921005717216357 1401828050985188571978067)
                ·
                  refine ⟨2102742076477782857967101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401828050985188571978067 2102742076477782857967101)
                  ·
                    refine ⟨788528278679168571737663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102742076477782857967101 788528278679168571737663)
                    ·
                      rfl

theorem cell22_2303480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_2303480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303480 prefixEnd_2303480 := by exact prefixLift 2303480
  have htrace : WordTrace (prefixWord ++ tailWord_2303480) baseStart_2303480 baseEnd_2303480 := by
    simpa [prefixWord, tailWord_2303480, baseEnd_2303480] using wordTrace_append hprefix tailTrace_2303480
  have hstable : (prefixWord ++ tailWord_2303480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303480).length < 2 ^ (prefixWord ++ tailWord_2303480).sum := by decide
  have hdescent : baseEnd_2303480 < baseStart_2303480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303551 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_2303551 : Nat := 118140960795 + 2303551 * 2 ^ 59
def prefixEnd_2303551 : Nat := 4983230072969 + 3 ^ 40 * 2303551 * 2
def baseEnd_2303551 : Nat := 788552583430148053212445

theorem tailTrace_2303551 : CollatzResearch.WordTrace tailWord_2303551 prefixEnd_2303551 788552583430148053212445 := by
  unfold tailWord_2303551
  simp only [CollatzResearch.WordTrace]
  refine ⟨84017407277635617034526507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56011604851757078023017671 84017407277635617034526507)
  ·
    refine ⟨126026110916453425551789761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84017407277635617034526507 126026110916453425551789761)
    ·
      refine ⟨94519583187340069163842321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126026110916453425551789761 94519583187340069163842321)
      ·
        refine ⟨70889687390505051872881741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94519583187340069163842321 70889687390505051872881741)
        ·
          refine ⟨26583632771439394452330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70889687390505051872881741 26583632771439394452330653)
          ·
            refine ⟨9968862289289772919623995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26583632771439394452330653 9968862289289772919623995)
            ·
              refine ⟨14953293433934659379435993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9968862289289772919623995 14953293433934659379435993)
              ·
                refine ⟨11214970075450994534576995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14953293433934659379435993 11214970075450994534576995)
                ·
                  refine ⟨16822455113176491801865493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11214970075450994534576995 16822455113176491801865493)
                  ·
                    refine ⟨788552583430148053212445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16822455113176491801865493 788552583430148053212445)
                    ·
                      rfl

theorem cell22_2303551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_2303551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303551 prefixEnd_2303551 := by exact prefixLift 2303551
  have htrace : WordTrace (prefixWord ++ tailWord_2303551) baseStart_2303551 baseEnd_2303551 := by
    simpa [prefixWord, tailWord_2303551, baseEnd_2303551] using wordTrace_append hprefix tailTrace_2303551
  have hstable : (prefixWord ++ tailWord_2303551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303551).length < 2 ^ (prefixWord ++ tailWord_2303551).sum := by decide
  have hdescent : baseEnd_2303551 < baseStart_2303551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303596 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2303596 : Nat := 118140960795 + 2303596 * 2 ^ 59
def prefixEnd_2303596 : Nat := 4983230072969 + 3 ^ 40 * 2303596 * 2
def baseEnd_2303596 : Nat := 788567987849782935837307

theorem tailTrace_2303596 : CollatzResearch.WordTrace tailWord_2303596 prefixEnd_2303596 788567987849782935837307 := by
  unfold tailWord_2303596
  simp only [CollatzResearch.WordTrace]
  refine ⟨42009524281236294859957321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56012699041648393146609761 42009524281236294859957321)
  ·
    refine ⟨31507143210927221144967991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42009524281236294859957321 31507143210927221144967991)
    ·
      refine ⟨47260714816390831717451987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31507143210927221144967991 47260714816390831717451987)
      ·
        refine ⟨70891072224586247576177981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47260714816390831717451987 70891072224586247576177981)
        ·
          refine ⟨26584152084219842841066743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70891072224586247576177981 26584152084219842841066743)
          ·
            refine ⟨39876228126329764261600115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26584152084219842841066743 39876228126329764261600115)
            ·
              refine ⟨59814342189494646392400173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39876228126329764261600115 59814342189494646392400173)
              ·
                refine ⟨22430378321060492397150065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59814342189494646392400173 22430378321060492397150065)
                ·
                  refine ⟨16822783740795369297862549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22430378321060492397150065 16822783740795369297862549)
                  ·
                    refine ⟨788567987849782935837307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16822783740795369297862549 788567987849782935837307)
                    ·
                      rfl

theorem cell22_2303596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2303596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303596 prefixEnd_2303596 := by exact prefixLift 2303596
  have htrace : WordTrace (prefixWord ++ tailWord_2303596) baseStart_2303596 baseEnd_2303596 := by
    simpa [prefixWord, tailWord_2303596, baseEnd_2303596] using wordTrace_append hprefix tailTrace_2303596
  have hstable : (prefixWord ++ tailWord_2303596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303596).length < 2 ^ (prefixWord ++ tailWord_2303596).sum := by decide
  have hdescent : baseEnd_2303596 < baseStart_2303596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303649 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2303649 : Nat := 118140960795 + 2303649 * 2 ^ 59
def prefixEnd_2303649 : Nat := 4983230072969 + 3 ^ 40 * 2303649 * 2
def baseEnd_2303649 : Nat := 788586130832908464262145

theorem tailTrace_2303649 : CollatzResearch.WordTrace tailWord_2303649 prefixEnd_2303649 788586130832908464262145 := by
  unfold tailWord_2303649
  simp only [CollatzResearch.WordTrace]
  refine ⟨84020981631280579771594001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56013987754187053181062667 84020981631280579771594001)
  ·
    refine ⟨63015736223460434828695501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84020981631280579771594001 63015736223460434828695501)
    ·
      refine ⟨23630901083797663060760813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63015736223460434828695501 23630901083797663060760813)
      ·
        refine ⟨8861587906424123647785305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23630901083797663060760813 8861587906424123647785305)
        ·
          refine ⟨6646190929818092735838979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861587906424123647785305 6646190929818092735838979)
          ·
            refine ⟨9969286394727139103758469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646190929818092735838979 9969286394727139103758469)
            ·
              refine ⟨1869241199011338581954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9969286394727139103758469 1869241199011338581954713)
              ·
                refine ⟨1401930899258503936466035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869241199011338581954713 1401930899258503936466035)
                ·
                  refine ⟨2102896348887755904699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401930899258503936466035 2102896348887755904699053)
                  ·
                    refine ⟨788586130832908464262145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102896348887755904699053 788586130832908464262145)
                    ·
                      rfl

theorem cell22_2303649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2303649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303649 prefixEnd_2303649 := by exact prefixLift 2303649
  have htrace : WordTrace (prefixWord ++ tailWord_2303649) baseStart_2303649 baseEnd_2303649 := by
    simpa [prefixWord, tailWord_2303649, baseEnd_2303649] using wordTrace_append hprefix tailTrace_2303649
  have hstable : (prefixWord ++ tailWord_2303649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303649).length < 2 ^ (prefixWord ++ tailWord_2303649).sum := by decide
  have hdescent : baseEnd_2303649 < baseStart_2303649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303688 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2303688 : Nat := 118140960795 + 2303688 * 2 ^ 59
def prefixEnd_2303688 : Nat := 4983230072969 + 3 ^ 40 * 2303688 * 2
def baseEnd_2303688 : Nat := 788599481329925362537025

theorem tailTrace_2303688 : CollatzResearch.WordTrace tailWord_2303688 prefixEnd_2303688 788599481329925362537025 := by
  unfold tailWord_2303688
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011202039069644716131859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56014936052092859621509145 42011202039069644716131859)
  ·
    refine ⟨63016803058604467074197789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42011202039069644716131859 63016803058604467074197789)
    ·
      refine ⟨23631301146976675152824171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63016803058604467074197789 23631301146976675152824171)
      ·
        refine ⟨35446951720465012729236257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23631301146976675152824171 35446951720465012729236257)
        ·
          refine ⟨26585213790348759546927193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35446951720465012729236257 26585213790348759546927193)
          ·
            refine ⟨19938910342761569660195395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26585213790348759546927193 19938910342761569660195395)
            ·
              refine ⟨29908365514142354490293093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19938910342761569660195395 29908365514142354490293093)
              ·
                refine ⟨5607818533901691466929955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29908365514142354490293093 5607818533901691466929955)
                ·
                  refine ⟨8411727800852537200394933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607818533901691466929955 8411727800852537200394933)
                  ·
                    refine ⟨788599481329925362537025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8411727800852537200394933 788599481329925362537025)
                    ·
                      rfl

theorem cell22_2303688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2303688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303688 prefixEnd_2303688 := by exact prefixLift 2303688
  have htrace : WordTrace (prefixWord ++ tailWord_2303688) baseStart_2303688 baseEnd_2303688 := by
    simpa [prefixWord, tailWord_2303688, baseEnd_2303688] using wordTrace_append hprefix tailTrace_2303688
  have hstable : (prefixWord ++ tailWord_2303688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303688).length < 2 ^ (prefixWord ++ tailWord_2303688).sum := by decide
  have hdescent : baseEnd_2303688 < baseStart_2303688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303692 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_2303692 : Nat := 118140960795 + 2303692 * 2 ^ 59
def prefixEnd_2303692 : Nat := 4983230072969 + 3 ^ 40 * 2303692 * 2
def baseEnd_2303692 : Nat := 788600850611670685437013

theorem tailTrace_2303692 : CollatzResearch.WordTrace tailWord_2303692 prefixEnd_2303692 788600850611670685437013 := by
  unfold tailWord_2303692
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011274985062399057704665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56015033313416532076939553 42011274985062399057704665)
  ·
    refine ⟨31508456238796799293278499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42011274985062399057704665 31508456238796799293278499)
    ·
      refine ⟨47262684358195198939917749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31508456238796799293278499 47262684358195198939917749)
      ·
        refine ⟨4430876658580799900617289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47262684358195198939917749 4430876658580799900617289)
        ·
          refine ⟨3323157493935599925462967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4430876658580799900617289 3323157493935599925462967)
          ·
            refine ⟨4984736240903399888194451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323157493935599925462967 4984736240903399888194451)
            ·
              refine ⟨7477104361355099832291677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984736240903399888194451 7477104361355099832291677)
              ·
                refine ⟨2803914135508162437109379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7477104361355099832291677 2803914135508162437109379)
                ·
                  refine ⟨4205871203262243655664069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803914135508162437109379 4205871203262243655664069)
                  ·
                    refine ⟨788600850611670685437013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205871203262243655664069 788600850611670685437013)
                    ·
                      rfl

theorem cell22_2303692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_2303692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303692 prefixEnd_2303692 := by exact prefixLift 2303692
  have htrace : WordTrace (prefixWord ++ tailWord_2303692) baseStart_2303692 baseEnd_2303692 := by
    simpa [prefixWord, tailWord_2303692, baseEnd_2303692] using wordTrace_append hprefix tailTrace_2303692
  have hstable : (prefixWord ++ tailWord_2303692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303692).length < 2 ^ (prefixWord ++ tailWord_2303692).sum := by decide
  have hdescent : baseEnd_2303692 < baseStart_2303692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303703 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2303703 : Nat := 118140960795 + 2303703 * 2 ^ 59
def prefixEnd_2303703 : Nat := 4983230072969 + 3 ^ 40 * 2303703 * 2
def baseEnd_2303703 : Nat := 788604616136470323411979

theorem tailTrace_2303703 : CollatzResearch.WordTrace tailWord_2303703 prefixEnd_2303703 788604616136470323411979 := by
  unfold tailWord_2303703
  simp only [CollatzResearch.WordTrace]
  refine ⟨84022951173084946994059763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56015300782056631329373175 84022951173084946994059763)
  ·
    refine ⟨126034426759627420491089645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84022951173084946994059763 126034426759627420491089645)
    ·
      refine ⟨47262910034860282684158617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126034426759627420491089645 47262910034860282684158617)
      ·
        refine ⟨35447182526145212013118963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47262910034860282684158617 35447182526145212013118963)
        ·
          refine ⟨53170773789217818019678445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35447182526145212013118963 53170773789217818019678445)
          ·
            refine ⟨19939040170956681757379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53170773789217818019678445 19939040170956681757379417)
            ·
              refine ⟨14954280128217511318034563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19939040170956681757379417 14954280128217511318034563)
              ·
                refine ⟨22431420192326266977051845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14954280128217511318034563 22431420192326266977051845)
                ·
                  refine ⟨4205891286061175058197221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22431420192326266977051845 4205891286061175058197221)
                  ·
                    refine ⟨788604616136470323411979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205891286061175058197221 788604616136470323411979)
                    ·
                      rfl

theorem cell22_2303703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2303703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303703 prefixEnd_2303703 := by exact prefixLift 2303703
  have htrace : WordTrace (prefixWord ++ tailWord_2303703) baseStart_2303703 baseEnd_2303703 := by
    simpa [prefixWord, tailWord_2303703, baseEnd_2303703] using wordTrace_append hprefix tailTrace_2303703
  have hstable : (prefixWord ++ tailWord_2303703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303703).length < 2 ^ (prefixWord ++ tailWord_2303703).sum := by decide
  have hdescent : baseEnd_2303703 < baseStart_2303703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303705 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_2303705 : Nat := 118140960795 + 2303705 * 2 ^ 59
def prefixEnd_2303705 : Nat := 4983230072969 + 3 ^ 40 * 2303705 * 2
def baseEnd_2303705 : Nat := 788605300777342984861973

theorem tailTrace_2303705 : CollatzResearch.WordTrace tailWord_2303705 prefixEnd_2303705 788605300777342984861973 := by
  unfold tailWord_2303705
  simp only [CollatzResearch.WordTrace]
  refine ⟨84023024119077701335632569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56015349412718467557088379 84023024119077701335632569)
  ·
    refine ⟨63017268089308276001724427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84023024119077701335632569 63017268089308276001724427)
    ·
      refine ⟨94525902133962414002586641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63017268089308276001724427 94525902133962414002586641)
      ·
        refine ⟨70894426600471810501939981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94525902133962414002586641 70894426600471810501939981)
        ·
          refine ⟨26585409975176928938227493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70894426600471810501939981 26585409975176928938227493)
          ·
            refine ⟨4984764370345674175917655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26585409975176928938227493 4984764370345674175917655)
            ·
              refine ⟨7477146555518511263876483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984764370345674175917655 7477146555518511263876483)
              ·
                refine ⟨11215719833277766895814725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477146555518511263876483 11215719833277766895814725)
                ·
                  refine ⟨2102947468739581292965261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11215719833277766895814725 2102947468739581292965261)
                  ·
                    refine ⟨788605300777342984861973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102947468739581292965261 788605300777342984861973)
                    ·
                      rfl

theorem cell22_2303705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_2303705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303705 prefixEnd_2303705 := by exact prefixLift 2303705
  have htrace : WordTrace (prefixWord ++ tailWord_2303705) baseStart_2303705 baseEnd_2303705 := by
    simpa [prefixWord, tailWord_2303705, baseEnd_2303705] using wordTrace_append hprefix tailTrace_2303705
  have hstable : (prefixWord ++ tailWord_2303705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303705).length < 2 ^ (prefixWord ++ tailWord_2303705).sum := by decide
  have hdescent : baseEnd_2303705 < baseStart_2303705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303767 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2303767 : Nat := 118140960795 + 2303767 * 2 ^ 59
def prefixEnd_2303767 : Nat := 4983230072969 + 3 ^ 40 * 2303767 * 2
def baseEnd_2303767 : Nat := 788626524644395489811783

theorem tailTrace_2303767 : CollatzResearch.WordTrace tailWord_2303767 prefixEnd_2303767 788626524644395489811783 := by
  unfold tailWord_2303767
  simp only [CollatzResearch.WordTrace]
  refine ⟨84025285444853085924389555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56016856963235390616259703 84025285444853085924389555)
  ·
    refine ⟨126037928167279628886584333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84025285444853085924389555 126037928167279628886584333)
    ·
      refine ⟨47264223062729860832469125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126037928167279628886584333 47264223062729860832469125)
      ·
        refine ⟨8862041824261848906087961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47264223062729860832469125 8862041824261848906087961)
        ·
          refine ⟨6646531368196386679565971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8862041824261848906087961 6646531368196386679565971)
          ·
            refine ⟨9969797052294580019348957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646531368196386679565971 9969797052294580019348957)
            ·
              refine ⟨3738673894610467507255859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9969797052294580019348957 3738673894610467507255859)
              ·
                refine ⟨5608010841915701260883789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738673894610467507255859 5608010841915701260883789)
                ·
                  refine ⟨2103004065718387972831421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5608010841915701260883789 2103004065718387972831421)
                  ·
                    refine ⟨788626524644395489811783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103004065718387972831421 788626524644395489811783)
                    ·
                      rfl

theorem cell22_2303767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2303767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303767 prefixEnd_2303767 := by exact prefixLift 2303767
  have htrace : WordTrace (prefixWord ++ tailWord_2303767) baseStart_2303767 baseEnd_2303767 := by
    simpa [prefixWord, tailWord_2303767, baseEnd_2303767] using wordTrace_append hprefix tailTrace_2303767
  have hstable : (prefixWord ++ tailWord_2303767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303767).length < 2 ^ (prefixWord ++ tailWord_2303767).sum := by decide
  have hdescent : baseEnd_2303767 < baseStart_2303767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303814 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2303814 : Nat := 118140960795 + 2303814 * 2 ^ 59
def prefixEnd_2303814 : Nat := 4983230072969 + 3 ^ 40 * 2303814 * 2
def baseEnd_2303814 : Nat := 262880871234967677962213

theorem tailTrace_2303814 : CollatzResearch.WordTrace tailWord_2303814 prefixEnd_2303814 262880871234967677962213 := by
  unfold tailWord_2303814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625843739865087904729703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56017999783788541967566997 2625843739865087904729703)
  ·
    refine ⟨3938765609797631857094555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2625843739865087904729703 3938765609797631857094555)
    ·
      refine ⟨5908148414696447785641833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3938765609797631857094555 5908148414696447785641833)
      ·
        refine ⟨4431111311022335839231375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5908148414696447785641833 4431111311022335839231375)
        ·
          refine ⟨6646666966533503758847063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431111311022335839231375 6646666966533503758847063)
          ·
            refine ⟨9970000449800255638270595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646666966533503758847063 9970000449800255638270595)
            ·
              refine ⟨14955000674700383457405893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9970000449800255638270595 14955000674700383457405893)
              ·
                refine ⟨2804062626506321898263605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14955000674700383457405893 2804062626506321898263605)
                ·
                  refine ⟨262880871234967677962213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804062626506321898263605 262880871234967677962213)
                  ·
                    rfl

theorem cell22_2303814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2303814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303814 prefixEnd_2303814 := by exact prefixLift 2303814
  have htrace : WordTrace (prefixWord ++ tailWord_2303814) baseStart_2303814 baseEnd_2303814 := by
    simpa [prefixWord, tailWord_2303814, baseEnd_2303814] using wordTrace_append hprefix tailTrace_2303814
  have hstable : (prefixWord ++ tailWord_2303814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303814).length < 2 ^ (prefixWord ++ tailWord_2303814).sum := by decide
  have hdescent : baseEnd_2303814 < baseStart_2303814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303840 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_2303840 : Nat := 118140960795 + 2303840 * 2 ^ 59
def prefixEnd_2303840 : Nat := 4983230072969 + 3 ^ 40 * 2303840 * 2
def baseEnd_2303840 : Nat := 788651514036247632736559

theorem tailTrace_2303840 : CollatzResearch.WordTrace tailWord_2303840 prefixEnd_2303840 788651514036247632736559 := by
  unfold tailWord_2303840
  simp only [CollatzResearch.WordTrace]
  refine ⟨42013973986794309695898487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56018631982392412927864649 42013973986794309695898487)
  ·
    refine ⟨63020960980191464543847731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42013973986794309695898487 63020960980191464543847731)
    ·
      refine ⟨94531441470287196815771597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63020960980191464543847731 94531441470287196815771597)
      ·
        refine ⟨35449290551357698805914349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94531441470287196815771597 35449290551357698805914349)
        ·
          refine ⟨13293483956759137052217881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35449290551357698805914349 13293483956759137052217881)
          ·
            refine ⟨9970112967569352789163411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13293483956759137052217881 9970112967569352789163411)
            ·
              refine ⟨14955169451354029183745117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9970112967569352789163411 14955169451354029183745117)
              ·
                refine ⟨5608188544257760943904419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14955169451354029183745117 5608188544257760943904419)
                ·
                  refine ⟨8412282816386641415856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608188544257760943904419 8412282816386641415856629)
                  ·
                    refine ⟨788651514036247632736559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8412282816386641415856629 788651514036247632736559)
                    ·
                      rfl

theorem cell22_2303840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_2303840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303840 prefixEnd_2303840 := by exact prefixLift 2303840
  have htrace : WordTrace (prefixWord ++ tailWord_2303840) baseStart_2303840 baseEnd_2303840 := by
    simpa [prefixWord, tailWord_2303840, baseEnd_2303840] using wordTrace_append hprefix tailTrace_2303840
  have hstable : (prefixWord ++ tailWord_2303840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303840).length < 2 ^ (prefixWord ++ tailWord_2303840).sum := by decide
  have hdescent : baseEnd_2303840 < baseStart_2303840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303842 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2303842 : Nat := 118140960795 + 2303842 * 2 ^ 59
def prefixEnd_2303842 : Nat := 4983230072969 + 3 ^ 40 * 2303842 * 2
def baseEnd_2303842 : Nat := 262884066225706764728851

theorem tailTrace_2303842 : CollatzResearch.WordTrace tailWord_2303842 prefixEnd_2303842 262884066225706764728851 := by
  unfold tailWord_2303842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007005229895343433342445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56018680613054249155579853 21007005229895343433342445)
  ·
    refine ⟨7877626961210753787503417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21007005229895343433342445 7877626961210753787503417)
    ·
      refine ⟨5908220220908065340627563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7877626961210753787503417 5908220220908065340627563)
      ·
        refine ⟨8862330331362098010941345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908220220908065340627563 8862330331362098010941345)
        ·
          refine ⟨6646747748521573508206009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8862330331362098010941345 6646747748521573508206009)
          ·
            refine ⟨4985060811391180131154507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646747748521573508206009 4985060811391180131154507)
            ·
              refine ⟨7477591217086770196731761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985060811391180131154507 7477591217086770196731761)
              ·
                refine ⟨5608193412815077647548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477591217086770196731761 5608193412815077647548821)
                ·
                  refine ⟨262884066225706764728851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5608193412815077647548821 262884066225706764728851)
                  ·
                    rfl

theorem cell22_2303842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2303842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303842 prefixEnd_2303842 := by exact prefixLift 2303842
  have htrace : WordTrace (prefixWord ++ tailWord_2303842) baseStart_2303842 baseEnd_2303842 := by
    simpa [prefixWord, tailWord_2303842, baseEnd_2303842] using wordTrace_append hprefix tailTrace_2303842
  have hstable : (prefixWord ++ tailWord_2303842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303842).length < 2 ^ (prefixWord ++ tailWord_2303842).sum := by decide
  have hdescent : baseEnd_2303842 < baseStart_2303842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303930 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_2303930 : Nat := 118140960795 + 2303930 * 2 ^ 59
def prefixEnd_2303930 : Nat := 4983230072969 + 3 ^ 40 * 2303930 * 2
def baseEnd_2303930 : Nat := 788682322875517397986283

theorem tailTrace_2303930 : CollatzResearch.WordTrace tailWord_2303930 prefixEnd_2303930 788682322875517397986283 := by
  unfold tailWord_2303930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007807635815641190643311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56020820362175043175048829 21007807635815641190643311)
  ·
    refine ⟨31511711453723461785964967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21007807635815641190643311 31511711453723461785964967)
    ·
      refine ⟨47267567180585192678947451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31511711453723461785964967 47267567180585192678947451)
      ·
        refine ⟨70901350770877789018421177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47267567180585192678947451 70901350770877789018421177)
        ·
          refine ⟨53176013078158341763815883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70901350770877789018421177 53176013078158341763815883)
          ·
            refine ⟨79764019617237512645723825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53176013078158341763815883 79764019617237512645723825)
            ·
              refine ⟨59823014712928134484292869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79764019617237512645723825 59823014712928134484292869)
              ·
                refine ⟨11216815258674025215804913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59823014712928134484292869 11216815258674025215804913)
                ·
                  refine ⟨8412611444005518911853685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11216815258674025215804913 8412611444005518911853685)
                  ·
                    refine ⟨788682322875517397986283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8412611444005518911853685 788682322875517397986283)
                    ·
                      rfl

theorem cell22_2303930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_2303930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303930 prefixEnd_2303930 := by exact prefixLift 2303930
  have htrace : WordTrace (prefixWord ++ tailWord_2303930) baseStart_2303930 baseEnd_2303930 := by
    simpa [prefixWord, tailWord_2303930, baseEnd_2303930] using wordTrace_append hprefix tailTrace_2303930
  have hstable : (prefixWord ++ tailWord_2303930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303930).length < 2 ^ (prefixWord ++ tailWord_2303930).sum := by decide
  have hdescent : baseEnd_2303930 < baseStart_2303930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303936 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_2303936 : Nat := 118140960795 + 2303936 * 2 ^ 59
def prefixEnd_2303936 : Nat := 4983230072969 + 3 ^ 40 * 2303936 * 2
def baseEnd_2303936 : Nat := 788684376798135382336265

theorem tailTrace_2303936 : CollatzResearch.WordTrace tailWord_2303936 prefixEnd_2303936 788684376798135382336265 := by
  unfold tailWord_2303936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42015724690620413893645831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56020966254160551858194441 42015724690620413893645831)
  ·
    refine ⟨63023587035930620840468747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42015724690620413893645831 63023587035930620840468747)
    ·
      refine ⟨94535380553895931260703121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63023587035930620840468747 94535380553895931260703121)
      ·
        refine ⟨70901535415421948445527341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94535380553895931260703121 70901535415421948445527341)
        ·
          refine ⟨26588075780783230667072753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70901535415421948445527341 26588075780783230667072753)
          ·
            refine ⟨19941056835587423000304565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26588075780783230667072753 19941056835587423000304565)
            ·
              refine ⟨1869474078336320906278553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19941056835587423000304565 1869474078336320906278553)
              ·
                refine ⟨1402105558752240679708915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869474078336320906278553 1402105558752240679708915)
                ·
                  refine ⟨2103158338128361019563373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402105558752240679708915 2103158338128361019563373)
                  ·
                    refine ⟨788684376798135382336265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103158338128361019563373 788684376798135382336265)
                    ·
                      rfl

theorem cell22_2303936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_2303936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303936 prefixEnd_2303936 := by exact prefixLift 2303936
  have htrace : WordTrace (prefixWord ++ tailWord_2303936) baseStart_2303936 baseEnd_2303936 := by
    simpa [prefixWord, tailWord_2303936, baseEnd_2303936] using wordTrace_append hprefix tailTrace_2303936
  have hstable : (prefixWord ++ tailWord_2303936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303936).length < 2 ^ (prefixWord ++ tailWord_2303936).sum := by decide
  have hdescent : baseEnd_2303936 < baseStart_2303936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303945 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_2303945 : Nat := 118140960795 + 2303945 * 2 ^ 59
def prefixEnd_2303945 : Nat := 4983230072969 + 3 ^ 40 * 2303945 * 2
def baseEnd_2303945 : Nat := 788687457682062358861237

theorem tailTrace_2303945 : CollatzResearch.WordTrace tailWord_2303945 prefixEnd_2303945 788687457682062358861237 := by
  unfold tailWord_2303945
  simp only [CollatzResearch.WordTrace]
  refine ⟨84031777638208222324369289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56021185092138814882912859 84031777638208222324369289)
  ·
    refine ⟨63023833228656166743276967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84031777638208222324369289 63023833228656166743276967)
    ·
      refine ⟨94535749842984250114915451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63023833228656166743276967 94535749842984250114915451)
      ·
        refine ⟨141803624764476375172373177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94535749842984250114915451 141803624764476375172373177)
        ·
          refine ⟨106352718573357281379279883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141803624764476375172373177 106352718573357281379279883)
          ·
            refine ⟨159529077860035922068919825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106352718573357281379279883 159529077860035922068919825)
            ·
              refine ⟨119646808395026941551689869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159529077860035922068919825 119646808395026941551689869)
              ·
                refine ⟨44867553148135103081883701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119646808395026941551689869 44867553148135103081883701)
                ·
                  refine ⟨4206333107637665913926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44867553148135103081883701 4206333107637665913926597)
                  ·
                    refine ⟨788687457682062358861237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206333107637665913926597 788687457682062358861237)
                    ·
                      rfl

theorem cell22_2303945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_2303945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303945 prefixEnd_2303945 := by exact prefixLift 2303945
  have htrace : WordTrace (prefixWord ++ tailWord_2303945) baseStart_2303945 baseEnd_2303945 := by
    simpa [prefixWord, tailWord_2303945, baseEnd_2303945] using wordTrace_append hprefix tailTrace_2303945
  have hstable : (prefixWord ++ tailWord_2303945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303945).length < 2 ^ (prefixWord ++ tailWord_2303945).sum := by decide
  have hdescent : baseEnd_2303945 < baseStart_2303945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303960 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_2303960 : Nat := 118140960795 + 2303960 * 2 ^ 59
def prefixEnd_2303960 : Nat := 4983230072969 + 3 ^ 40 * 2303960 * 2
def baseEnd_2303960 : Nat := 262897530829535773245397

theorem tailTrace_2303960 : CollatzResearch.WordTrace tailWord_2303960 prefixEnd_2303960 262897530829535773245397 := by
  unfold tailWord_2303960
  simp only [CollatzResearch.WordTrace]
  refine ⟨42016162366576939943082667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56021549822102586590776889 42016162366576939943082667)
  ·
    refine ⟨63024243549865409914624001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42016162366576939943082667 63024243549865409914624001)
    ·
      refine ⟨47268182662399057435968001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63024243549865409914624001 47268182662399057435968001)
      ·
        refine ⟨35451136996799293076976001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47268182662399057435968001 35451136996799293076976001)
        ·
          refine ⟨26588352747599469807732001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35451136996799293076976001 26588352747599469807732001)
          ·
            refine ⟨19941264560699602355799001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26588352747599469807732001 19941264560699602355799001)
            ·
              refine ⟨14955948420524701766849251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19941264560699602355799001 14955948420524701766849251)
              ·
                refine ⟨22433922630787052650273877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14955948420524701766849251 22433922630787052650273877)
                ·
                  refine ⟨262897530829535773245397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22433922630787052650273877 262897530829535773245397)
                  ·
                    rfl

theorem cell22_2303960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_2303960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303960 prefixEnd_2303960 := by exact prefixLift 2303960
  have htrace : WordTrace (prefixWord ++ tailWord_2303960) baseStart_2303960 baseEnd_2303960 := by
    simpa [prefixWord, tailWord_2303960, baseEnd_2303960] using wordTrace_append hprefix tailTrace_2303960
  have hstable : (prefixWord ++ tailWord_2303960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303960).length < 2 ^ (prefixWord ++ tailWord_2303960).sum := by decide
  have hdescent : baseEnd_2303960 < baseStart_2303960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303992 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_2303992 : Nat := 118140960795 + 2303992 * 2 ^ 59
def prefixEnd_2303992 : Nat := 4983230072969 + 3 ^ 40 * 2303992 * 2
def baseEnd_2303992 : Nat := 788703546742569902936093

theorem tailTrace_2303992 : CollatzResearch.WordTrace tailWord_2303992 prefixEnd_2303992 788703546742569902936093 := by
  unfold tailWord_2303992
  simp only [CollatzResearch.WordTrace]
  refine ⟨42016745934518974675665115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56022327912691966234220153 42016745934518974675665115)
  ·
    refine ⟨63025118901778462013497673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42016745934518974675665115 63025118901778462013497673)
    ·
      refine ⟨47268839176333846510123255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63025118901778462013497673 47268839176333846510123255)
      ·
        refine ⟨70903258764500769765184883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47268839176333846510123255 70903258764500769765184883)
        ·
          refine ⟨106354888146751154647777325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70903258764500769765184883 106354888146751154647777325)
          ·
            refine ⟨39883083055031682992916497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106354888146751154647777325 39883083055031682992916497)
            ·
              refine ⟨29912312291273762244687373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39883083055031682992916497 29912312291273762244687373)
              ·
                refine ⟨11217117109227660841757765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29912312291273762244687373 11217117109227660841757765)
                ·
                  refine ⟨2103209457980186407829581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11217117109227660841757765 2103209457980186407829581)
                  ·
                    refine ⟨788703546742569902936093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103209457980186407829581 788703546742569902936093)
                    ·
                      rfl

theorem cell22_2303992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_2303992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2303992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2303992 prefixEnd_2303992 := by exact prefixLift 2303992
  have htrace : WordTrace (prefixWord ++ tailWord_2303992) baseStart_2303992 baseEnd_2303992 := by
    simpa [prefixWord, tailWord_2303992, baseEnd_2303992] using wordTrace_append hprefix tailTrace_2303992
  have hstable : (prefixWord ++ tailWord_2303992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303992).length < 2 ^ (prefixWord ++ tailWord_2303992).sum := by decide
  have hdescent : baseEnd_2303992 < baseStart_2303992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304039 : List Nat := [1, 1, 7, 1, 2, 1, 9]
def baseStart_2304039 : Nat := 118140960795 + 2304039 * 2 ^ 59
def prefixEnd_2304039 : Nat := 4983230072969 + 3 ^ 40 * 2304039 * 2
def baseEnd_2304039 : Nat := 29211838363076942481887

theorem tailTrace_2304039 : CollatzResearch.WordTrace tailWord_2304039 prefixEnd_2304039 29211838363076942481887 := by
  unfold tailWord_2304039
  simp only [CollatzResearch.WordTrace]
  refine ⟨84035206099867676378291171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56023470733245117585527447 84035206099867676378291171)
  ·
    refine ⟨126052809149801514567436757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84035206099867676378291171 126052809149801514567436757)
    ·
      refine ⟨2954362714448472997674299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 126052809149801514567436757 2954362714448472997674299)
      ·
        refine ⟨4431544071672709496511449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954362714448472997674299 4431544071672709496511449)
        ·
          refine ⟨3323658053754532122383587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4431544071672709496511449 3323658053754532122383587)
          ·
            refine ⟨4985487080631798183575381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323658053754532122383587 4985487080631798183575381)
            ·
              refine ⟨29211838363076942481887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4985487080631798183575381 29211838363076942481887)
              ·
                rfl

theorem cell22_2304039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 9].length) (baseStart_2304039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304039 prefixEnd_2304039 := by exact prefixLift 2304039
  have htrace : WordTrace (prefixWord ++ tailWord_2304039) baseStart_2304039 baseEnd_2304039 := by
    simpa [prefixWord, tailWord_2304039, baseEnd_2304039] using wordTrace_append hprefix tailTrace_2304039
  have hstable : (prefixWord ++ tailWord_2304039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304039).length < 2 ^ (prefixWord ++ tailWord_2304039).sum := by decide
  have hdescent : baseEnd_2304039 < baseStart_2304039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304088 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_2304088 : Nat := 118140960795 + 2304088 * 2 ^ 59
def prefixEnd_2304088 : Nat := 4983230072969 + 3 ^ 40 * 2304088 * 2
def baseEnd_2304088 : Nat := 788736409504457652535799

theorem tailTrace_2304088 : CollatzResearch.WordTrace tailWord_2304088 prefixEnd_2304088 788736409504457652535799 := by
  unfold tailWord_2304088
  simp only [CollatzResearch.WordTrace]
  refine ⟨42018496638345078873412459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56024662184460105164549945 42018496638345078873412459)
  ·
    refine ⟨63027744957517618310118689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42018496638345078873412459 63027744957517618310118689)
    ·
      refine ⟨47270808718138213732589017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63027744957517618310118689 47270808718138213732589017)
      ·
        refine ⟨35453106538603660299441763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47270808718138213732589017 35453106538603660299441763)
        ·
          refine ⟨53179659807905490449162645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35453106538603660299441763 53179659807905490449162645)
          ·
            refine ⟨2492796553495569864804499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53179659807905490449162645 2492796553495569864804499)
            ·
              refine ⟨3739194830243354797206749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492796553495569864804499 3739194830243354797206749)
              ·
                refine ⟨1402198061341258048952531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3739194830243354797206749 1402198061341258048952531)
                ·
                  refine ⟨2103297092011887073428797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402198061341258048952531 2103297092011887073428797)
                  ·
                    refine ⟨788736409504457652535799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103297092011887073428797 788736409504457652535799)
                    ·
                      rfl

theorem cell22_2304088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_2304088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304088 prefixEnd_2304088 := by exact prefixLift 2304088
  have htrace : WordTrace (prefixWord ++ tailWord_2304088) baseStart_2304088 baseEnd_2304088 := by
    simpa [prefixWord, tailWord_2304088, baseEnd_2304088] using wordTrace_append hprefix tailTrace_2304088
  have hstable : (prefixWord ++ tailWord_2304088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304088).length < 2 ^ (prefixWord ++ tailWord_2304088).sum := by decide
  have hdescent : baseEnd_2304088 < baseStart_2304088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2304097 : Nat := 118140960795 + 2304097 * 2 ^ 59
def prefixEnd_2304097 : Nat := 4983230072969 + 3 ^ 40 * 2304097 * 2
def baseEnd_2304097 : Nat := 788739490388384629060771

theorem tailTrace_2304097 : CollatzResearch.WordTrace tailWord_2304097 prefixEnd_2304097 788739490388384629060771 := by
  unfold tailWord_2304097
  simp only [CollatzResearch.WordTrace]
  refine ⟨84037321533657552283902545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56024881022438368189268363 84037321533657552283902545)
  ·
    refine ⟨63027991150243164212926909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84037321533657552283902545 63027991150243164212926909)
    ·
      refine ⟨23635496681341186579847591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63027991150243164212926909 23635496681341186579847591)
      ·
        refine ⟨35453245022011779869771387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23635496681341186579847591 35453245022011779869771387)
        ·
          refine ⟨53179867533017669804657081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35453245022011779869771387 53179867533017669804657081)
          ·
            refine ⟨39884900649763252353492811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53179867533017669804657081 39884900649763252353492811)
            ·
              refine ⟨59827350974644878530239217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39884900649763252353492811 59827350974644878530239217)
              ·
                refine ⟨44870513230983658897679413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59827350974644878530239217 44870513230983658897679413)
                ·
                  refine ⟨4206610615404718021657445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44870513230983658897679413 4206610615404718021657445)
                  ·
                    refine ⟨788739490388384629060771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206610615404718021657445 788739490388384629060771)
                    ·
                      rfl

theorem cell22_2304097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2304097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304097 prefixEnd_2304097 := by exact prefixLift 2304097
  have htrace : WordTrace (prefixWord ++ tailWord_2304097) baseStart_2304097 baseEnd_2304097 := by
    simpa [prefixWord, tailWord_2304097, baseEnd_2304097] using wordTrace_append hprefix tailTrace_2304097
  have hstable : (prefixWord ++ tailWord_2304097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304097).length < 2 ^ (prefixWord ++ tailWord_2304097).sum := by decide
  have hdescent : baseEnd_2304097 < baseStart_2304097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304118 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2304118 : Nat := 118140960795 + 2304118 * 2 ^ 59
def prefixEnd_2304118 : Nat := 4983230072969 + 3 ^ 40 * 2304118 * 2
def baseEnd_2304118 : Nat := 262915559705849191428569

theorem tailTrace_2304118 : CollatzResearch.WordTrace tailWord_2304118 prefixEnd_2304118 262915559705849191428569 := by
  unfold tailWord_2304118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252380466661342054401063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56025391644387648580278005 5252380466661342054401063)
  ·
    refine ⟨7878570699992013081601595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5252380466661342054401063 7878570699992013081601595)
    ·
      refine ⟨11817856049988019622402393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7878570699992013081601595 11817856049988019622402393)
      ·
        refine ⟨8863392037491014716801795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11817856049988019622402393 8863392037491014716801795)
        ·
          refine ⟨13295088056236522075202693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863392037491014716801795 13295088056236522075202693)
          ·
            refine ⟨2492829010544347889100505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13295088056236522075202693 2492829010544347889100505)
            ·
              refine ⟨1869621757908260916825379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492829010544347889100505 1869621757908260916825379)
              ·
                refine ⟨2804432636862391375238069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869621757908260916825379 2804432636862391375238069)
                ·
                  refine ⟨262915559705849191428569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804432636862391375238069 262915559705849191428569)
                  ·
                    rfl

theorem cell22_2304118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2304118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304118 prefixEnd_2304118 := by exact prefixLift 2304118
  have htrace : WordTrace (prefixWord ++ tailWord_2304118) baseStart_2304118 baseEnd_2304118 := by
    simpa [prefixWord, tailWord_2304118, baseEnd_2304118] using wordTrace_append hprefix tailTrace_2304118
  have hstable : (prefixWord ++ tailWord_2304118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304118).length < 2 ^ (prefixWord ++ tailWord_2304118).sum := by decide
  have hdescent : baseEnd_2304118 < baseStart_2304118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304131 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 1, 4]
def baseStart_2304131 : Nat := 118140960795 + 2304131 * 2 ^ 59
def prefixEnd_2304131 : Nat := 4983230072969 + 3 ^ 40 * 2304131 * 2
def baseEnd_2304131 : Nat := 788751129283219873710667

theorem tailTrace_2304131 : CollatzResearch.WordTrace tailWord_2304131 prefixEnd_2304131 788751129283219873710667 := by
  unfold tailWord_2304131
  simp only [CollatzResearch.WordTrace]
  refine ⟨84038561615534376090640247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56025707743689584060426831 84038561615534376090640247)
  ·
    refine ⟨126057842423301564135960371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84038561615534376090640247 126057842423301564135960371)
    ·
      refine ⟨189086763634952346203940557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126057842423301564135960371 189086763634952346203940557)
      ·
        refine ⟨70907536363107129826477709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189086763634952346203940557 70907536363107129826477709)
        ·
          refine ⟨26590326136165173684929141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70907536363107129826477709 26590326136165173684929141)
          ·
            refine ⟨2492843075265485032962107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26590326136165173684929141 2492843075265485032962107)
            ·
              refine ⟨3739264612898227549443161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492843075265485032962107 3739264612898227549443161)
              ·
                refine ⟨2804448459673670662082371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739264612898227549443161 2804448459673670662082371)
                ·
                  refine ⟨4206672689510505993123557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804448459673670662082371 4206672689510505993123557)
                  ·
                    refine ⟨788751129283219873710667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206672689510505993123557 788751129283219873710667)
                    ·
                      rfl

theorem cell22_2304131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].length) (baseStart_2304131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304131 prefixEnd_2304131 := by exact prefixLift 2304131
  have htrace : WordTrace (prefixWord ++ tailWord_2304131) baseStart_2304131 baseEnd_2304131 := by
    simpa [prefixWord, tailWord_2304131, baseEnd_2304131] using wordTrace_append hprefix tailTrace_2304131
  have hstable : (prefixWord ++ tailWord_2304131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304131).length < 2 ^ (prefixWord ++ tailWord_2304131).sum := by decide
  have hdescent : baseEnd_2304131 < baseStart_2304131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304146 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_2304146 : Nat := 118140960795 + 2304146 * 2 ^ 59
def prefixEnd_2304146 : Nat := 4983230072969 + 3 ^ 40 * 2304146 * 2
def baseEnd_2304146 : Nat := 262918754696588278195207

theorem tailTrace_2304146 : CollatzResearch.WordTrace tailWord_2304146 prefixEnd_2304146 262918754696588278195207 := by
  unfold tailWord_2304146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21009777177620008413109073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56026072473653355768290861 21009777177620008413109073)
  ·
    refine ⟨15757332883215006309831805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21009777177620008413109073 15757332883215006309831805)
    ·
      refine ⟨5908999831205627366186927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15757332883215006309831805 5908999831205627366186927)
      ·
        refine ⟨8863499746808441049280391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908999831205627366186927 8863499746808441049280391)
        ·
          refine ⟨13295249620212661573920587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863499746808441049280391 13295249620212661573920587)
          ·
            refine ⟨19942874430318992360880881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13295249620212661573920587 19942874430318992360880881)
            ·
              refine ⟨14957155822739244270660661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19942874430318992360880881 14957155822739244270660661)
              ·
                refine ⟨1402233358381804150374437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14957155822739244270660661 1402233358381804150374437)
                ·
                  refine ⟨262918754696588278195207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402233358381804150374437 262918754696588278195207)
                  ·
                    rfl

theorem cell22_2304146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_2304146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304146 prefixEnd_2304146 := by exact prefixLift 2304146
  have htrace : WordTrace (prefixWord ++ tailWord_2304146) baseStart_2304146 baseEnd_2304146 := by
    simpa [prefixWord, tailWord_2304146, baseEnd_2304146] using wordTrace_append hprefix tailTrace_2304146
  have hstable : (prefixWord ++ tailWord_2304146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304146).length < 2 ^ (prefixWord ++ tailWord_2304146).sum := by decide
  have hdescent : baseEnd_2304146 < baseStart_2304146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304157 : List Nat := [1, 4, 2, 1, 1, 13]
def baseStart_2304157 : Nat := 118140960795 + 2304157 * 2 ^ 59
def prefixEnd_2304157 : Nat := 4983230072969 + 3 ^ 40 * 2304157 * 2
def baseEnd_2304157 : Nat := 9737778143389684846427

theorem tailTrace_2304157 : CollatzResearch.WordTrace tailWord_2304157 prefixEnd_2304157 9737778143389684846427 := by
  unfold tailWord_2304157
  simp only [CollatzResearch.WordTrace]
  refine ⟨84039509913440182531086725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56026339942293455020724483 84039509913440182531086725)
  ·
    refine ⟨15757408108770034224578761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84039509913440182531086725 15757408108770034224578761)
    ·
      refine ⟨11818056081577525668434071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15757408108770034224578761 11818056081577525668434071)
      ·
        refine ⟨17727084122366288502651107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818056081577525668434071 17727084122366288502651107)
        ·
          refine ⟨26590626183549432753976661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727084122366288502651107 26590626183549432753976661)
          ·
            refine ⟨9737778143389684846427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 26590626183549432753976661 9737778143389684846427)
            ·
              rfl

theorem cell22_2304157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 13].length) (baseStart_2304157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304157 prefixEnd_2304157 := by exact prefixLift 2304157
  have htrace : WordTrace (prefixWord ++ tailWord_2304157) baseStart_2304157 baseEnd_2304157 := by
    simpa [prefixWord, tailWord_2304157, baseEnd_2304157] using wordTrace_append hprefix tailTrace_2304157
  have hstable : (prefixWord ++ tailWord_2304157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304157).length < 2 ^ (prefixWord ++ tailWord_2304157).sum := by decide
  have hdescent : baseEnd_2304157 < baseStart_2304157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304161 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2304161 : Nat := 118140960795 + 2304161 * 2 ^ 59
def prefixEnd_2304161 : Nat := 4983230072969 + 3 ^ 40 * 2304161 * 2
def baseEnd_2304161 : Nat := 788761398896309795460575

theorem tailTrace_2304161 : CollatzResearch.WordTrace tailWord_2304161 prefixEnd_2304161 788761398896309795460575 := by
  unfold tailWord_2304161
  simp only [CollatzResearch.WordTrace]
  refine ⟨84039655805425691214232337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56026437203617127476154891 84039655805425691214232337)
  ·
    refine ⟨63029741854069268410674253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84039655805425691214232337 63029741854069268410674253)
    ·
      refine ⟨23636153195275975654002845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63029741854069268410674253 23636153195275975654002845)
      ·
        refine ⟨8863557448228490870251067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23636153195275975654002845 8863557448228490870251067)
        ·
          refine ⟨13295336172342736305376601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863557448228490870251067 13295336172342736305376601)
          ·
            refine ⟨9971502129257052229032451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13295336172342736305376601 9971502129257052229032451)
            ·
              refine ⟨14957253193885578343548677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9971502129257052229032451 14957253193885578343548677)
              ·
                refine ⟨2804484973853545939415377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14957253193885578343548677 2804484973853545939415377)
                ·
                  refine ⟨2103363730390159454561533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804484973853545939415377 2103363730390159454561533)
                  ·
                    refine ⟨788761398896309795460575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103363730390159454561533 788761398896309795460575)
                    ·
                      rfl

theorem cell22_2304161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2304161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304161 prefixEnd_2304161 := by exact prefixLift 2304161
  have htrace : WordTrace (prefixWord ++ tailWord_2304161) baseStart_2304161 baseEnd_2304161 := by
    simpa [prefixWord, tailWord_2304161, baseEnd_2304161] using wordTrace_append hprefix tailTrace_2304161
  have hstable : (prefixWord ++ tailWord_2304161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304161).length < 2 ^ (prefixWord ++ tailWord_2304161).sum := by decide
  have hdescent : baseEnd_2304161 < baseStart_2304161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304180 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2304180 : Nat := 118140960795 + 2304180 * 2 ^ 59
def prefixEnd_2304180 : Nat := 4983230072969 + 3 ^ 40 * 2304180 * 2
def baseEnd_2304180 : Nat := 262922634328200026411839

theorem tailTrace_2304180 : CollatzResearch.WordTrace tailWord_2304180 prefixEnd_2304180 262922634328200026411839 := by
  unfold tailWord_2304180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42020174396178428729586997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56026899194904571639449329 42020174396178428729586997)
  ·
    refine ⟨3939391349641727693398781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42020174396178428729586997 3939391349641727693398781)
    ·
      refine ⟨1477271756115647885024543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3939391349641727693398781 1477271756115647885024543)
      ·
        refine ⟨2215907634173471827536815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477271756115647885024543 2215907634173471827536815)
        ·
          refine ⟨3323861451260207741305223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215907634173471827536815 3323861451260207741305223)
          ·
            refine ⟨4985792176890311611957835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323861451260207741305223 4985792176890311611957835)
            ·
              refine ⟨7478688265335467417936753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985792176890311611957835 7478688265335467417936753)
              ·
                refine ⟨5609016199001600563452565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7478688265335467417936753 5609016199001600563452565)
                ·
                  refine ⟨262922634328200026411839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5609016199001600563452565 262922634328200026411839)
                  ·
                    rfl

theorem cell22_2304180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2304180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304180 prefixEnd_2304180 := by exact prefixLift 2304180
  have htrace : WordTrace (prefixWord ++ tailWord_2304180) baseStart_2304180 baseEnd_2304180 := by
    simpa [prefixWord, tailWord_2304180, baseEnd_2304180] using wordTrace_append hprefix tailTrace_2304180
  have hstable : (prefixWord ++ tailWord_2304180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304180).length < 2 ^ (prefixWord ++ tailWord_2304180).sum := by decide
  have hdescent : baseEnd_2304180 < baseStart_2304180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304187 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_2304187 : Nat := 118140960795 + 2304187 * 2 ^ 59
def prefixEnd_2304187 : Nat := 4983230072969 + 3 ^ 40 * 2304187 * 2
def baseEnd_2304187 : Nat := 788770299227654394310495

theorem tailTrace_2304187 : CollatzResearch.WordTrace tailWord_2304187 prefixEnd_2304187 788770299227654394310495 := by
  unfold tailWord_2304187
  simp only [CollatzResearch.WordTrace]
  refine ⟨84040604103331497654678815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56027069402220998436452543 84040604103331497654678815)
  ·
    refine ⟨126060906154997246482018223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84040604103331497654678815 126060906154997246482018223)
    ·
      refine ⟨189091359232495869723027335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126060906154997246482018223 189091359232495869723027335)
      ·
        refine ⟨283637038848743804584541003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189091359232495869723027335 283637038848743804584541003)
        ·
          refine ⟨425455558273115706876811505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283637038848743804584541003 425455558273115706876811505)
          ·
            refine ⟨319091668704836780157608629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425455558273115706876811505 319091668704836780157608629)
            ·
              refine ⟨29914843941078448139775809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 319091668704836780157608629 29914843941078448139775809)
              ·
                refine ⟨22436132955808836104831857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29914843941078448139775809 22436132955808836104831857)
                ·
                  refine ⟨16827099716856627078623893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22436132955808836104831857 16827099716856627078623893)
                  ·
                    refine ⟨788770299227654394310495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16827099716856627078623893 788770299227654394310495)
                    ·
                      rfl

theorem cell22_2304187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_2304187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304187 prefixEnd_2304187 := by exact prefixLift 2304187
  have htrace : WordTrace (prefixWord ++ tailWord_2304187) baseStart_2304187 baseEnd_2304187 := by
    simpa [prefixWord, tailWord_2304187, baseEnd_2304187] using wordTrace_append hprefix tailTrace_2304187
  have hstable : (prefixWord ++ tailWord_2304187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304187).length < 2 ^ (prefixWord ++ tailWord_2304187).sum := by decide
  have hdescent : baseEnd_2304187 < baseStart_2304187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304234 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2304234 : Nat := 118140960795 + 2304234 * 2 ^ 59
def prefixEnd_2304234 : Nat := 4983230072969 + 3 ^ 40 * 2304234 * 2
def baseEnd_2304234 : Nat := 788786388288161938385351

theorem tailTrace_2304234 : CollatzResearch.WordTrace tailWord_2304234 prefixEnd_2304234 788786388288161938385351 := by
  unfold tailWord_2304234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010579583540306170409939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56028212222774149787759837 21010579583540306170409939)
  ·
    refine ⟨31515869375310459255614909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010579583540306170409939 31515869375310459255614909)
    ·
      refine ⟨11818451015741422220855591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31515869375310459255614909 11818451015741422220855591)
      ·
        refine ⟨17727676523612133331283387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818451015741422220855591 17727676523612133331283387)
        ·
          refine ⟨26591514785418199996925081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727676523612133331283387 26591514785418199996925081)
          ·
            refine ⟨19943636089063649997693811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26591514785418199996925081 19943636089063649997693811)
            ·
              refine ⟨29915454133595474996540717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19943636089063649997693811 29915454133595474996540717)
              ·
                refine ⟨11218295300098303123702769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29915454133595474996540717 11218295300098303123702769)
                ·
                  refine ⟨8413721475073727342777077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11218295300098303123702769 8413721475073727342777077)
                  ·
                    refine ⟨788786388288161938385351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8413721475073727342777077 788786388288161938385351)
                    ·
                      rfl

theorem cell22_2304234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2304234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304234 prefixEnd_2304234 := by exact prefixLift 2304234
  have htrace : WordTrace (prefixWord ++ tailWord_2304234) baseStart_2304234 baseEnd_2304234 := by
    simpa [prefixWord, tailWord_2304234, baseEnd_2304234] using wordTrace_append hprefix tailTrace_2304234
  have hstable : (prefixWord ++ tailWord_2304234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304234).length < 2 ^ (prefixWord ++ tailWord_2304234).sum := by decide
  have hdescent : baseEnd_2304234 < baseStart_2304234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304236 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_2304236 : Nat := 118140960795 + 2304236 * 2 ^ 59
def prefixEnd_2304236 : Nat := 4983230072969 + 3 ^ 40 * 2304236 * 2
def baseEnd_2304236 : Nat := 262929024309678199945115

theorem tailTrace_2304236 : CollatzResearch.WordTrace tailWord_2304236 prefixEnd_2304236 262929024309678199945115 := by
  unfold tailWord_2304236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42021195640076989511606281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56028260853435986015475041 42021195640076989511606281)
  ·
    refine ⟨31515896730057742133704711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42021195640076989511606281 31515896730057742133704711)
    ·
      refine ⟨47273845095086613200557067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31515896730057742133704711 47273845095086613200557067)
      ·
        refine ⟨70910767642629919800835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47273845095086613200557067 70910767642629919800835601)
        ·
          refine ⟨53183075731972439850626701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70910767642629919800835601 53183075731972439850626701)
          ·
            refine ⟨19943653399489664943985013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53183075731972439850626701 19943653399489664943985013)
            ·
              refine ⟨1869717506202156088498595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19943653399489664943985013 1869717506202156088498595)
              ·
                refine ⟨2804576259303234132747893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869717506202156088498595 2804576259303234132747893)
                ·
                  refine ⟨262929024309678199945115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804576259303234132747893 262929024309678199945115)
                  ·
                    rfl

theorem cell22_2304236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_2304236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304236 prefixEnd_2304236 := by exact prefixLift 2304236
  have htrace : WordTrace (prefixWord ++ tailWord_2304236) baseStart_2304236 baseEnd_2304236 := by
    simpa [prefixWord, tailWord_2304236, baseEnd_2304236] using wordTrace_append hprefix tailTrace_2304236
  have hstable : (prefixWord ++ tailWord_2304236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304236).length < 2 ^ (prefixWord ++ tailWord_2304236).sum := by decide
  have hdescent : baseEnd_2304236 < baseStart_2304236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304266 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_2304266 : Nat := 118140960795 + 2304266 * 2 ^ 59
def prefixEnd_2304266 : Nat := 4983230072969 + 3 ^ 40 * 2304266 * 2
def baseEnd_2304266 : Nat := 788797342542124521585253

theorem tailTrace_2304266 : CollatzResearch.WordTrace tailWord_2304266 prefixEnd_2304266 788797342542124521585253 := by
  unfold tailWord_2304266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010871367511323536701163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56028990313363529431203101 21010871367511323536701163)
  ·
    refine ⟨31516307051266985305051745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010871367511323536701163 31516307051266985305051745)
    ·
      refine ⟨23637230288450238978788809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31516307051266985305051745 23637230288450238978788809)
      ·
        refine ⟨17727922716337679234091607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23637230288450238978788809 17727922716337679234091607)
        ·
          refine ⟨26591884074506518851137411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727922716337679234091607 26591884074506518851137411)
          ·
            refine ⟨39887826111759778276706117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26591884074506518851137411 39887826111759778276706117)
            ·
              refine ⟨7478967395954958426882397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39887826111759778276706117 7478967395954958426882397)
              ·
                refine ⟨2804612773483109410080899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7478967395954958426882397 2804612773483109410080899)
                ·
                  refine ⟨4206919160224664115121349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804612773483109410080899 4206919160224664115121349)
                  ·
                    refine ⟨788797342542124521585253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206919160224664115121349 788797342542124521585253)
                    ·
                      rfl

theorem cell22_2304266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_2304266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304266 prefixEnd_2304266 := by exact prefixLift 2304266
  have htrace : WordTrace (prefixWord ++ tailWord_2304266) baseStart_2304266 baseEnd_2304266 := by
    simpa [prefixWord, tailWord_2304266, baseEnd_2304266] using wordTrace_append hprefix tailTrace_2304266
  have hstable : (prefixWord ++ tailWord_2304266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304266).length < 2 ^ (prefixWord ++ tailWord_2304266).sum := by decide
  have hdescent : baseEnd_2304266 < baseStart_2304266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304309 : List Nat := [1, 3, 3, 1, 2, 1, 1, 10]
def baseStart_2304309 : Nat := 118140960795 + 2304309 * 2 ^ 59
def prefixEnd_2304309 : Nat := 4983230072969 + 3 ^ 40 * 2304309 * 2
def baseEnd_2304309 : Nat := 87645784702320749195569

theorem tailTrace_2304309 : CollatzResearch.WordTrace tailWord_2304309 prefixEnd_2304309 87645784702320749195569 := by
  unfold tailWord_2304309
  simp only [CollatzResearch.WordTrace]
  refine ⟨84045053808889512490619981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56030035872593008327079987 84045053808889512490619981)
  ·
    refine ⟨31516895178333567183982493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84045053808889512490619981 31516895178333567183982493)
    ·
      refine ⟨11818835691875087693993435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31516895178333567183982493 11818835691875087693993435)
      ·
        refine ⟨17728253537812631540990153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818835691875087693993435 17728253537812631540990153)
        ·
          refine ⟨13296190153359473655742615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17728253537812631540990153 13296190153359473655742615)
          ·
            refine ⟨19944285230039210483613923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13296190153359473655742615 19944285230039210483613923)
            ·
              refine ⟨29916427845058815725420885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19944285230039210483613923 29916427845058815725420885)
              ·
                refine ⟨87645784702320749195569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29916427845058815725420885 87645784702320749195569)
                ·
                  rfl

theorem cell22_2304309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 10].length) (baseStart_2304309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304309 prefixEnd_2304309 := by exact prefixLift 2304309
  have htrace : WordTrace (prefixWord ++ tailWord_2304309) baseStart_2304309 baseEnd_2304309 := by
    simpa [prefixWord, tailWord_2304309, baseEnd_2304309] using wordTrace_append hprefix tailTrace_2304309
  have hstable : (prefixWord ++ tailWord_2304309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304309).length < 2 ^ (prefixWord ++ tailWord_2304309).sum := by decide
  have hdescent : baseEnd_2304309 < baseStart_2304309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304326 : List Nat := [6, 1, 1, 14]
def baseStart_2304326 : Nat := 118140960795 + 2304326 * 2 ^ 59
def prefixEnd_2304326 : Nat := 4983230072969 + 3 ^ 40 * 2304326 * 2
def baseEnd_2304326 : Nat := 1082054707501103381461

theorem tailTrace_2304326 : CollatzResearch.WordTrace tailWord_2304326 prefixEnd_2304326 1082054707501103381461 := by
  unfold tailWord_2304326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626427307807122637312151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56030449233218616262659221 2626427307807122637312151)
  ·
    refine ⟨3939640961710683955968227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626427307807122637312151 3939640961710683955968227)
    ·
      refine ⟨5909461442566025933952341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939640961710683955968227 5909461442566025933952341)
      ·
        refine ⟨1082054707501103381461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5909461442566025933952341 1082054707501103381461)
        ·
          rfl

theorem cell22_2304326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 14].length) (baseStart_2304326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304326 prefixEnd_2304326 := by exact prefixLift 2304326
  have htrace : WordTrace (prefixWord ++ tailWord_2304326) baseStart_2304326 baseEnd_2304326 := by
    simpa [prefixWord, tailWord_2304326, baseEnd_2304326] using wordTrace_append hprefix tailTrace_2304326
  have hstable : (prefixWord ++ tailWord_2304326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304326).length < 2 ^ (prefixWord ++ tailWord_2304326).sum := by decide
  have hdescent : baseEnd_2304326 < baseStart_2304326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2304369 : Nat := 118140960795 + 2304369 * 2 ^ 59
def prefixEnd_2304369 : Nat := 4983230072969 + 3 ^ 40 * 2304369 * 2
def baseEnd_2304369 : Nat := 788832601547066586259937

theorem tailTrace_2304369 : CollatzResearch.WordTrace tailWord_2304369 prefixEnd_2304369 788832601547066586259937 := by
  unfold tailWord_2304369
  simp only [CollatzResearch.WordTrace]
  refine ⟨84047242188672142737804161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56031494792448095158536107 84047242188672142737804161)
  ·
    refine ⟨63035431641504107053353121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84047242188672142737804161 63035431641504107053353121)
    ·
      refine ⟨47276573731128080290014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63035431641504107053353121 47276573731128080290014841)
      ·
        refine ⟨35457430298346060217511131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47276573731128080290014841 35457430298346060217511131)
        ·
          refine ⟨53186145447519090326266697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35457430298346060217511131 53186145447519090326266697)
          ·
            refine ⟨39889609085639317744700023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53186145447519090326266697 39889609085639317744700023)
            ·
              refine ⟨59834413628458976617050035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39889609085639317744700023 59834413628458976617050035)
              ·
                refine ⟨89751620442688464925575053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59834413628458976617050035 89751620442688464925575053)
                ·
                  refine ⟨33656857666008174347090645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89751620442688464925575053 33656857666008174347090645)
                  ·
                    refine ⟨788832601547066586259937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33656857666008174347090645 788832601547066586259937)
                    ·
                      rfl

theorem cell22_2304369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2304369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304369 prefixEnd_2304369 := by exact prefixLift 2304369
  have htrace : WordTrace (prefixWord ++ tailWord_2304369) baseStart_2304369 baseEnd_2304369 := by
    simpa [prefixWord, tailWord_2304369, baseEnd_2304369] using wordTrace_append hprefix tailTrace_2304369
  have hstable : (prefixWord ++ tailWord_2304369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304369).length < 2 ^ (prefixWord ++ tailWord_2304369).sum := by decide
  have hdescent : baseEnd_2304369 < baseStart_2304369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304416 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_2304416 : Nat := 118140960795 + 2304416 * 2 ^ 59
def prefixEnd_2304416 : Nat := 4983230072969 + 3 ^ 40 * 2304416 * 2
def baseEnd_2304416 : Nat := 262949563535858043444931

theorem tailTrace_2304416 : CollatzResearch.WordTrace tailWord_2304416 prefixEnd_2304416 262949563535858043444931 := by
  unfold tailWord_2304416
  simp only [CollatzResearch.WordTrace]
  refine ⟨42024478209750934882382551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56032637613001246509843401 42024478209750934882382551)
  ·
    refine ⟨63036717314626402323573827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42024478209750934882382551 63036717314626402323573827)
    ·
      refine ⟨94555075971939603485360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63036717314626402323573827 94555075971939603485360741)
      ·
        refine ⟨17729076744738675653505139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94555075971939603485360741 17729076744738675653505139)
        ·
          refine ⟨26593615117108013480257709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17729076744738675653505139 26593615117108013480257709)
          ·
            refine ⟨9972605668915505055096641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26593615117108013480257709 9972605668915505055096641)
            ·
              refine ⟨7479454251686628791322481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9972605668915505055096641 7479454251686628791322481)
              ·
                refine ⟨5609590688764971593491861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7479454251686628791322481 5609590688764971593491861)
                ·
                  refine ⟨262949563535858043444931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5609590688764971593491861 262949563535858043444931)
                  ·
                    rfl

theorem cell22_2304416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_2304416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304416 prefixEnd_2304416 := by exact prefixLift 2304416
  have htrace : WordTrace (prefixWord ++ tailWord_2304416) baseStart_2304416 baseEnd_2304416 := by
    simpa [prefixWord, tailWord_2304416, baseEnd_2304416] using wordTrace_append hprefix tailTrace_2304416
  have hstable : (prefixWord ++ tailWord_2304416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304416).length < 2 ^ (prefixWord ++ tailWord_2304416).sum := by decide
  have hdescent : baseEnd_2304416 < baseStart_2304416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304448 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_2304448 : Nat := 118140960795 + 2304448 * 2 ^ 59
def prefixEnd_2304448 : Nat := 4983230072969 + 3 ^ 40 * 2304448 * 2
def baseEnd_2304448 : Nat := 788859644861536713534695

theorem tailTrace_2304448 : CollatzResearch.WordTrace tailWord_2304448 prefixEnd_2304448 788859644861536713534695 := by
  unfold tailWord_2304448
  simp only [CollatzResearch.WordTrace]
  refine ⟨42025061777692969614964999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56033415703590626153286665 42025061777692969614964999)
  ·
    refine ⟨63037592666539454422447499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42025061777692969614964999 63037592666539454422447499)
    ·
      refine ⟨94556388999809181633671249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63037592666539454422447499 94556388999809181633671249)
      ·
        refine ⟨70917291749856886225253437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94556388999809181633671249 70917291749856886225253437)
        ·
          refine ⟨26593984406196332334470039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70917291749856886225253437 26593984406196332334470039)
          ·
            refine ⟨39890976609294498501705059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26593984406196332334470039 39890976609294498501705059)
            ·
              refine ⟨59836464913941747752557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39890976609294498501705059 59836464913941747752557589)
              ·
                refine ⟨2804834292841019425901137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59836464913941747752557589 2804834292841019425901137)
                ·
                  refine ⟨2103625719630764569425853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804834292841019425901137 2103625719630764569425853)
                  ·
                    refine ⟨788859644861536713534695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103625719630764569425853 788859644861536713534695)
                    ·
                      rfl

theorem cell22_2304448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_2304448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304448 prefixEnd_2304448 := by exact prefixLift 2304448
  have htrace : WordTrace (prefixWord ++ tailWord_2304448) baseStart_2304448 baseEnd_2304448 := by
    simpa [prefixWord, tailWord_2304448, baseEnd_2304448] using wordTrace_append hprefix tailTrace_2304448
  have hstable : (prefixWord ++ tailWord_2304448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304448).length < 2 ^ (prefixWord ++ tailWord_2304448).sum := by decide
  have hdescent : baseEnd_2304448 < baseStart_2304448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304482 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2304482 : Nat := 118140960795 + 2304482 * 2 ^ 59
def prefixEnd_2304482 : Nat := 4983230072969 + 3 ^ 40 * 2304482 * 2
def baseEnd_2304482 : Nat := 788871283756371958184591

theorem tailTrace_2304482 : CollatzResearch.WordTrace tailWord_2304482 prefixEnd_2304482 788871283756371958184591 := by
  unfold tailWord_2304482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012840909315690759166925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56034242424841842024445133 21012840909315690759166925)
  ·
    refine ⟨7879815340993384034687597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21012840909315690759166925 7879815340993384034687597)
    ·
      refine ⟨2954930752872519013007849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7879815340993384034687597 2954930752872519013007849)
      ·
        refine ⟨2216198064654389259755887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2954930752872519013007849 2216198064654389259755887)
        ·
          refine ⟨3324297096981583889633831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216198064654389259755887 3324297096981583889633831)
          ·
            refine ⟨4986445645472375834450747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324297096981583889633831 4986445645472375834450747)
            ·
              refine ⟨7479668468208563751676121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986445645472375834450747 7479668468208563751676121)
              ·
                refine ⟨5609751351156422813757091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7479668468208563751676121 5609751351156422813757091)
                ·
                  refine ⟨8414627026734634220635637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609751351156422813757091 8414627026734634220635637)
                  ·
                    refine ⟨788871283756371958184591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8414627026734634220635637 788871283756371958184591)
                    ·
                      rfl

theorem cell22_2304482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2304482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304482 prefixEnd_2304482 := by exact prefixLift 2304482
  have htrace : WordTrace (prefixWord ++ tailWord_2304482) baseStart_2304482 baseEnd_2304482 := by
    simpa [prefixWord, tailWord_2304482, baseEnd_2304482] using wordTrace_append hprefix tailTrace_2304482
  have hstable : (prefixWord ++ tailWord_2304482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304482).length < 2 ^ (prefixWord ++ tailWord_2304482).sum := by decide
  have hdescent : baseEnd_2304482 < baseStart_2304482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304501 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 4]
def baseStart_2304501 : Nat := 118140960795 + 2304501 * 2 ^ 59
def prefixEnd_2304501 : Nat := 4983230072969 + 3 ^ 40 * 2304501 * 2
def baseEnd_2304501 : Nat := 262959262614887413986511

theorem tailTrace_2304501 : CollatzResearch.WordTrace tailWord_2304501 prefixEnd_2304501 262959262614887413986511 := by
  unfold tailWord_2304501
  simp only [CollatzResearch.WordTrace]
  refine ⟨84052056624193929281609357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56034704416129286187739571 84052056624193929281609357)
  ·
    refine ⟨31519521234072723480603509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84052056624193929281609357 31519521234072723480603509)
    ·
      refine ⟨2954955115694317826306579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31519521234072723480603509 2954955115694317826306579)
      ·
        refine ⟨4432432673541476739459869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954955115694317826306579 4432432673541476739459869)
        ·
          refine ⟨1662162252578053777297451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4432432673541476739459869 1662162252578053777297451)
          ·
            refine ⟨2493243378867080665946177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662162252578053777297451 2493243378867080665946177)
            ·
              refine ⟨1869932534150310499459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2493243378867080665946177 1869932534150310499459633)
              ·
                refine ⟨1402449400612732874594725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869932534150310499459633 1402449400612732874594725)
                ·
                  refine ⟨262959262614887413986511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402449400612732874594725 262959262614887413986511)
                  ·
                    rfl

theorem cell22_2304501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_2304501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304501 prefixEnd_2304501 := by exact prefixLift 2304501
  have htrace : WordTrace (prefixWord ++ tailWord_2304501) baseStart_2304501 baseEnd_2304501 := by
    simpa [prefixWord, tailWord_2304501, baseEnd_2304501] using wordTrace_append hprefix tailTrace_2304501
  have hstable : (prefixWord ++ tailWord_2304501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304501).length < 2 ^ (prefixWord ++ tailWord_2304501).sum := by decide
  have hdescent : baseEnd_2304501 < baseStart_2304501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304523 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 5]
def baseStart_2304523 : Nat := 118140960795 + 2304523 * 2 ^ 59
def prefixEnd_2304523 : Nat := 4983230072969 + 3 ^ 40 * 2304523 * 2
def baseEnd_2304523 : Nat := 262961772964753839303155

theorem tailTrace_2304523 : CollatzResearch.WordTrace tailWord_2304523 prefixEnd_2304523 262961772964753839303155 := by
  unfold tailWord_2304523
  simp only [CollatzResearch.WordTrace]
  refine ⟨84052859030114227038910223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035239353409484692606815 84052859030114227038910223)
  ·
    refine ⟨126079288545171340558365335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84052859030114227038910223 126079288545171340558365335)
    ·
      refine ⟨189118932817757010837548003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126079288545171340558365335 189118932817757010837548003)
      ·
        refine ⟨283678399226635516256322005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189118932817757010837548003 283678399226635516256322005)
        ·
          refine ⟨6648712481874269912257547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 283678399226635516256322005 6648712481874269912257547)
          ·
            refine ⟨9973068722811404868386321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648712481874269912257547 9973068722811404868386321)
            ·
              refine ⟨7479801542108553651289741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9973068722811404868386321 7479801542108553651289741)
              ·
                refine ⟨2804925578290707619233653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7479801542108553651289741 2804925578290707619233653)
                ·
                  refine ⟨262961772964753839303155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804925578290707619233653 262961772964753839303155)
                  ·
                    rfl

theorem cell22_2304523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].length) (baseStart_2304523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304523 prefixEnd_2304523 := by exact prefixLift 2304523
  have htrace : WordTrace (prefixWord ++ tailWord_2304523) baseStart_2304523 baseEnd_2304523 := by
    simpa [prefixWord, tailWord_2304523, baseEnd_2304523] using wordTrace_append hprefix tailTrace_2304523
  have hstable : (prefixWord ++ tailWord_2304523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304523).length < 2 ^ (prefixWord ++ tailWord_2304523).sum := by decide
  have hdescent : baseEnd_2304523 < baseStart_2304523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304544 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_2304544 : Nat := 118140960795 + 2304544 * 2 ^ 59
def prefixEnd_2304544 : Nat := 4983230072969 + 3 ^ 40 * 2304544 * 2
def baseEnd_2304544 : Nat := 788892507623424463134401

theorem tailTrace_2304544 : CollatzResearch.WordTrace tailWord_2304544 prefixEnd_2304544 788892507623424463134401 := by
  unfold tailWord_2304544
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026812481519073812712343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56035749975358765083616457 42026812481519073812712343)
  ·
    refine ⟨63040218722278610719068515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42026812481519073812712343 63040218722278610719068515)
    ·
      refine ⟨94560328083417916078602773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63040218722278610719068515 94560328083417916078602773)
      ·
        refine ⟨4432515378910214816184505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94560328083417916078602773 4432515378910214816184505)
        ·
          refine ⟨3324386534182661112138379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4432515378910214816184505 3324386534182661112138379)
          ·
            refine ⟨4986579801273991668207569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324386534182661112138379 4986579801273991668207569)
            ·
              refine ⟨3739934850955493751155677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986579801273991668207569 3739934850955493751155677)
              ·
                refine ⟨1402475569108310156683379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3739934850955493751155677 1402475569108310156683379)
                ·
                  refine ⟨2103713353662465235025069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402475569108310156683379 2103713353662465235025069)
                  ·
                    refine ⟨788892507623424463134401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103713353662465235025069 788892507623424463134401)
                    ·
                      rfl

theorem cell22_2304544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_2304544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304544 prefixEnd_2304544 := by exact prefixLift 2304544
  have htrace : WordTrace (prefixWord ++ tailWord_2304544) baseStart_2304544 baseEnd_2304544 := by
    simpa [prefixWord, tailWord_2304544, baseEnd_2304544] using wordTrace_append hprefix tailTrace_2304544
  have hstable : (prefixWord ++ tailWord_2304544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304544).length < 2 ^ (prefixWord ++ tailWord_2304544).sum := by decide
  have hdescent : baseEnd_2304544 < baseStart_2304544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304568 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_2304568 : Nat := 118140960795 + 2304568 * 2 ^ 59
def prefixEnd_2304568 : Nat := 4983230072969 + 3 ^ 40 * 2304568 * 2
def baseEnd_2304568 : Nat := 262966907771298800178109

theorem tailTrace_2304568 : CollatzResearch.WordTrace tailWord_2304568 prefixEnd_2304568 262966907771298800178109 := by
  unfold tailWord_2304568
  simp only [CollatzResearch.WordTrace]
  refine ⟨42027250157475599862149179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56036333543300799816198905 42027250157475599862149179)
  ·
    refine ⟨63040875236213399793223769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42027250157475599862149179 63040875236213399793223769)
    ·
      refine ⟨47280656427160049844917827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63040875236213399793223769 47280656427160049844917827)
      ·
        refine ⟨70920984640740074767376741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47280656427160049844917827 70920984640740074767376741)
        ·
          refine ⟨13297684620138764018883139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70920984640740074767376741 13297684620138764018883139)
          ·
            refine ⟨19946526930208146028324709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13297684620138764018883139 19946526930208146028324709)
            ·
              refine ⟨3739973799414027380310883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19946526930208146028324709 3739973799414027380310883)
              ·
                refine ⟨5609960699121041070466325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739973799414027380310883 5609960699121041070466325)
                ·
                  refine ⟨262966907771298800178109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5609960699121041070466325 262966907771298800178109)
                  ·
                    rfl

theorem cell22_2304568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_2304568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304568 prefixEnd_2304568 := by exact prefixLift 2304568
  have htrace : WordTrace (prefixWord ++ tailWord_2304568) baseStart_2304568 baseEnd_2304568 := by
    simpa [prefixWord, tailWord_2304568, baseEnd_2304568] using wordTrace_append hprefix tailTrace_2304568
  have hstable : (prefixWord ++ tailWord_2304568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304568).length < 2 ^ (prefixWord ++ tailWord_2304568).sum := by decide
  have hdescent : baseEnd_2304568 < baseStart_2304568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304574 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2304574 : Nat := 118140960795 + 2304574 * 2 ^ 59
def prefixEnd_2304574 : Nat := 4983230072969 + 3 ^ 40 * 2304574 * 2
def baseEnd_2304574 : Nat := 262967592412171461628103

theorem tailTrace_2304574 : CollatzResearch.WordTrace tailWord_2304574 prefixEnd_2304574 262967592412171461628103 := by
  unfold tailWord_2304574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506839894116182843627097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56036479435286308499344517 10506839894116182843627097)
  ·
    refine ⟨7880129920587137132720323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10506839894116182843627097 7880129920587137132720323)
    ·
      refine ⟨11820194880880705699080485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7880129920587137132720323 11820194880880705699080485)
      ·
        refine ⟨2216286540165132318577591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11820194880880705699080485 2216286540165132318577591)
        ·
          refine ⟨3324429810247698477866387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216286540165132318577591 3324429810247698477866387)
          ·
            refine ⟨4986644715371547716799581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324429810247698477866387 4986644715371547716799581)
            ·
              refine ⟨1869991768264330393799843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4986644715371547716799581 1869991768264330393799843)
              ·
                refine ⟨2804987652396495590699765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869991768264330393799843 2804987652396495590699765)
                ·
                  refine ⟨262967592412171461628103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804987652396495590699765 262967592412171461628103)
                  ·
                    rfl

theorem cell22_2304574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2304574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304574 prefixEnd_2304574 := by exact prefixLift 2304574
  have htrace : WordTrace (prefixWord ++ tailWord_2304574) baseStart_2304574 baseEnd_2304574 := by
    simpa [prefixWord, tailWord_2304574, baseEnd_2304574] using wordTrace_append hprefix tailTrace_2304574
  have hstable : (prefixWord ++ tailWord_2304574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304574).length < 2 ^ (prefixWord ++ tailWord_2304574).sum := by decide
  have hdescent : baseEnd_2304574 < baseStart_2304574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304703 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 8]
def baseStart_2304703 : Nat := 118140960795 + 2304703 * 2 ^ 59
def prefixEnd_2304703 : Nat := 4983230072969 + 3 ^ 40 * 2304703 * 2
def baseEnd_2304703 : Nat := 262982312190933682802971

theorem tailTrace_2304703 : CollatzResearch.WordTrace tailWord_2304703 prefixEnd_2304703 262982312190933682802971 := by
  unfold tailWord_2304703
  simp only [CollatzResearch.WordTrace]
  refine ⟨84059424169462117780462763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56039616112974745186975175 84059424169462117780462763)
  ·
    refine ⟨126089136254193176670694145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84059424169462117780462763 126089136254193176670694145)
    ·
      refine ⟨94566852190644882503020609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126089136254193176670694145 94566852190644882503020609)
      ·
        refine ⟨70925139142983661877265457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94566852190644882503020609 70925139142983661877265457)
        ·
          refine ⟨53193854357237746407949093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70925139142983661877265457 53193854357237746407949093)
          ·
            refine ⟨9973847691982077451490455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53193854357237746407949093 9973847691982077451490455)
            ·
              refine ⟨14960771537973116177235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9973847691982077451490455 14960771537973116177235683)
              ·
                refine ⟨22441157306959674265853525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960771537973116177235683 22441157306959674265853525)
                ·
                  refine ⟨262982312190933682802971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22441157306959674265853525 262982312190933682802971)
                  ·
                    rfl

theorem cell22_2304703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_2304703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304703 prefixEnd_2304703 := by exact prefixLift 2304703
  have htrace : WordTrace (prefixWord ++ tailWord_2304703) baseStart_2304703 baseEnd_2304703 := by
    simpa [prefixWord, tailWord_2304703, baseEnd_2304703] using wordTrace_append hprefix tailTrace_2304703
  have hstable : (prefixWord ++ tailWord_2304703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304703).length < 2 ^ (prefixWord ++ tailWord_2304703).sum := by decide
  have hdescent : baseEnd_2304703 < baseStart_2304703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304737 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 4]
def baseStart_2304737 : Nat := 118140960795 + 2304737 * 2 ^ 59
def prefixEnd_2304737 : Nat := 4983230072969 + 3 ^ 40 * 2304737 * 2
def baseEnd_2304737 : Nat := 262986191822545431019603

theorem tailTrace_2304737 : CollatzResearch.WordTrace tailWord_2304737 prefixEnd_2304737 262986191822545431019603 := by
  unfold tailWord_2304737
  simp only [CollatzResearch.WordTrace]
  refine ⟨84060664251338941587200465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56040442834225961058133643 84060664251338941587200465)
  ·
    refine ⟨63045498188504206190400349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84060664251338941587200465 63045498188504206190400349)
    ·
      refine ⟨23642061820689077321400131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63045498188504206190400349 23642061820689077321400131)
      ·
        refine ⟨35463092731033615982100197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23642061820689077321400131 35463092731033615982100197)
        ·
          refine ⟨6649329887068802996643787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35463092731033615982100197 6649329887068802996643787)
          ·
            refine ⟨9973994830603204494965681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649329887068802996643787 9973994830603204494965681)
            ·
              refine ⟨7480496122952403371224261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9973994830603204494965681 7480496122952403371224261)
              ·
                refine ⟨1402593023053575632104549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7480496122952403371224261 1402593023053575632104549)
                ·
                  refine ⟨262986191822545431019603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402593023053575632104549 262986191822545431019603)
                  ·
                    rfl

theorem cell22_2304737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_2304737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304737 prefixEnd_2304737 := by exact prefixLift 2304737
  have htrace : WordTrace (prefixWord ++ tailWord_2304737) baseStart_2304737 baseEnd_2304737 := by
    simpa [prefixWord, tailWord_2304737, baseEnd_2304737] using wordTrace_append hprefix tailTrace_2304737
  have hstable : (prefixWord ++ tailWord_2304737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304737).length < 2 ^ (prefixWord ++ tailWord_2304737).sum := by decide
  have hdescent : baseEnd_2304737 < baseStart_2304737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304748 : List Nat := [2, 2, 1, 1, 2, 2, 1, 11]
def baseStart_2304748 : Nat := 118140960795 + 2304748 * 2 ^ 59
def prefixEnd_2304748 : Nat := 4983230072969 + 3 ^ 40 * 2304748 * 2
def baseEnd_2304748 : Nat := 87662482332492881225975

theorem tailTrace_2304748 : CollatzResearch.WordTrace tailWord_2304748 prefixEnd_2304748 87662482332492881225975 := by
  unfold tailWord_2304748
  simp only [CollatzResearch.WordTrace]
  refine ⟨42030532727149545232925449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56040710302866060310567265 42030532727149545232925449)
  ·
    refine ⟨31522899545362158924694087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42030532727149545232925449 31522899545362158924694087)
    ·
      refine ⟨47284349318043238387041131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31522899545362158924694087 47284349318043238387041131)
      ·
        refine ⟨70926523977064857580561697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47284349318043238387041131 70926523977064857580561697)
        ·
          refine ⟨53194892982798643185421273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70926523977064857580561697 53194892982798643185421273)
          ·
            refine ⟨39896169737098982389065955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53194892982798643185421273 39896169737098982389065955)
            ·
              refine ⟨59844254605648473583598933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39896169737098982389065955 59844254605648473583598933)
              ·
                refine ⟨87662482332492881225975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59844254605648473583598933 87662482332492881225975)
                ·
                  rfl

theorem cell22_2304748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_2304748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304748 prefixEnd_2304748 := by exact prefixLift 2304748
  have htrace : WordTrace (prefixWord ++ tailWord_2304748) baseStart_2304748 baseEnd_2304748 := by
    simpa [prefixWord, tailWord_2304748, baseEnd_2304748] using wordTrace_append hprefix tailTrace_2304748
  have hstable : (prefixWord ++ tailWord_2304748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304748).length < 2 ^ (prefixWord ++ tailWord_2304748).sum := by decide
  have hdescent : baseEnd_2304748 < baseStart_2304748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304750 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2304750 : Nat := 118140960795 + 2304750 * 2 ^ 59
def prefixEnd_2304750 : Nat := 4983230072969 + 3 ^ 40 * 2304750 * 2
def baseEnd_2304750 : Nat := 788963025633308592483769

theorem tailTrace_2304750 : CollatzResearch.WordTrace tailWord_2304750 prefixEnd_2304750 788963025633308592483769 := by
  unfold tailWord_2304750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507642300036480600927963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56040758933527896538282469 10507642300036480600927963)
  ·
    refine ⟨15761463450054720901391945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10507642300036480600927963 15761463450054720901391945)
    ·
      refine ⟨11821097587541040676043959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15761463450054720901391945 11821097587541040676043959)
      ·
        refine ⟨17731646381311561014065939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11821097587541040676043959 17731646381311561014065939)
        ·
          refine ⟨26597469571967341521098909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17731646381311561014065939 26597469571967341521098909)
          ·
            refine ⟨9974051089487753070412091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26597469571967341521098909 9974051089487753070412091)
            ·
              refine ⟨14961076634231629605618137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974051089487753070412091 14961076634231629605618137)
              ·
                refine ⟨11220807475673722204213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14961076634231629605618137 11220807475673722204213603)
                ·
                  refine ⟨16831211213510583306320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11220807475673722204213603 16831211213510583306320405)
                  ·
                    refine ⟨788963025633308592483769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16831211213510583306320405 788963025633308592483769)
                    ·
                      rfl

theorem cell22_2304750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2304750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304750 prefixEnd_2304750 := by exact prefixLift 2304750
  have htrace : WordTrace (prefixWord ++ tailWord_2304750) baseStart_2304750 baseEnd_2304750 := by
    simpa [prefixWord, tailWord_2304750, baseEnd_2304750] using wordTrace_append hprefix tailTrace_2304750
  have hstable : (prefixWord ++ tailWord_2304750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304750).length < 2 ^ (prefixWord ++ tailWord_2304750).sum := by decide
  have hdescent : baseEnd_2304750 < baseStart_2304750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304872 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_2304872 : Nat := 118140960795 + 2304872 * 2 ^ 59
def prefixEnd_2304872 : Nat := 4983230072969 + 3 ^ 40 * 2304872 * 2
def baseEnd_2304872 : Nat := 263001596242180313644465

theorem tailTrace_2304872 : CollatzResearch.WordTrace tailWord_2304872 prefixEnd_2304872 263001596242180313644465 := by
  unfold tailWord_2304872
  simp only [CollatzResearch.WordTrace]
  refine ⟨42032794052924929821682435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56043725403899906428909913 42032794052924929821682435)
  ·
    refine ⟨63049191079387394732523653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42032794052924929821682435 63049191079387394732523653)
    ·
      refine ⟨11821723327385136512348185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63049191079387394732523653 11821723327385136512348185)
      ·
        refine ⟨8866292495538852384261139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11821723327385136512348185 8866292495538852384261139)
        ·
          refine ⟨13299438743308278576391709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866292495538852384261139 13299438743308278576391709)
          ·
            refine ⟨4987289528740604466146891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13299438743308278576391709 4987289528740604466146891)
            ·
              refine ⟨7480934293110906699220337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987289528740604466146891 7480934293110906699220337)
              ·
                refine ⟨5610700719833180024415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7480934293110906699220337 5610700719833180024415253)
                ·
                  refine ⟨263001596242180313644465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5610700719833180024415253 263001596242180313644465)
                  ·
                    rfl

theorem cell22_2304872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_2304872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304872 prefixEnd_2304872 := by exact prefixLift 2304872
  have htrace : WordTrace (prefixWord ++ tailWord_2304872) baseStart_2304872 baseEnd_2304872 := by
    simpa [prefixWord, tailWord_2304872, baseEnd_2304872] using wordTrace_append hprefix tailTrace_2304872
  have hstable : (prefixWord ++ tailWord_2304872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304872).length < 2 ^ (prefixWord ++ tailWord_2304872).sum := by decide
  have hdescent : baseEnd_2304872 < baseStart_2304872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304889 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 4]
def baseStart_2304889 : Nat := 118140960795 + 2304889 * 2 ^ 59
def prefixEnd_2304889 : Nat := 4983230072969 + 3 ^ 40 * 2304889 * 2
def baseEnd_2304889 : Nat := 263003536057986187752781

theorem tailTrace_2304889 : CollatzResearch.WordTrace tailWord_2304889 prefixEnd_2304889 263003536057986187752781 := by
  unfold tailWord_2304889
  simp only [CollatzResearch.WordTrace]
  refine ⟨84066208146788271546733721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56044138764525514364489147 84066208146788271546733721)
  ·
    refine ⟨63049656110091203660050291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84066208146788271546733721 63049656110091203660050291)
    ·
      refine ⟨94574484165136805490075437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63049656110091203660050291 94574484165136805490075437)
      ·
        refine ⟨35465431561926302058778289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94574484165136805490075437 35465431561926302058778289)
        ·
          refine ⟨26599073671444726544083717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35465431561926302058778289 26599073671444726544083717)
          ·
            refine ⟨4987326313395886227015697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26599073671444726544083717 4987326313395886227015697)
            ·
              refine ⟨3740494735046914670261773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987326313395886227015697 3740494735046914670261773)
              ·
                refine ⟨1402685525642593001348165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740494735046914670261773 1402685525642593001348165)
                ·
                  refine ⟨263003536057986187752781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402685525642593001348165 263003536057986187752781)
                  ·
                    rfl

theorem cell22_2304889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_2304889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304889 prefixEnd_2304889 := by exact prefixLift 2304889
  have htrace : WordTrace (prefixWord ++ tailWord_2304889) baseStart_2304889 baseEnd_2304889 := by
    simpa [prefixWord, tailWord_2304889, baseEnd_2304889] using wordTrace_append hprefix tailTrace_2304889
  have hstable : (prefixWord ++ tailWord_2304889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304889).length < 2 ^ (prefixWord ++ tailWord_2304889).sum := by decide
  have hdescent : baseEnd_2304889 < baseStart_2304889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304904 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_2304904 : Nat := 118140960795 + 2304904 * 2 ^ 59
def prefixEnd_2304904 : Nat := 4983230072969 + 3 ^ 40 * 2304904 * 2
def baseEnd_2304904 : Nat := 789015742980503524133297

theorem tailTrace_2304904 : CollatzResearch.WordTrace tailWord_2304904 prefixEnd_2304904 789015742980503524133297 := by
  unfold tailWord_2304904
  simp only [CollatzResearch.WordTrace]
  refine ⟨42033377620866964554264883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56044503494489286072353177 42033377620866964554264883)
  ·
    refine ⟨63050066431300446831397325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42033377620866964554264883 63050066431300446831397325)
    ·
      refine ⟨23643774911737667561773997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63050066431300446831397325 23643774911737667561773997)
      ·
        refine ⟨8866415591901625335665249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23643774911737667561773997 8866415591901625335665249)
        ·
          refine ⟨6649811693926219001748937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8866415591901625335665249 6649811693926219001748937)
          ·
            refine ⟨4987358770444664251311703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6649811693926219001748937 4987358770444664251311703)
            ·
              refine ⟨7481038155666996376967555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987358770444664251311703 7481038155666996376967555)
              ·
                refine ⟨11221557233500494565451333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7481038155666996376967555 11221557233500494565451333)
                ·
                  refine ⟨2104041981281342731022125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11221557233500494565451333 2104041981281342731022125)
                  ·
                    refine ⟨789015742980503524133297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104041981281342731022125 789015742980503524133297)
                    ·
                      rfl

theorem cell22_2304904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_2304904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2304904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2304904 prefixEnd_2304904 := by exact prefixLift 2304904
  have htrace : WordTrace (prefixWord ++ tailWord_2304904) baseStart_2304904 baseEnd_2304904 := by
    simpa [prefixWord, tailWord_2304904, baseEnd_2304904] using wordTrace_append hprefix tailTrace_2304904
  have hstable : (prefixWord ++ tailWord_2304904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304904).length < 2 ^ (prefixWord ++ tailWord_2304904).sum := by decide
  have hdescent : baseEnd_2304904 < baseStart_2304904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305013 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 5]
def baseStart_2305013 : Nat := 118140960795 + 2305013 * 2 ^ 59
def prefixEnd_2305013 : Nat := 4983230072969 + 3 ^ 40 * 2305013 * 2
def baseEnd_2305013 : Nat := 263017685302687857719321

theorem tailTrace_2305013 : CollatzResearch.WordTrace tailWord_2305013 prefixEnd_2305013 263017685302687857719321 := by
  unfold tailWord_2305013
  simp only [CollatzResearch.WordTrace]
  refine ⟨84070730798339040724247693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56047153865559360482831795 84070730798339040724247693)
  ·
    refine ⟨31526524049377140271592885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84070730798339040724247693 31526524049377140271592885)
    ·
      refine ⟨2955611629629106900461833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31526524049377140271592885 2955611629629106900461833)
      ·
        refine ⟨2216708722221830175346375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955611629629106900461833 2216708722221830175346375)
        ·
          refine ⟨3325063083332745263019563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216708722221830175346375 3325063083332745263019563)
          ·
            refine ⟨4987594624999117894529345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325063083332745263019563 4987594624999117894529345)
            ·
              refine ⟨3740695968749338420897009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987594624999117894529345 3740695968749338420897009)
              ·
                refine ⟨2805521976562003815672757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740695968749338420897009 2805521976562003815672757)
                ·
                  refine ⟨263017685302687857719321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805521976562003815672757 263017685302687857719321)
                  ·
                    rfl

theorem cell22_2305013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_2305013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305013 prefixEnd_2305013 := by exact prefixLift 2305013
  have htrace : WordTrace (prefixWord ++ tailWord_2305013) baseStart_2305013 baseEnd_2305013 := by
    simpa [prefixWord, tailWord_2305013, baseEnd_2305013] using wordTrace_append hprefix tailTrace_2305013
  have hstable : (prefixWord ++ tailWord_2305013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305013).length < 2 ^ (prefixWord ++ tailWord_2305013).sum := by decide
  have hdescent : baseEnd_2305013 < baseStart_2305013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305082 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_2305082 : Nat := 118140960795 + 2305082 * 2 ^ 59
def prefixEnd_2305082 : Nat := 4983230072969 + 3 ^ 40 * 2305082 * 2
def baseEnd_2305082 : Nat := 789076676018170393182751

theorem tailTrace_2305082 : CollatzResearch.WordTrace tailWord_2305082 prefixEnd_2305082 789076676018170393182751 := by
  unfold tailWord_2305082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21018311858772266377127375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56048831623392710339006333 21018311858772266377127375)
  ·
    refine ⟨31527467788158399565691063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21018311858772266377127375 31527467788158399565691063)
    ·
      refine ⟨47291201682237599348536595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31527467788158399565691063 47291201682237599348536595)
      ·
        refine ⟨70936802523356399022804893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47291201682237599348536595 70936802523356399022804893)
        ·
          refine ⟨26601300946258649633551835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70936802523356399022804893 26601300946258649633551835)
          ·
            refine ⟨39901951419387974450327753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26601300946258649633551835 39901951419387974450327753)
            ·
              refine ⟨29926463564540980837745815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39901951419387974450327753 29926463564540980837745815)
              ·
                refine ⟨44889695346811471256618723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29926463564540980837745815 44889695346811471256618723)
                ·
                  refine ⟨67334543020217206884928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44889695346811471256618723 67334543020217206884928085)
                  ·
                    refine ⟨789076676018170393182751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67334543020217206884928085 789076676018170393182751)
                    ·
                      rfl

theorem cell22_2305082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_2305082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305082 prefixEnd_2305082 := by exact prefixLift 2305082
  have htrace : WordTrace (prefixWord ++ tailWord_2305082) baseStart_2305082 baseEnd_2305082 := by
    simpa [prefixWord, tailWord_2305082, baseEnd_2305082] using wordTrace_append hprefix tailTrace_2305082
  have hstable : (prefixWord ++ tailWord_2305082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305082).length < 2 ^ (prefixWord ++ tailWord_2305082).sum := by decide
  have hdescent : baseEnd_2305082 < baseStart_2305082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305161 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_2305161 : Nat := 118140960795 + 2305161 * 2 ^ 59
def prefixEnd_2305161 : Nat := 4983230072969 + 3 ^ 40 * 2305161 * 2
def baseEnd_2305161 : Nat := 789103719332640520457509

theorem tailTrace_2305161 : CollatzResearch.WordTrace tailWord_2305161 prefixEnd_2305161 789103719332640520457509 := by
  unfold tailWord_2305161
  simp only [CollatzResearch.WordTrace]
  refine ⟨84076128801802862000635337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56050752534535241333756891 84076128801802862000635337)
  ·
    refine ⟨63057096601352146500476503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84076128801802862000635337 63057096601352146500476503)
    ·
      refine ⟨94585644902028219750714755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63057096601352146500476503 94585644902028219750714755)
      ·
        refine ⟨141878467353042329626072133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94585644902028219750714755 141878467353042329626072133)
        ·
          refine ⟨26602212628695436804888525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141878467353042329626072133 26602212628695436804888525)
          ·
            refine ⟨9975829735760788801833197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26602212628695436804888525 9975829735760788801833197)
            ·
              refine ⟨3740936150910295800687449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9975829735760788801833197 3740936150910295800687449)
              ·
                refine ⟨2805702113182721850515587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740936150910295800687449 2805702113182721850515587)
                ·
                  refine ⟨4208553169774082775773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805702113182721850515587 4208553169774082775773381)
                  ·
                    refine ⟨789103719332640520457509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208553169774082775773381 789103719332640520457509)
                    ·
                      rfl

theorem cell22_2305161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_2305161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305161 prefixEnd_2305161 := by exact prefixLift 2305161
  have htrace : WordTrace (prefixWord ++ tailWord_2305161) baseStart_2305161 baseEnd_2305161 := by
    simpa [prefixWord, tailWord_2305161, baseEnd_2305161] using wordTrace_append hprefix tailTrace_2305161
  have hstable : (prefixWord ++ tailWord_2305161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305161).length < 2 ^ (prefixWord ++ tailWord_2305161).sum := by decide
  have hdescent : baseEnd_2305161 < baseStart_2305161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305229 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2305229 : Nat := 118140960795 + 2305229 * 2 ^ 59
def prefixEnd_2305229 : Nat := 4983230072969 + 3 ^ 40 * 2305229 * 2
def baseEnd_2305229 : Nat := 789126997122311009757301

theorem tailTrace_2305229 : CollatzResearch.WordTrace tailWord_2305229 prefixEnd_2305229 789126997122311009757301 := by
  unfold tailWord_2305229
  simp only [CollatzResearch.WordTrace]
  refine ⟨84078608965556509614110741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56052405977037673076073827 84078608965556509614110741)
  ·
    refine ⟨3941184795260461388161441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84078608965556509614110741 3941184795260461388161441)
    ·
      refine ⟨2955888596445346041121081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3941184795260461388161441 2955888596445346041121081)
      ·
        refine ⟨2216916447334009530840811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955888596445346041121081 2216916447334009530840811)
        ·
          refine ⟨3325374671001014296261217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216916447334009530840811 3325374671001014296261217)
          ·
            refine ⟨2494031003250760722195913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3325374671001014296261217 2494031003250760722195913)
            ·
              refine ⟨1870523252438070541646935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494031003250760722195913 1870523252438070541646935)
              ·
                refine ⟨2805784878657105812470403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870523252438070541646935 2805784878657105812470403)
                ·
                  refine ⟨4208677317985658718705605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805784878657105812470403 4208677317985658718705605)
                  ·
                    refine ⟨789126997122311009757301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208677317985658718705605 789126997122311009757301)
                    ·
                      rfl

theorem cell22_2305229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2305229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305229 prefixEnd_2305229 := by exact prefixLift 2305229
  have htrace : WordTrace (prefixWord ++ tailWord_2305229) baseStart_2305229 baseEnd_2305229 := by
    simpa [prefixWord, tailWord_2305229, baseEnd_2305229] using wordTrace_append hprefix tailTrace_2305229
  have hstable : (prefixWord ++ tailWord_2305229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305229).length < 2 ^ (prefixWord ++ tailWord_2305229).sum := by decide
  have hdescent : baseEnd_2305229 < baseStart_2305229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305238 : List Nat := [5, 2, 1, 2, 2, 1, 9]
def baseStart_2305238 : Nat := 118140960795 + 2305238 * 2 ^ 59
def prefixEnd_2305238 : Nat := 4983230072969 + 3 ^ 40 * 2305238 * 2
def baseEnd_2305238 : Nat := 29227039926156962454899

theorem tailTrace_2305238 : CollatzResearch.WordTrace tailWord_2305238 prefixEnd_2305238 29227039926156962454899 := by
  unfold tailWord_2305238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254933576407744009449273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56052624815015936100792245 5254933576407744009449273)
  ·
    refine ⟨3941200182305808007086955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254933576407744009449273 3941200182305808007086955)
    ·
      refine ⟨5911800273458712010630433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941200182305808007086955 5911800273458712010630433)
      ·
        refine ⟨4433850205094034007972825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5911800273458712010630433 4433850205094034007972825)
        ·
          refine ⟨3325387653820525505979619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433850205094034007972825 3325387653820525505979619)
          ·
            refine ⟨4988081480730788258969429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325387653820525505979619 4988081480730788258969429)
            ·
              refine ⟨29227039926156962454899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4988081480730788258969429 29227039926156962454899)
              ·
                rfl

theorem cell22_2305238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 9].length) (baseStart_2305238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305238 prefixEnd_2305238 := by exact prefixLift 2305238
  have htrace : WordTrace (prefixWord ++ tailWord_2305238) baseStart_2305238 baseEnd_2305238 := by
    simpa [prefixWord, tailWord_2305238, baseEnd_2305238] using wordTrace_append hprefix tailTrace_2305238
  have hstable : (prefixWord ++ tailWord_2305238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305238).length < 2 ^ (prefixWord ++ tailWord_2305238).sum := by decide
  have hdescent : baseEnd_2305238 < baseStart_2305238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305330 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_2305330 : Nat := 118140960795 + 2305330 * 2 ^ 59
def prefixEnd_2305330 : Nat := 4983230072969 + 3 ^ 40 * 2305330 * 2
def baseEnd_2305330 : Nat := 789161571486380412981991

theorem tailTrace_2305330 : CollatzResearch.WordTrace tailWord_2305330 prefixEnd_2305330 789161571486380412981991 := by
  unfold tailWord_2305330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21020573184547650965884361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56054861825460402575691629 21020573184547650965884361)
  ·
    refine ⟨15765429888410738224413271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21020573184547650965884361 15765429888410738224413271)
    ·
      refine ⟨23648144832616107336619907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15765429888410738224413271 23648144832616107336619907)
      ·
        refine ⟨35472217248924161004929861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23648144832616107336619907 35472217248924161004929861)
        ·
          refine ⟨6651040734173280188424349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35472217248924161004929861 6651040734173280188424349)
          ·
            refine ⟨2494140275314980070659131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6651040734173280188424349 2494140275314980070659131)
            ·
              refine ⟨3741210412972470105988697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494140275314980070659131 3741210412972470105988697)
              ·
                refine ⟨2805907809729352579491523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741210412972470105988697 2805907809729352579491523)
                ·
                  refine ⟨4208861714594028869237285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805907809729352579491523 4208861714594028869237285)
                  ·
                    refine ⟨789161571486380412981991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208861714594028869237285 789161571486380412981991)
                    ·
                      rfl

theorem cell22_2305330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_2305330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305330 prefixEnd_2305330 := by exact prefixLift 2305330
  have htrace : WordTrace (prefixWord ++ tailWord_2305330) baseStart_2305330 baseEnd_2305330 := by
    simpa [prefixWord, tailWord_2305330, baseEnd_2305330] using wordTrace_append hprefix tailTrace_2305330
  have hstable : (prefixWord ++ tailWord_2305330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305330).length < 2 ^ (prefixWord ++ tailWord_2305330).sum := by decide
  have hdescent : baseEnd_2305330 < baseStart_2305330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305388 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_2305388 : Nat := 118140960795 + 2305388 * 2 ^ 59
def prefixEnd_2305388 : Nat := 4983230072969 + 3 ^ 40 * 2305388 * 2
def baseEnd_2305388 : Nat := 789181426071687595031813

theorem tailTrace_2305388 : CollatzResearch.WordTrace tailWord_2305388 prefixEnd_2305388 789181426071687595031813 := by
  unfold tailWord_2305388
  simp only [CollatzResearch.WordTrace]
  refine ⟨42042204085990239884574409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56056272114653653179432545 42042204085990239884574409)
  ·
    refine ⟨31531653064492679913430807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42042204085990239884574409 31531653064492679913430807)
    ·
      refine ⟨47297479596739019870146211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31531653064492679913430807 47297479596739019870146211)
      ·
        refine ⟨70946219395108529805219317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47297479596739019870146211 70946219395108529805219317)
        ·
          refine ⟨6651208068291424669239311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70946219395108529805219317 6651208068291424669239311)
          ·
            refine ⟨9976812102437137003858967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6651208068291424669239311 9976812102437137003858967)
            ·
              refine ⟨14965218153655705505788451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9976812102437137003858967 14965218153655705505788451)
              ·
                refine ⟨22447827230483558258682677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14965218153655705505788451 22447827230483558258682677)
                ·
                  refine ⟨2104483802857833586751501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22447827230483558258682677 2104483802857833586751501)
                  ·
                    refine ⟨789181426071687595031813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104483802857833586751501 789181426071687595031813)
                    ·
                      rfl

theorem cell22_2305388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_2305388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305388 prefixEnd_2305388 := by exact prefixLift 2305388
  have htrace : WordTrace (prefixWord ++ tailWord_2305388) baseStart_2305388 baseEnd_2305388 := by
    simpa [prefixWord, tailWord_2305388, baseEnd_2305388] using wordTrace_append hprefix tailTrace_2305388
  have hstable : (prefixWord ++ tailWord_2305388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305388).length < 2 ^ (prefixWord ++ tailWord_2305388).sum := by decide
  have hdescent : baseEnd_2305388 < baseStart_2305388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305422 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_2305422 : Nat := 118140960795 + 2305422 * 2 ^ 59
def prefixEnd_2305422 : Nat := 4983230072969 + 3 ^ 40 * 2305422 * 2
def baseEnd_2305422 : Nat := 789193064966522839681709

theorem tailTrace_2305422 : CollatzResearch.WordTrace tailWord_2305422 prefixEnd_2305422 789193064966522839681709 := by
  unfold tailWord_2305422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510706031732162946985815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56057098835904869050591013 10510706031732162946985815)
  ·
    refine ⟨15766059047598244420478723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10510706031732162946985815 15766059047598244420478723)
    ·
      refine ⟨23649088571397366630718085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15766059047598244420478723 23649088571397366630718085)
      ·
        refine ⟨4434204107137006243259641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23649088571397366630718085 4434204107137006243259641)
        ·
          refine ⟨3325653080352754682444731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434204107137006243259641 3325653080352754682444731)
          ·
            refine ⟨4988479620529132023667097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325653080352754682444731 4988479620529132023667097)
            ·
              refine ⟨3741359715396849017750323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988479620529132023667097 3741359715396849017750323)
              ·
                refine ⟨5612039573095273526625485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741359715396849017750323 5612039573095273526625485)
                ·
                  refine ⟨2104514839910727572484557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5612039573095273526625485 2104514839910727572484557)
                  ·
                    refine ⟨789193064966522839681709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104514839910727572484557 789193064966522839681709)
                    ·
                      rfl

theorem cell22_2305422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_2305422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305422 prefixEnd_2305422 := by exact prefixLift 2305422
  have htrace : WordTrace (prefixWord ++ tailWord_2305422) baseStart_2305422 baseEnd_2305422 := by
    simpa [prefixWord, tailWord_2305422, baseEnd_2305422] using wordTrace_append hprefix tailTrace_2305422
  have hstable : (prefixWord ++ tailWord_2305422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305422).length < 2 ^ (prefixWord ++ tailWord_2305422).sum := by decide
  have hdescent : baseEnd_2305422 < baseStart_2305422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305493 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2305493 : Nat := 118140960795 + 2305493 * 2 ^ 59
def prefixEnd_2305493 : Nat := 4983230072969 + 3 ^ 40 * 2305493 * 2
def baseEnd_2305493 : Nat := 789217369717502321156491

theorem tailTrace_2305493 : CollatzResearch.WordTrace tailWord_2305493 prefixEnd_2305493 789217369717502321156491 := by
  unfold tailWord_2305493
  simp only [CollatzResearch.WordTrace]
  refine ⟨84088237836600082701721133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56058825224400055134480755 84088237836600082701721133)
  ·
    refine ⟨31533089188725031013145425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84088237836600082701721133 31533089188725031013145425)
    ·
      refine ⟨23649816891543773259859069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31533089188725031013145425 23649816891543773259859069)
      ·
        refine ⟨8868681334328914972447151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23649816891543773259859069 8868681334328914972447151)
        ·
          refine ⟨13303022001493372458670727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868681334328914972447151 13303022001493372458670727)
          ·
            refine ⟨19954533002240058688006091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13303022001493372458670727 19954533002240058688006091)
            ·
              refine ⟨29931799503360088032009137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19954533002240058688006091 29931799503360088032009137)
              ·
                refine ⟨22448849627520066024006853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29931799503360088032009137 22448849627520066024006853)
                ·
                  refine ⟨4209159305160012379501285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22448849627520066024006853 4209159305160012379501285)
                  ·
                    refine ⟨789217369717502321156491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209159305160012379501285 789217369717502321156491)
                    ·
                      rfl

theorem cell22_2305493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2305493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305493 prefixEnd_2305493 := by exact prefixLift 2305493
  have htrace : WordTrace (prefixWord ++ tailWord_2305493) baseStart_2305493 baseEnd_2305493 := by
    simpa [prefixWord, tailWord_2305493, baseEnd_2305493] using wordTrace_append hprefix tailTrace_2305493
  have hstable : (prefixWord ++ tailWord_2305493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305493).length < 2 ^ (prefixWord ++ tailWord_2305493).sum := by decide
  have hdescent : baseEnd_2305493 < baseStart_2305493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305523 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 7, 3]
def baseStart_2305523 : Nat := 118140960795 + 2305523 * 2 ^ 59
def prefixEnd_2305523 : Nat := 4983230072969 + 3 ^ 40 * 2305523 * 2
def baseEnd_2305523 : Nat := 789227639330592242906399

theorem tailTrace_2305523 : CollatzResearch.WordTrace tailWord_2305523 prefixEnd_2305523 789227639330592242906399 := by
  unfold tailWord_2305523
  simp only [CollatzResearch.WordTrace]
  refine ⟨84089332026491397825313223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56059554684327598550208815 84089332026491397825313223)
  ·
    refine ⟨126133998039737096737969835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84089332026491397825313223 126133998039737096737969835)
    ·
      refine ⟨189200997059605645106954753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126133998039737096737969835 189200997059605645106954753)
      ·
        refine ⟨141900747794704233830216065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189200997059605645106954753 141900747794704233830216065)
        ·
          refine ⟨106425560846028175372662049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141900747794704233830216065 106425560846028175372662049)
          ·
            refine ⟨79819170634521131529496537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106425560846028175372662049 79819170634521131529496537)
            ·
              refine ⟨59864377975890848647122403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79819170634521131529496537 59864377975890848647122403)
              ·
                refine ⟨89796566963836272970683605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59864377975890848647122403 89796566963836272970683605)
                ·
                  refine ⟨2104607038214912647750397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89796566963836272970683605 2104607038214912647750397)
                  ·
                    refine ⟨789227639330592242906399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104607038214912647750397 789227639330592242906399)
                    ·
                      rfl

theorem cell22_2305523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].length) (baseStart_2305523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305523 prefixEnd_2305523 := by exact prefixLift 2305523
  have htrace : WordTrace (prefixWord ++ tailWord_2305523) baseStart_2305523 baseEnd_2305523 := by
    simpa [prefixWord, tailWord_2305523, baseEnd_2305523] using wordTrace_append hprefix tailTrace_2305523
  have hstable : (prefixWord ++ tailWord_2305523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305523).length < 2 ^ (prefixWord ++ tailWord_2305523).sum := by decide
  have hdescent : baseEnd_2305523 < baseStart_2305523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305553 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 5]
def baseStart_2305553 : Nat := 118140960795 + 2305553 * 2 ^ 59
def prefixEnd_2305553 : Nat := 4983230072969 + 3 ^ 40 * 2305553 * 2
def baseEnd_2305553 : Nat := 263079302981227388218769

theorem tailTrace_2305553 : CollatzResearch.WordTrace tailWord_2305553 prefixEnd_2305553 263079302981227388218769 := by
  unfold tailWord_2305553
  simp only [CollatzResearch.WordTrace]
  refine ⟨84090426216382712948905313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56060284144255141965936875 84090426216382712948905313)
  ·
    refine ⟨63067819662287034711678985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84090426216382712948905313 63067819662287034711678985)
    ·
      refine ⟨47300864746715276033759239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63067819662287034711678985 47300864746715276033759239)
      ·
        refine ⟨70951297120072914050638859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47300864746715276033759239 70951297120072914050638859)
        ·
          refine ⟨106426945680109371075958289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70951297120072914050638859 106426945680109371075958289)
          ·
            refine ⟨79820209260082028306968717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106426945680109371075958289 79820209260082028306968717)
            ·
              refine ⟨29932578472530760615113269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79820209260082028306968717 29932578472530760615113269)
              ·
                refine ⟨2806179231799758807666869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29932578472530760615113269 2806179231799758807666869)
                ·
                  refine ⟨263079302981227388218769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806179231799758807666869 263079302981227388218769)
                  ·
                    rfl

theorem cell22_2305553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_2305553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305553 prefixEnd_2305553 := by exact prefixLift 2305553
  have htrace : WordTrace (prefixWord ++ tailWord_2305553) baseStart_2305553 baseEnd_2305553 := by
    simpa [prefixWord, tailWord_2305553, baseEnd_2305553] using wordTrace_append hprefix tailTrace_2305553
  have hstable : (prefixWord ++ tailWord_2305553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305553).length < 2 ^ (prefixWord ++ tailWord_2305553).sum := by decide
  have hdescent : baseEnd_2305553 < baseStart_2305553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_2305658 : Nat := 118140960795 + 2305658 * 2 ^ 59
def prefixEnd_2305658 : Nat := 4983230072969 + 3 ^ 40 * 2305658 * 2
def baseEnd_2305658 : Nat := 789273852589496890780985

theorem tailTrace_2305658 : CollatzResearch.WordTrace tailWord_2305658 prefixEnd_2305658 789273852589496890780985 := by
  unfold tailWord_2305658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023563970250578970369407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56062837254001543920985085 21023563970250578970369407)
  ·
    refine ⟨31535345955375868455554111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21023563970250578970369407 31535345955375868455554111)
    ·
      refine ⟨47303018933063802683331167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31535345955375868455554111 47303018933063802683331167)
      ·
        refine ⟨70954528399595704024996751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47303018933063802683331167 70954528399595704024996751)
        ·
          refine ⟨106431792599393556037495127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70954528399595704024996751 106431792599393556037495127)
          ·
            refine ⟨159647688899090334056242691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106431792599393556037495127 159647688899090334056242691)
            ·
              refine ⟨239471533348635501084364037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159647688899090334056242691 239471533348635501084364037)
              ·
                refine ⟨44900912502869156453318257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239471533348635501084364037 44900912502869156453318257)
                ·
                  refine ⟨33675684377151867339988693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44900912502869156453318257 33675684377151867339988693)
                  ·
                    refine ⟨789273852589496890780985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33675684377151867339988693 789273852589496890780985)
                    ·
                      rfl

theorem cell22_2305658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_2305658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305658 prefixEnd_2305658 := by exact prefixLift 2305658
  have htrace : WordTrace (prefixWord ++ tailWord_2305658) baseStart_2305658 baseEnd_2305658 := by
    simpa [prefixWord, tailWord_2305658, baseEnd_2305658] using wordTrace_append hprefix tailTrace_2305658
  have hstable : (prefixWord ++ tailWord_2305658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305658).length < 2 ^ (prefixWord ++ tailWord_2305658).sum := by decide
  have hdescent : baseEnd_2305658 < baseStart_2305658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305675 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 5, 3]
def baseStart_2305675 : Nat := 118140960795 + 2305675 * 2 ^ 59
def prefixEnd_2305675 : Nat := 4983230072969 + 3 ^ 40 * 2305675 * 2
def baseEnd_2305675 : Nat := 789279672036914513105933

theorem tailTrace_2305675 : CollatzResearch.WordTrace tailWord_2305675 prefixEnd_2305675 789279672036914513105933 := by
  unfold tailWord_2305675
  simp only [CollatzResearch.WordTrace]
  refine ⟨84094875921940727784846479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56063250614627151856564319 84094875921940727784846479)
  ·
    refine ⟨126142313882911091677269719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84094875921940727784846479 126142313882911091677269719)
    ·
      refine ⟨189213470824366637515904579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126142313882911091677269719 189213470824366637515904579)
      ·
        refine ⟨283820206236549956273856869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189213470824366637515904579 283820206236549956273856869)
        ·
          refine ⟨53216288669353116801348163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283820206236549956273856869 53216288669353116801348163)
          ·
            refine ⟨79824433004029675202022245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53216288669353116801348163 79824433004029675202022245)
            ·
              refine ⟨14967081188255564100379171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79824433004029675202022245 14967081188255564100379171)
              ·
                refine ⟨22450621782383346150568757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14967081188255564100379171 22450621782383346150568757)
                ·
                  refine ⟨2104745792098438701615821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22450621782383346150568757 2104745792098438701615821)
                  ·
                    refine ⟨789279672036914513105933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104745792098438701615821 789279672036914513105933)
                    ·
                      rfl

theorem cell22_2305675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].length) (baseStart_2305675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305675 prefixEnd_2305675 := by exact prefixLift 2305675
  have htrace : WordTrace (prefixWord ++ tailWord_2305675) baseStart_2305675 baseEnd_2305675 := by
    simpa [prefixWord, tailWord_2305675, baseEnd_2305675] using wordTrace_append hprefix tailTrace_2305675
  have hstable : (prefixWord ++ tailWord_2305675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305675).length < 2 ^ (prefixWord ++ tailWord_2305675).sum := by decide
  have hdescent : baseEnd_2305675 < baseStart_2305675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305730 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2305730 : Nat := 118140960795 + 2305730 * 2 ^ 59
def prefixEnd_2305730 : Nat := 4983230072969 + 3 ^ 40 * 2305730 * 2
def baseEnd_2305730 : Nat := 789298499660912702980765

theorem tailTrace_2305730 : CollatzResearch.WordTrace tailWord_2305730 prefixEnd_2305730 789298499660912702980765 := by
  unfold tailWord_2305730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21024220484185368044524661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56064587957827648118732429 21024220484185368044524661)
  ·
    refine ⟨1971020670392378254174187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21024220484185368044524661 1971020670392378254174187)
    ·
      refine ⟨2956531005588567381261281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971020670392378254174187 2956531005588567381261281)
      ·
        refine ⟨2217398254191425535945961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956531005588567381261281 2217398254191425535945961)
        ·
          refine ⟨1663048690643569151959471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217398254191425535945961 1663048690643569151959471)
          ·
            refine ⟨2494573035965353727939207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663048690643569151959471 2494573035965353727939207)
            ·
              refine ⟨3741859553948030591908811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494573035965353727939207 3741859553948030591908811)
              ·
                refine ⟨5612789330922045887863217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741859553948030591908811 5612789330922045887863217)
                ·
                  refine ⟨4209591998191534415897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612789330922045887863217 4209591998191534415897413)
                  ·
                    refine ⟨789298499660912702980765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209591998191534415897413 789298499660912702980765)
                    ·
                      rfl

theorem cell22_2305730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2305730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305730 prefixEnd_2305730 := by exact prefixLift 2305730
  have htrace : WordTrace (prefixWord ++ tailWord_2305730) baseStart_2305730 baseEnd_2305730 := by
    simpa [prefixWord, tailWord_2305730, baseEnd_2305730] using wordTrace_append hprefix tailTrace_2305730
  have hstable : (prefixWord ++ tailWord_2305730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305730).length < 2 ^ (prefixWord ++ tailWord_2305730).sum := by decide
  have hdescent : baseEnd_2305730 < baseStart_2305730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305735 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2305735 : Nat := 118140960795 + 2305735 * 2 ^ 59
def prefixEnd_2305735 : Nat := 4983230072969 + 3 ^ 40 * 2305735 * 2
def baseEnd_2305735 : Nat := 789300211263094356605749

theorem tailTrace_2305735 : CollatzResearch.WordTrace tailWord_2305735 prefixEnd_2305735 789300211263094356605749 := by
  unfold tailWord_2305735
  simp only [CollatzResearch.WordTrace]
  refine ⟨84097064301723358032030659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56064709534482238688020439 84097064301723358032030659)
  ·
    refine ⟨126145596452585037048045989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84097064301723358032030659 126145596452585037048045989)
    ·
      refine ⟨23652299334859694446508623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126145596452585037048045989 23652299334859694446508623)
      ·
        refine ⟨35478449002289541669762935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23652299334859694446508623 35478449002289541669762935)
        ·
          refine ⟨53217673503434312504644403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35478449002289541669762935 53217673503434312504644403)
          ·
            refine ⟨79826510255151468756966605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53217673503434312504644403 79826510255151468756966605)
            ·
              refine ⟨29934941345681800783862477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79826510255151468756966605 29934941345681800783862477)
              ·
                refine ⟨11225603004630675293948429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29934941345681800783862477 11225603004630675293948429)
                ·
                  refine ⟨4209601126736503235230661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11225603004630675293948429 4209601126736503235230661)
                  ·
                    refine ⟨789300211263094356605749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209601126736503235230661 789300211263094356605749)
                    ·
                      rfl

theorem cell22_2305735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2305735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305735 prefixEnd_2305735 := by exact prefixLift 2305735
  have htrace : WordTrace (prefixWord ++ tailWord_2305735) baseStart_2305735 baseEnd_2305735 := by
    simpa [prefixWord, tailWord_2305735, baseEnd_2305735] using wordTrace_append hprefix tailTrace_2305735
  have hstable : (prefixWord ++ tailWord_2305735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305735).length < 2 ^ (prefixWord ++ tailWord_2305735).sum := by decide
  have hdescent : baseEnd_2305735 < baseStart_2305735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305752 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_2305752 : Nat := 118140960795 + 2305752 * 2 ^ 59
def prefixEnd_2305752 : Nat := 4983230072969 + 3 ^ 40 * 2305752 * 2
def baseEnd_2305752 : Nat := 789306030710511978930697

theorem tailTrace_2305752 : CollatzResearch.WordTrace tailWord_2305752 prefixEnd_2305752 789306030710511978930697 := by
  unfold tailWord_2305752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42048842171330884967699755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56065122895107846623599673 42048842171330884967699755)
  ·
    refine ⟨63073263256996327451549633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42048842171330884967699755 63073263256996327451549633)
    ·
      refine ⟨47304947442747245588662225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63073263256996327451549633 47304947442747245588662225)
      ·
        refine ⟨35478710582060434191496669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47304947442747245588662225 35478710582060434191496669)
        ·
          refine ⟨13304516468272662821811251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35478710582060434191496669 13304516468272662821811251)
          ·
            refine ⟨19956774702408994232716877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13304516468272662821811251 19956774702408994232716877)
            ·
              refine ⟨7483790513403372837268829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19956774702408994232716877 7483790513403372837268829)
              ·
                refine ⟨2806421442526264813975811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483790513403372837268829 2806421442526264813975811)
                ·
                  refine ⟨4209632163789397220963717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806421442526264813975811 4209632163789397220963717)
                  ·
                    refine ⟨789306030710511978930697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209632163789397220963717 789306030710511978930697)
                    ·
                      rfl

theorem cell22_2305752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_2305752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305752 prefixEnd_2305752 := by exact prefixLift 2305752
  have htrace : WordTrace (prefixWord ++ tailWord_2305752) baseStart_2305752 baseEnd_2305752 := by
    simpa [prefixWord, tailWord_2305752, baseEnd_2305752] using wordTrace_append hprefix tailTrace_2305752
  have hstable : (prefixWord ++ tailWord_2305752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305752).length < 2 ^ (prefixWord ++ tailWord_2305752).sum := by decide
  have hdescent : baseEnd_2305752 < baseStart_2305752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305756 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_2305756 : Nat := 118140960795 + 2305756 * 2 ^ 59
def prefixEnd_2305756 : Nat := 4983230072969 + 3 ^ 40 * 2305756 * 2
def baseEnd_2305756 : Nat := 263102466664085767276895

theorem tailTrace_2305756 : CollatzResearch.WordTrace tailWord_2305756 prefixEnd_2305756 263102466664085767276895 := by
  unfold tailWord_2305756
  simp only [CollatzResearch.WordTrace]
  refine ⟨42048915117323639309272561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56065220156431519079030081 42048915117323639309272561)
  ·
    refine ⟨31536686337992729481954421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42048915117323639309272561 31536686337992729481954421)
    ·
      refine ⟨2956564344186818388933227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31536686337992729481954421 2956564344186818388933227)
      ·
        refine ⟨4434846516280227583399841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956564344186818388933227 4434846516280227583399841)
        ·
          refine ⟨3326134887210170687549881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434846516280227583399841 3326134887210170687549881)
          ·
            refine ⟨2494601165407628015662411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326134887210170687549881 2494601165407628015662411)
            ·
              refine ⟨3741901748111442023493617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494601165407628015662411 3741901748111442023493617)
              ·
                refine ⟨2806426311083581517620213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741901748111442023493617 2806426311083581517620213)
                ·
                  refine ⟨263102466664085767276895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806426311083581517620213 263102466664085767276895)
                  ·
                    rfl

theorem cell22_2305756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_2305756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305756 prefixEnd_2305756 := by exact prefixLift 2305756
  have htrace : WordTrace (prefixWord ++ tailWord_2305756) baseStart_2305756 baseEnd_2305756 := by
    simpa [prefixWord, tailWord_2305756, baseEnd_2305756] using wordTrace_append hprefix tailTrace_2305756
  have hstable : (prefixWord ++ tailWord_2305756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305756).length < 2 ^ (prefixWord ++ tailWord_2305756).sum := by decide
  have hdescent : baseEnd_2305756 < baseStart_2305756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305874 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_2305874 : Nat := 118140960795 + 2305874 * 2 ^ 59
def prefixEnd_2305874 : Nat := 4983230072969 + 3 ^ 40 * 2305874 * 2
def baseEnd_2305874 : Nat := 263115931267914775793441

theorem tailTrace_2305874 : CollatzResearch.WordTrace tailWord_2305874 prefixEnd_2305874 263115931267914775793441 := by
  unfold tailWord_2305874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025533512054946192835169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56068089365479856514227117 21025533512054946192835169)
  ·
    refine ⟨15769150134041209644626377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21025533512054946192835169 15769150134041209644626377)
    ·
      refine ⟨11826862600530907233469783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15769150134041209644626377 11826862600530907233469783)
      ·
        refine ⟨17740293900796360850204675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826862600530907233469783 17740293900796360850204675)
        ·
          refine ⟨26610440851194541275307013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17740293900796360850204675 26610440851194541275307013)
          ·
            refine ⟨4989457659598976489120065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26610440851194541275307013 4989457659598976489120065)
            ·
              refine ⟨3742093244699232366840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989457659598976489120065 3742093244699232366840049)
              ·
                refine ⟨2806569933524424275130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3742093244699232366840049 2806569933524424275130037)
                ·
                  refine ⟨263115931267914775793441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806569933524424275130037 263115931267914775793441)
                  ·
                    rfl

theorem cell22_2305874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_2305874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305874 prefixEnd_2305874 := by exact prefixLift 2305874
  have htrace : WordTrace (prefixWord ++ tailWord_2305874) baseStart_2305874 baseEnd_2305874 := by
    simpa [prefixWord, tailWord_2305874, baseEnd_2305874] using wordTrace_append hprefix tailTrace_2305874
  have hstable : (prefixWord ++ tailWord_2305874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305874).length < 2 ^ (prefixWord ++ tailWord_2305874).sum := by decide
  have hdescent : baseEnd_2305874 < baseStart_2305874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305887 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_2305887 : Nat := 118140960795 + 2305887 * 2 ^ 59
def prefixEnd_2305887 : Nat := 4983230072969 + 3 ^ 40 * 2305887 * 2
def baseEnd_2305887 : Nat := 789352243969416626805283

theorem tailTrace_2305887 : CollatzResearch.WordTrace tailWord_2305887 prefixEnd_2305887 789352243969416626805283 := by
  unfold tailWord_2305887
  simp only [CollatzResearch.WordTrace]
  refine ⟨84102608197172687991563915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56068405464781791994375943 84102608197172687991563915)
  ·
    refine ⟨126153912295759031987345873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84102608197172687991563915 126153912295759031987345873)
    ·
      refine ⟨94615434221819273990509405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126153912295759031987345873 94615434221819273990509405)
      ·
        refine ⟨35480787833182227746441027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94615434221819273990509405 35480787833182227746441027)
        ·
          refine ⟨53221181749773341619661541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35480787833182227746441027 53221181749773341619661541)
          ·
            refine ⟨9978971578082501553686539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53221181749773341619661541 9978971578082501553686539)
            ·
              refine ⟨14968457367123752330529809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9978971578082501553686539 14968457367123752330529809)
              ·
                refine ⟨11226343025342814247897357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14968457367123752330529809 11226343025342814247897357)
                ·
                  refine ⟨4209878634503555342961509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11226343025342814247897357 4209878634503555342961509)
                  ·
                    refine ⟨789352243969416626805283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209878634503555342961509 789352243969416626805283)
                    ·
                      rfl

theorem cell22_2305887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_2305887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305887 prefixEnd_2305887 := by exact prefixLift 2305887
  have htrace : WordTrace (prefixWord ++ tailWord_2305887) baseStart_2305887 baseEnd_2305887 := by
    simpa [prefixWord, tailWord_2305887, baseEnd_2305887] using wordTrace_append hprefix tailTrace_2305887
  have hstable : (prefixWord ++ tailWord_2305887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305887).length < 2 ^ (prefixWord ++ tailWord_2305887).sum := by decide
  have hdescent : baseEnd_2305887 < baseStart_2305887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305932 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_2305932 : Nat := 118140960795 + 2305932 * 2 ^ 59
def prefixEnd_2305932 : Nat := 4983230072969 + 3 ^ 40 * 2305932 * 2
def baseEnd_2305932 : Nat := 789367648389051509430145

theorem tailTrace_2305932 : CollatzResearch.WordTrace tailWord_2305932 prefixEnd_2305932 789367648389051509430145 := by
  unfold tailWord_2305932
  simp only [CollatzResearch.WordTrace]
  refine ⟨42052124741004830338476025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56069499654673107117968033 42052124741004830338476025)
  ·
    refine ⟨31539093555753622753857019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42052124741004830338476025 31539093555753622753857019)
    ·
      refine ⟨47308640333630434130785529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31539093555753622753857019 47308640333630434130785529)
      ·
        refine ⟨35481480250222825598089147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47308640333630434130785529 35481480250222825598089147)
        ·
          refine ⟨53222220375334238397133721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35481480250222825598089147 53222220375334238397133721)
          ·
            refine ⟨39916665281500678797850291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53222220375334238397133721 39916665281500678797850291)
            ·
              refine ⟨59874997922251018196775437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39916665281500678797850291 59874997922251018196775437)
              ·
                refine ⟨22453124220844131823790789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59874997922251018196775437 22453124220844131823790789)
                ·
                  refine ⟨4209960791408274716960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22453124220844131823790789 4209960791408274716960773)
                  ·
                    refine ⟨789367648389051509430145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209960791408274716960773 789367648389051509430145)
                    ·
                      rfl

theorem cell22_2305932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_2305932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305932 prefixEnd_2305932 := by exact prefixLift 2305932
  have htrace : WordTrace (prefixWord ++ tailWord_2305932) baseStart_2305932 baseEnd_2305932 := by
    simpa [prefixWord, tailWord_2305932, baseEnd_2305932] using wordTrace_append hprefix tailTrace_2305932
  have hstable : (prefixWord ++ tailWord_2305932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305932).length < 2 ^ (prefixWord ++ tailWord_2305932).sum := by decide
  have hdescent : baseEnd_2305932 < baseStart_2305932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305951 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 5]
def baseStart_2305951 : Nat := 118140960795 + 2305951 * 2 ^ 59
def prefixEnd_2305951 : Nat := 4983230072969 + 3 ^ 40 * 2305951 * 2
def baseEnd_2305951 : Nat := 789374152477341793205087

theorem tailTrace_2305951 : CollatzResearch.WordTrace tailWord_2305951 prefixEnd_2305951 789374152477341793205087 := by
  unfold tailWord_2305951
  simp only [CollatzResearch.WordTrace]
  refine ⟨84104942468940826921893707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56069961645960551281262471 84104942468940826921893707)
  ·
    refine ⟨126157413703411240382840561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84104942468940826921893707 126157413703411240382840561)
    ·
      refine ⟨94618060277558430287130421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126157413703411240382840561 94618060277558430287130421)
      ·
        refine ⟨8870443151021102839418477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94618060277558430287130421 8870443151021102839418477)
        ·
          refine ⟨3326416181632913564781929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8870443151021102839418477 3326416181632913564781929)
          ·
            refine ⟨2494812136224685173586447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326416181632913564781929 2494812136224685173586447)
            ·
              refine ⟨3742218204337027760379671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494812136224685173586447 3742218204337027760379671)
              ·
                refine ⟨5613327306505541640569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742218204337027760379671 5613327306505541640569507)
                ·
                  refine ⟨8419990959758312460854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613327306505541640569507 8419990959758312460854261)
                  ·
                    refine ⟨789374152477341793205087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8419990959758312460854261 789374152477341793205087)
                    ·
                      rfl

theorem cell22_2305951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_2305951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305951 prefixEnd_2305951 := by exact prefixLift 2305951
  have htrace : WordTrace (prefixWord ++ tailWord_2305951) baseStart_2305951 baseEnd_2305951 := by
    simpa [prefixWord, tailWord_2305951, baseEnd_2305951] using wordTrace_append hprefix tailTrace_2305951
  have hstable : (prefixWord ++ tailWord_2305951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305951).length < 2 ^ (prefixWord ++ tailWord_2305951).sum := by decide
  have hdescent : baseEnd_2305951 < baseStart_2305951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305996 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_2305996 : Nat := 118140960795 + 2305996 * 2 ^ 59
def prefixEnd_2305996 : Nat := 4983230072969 + 3 ^ 40 * 2305996 * 2
def baseEnd_2305996 : Nat := 789389556896976675829949

theorem tailTrace_2305996 : CollatzResearch.WordTrace tailWord_2305996 prefixEnd_2305996 789389556896976675829949 := by
  unfold tailWord_2305996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42053291876888899803640921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56071055835851866404854561 42053291876888899803640921)
  ·
    refine ⟨31539968907666674852730691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42053291876888899803640921 31539968907666674852730691)
    ·
      refine ⟨47309953361500012279096037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31539968907666674852730691 47309953361500012279096037)
      ·
        refine ⟨8870616255281252302330507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47309953361500012279096037 8870616255281252302330507)
        ·
          refine ⟨13305924382921878453495761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870616255281252302330507 13305924382921878453495761)
          ·
            refine ⟨9979443287191408840121821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13305924382921878453495761 9979443287191408840121821)
            ·
              refine ⟨3742291232696778315045683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9979443287191408840121821 3742291232696778315045683)
              ·
                refine ⟨5613436849045167472568525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742291232696778315045683 5613436849045167472568525)
                ·
                  refine ⟨2105038818391937802213197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5613436849045167472568525 2105038818391937802213197)
                  ·
                    refine ⟨789389556896976675829949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2105038818391937802213197 789389556896976675829949)
                    ·
                      rfl

theorem cell22_2305996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_2305996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305996 prefixEnd_2305996 := by exact prefixLift 2305996
  have htrace : WordTrace (prefixWord ++ tailWord_2305996) baseStart_2305996 baseEnd_2305996 := by
    simpa [prefixWord, tailWord_2305996, baseEnd_2305996] using wordTrace_append hprefix tailTrace_2305996
  have hstable : (prefixWord ++ tailWord_2305996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305996).length < 2 ^ (prefixWord ++ tailWord_2305996).sum := by decide
  have hdescent : baseEnd_2305996 < baseStart_2305996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306002 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2306002 : Nat := 118140960795 + 2306002 * 2 ^ 59
def prefixEnd_2306002 : Nat := 4983230072969 + 3 ^ 40 * 2306002 * 2
def baseEnd_2306002 : Nat := 789391610819594660179931

theorem tailTrace_2306002 : CollatzResearch.WordTrace tailWord_2306002 prefixEnd_2306002 789391610819594660179931 := by
  unfold tailWord_2306002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21026700647939015658000065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56071201727837375088000173 21026700647939015658000065)
  ·
    refine ⟨15770025485954261743500049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21026700647939015658000065 15770025485954261743500049)
    ·
      refine ⟨11827519114465696307625037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15770025485954261743500049 11827519114465696307625037)
      ·
        refine ⟨4435319667924636115359389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11827519114465696307625037 4435319667924636115359389)
        ·
          refine ⟨1663244875471738543259771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4435319667924636115359389 1663244875471738543259771)
          ·
            refine ⟨2494867313207607814889657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663244875471738543259771 2494867313207607814889657)
            ·
              refine ⟨1871150484905705861167243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494867313207607814889657 1871150484905705861167243)
              ·
                refine ⟨2806725727358558791750865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871150484905705861167243 2806725727358558791750865)
                ·
                  refine ⟨2105044295518919093813149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806725727358558791750865 2105044295518919093813149)
                  ·
                    refine ⟨789391610819594660179931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2105044295518919093813149 789391610819594660179931)
                    ·
                      rfl

theorem cell22_2306002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2306002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306002 prefixEnd_2306002 := by exact prefixLift 2306002
  have htrace : WordTrace (prefixWord ++ tailWord_2306002) baseStart_2306002 baseEnd_2306002 := by
    simpa [prefixWord, tailWord_2306002, baseEnd_2306002] using wordTrace_append hprefix tailTrace_2306002
  have hstable : (prefixWord ++ tailWord_2306002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306002).length < 2 ^ (prefixWord ++ tailWord_2306002).sum := by decide
  have hdescent : baseEnd_2306002 < baseStart_2306002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306007 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2306007 : Nat := 118140960795 + 2306007 * 2 ^ 59
def prefixEnd_2306007 : Nat := 4983230072969 + 3 ^ 40 * 2306007 * 2
def baseEnd_2306007 : Nat := 789393322421776313804915

theorem tailTrace_2306007 : CollatzResearch.WordTrace tailWord_2306007 prefixEnd_2306007 789393322421776313804915 := by
  unfold tailWord_2306007
  simp only [CollatzResearch.WordTrace]
  refine ⟨84106984956737948485932275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56071323304491965657288183 84106984956737948485932275)
  ·
    refine ⟨126160477435106922728898413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84106984956737948485932275 126160477435106922728898413)
    ·
      refine ⟨47310179038165096023336905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126160477435106922728898413 47310179038165096023336905)
      ·
        refine ⟨35482634278623822017502679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47310179038165096023336905 35482634278623822017502679)
        ·
          refine ⟨53223951417935733026254019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35482634278623822017502679 53223951417935733026254019)
          ·
            refine ⟨79835927126903599539381029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53223951417935733026254019 79835927126903599539381029)
            ·
              refine ⟨14969236336294424913633943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79835927126903599539381029 14969236336294424913633943)
              ·
                refine ⟨22453854504441637370450915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14969236336294424913633943 22453854504441637370450915)
                ·
                  refine ⟨33680781756662456055676373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22453854504441637370450915 33680781756662456055676373)
                  ·
                    refine ⟨789393322421776313804915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33680781756662456055676373 789393322421776313804915)
                    ·
                      rfl

theorem cell22_2306007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2306007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306007 prefixEnd_2306007 := by exact prefixLift 2306007
  have htrace : WordTrace (prefixWord ++ tailWord_2306007) baseStart_2306007 baseEnd_2306007 := by
    simpa [prefixWord, tailWord_2306007, baseEnd_2306007] using wordTrace_append hprefix tailTrace_2306007
  have hstable : (prefixWord ++ tailWord_2306007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306007).length < 2 ^ (prefixWord ++ tailWord_2306007).sum := by decide
  have hdescent : baseEnd_2306007 < baseStart_2306007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306071 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 6]
def baseStart_2306071 : Nat := 118140960795 + 2306071 * 2 ^ 59
def prefixEnd_2306071 : Nat := 4983230072969 + 3 ^ 40 * 2306071 * 2
def baseEnd_2306071 : Nat := 263138410309900493401573

theorem tailTrace_2306071 : CollatzResearch.WordTrace tailWord_2306071 prefixEnd_2306071 263138410309900493401573 := by
  unfold tailWord_2306071
  simp only [CollatzResearch.WordTrace]
  refine ⟨84109319228506087416262067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56072879485670724944174711 84109319228506087416262067)
  ·
    refine ⟨126163978842759131124393101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84109319228506087416262067 126163978842759131124393101)
    ·
      refine ⟨47311492066034674171647413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126163978842759131124393101 47311492066034674171647413)
      ·
        refine ⟨4435452381190750703591945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47311492066034674171647413 4435452381190750703591945)
        ·
          refine ⟨3326589285893063027693959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435452381190750703591945 3326589285893063027693959)
          ·
            refine ⟨4989883928839594541540939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326589285893063027693959 4989883928839594541540939)
            ·
              refine ⟨7484825893259391812311409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989883928839594541540939 7484825893259391812311409)
              ·
                refine ⟨5613619419944543859233557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484825893259391812311409 5613619419944543859233557)
                ·
                  refine ⟨263138410309900493401573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5613619419944543859233557 263138410309900493401573)
                  ·
                    rfl

theorem cell22_2306071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_2306071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306071 prefixEnd_2306071 := by exact prefixLift 2306071
  have htrace : WordTrace (prefixWord ++ tailWord_2306071) baseStart_2306071 baseEnd_2306071 := by
    simpa [prefixWord, tailWord_2306071, baseEnd_2306071] using wordTrace_append hprefix tailTrace_2306071
  have hstable : (prefixWord ++ tailWord_2306071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306071).length < 2 ^ (prefixWord ++ tailWord_2306071).sum := by decide
  have hdescent : baseEnd_2306071 < baseStart_2306071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306090 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2306090 : Nat := 118140960795 + 2306090 * 2 ^ 59
def prefixEnd_2306090 : Nat := 4983230072969 + 3 ^ 40 * 2306090 * 2
def baseEnd_2306090 : Nat := 789421735017991763979661

theorem tailTrace_2306090 : CollatzResearch.WordTrace tailWord_2306090 prefixEnd_2306090 789421735017991763979661 := by
  unfold tailWord_2306090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027503053859313415300931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56073341476958169107469149 21027503053859313415300931)
  ·
    refine ⟨31541254580788970122951397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027503053859313415300931 31541254580788970122951397)
    ·
      refine ⟨5913985233897931898053387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31541254580788970122951397 5913985233897931898053387)
      ·
        refine ⟨8870977850846897847080081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5913985233897931898053387 8870977850846897847080081)
        ·
          refine ⟨6653233388135173385310061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8870977850846897847080081 6653233388135173385310061)
          ·
            refine ⟨2494962520550690019491273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6653233388135173385310061 2494962520550690019491273)
            ·
              refine ⟨1871221890413017514618455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494962520550690019491273 1871221890413017514618455)
              ·
                refine ⟨2806832835619526271927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871221890413017514618455 2806832835619526271927683)
                ·
                  refine ⟨4210249253429289407891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806832835619526271927683 4210249253429289407891525)
                  ·
                    refine ⟨789421735017991763979661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4210249253429289407891525 789421735017991763979661)
                    ·
                      rfl

theorem cell22_2306090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2306090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306090 prefixEnd_2306090 := by exact prefixLift 2306090
  have htrace : WordTrace (prefixWord ++ tailWord_2306090) baseStart_2306090 baseEnd_2306090 := by
    simpa [prefixWord, tailWord_2306090, baseEnd_2306090] using wordTrace_append hprefix tailTrace_2306090
  have hstable : (prefixWord ++ tailWord_2306090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306090).length < 2 ^ (prefixWord ++ tailWord_2306090).sum := by decide
  have hdescent : baseEnd_2306090 < baseStart_2306090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306144 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_2306144 : Nat := 118140960795 + 2306144 * 2 ^ 59
def prefixEnd_2306144 : Nat := 4983230072969 + 3 ^ 40 * 2306144 * 2
def baseEnd_2306144 : Nat := 263146740107184541043165

theorem tailTrace_2306144 : CollatzResearch.WordTrace tailWord_2306144 prefixEnd_2306144 263146740107184541043165 := by
  unfold tailWord_2306144
  simp only [CollatzResearch.WordTrace]
  refine ⟨42055990878620810441834743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56074654504827747255779657 42055990878620810441834743)
  ·
    refine ⟨63083986317931215662752115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42055990878620810441834743 63083986317931215662752115)
    ·
      refine ⟨94625979476896823494128173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63083986317931215662752115 94625979476896823494128173)
      ·
        refine ⟨35484742303836308810298065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94625979476896823494128173 35484742303836308810298065)
        ·
          refine ⟨26613556727877231607723549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35484742303836308810298065 26613556727877231607723549)
          ·
            refine ⟨9980083772953961852896331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26613556727877231607723549 9980083772953961852896331)
            ·
              refine ⟨14970125659430942779344497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9980083772953961852896331 14970125659430942779344497)
              ·
                refine ⟨11227594244573207084508373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14970125659430942779344497 11227594244573207084508373)
                ·
                  refine ⟨263146740107184541043165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11227594244573207084508373 263146740107184541043165)
                  ·
                    rfl

theorem cell22_2306144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_2306144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306144 prefixEnd_2306144 := by exact prefixLift 2306144
  have htrace : WordTrace (prefixWord ++ tailWord_2306144) baseStart_2306144 baseEnd_2306144 := by
    simpa [prefixWord, tailWord_2306144, baseEnd_2306144] using wordTrace_append hprefix tailTrace_2306144
  have hstable : (prefixWord ++ tailWord_2306144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306144).length < 2 ^ (prefixWord ++ tailWord_2306144).sum := by decide
  have hdescent : baseEnd_2306144 < baseStart_2306144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_2306249 : Nat := 118140960795 + 2306249 * 2 ^ 59
def prefixEnd_2306249 : Nat := 4983230072969 + 3 ^ 40 * 2306249 * 2
def baseEnd_2306249 : Nat := 789476163967368349254173

theorem tailTrace_2306249 : CollatzResearch.WordTrace tailWord_2306249 prefixEnd_2306249 789476163967368349254173 := by
  unfold tailWord_2306249
  simp only [CollatzResearch.WordTrace]
  refine ⟨84115811421861223816241801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56077207614574149210827867 84115811421861223816241801)
  ·
    refine ⟨63086858566395917862181351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84115811421861223816241801 63086858566395917862181351)
    ·
      refine ⟨94630287849593876793272027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63086858566395917862181351 94630287849593876793272027)
      ·
        refine ⟨141945431774390815189908041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94630287849593876793272027 141945431774390815189908041)
        ·
          refine ⟨106459073830793111392431031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141945431774390815189908041 106459073830793111392431031)
          ·
            refine ⟨159688610746189667088646547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106459073830793111392431031 159688610746189667088646547)
            ·
              refine ⟨239532916119284500632969821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159688610746189667088646547 239532916119284500632969821)
              ·
                refine ⟨89824843544731687737363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239532916119284500632969821 89824843544731687737363683)
                ·
                  refine ⟨134737265317097531606045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89824843544731687737363683 134737265317097531606045525)
                  ·
                    refine ⟨789476163967368349254173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134737265317097531606045525 789476163967368349254173)
                    ·
                      rfl

theorem cell22_2306249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_2306249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306249 prefixEnd_2306249 := by exact prefixLift 2306249
  have htrace : WordTrace (prefixWord ++ tailWord_2306249) baseStart_2306249 baseEnd_2306249 := by
    simpa [prefixWord, tailWord_2306249, baseEnd_2306249] using wordTrace_append hprefix tailTrace_2306249
  have hstable : (prefixWord ++ tailWord_2306249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306249).length < 2 ^ (prefixWord ++ tailWord_2306249).sum := by decide
  have hdescent : baseEnd_2306249 < baseStart_2306249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306251 : List Nat := [1, 1, 1, 1, 3, 2, 7, 6]
def baseStart_2306251 : Nat := 118140960795 + 2306251 * 2 ^ 59
def prefixEnd_2306251 : Nat := 4983230072969 + 3 ^ 40 * 2306251 * 2
def baseEnd_2306251 : Nat := 87719649845360112300463

theorem tailTrace_2306251 : CollatzResearch.WordTrace tailWord_2306251 prefixEnd_2306251 87719649845360112300463 := by
  unfold tailWord_2306251
  simp only [CollatzResearch.WordTrace]
  refine ⟨84115884367853978157814607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56077256245235985438543071 84115884367853978157814607)
  ·
    refine ⟨126173826551780967236721911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84115884367853978157814607 126173826551780967236721911)
    ·
      refine ⟨189260739827671450855082867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126173826551780967236721911 189260739827671450855082867)
      ·
        refine ⟨283891109741507176282624301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189260739827671450855082867 283891109741507176282624301)
        ·
          refine ⟨106459166153065191105984113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283891109741507176282624301 106459166153065191105984113)
          ·
            refine ⟨79844374614798893329488085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106459166153065191105984113 79844374614798893329488085)
            ·
              refine ⟨1871352530034349062409877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79844374614798893329488085 1871352530034349062409877)
              ·
                refine ⟨87719649845360112300463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1871352530034349062409877 87719649845360112300463)
                ·
                  rfl

theorem cell22_2306251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 6].length) (baseStart_2306251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306251 prefixEnd_2306251 := by exact prefixLift 2306251
  have htrace : WordTrace (prefixWord ++ tailWord_2306251) baseStart_2306251 baseEnd_2306251 := by
    simpa [prefixWord, tailWord_2306251, baseEnd_2306251] using wordTrace_append hprefix tailTrace_2306251
  have hstable : (prefixWord ++ tailWord_2306251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306251).length < 2 ^ (prefixWord ++ tailWord_2306251).sum := by decide
  have hdescent : baseEnd_2306251 < baseStart_2306251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306283 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 3, 3]
def baseStart_2306283 : Nat := 118140960795 + 2306283 * 2 ^ 59
def prefixEnd_2306283 : Nat := 4983230072969 + 3 ^ 40 * 2306283 * 2
def baseEnd_2306283 : Nat := 789487802862203593904069

theorem tailTrace_2306283 : CollatzResearch.WordTrace tailWord_2306283 prefixEnd_2306283 789487802862203593904069 := by
  unfold tailWord_2306283
  simp only [CollatzResearch.WordTrace]
  refine ⟨84117051503738047622979503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56078034335825365081986335 84117051503738047622979503)
  ·
    refine ⟨126175577255607071434469255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84117051503738047622979503 126175577255607071434469255)
    ·
      refine ⟨189263365883410607151703883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126175577255607071434469255 189263365883410607151703883)
      ·
        refine ⟨283895048825115910727555825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189263365883410607151703883 283895048825115910727555825)
        ·
          refine ⟨212921286618836933045666869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283895048825115910727555825 212921286618836933045666869)
          ·
            refine ⟨19961370620515962473031269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212921286618836933045666869 19961370620515962473031269)
            ·
              refine ⟨3742756991346742963693363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19961370620515962473031269 3742756991346742963693363)
              ·
                refine ⟨5614135487020114445540045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742756991346742963693363 5614135487020114445540045)
                ·
                  refine ⟨2105300807632542917077517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5614135487020114445540045 2105300807632542917077517)
                  ·
                    refine ⟨789487802862203593904069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2105300807632542917077517 789487802862203593904069)
                    ·
                      rfl

theorem cell22_2306283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].length) (baseStart_2306283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306283 prefixEnd_2306283 := by exact prefixLift 2306283
  have htrace : WordTrace (prefixWord ++ tailWord_2306283) baseStart_2306283 baseEnd_2306283 := by
    simpa [prefixWord, tailWord_2306283, baseEnd_2306283] using wordTrace_append hprefix tailTrace_2306283
  have hstable : (prefixWord ++ tailWord_2306283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306283).length < 2 ^ (prefixWord ++ tailWord_2306283).sum := by decide
  have hdescent : baseEnd_2306283 < baseStart_2306283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306296 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_2306296 : Nat := 118140960795 + 2306296 * 2 ^ 59
def prefixEnd_2306296 : Nat := 4983230072969 + 3 ^ 40 * 2306296 * 2
def baseEnd_2306296 : Nat := 263164084342625297776343

theorem tailTrace_2306296 : CollatzResearch.WordTrace tailWord_2306296 prefixEnd_2306296 263164084342625297776343 := by
  unfold tailWord_2306296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42058762826345475421601371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56078350435127300562135161 42058762826345475421601371)
  ·
    refine ⟨63088144239518213132402057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42058762826345475421601371 63088144239518213132402057)
    ·
      refine ⟨47316108179638659849301543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63088144239518213132402057 47316108179638659849301543)
      ·
        refine ⟨70974162269457989773952315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47316108179638659849301543 70974162269457989773952315)
        ·
          refine ⟨106461243404186984660928473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70974162269457989773952315 106461243404186984660928473)
          ·
            refine ⟨79845932553140238495696355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106461243404186984660928473 79845932553140238495696355)
            ·
              refine ⟨119768898829710357743544533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79845932553140238495696355 119768898829710357743544533)
              ·
                refine ⟨2807083566321336509614325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119768898829710357743544533 2807083566321336509614325)
                ·
                  refine ⟨263164084342625297776343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807083566321336509614325 263164084342625297776343)
                  ·
                    rfl

theorem cell22_2306296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_2306296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306296 prefixEnd_2306296 := by exact prefixLift 2306296
  have htrace : WordTrace (prefixWord ++ tailWord_2306296) baseStart_2306296 baseEnd_2306296 := by
    simpa [prefixWord, tailWord_2306296, baseEnd_2306296] using wordTrace_append hprefix tailTrace_2306296
  have hstable : (prefixWord ++ tailWord_2306296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306296).length < 2 ^ (prefixWord ++ tailWord_2306296).sum := by decide
  have hdescent : baseEnd_2306296 < baseStart_2306296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306334 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2306334 : Nat := 118140960795 + 2306334 * 2 ^ 59
def prefixEnd_2306334 : Nat := 4983230072969 + 3 ^ 40 * 2306334 * 2
def baseEnd_2306334 : Nat := 789505261204456460878913

theorem tailTrace_2306334 : CollatzResearch.WordTrace tailWord_2306334 prefixEnd_2306334 789505261204456460878913 := by
  unfold tailWord_2306334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514863953319160416635757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56079274417702188888724037 10514863953319160416635757)
  ·
    refine ⟨3943073982494685156238409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10514863953319160416635757 3943073982494685156238409)
    ·
      refine ⟨2957305486871013867178807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3943073982494685156238409 2957305486871013867178807)
      ·
        refine ⟨4435958230306520800768211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957305486871013867178807 4435958230306520800768211)
        ·
          refine ⟨6653937345459781201152317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435958230306520800768211 6653937345459781201152317)
          ·
            refine ⟨2495226504547417950432119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6653937345459781201152317 2495226504547417950432119)
            ·
              refine ⟨3742839756821126925648179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495226504547417950432119 3742839756821126925648179)
              ·
                refine ⟨5614259635231690388472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742839756821126925648179 5614259635231690388472269)
                ·
                  refine ⟨2105347363211883895677101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5614259635231690388472269 2105347363211883895677101)
                  ·
                    refine ⟨789505261204456460878913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2105347363211883895677101 789505261204456460878913)
                    ·
                      rfl

theorem cell22_2306334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2306334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306334 prefixEnd_2306334 := by exact prefixLift 2306334
  have htrace : WordTrace (prefixWord ++ tailWord_2306334) baseStart_2306334 baseEnd_2306334 := by
    simpa [prefixWord, tailWord_2306334, baseEnd_2306334] using wordTrace_append hprefix tailTrace_2306334
  have hstable : (prefixWord ++ tailWord_2306334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306334).length < 2 ^ (prefixWord ++ tailWord_2306334).sum := by decide
  have hdescent : baseEnd_2306334 < baseStart_2306334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306371 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_2306371 : Nat := 118140960795 + 2306371 * 2 ^ 59
def prefixEnd_2306371 : Nat := 4983230072969 + 3 ^ 40 * 2306371 * 2
def baseEnd_2306371 : Nat := 789517927060600697703799

theorem tailTrace_2306371 : CollatzResearch.WordTrace tailWord_2306371 prefixEnd_2306371 789517927060600697703799 := by
  unfold tailWord_2306371
  simp only [CollatzResearch.WordTrace]
  refine ⟨84120261127419238652182967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56080174084946159101455311 84120261127419238652182967)
  ·
    refine ⟨126180391691128857978274451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84120261127419238652182967 126180391691128857978274451)
    ·
      refine ⟨189270587536693286967411677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126180391691128857978274451 189270587536693286967411677)
      ·
        refine ⟨70976470326259982612779379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189270587536693286967411677 70976470326259982612779379)
        ·
          refine ⟨106464705489389973919169069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70976470326259982612779379 106464705489389973919169069)
          ·
            refine ⟨39924264558521240219688401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106464705489389973919169069 39924264558521240219688401)
            ·
              refine ⟨29943198418890930164766301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39924264558521240219688401 29943198418890930164766301)
              ·
                refine ⟨11228699407084098811787363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29943198418890930164766301 11228699407084098811787363)
                ·
                  refine ⟨16843049110626148217681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11228699407084098811787363 16843049110626148217681045)
                  ·
                    refine ⟨789517927060600697703799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16843049110626148217681045 789517927060600697703799)
                    ·
                      rfl

theorem cell22_2306371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_2306371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306371 prefixEnd_2306371 := by exact prefixLift 2306371
  have htrace : WordTrace (prefixWord ++ tailWord_2306371) baseStart_2306371 baseEnd_2306371 := by
    simpa [prefixWord, tailWord_2306371, baseEnd_2306371] using wordTrace_append hprefix tailTrace_2306371
  have hstable : (prefixWord ++ tailWord_2306371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306371).length < 2 ^ (prefixWord ++ tailWord_2306371).sum := by decide
  have hdescent : baseEnd_2306371 < baseStart_2306371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306401 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2306401 : Nat := 118140960795 + 2306401 * 2 ^ 59
def prefixEnd_2306401 : Nat := 4983230072969 + 3 ^ 40 * 2306401 * 2
def baseEnd_2306401 : Nat := 789528196673690619453707

theorem tailTrace_2306401 : CollatzResearch.WordTrace tailWord_2306401 prefixEnd_2306401 789528196673690619453707 := by
  unfold tailWord_2306401
  simp only [CollatzResearch.WordTrace]
  refine ⟨84121355317310553775775057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56080903544873702517183371 84121355317310553775775057)
  ·
    refine ⟨63091016487982915331831293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84121355317310553775775057 63091016487982915331831293)
    ·
      refine ⟨23659131182993593249436735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63091016487982915331831293 23659131182993593249436735)
      ·
        refine ⟨35488696774490389874155103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23659131182993593249436735 35488696774490389874155103)
        ·
          refine ⟨53233045161735584811232655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35488696774490389874155103 53233045161735584811232655)
          ·
            refine ⟨79849567742603377216848983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53233045161735584811232655 79849567742603377216848983)
            ·
              refine ⟨119774351613905065825273475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79849567742603377216848983 119774351613905065825273475)
              ·
                refine ⟨179661527420857598737910213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119774351613905065825273475 179661527420857598737910213)
                ·
                  refine ⟨33686536391410799763358165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179661527420857598737910213 33686536391410799763358165)
                  ·
                    refine ⟨789528196673690619453707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33686536391410799763358165 789528196673690619453707)
                    ·
                      rfl

theorem cell22_2306401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2306401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306401 prefixEnd_2306401 := by exact prefixLift 2306401
  have htrace : WordTrace (prefixWord ++ tailWord_2306401) baseStart_2306401 baseEnd_2306401 := by
    simpa [prefixWord, tailWord_2306401, baseEnd_2306401] using wordTrace_append hprefix tailTrace_2306401
  have hstable : (prefixWord ++ tailWord_2306401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306401).length < 2 ^ (prefixWord ++ tailWord_2306401).sum := by decide
  have hdescent : baseEnd_2306401 < baseStart_2306401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306422 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2306422 : Nat := 118140960795 + 2306422 * 2 ^ 59
def prefixEnd_2306422 : Nat := 4983230072969 + 3 ^ 40 * 2306422 * 2
def baseEnd_2306422 : Nat := 789535385402853564678643

theorem tailTrace_2306422 : CollatzResearch.WordTrace tailWord_2306422 prefixEnd_2306422 789535385402853564678643 := by
  unfold tailWord_2306422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257632578139654647643095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56081414166822982908193013 5257632578139654647643095)
  ·
    refine ⟨7886448867209481971464643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5257632578139654647643095 7886448867209481971464643)
    ·
      refine ⟨11829673300814222957196965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886448867209481971464643 11829673300814222957196965)
      ·
        refine ⟨2218063743902666804474431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11829673300814222957196965 2218063743902666804474431)
        ·
          refine ⟨3327095615854000206711647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218063743902666804474431 3327095615854000206711647)
          ·
            refine ⟨4990643423781000310067471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327095615854000206711647 4990643423781000310067471)
            ·
              refine ⟨7485965135671500465101207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990643423781000310067471 7485965135671500465101207)
              ·
                refine ⟨11228947703507250697651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485965135671500465101207 11228947703507250697651811)
                ·
                  refine ⟨16843421555260876046477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11228947703507250697651811 16843421555260876046477717)
                  ·
                    refine ⟨789535385402853564678643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16843421555260876046477717 789535385402853564678643)
                    ·
                      rfl

theorem cell22_2306422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2306422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306422 prefixEnd_2306422 := by exact prefixLift 2306422
  have htrace : WordTrace (prefixWord ++ tailWord_2306422) baseStart_2306422 baseEnd_2306422 := by
    simpa [prefixWord, tailWord_2306422, baseEnd_2306422] using wordTrace_append hprefix tailTrace_2306422
  have hstable : (prefixWord ++ tailWord_2306422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306422).length < 2 ^ (prefixWord ++ tailWord_2306422).sum := by decide
  have hdescent : baseEnd_2306422 < baseStart_2306422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306431 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 9]
def baseStart_2306431 : Nat := 118140960795 + 2306431 * 2 ^ 59
def prefixEnd_2306431 : Nat := 4983230072969 + 3 ^ 40 * 2306431 * 2
def baseEnd_2306431 : Nat := 263179488762260180401205

theorem tailTrace_2306431 : CollatzResearch.WordTrace tailWord_2306431 prefixEnd_2306431 263179488762260180401205 := by
  unfold tailWord_2306431
  simp only [CollatzResearch.WordTrace]
  refine ⟨84122449507201868899367147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56081633004801245932911431 84122449507201868899367147)
  ·
    refine ⟨126183674260802803349050721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84122449507201868899367147 126183674260802803349050721)
    ·
      refine ⟨94637755695602102511788041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126183674260802803349050721 94637755695602102511788041)
      ·
        refine ⟨70978316771701576883841031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94637755695602102511788041 70978316771701576883841031)
        ·
          refine ⟨106467475157552365325761547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70978316771701576883841031 106467475157552365325761547)
          ·
            refine ⟨159701212736328547988642321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106467475157552365325761547 159701212736328547988642321)
            ·
              refine ⟨119775909552246410991481741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159701212736328547988642321 119775909552246410991481741)
              ·
                refine ⟨44915966082092404121805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119775909552246410991481741 44915966082092404121805653)
                ·
                  refine ⟨263179488762260180401205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44915966082092404121805653 263179488762260180401205)
                  ·
                    rfl

theorem cell22_2306431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_2306431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306431 prefixEnd_2306431 := by exact prefixLift 2306431
  have htrace : WordTrace (prefixWord ++ tailWord_2306431) baseStart_2306431 baseEnd_2306431 := by
    simpa [prefixWord, tailWord_2306431, baseEnd_2306431] using wordTrace_append hprefix tailTrace_2306431
  have hstable : (prefixWord ++ tailWord_2306431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306431).length < 2 ^ (prefixWord ++ tailWord_2306431).sum := by decide
  have hdescent : baseEnd_2306431 < baseStart_2306431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306463 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_2306463 : Nat := 118140960795 + 2306463 * 2 ^ 59
def prefixEnd_2306463 : Nat := 4983230072969 + 3 ^ 40 * 2306463 * 2
def baseEnd_2306463 : Nat := 789549420540743124403517

theorem tailTrace_2306463 : CollatzResearch.WordTrace tailWord_2306463 prefixEnd_2306463 789549420540743124403517 := by
  unfold tailWord_2306463
  simp only [CollatzResearch.WordTrace]
  refine ⟨84123616643085938364532043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56082411095390625576354695 84123616643085938364532043)
  ·
    refine ⟨126185424964628907546798065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84123616643085938364532043 126185424964628907546798065)
    ·
      refine ⟨94639068723471680660098549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126185424964628907546798065 94639068723471680660098549)
      ·
        refine ⟨8872412692825470061884239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94639068723471680660098549 8872412692825470061884239)
        ·
          refine ⟨13308619039238205092826359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872412692825470061884239 13308619039238205092826359)
          ·
            refine ⟨19962928558857307639239539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13308619039238205092826359 19962928558857307639239539)
            ·
              refine ⟨29944392838285961458859309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19962928558857307639239539 29944392838285961458859309)
              ·
                refine ⟨11229147314357235547072241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29944392838285961458859309 11229147314357235547072241)
                ·
                  refine ⟨8421860485767926660304181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11229147314357235547072241 8421860485767926660304181)
                  ·
                    refine ⟨789549420540743124403517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8421860485767926660304181 789549420540743124403517)
                    ·
                      rfl

theorem cell22_2306463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_2306463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306463 prefixEnd_2306463 := by exact prefixLift 2306463
  have htrace : WordTrace (prefixWord ++ tailWord_2306463) baseStart_2306463 baseEnd_2306463 := by
    simpa [prefixWord, tailWord_2306463, baseEnd_2306463] using wordTrace_append hprefix tailTrace_2306463
  have hstable : (prefixWord ++ tailWord_2306463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306463).length < 2 ^ (prefixWord ++ tailWord_2306463).sum := by decide
  have hdescent : baseEnd_2306463 < baseStart_2306463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306525 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2306525 : Nat := 118140960795 + 2306525 * 2 ^ 59
def prefixEnd_2306525 : Nat := 4983230072969 + 3 ^ 40 * 2306525 * 2
def baseEnd_2306525 : Nat := 789570644407795629353327

theorem tailTrace_2306525 : CollatzResearch.WordTrace tailWord_2306525 prefixEnd_2306525 789570644407795629353327 := by
  unfold tailWord_2306525
  simp only [CollatzResearch.WordTrace]
  refine ⟨84125877968861322953289029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56083918645907548635526019 84125877968861322953289029)
  ·
    refine ⟨15773602119161498053741693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84125877968861322953289029 15773602119161498053741693)
    ·
      refine ⟨5915100794685561770153135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15773602119161498053741693 5915100794685561770153135)
      ·
        refine ⟨8872651192028342655229703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915100794685561770153135 8872651192028342655229703)
        ·
          refine ⟨13308976788042513982844555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872651192028342655229703 13308976788042513982844555)
          ·
            refine ⟨19963465182063770974266833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13308976788042513982844555 19963465182063770974266833)
            ·
              refine ⟨14972598886547828230700125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19963465182063770974266833 14972598886547828230700125)
              ·
                refine ⟨5614724582455435586512547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14972598886547828230700125 5614724582455435586512547)
                ·
                  refine ⟨8422086873683153379768821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614724582455435586512547 8422086873683153379768821)
                  ·
                    refine ⟨789570644407795629353327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8422086873683153379768821 789570644407795629353327)
                    ·
                      rfl

theorem cell22_2306525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2306525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306525 prefixEnd_2306525 := by exact prefixLift 2306525
  have htrace : WordTrace (prefixWord ++ tailWord_2306525) baseStart_2306525 baseEnd_2306525 := by
    simpa [prefixWord, tailWord_2306525, baseEnd_2306525] using wordTrace_append hprefix tailTrace_2306525
  have hstable : (prefixWord ++ tailWord_2306525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306525).length < 2 ^ (prefixWord ++ tailWord_2306525).sum := by decide
  have hdescent : baseEnd_2306525 < baseStart_2306525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306540 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_2306540 : Nat := 118140960795 + 2306540 * 2 ^ 59
def prefixEnd_2306540 : Nat := 4983230072969 + 3 ^ 40 * 2306540 * 2
def baseEnd_2306540 : Nat := 789575779214340590228281

theorem tailTrace_2306540 : CollatzResearch.WordTrace tailWord_2306540 prefixEnd_2306540 789575779214340590228281 := by
  unfold tailWord_2306540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42063212531903490257542537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56084283375871320343390049 42063212531903490257542537)
  ·
    refine ⟨31547409398927617693156903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42063212531903490257542537 31547409398927617693156903)
    ·
      refine ⟨47321114098391426539735355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31547409398927617693156903 47321114098391426539735355)
      ·
        refine ⟨70981671147587139809603033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47321114098391426539735355 70981671147587139809603033)
        ·
          refine ⟨53236253360690354857202275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70981671147587139809603033 53236253360690354857202275)
          ·
            refine ⟨79854380041035532285803413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53236253360690354857202275 79854380041035532285803413)
            ·
              refine ⟨3743174064423540575897035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79854380041035532285803413 3743174064423540575897035)
              ·
                refine ⟨5614761096635310863845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743174064423540575897035 5614761096635310863845553)
                ·
                  refine ⟨4211070822476483147884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5614761096635310863845553 4211070822476483147884165)
                  ·
                    refine ⟨789575779214340590228281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211070822476483147884165 789575779214340590228281)
                    ·
                      rfl

theorem cell22_2306540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_2306540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306540 prefixEnd_2306540 := by exact prefixLift 2306540
  have htrace : WordTrace (prefixWord ++ tailWord_2306540) baseStart_2306540 baseEnd_2306540 := by
    simpa [prefixWord, tailWord_2306540, baseEnd_2306540] using wordTrace_append hprefix tailTrace_2306540
  have hstable : (prefixWord ++ tailWord_2306540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306540).length < 2 ^ (prefixWord ++ tailWord_2306540).sum := by decide
  have hdescent : baseEnd_2306540 < baseStart_2306540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306645 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 6]
def baseStart_2306645 : Nat := 118140960795 + 2306645 * 2 ^ 59
def prefixEnd_2306645 : Nat := 4983230072969 + 3 ^ 40 * 2306645 * 2
def baseEnd_2306645 : Nat := 263203907620051772117653

theorem tailTrace_2306645 : CollatzResearch.WordTrace tailWord_2306645 prefixEnd_2306645 263203907620051772117653 := by
  unfold tailWord_2306645
  simp only [CollatzResearch.WordTrace]
  refine ⟨84130254728426583447657389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56086836485617722298438259 84130254728426583447657389)
  ·
    refine ⟨31548845523159968792871521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84130254728426583447657389 31548845523159968792871521)
    ·
      refine ⟨23661634142369976594653641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31548845523159968792871521 23661634142369976594653641)
      ·
        refine ⟨17746225606777482445990231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23661634142369976594653641 17746225606777482445990231)
        ·
          refine ⟨26619338410166223668985347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17746225606777482445990231 26619338410166223668985347)
          ·
            refine ⟨39929007615249335503478021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26619338410166223668985347 39929007615249335503478021)
            ·
              refine ⟨7486688927859250406902129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39929007615249335503478021 7486688927859250406902129)
              ·
                refine ⟨5615016695894437805176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7486688927859250406902129 5615016695894437805176597)
                ·
                  refine ⟨263203907620051772117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5615016695894437805176597 263203907620051772117653)
                  ·
                    rfl

theorem cell22_2306645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_2306645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306645 prefixEnd_2306645 := by exact prefixLift 2306645
  have htrace : WordTrace (prefixWord ++ tailWord_2306645) baseStart_2306645 baseEnd_2306645 := by
    simpa [prefixWord, tailWord_2306645, baseEnd_2306645] using wordTrace_append hprefix tailTrace_2306645
  have hstable : (prefixWord ++ tailWord_2306645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306645).length < 2 ^ (prefixWord ++ tailWord_2306645).sum := by decide
  have hdescent : baseEnd_2306645 < baseStart_2306645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306647 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2306647 : Nat := 118140960795 + 2306647 * 2 ^ 59
def prefixEnd_2306647 : Nat := 4983230072969 + 3 ^ 40 * 2306647 * 2
def baseEnd_2306647 : Nat := 789612407501027977802953

theorem tailTrace_2306647 : CollatzResearch.WordTrace tailWord_2306647 prefixEnd_2306647 789612407501027977802953 := by
  unfold tailWord_2306647
  simp only [CollatzResearch.WordTrace]
  refine ⟨84130327674419337789230195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56086885116279558526153463 84130327674419337789230195)
  ·
    refine ⟨126195491511629006683845293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84130327674419337789230195 126195491511629006683845293)
    ·
      refine ⟨47323309316860877506441985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126195491511629006683845293 47323309316860877506441985)
      ·
        refine ⟨35492481987645658129831489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47323309316860877506441985 35492481987645658129831489)
        ·
          refine ⟨26619361490734243597373617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35492481987645658129831489 26619361490734243597373617)
          ·
            refine ⟨19964521118050682698030213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26619361490734243597373617 19964521118050682698030213)
            ·
              refine ⟨3743347709634503005880665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19964521118050682698030213 3743347709634503005880665)
              ·
                refine ⟨2807510782225877254410499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743347709634503005880665 2807510782225877254410499)
                ·
                  refine ⟨4211266173338815881615749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807510782225877254410499 4211266173338815881615749)
                  ·
                    refine ⟨789612407501027977802953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211266173338815881615749 789612407501027977802953)
                    ·
                      rfl

theorem cell22_2306647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2306647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306647 prefixEnd_2306647 := by exact prefixLift 2306647
  have htrace : WordTrace (prefixWord ++ tailWord_2306647) baseStart_2306647 baseEnd_2306647 := by
    simpa [prefixWord, tailWord_2306647, baseEnd_2306647] using wordTrace_append hprefix tailTrace_2306647
  have hstable : (prefixWord ++ tailWord_2306647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306647).length < 2 ^ (prefixWord ++ tailWord_2306647).sum := by decide
  have hdescent : baseEnd_2306647 < baseStart_2306647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306660 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2306660 : Nat := 118140960795 + 2306660 * 2 ^ 59
def prefixEnd_2306660 : Nat := 4983230072969 + 3 ^ 40 * 2306660 * 2
def baseEnd_2306660 : Nat := 789616857666700277227913

theorem tailTrace_2306660 : CollatzResearch.WordTrace tailWord_2306660 prefixEnd_2306660 789616857666700277227913 := by
  unfold tailWord_2306660
  simp only [CollatzResearch.WordTrace]
  refine ⟨42065400911686120504726717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56087201215581494006302289 42065400911686120504726717)
  ·
    refine ⟨15774525341882295189272519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42065400911686120504726717 15774525341882295189272519)
    ·
      refine ⟨23661788012823442783908779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15774525341882295189272519 23661788012823442783908779)
      ·
        refine ⟨35492682019235164175863169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23661788012823442783908779 35492682019235164175863169)
        ·
          refine ⟨26619511514426373131897377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35492682019235164175863169 26619511514426373131897377)
          ·
            refine ⟨19964633635819779848923033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26619511514426373131897377 19964633635819779848923033)
            ·
              refine ⟨14973475226864834886692275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19964633635819779848923033 14973475226864834886692275)
              ·
                refine ⟨22460212840297252330038413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14973475226864834886692275 22460212840297252330038413)
                ·
                  refine ⟨8422579815111469623764405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22460212840297252330038413 8422579815111469623764405)
                  ·
                    refine ⟨789616857666700277227913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8422579815111469623764405 789616857666700277227913)
                    ·
                      rfl

theorem cell22_2306660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2306660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306660 prefixEnd_2306660 := by exact prefixLift 2306660
  have htrace : WordTrace (prefixWord ++ tailWord_2306660) baseStart_2306660 baseEnd_2306660 := by
    simpa [prefixWord, tailWord_2306660, baseEnd_2306660] using wordTrace_append hprefix tailTrace_2306660
  have hstable : (prefixWord ++ tailWord_2306660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306660).length < 2 ^ (prefixWord ++ tailWord_2306660).sum := by decide
  have hdescent : baseEnd_2306660 < baseStart_2306660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306730 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_2306730 : Nat := 118140960795 + 2306730 * 2 ^ 59
def prefixEnd_2306730 : Nat := 4983230072969 + 3 ^ 40 * 2306730 * 2
def baseEnd_2306730 : Nat := 263213606699081142659233

theorem tailTrace_2306730 : CollatzResearch.WordTrace tailWord_2306730 prefixEnd_2306730 263213606699081142659233 := by
  unfold tailWord_2306730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21033338733279660741125411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56088903288745761976334429 21033338733279660741125411)
  ·
    refine ⟨31550008099919491111688117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21033338733279660741125411 31550008099919491111688117)
    ·
      refine ⟨2957813259367452291720761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31550008099919491111688117 2957813259367452291720761)
      ·
        refine ⟨2218359944525589218790571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2957813259367452291720761 2218359944525589218790571)
        ·
          refine ⟨3327539916788383828185857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218359944525589218790571 3327539916788383828185857)
          ·
            refine ⟨2495654937591287871139393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3327539916788383828185857 2495654937591287871139393)
            ·
              refine ⟨1871741203193465903354545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495654937591287871139393 1871741203193465903354545)
              ·
                refine ⟨1403805902395099427515909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871741203193465903354545 1403805902395099427515909)
                ·
                  refine ⟨263213606699081142659233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403805902395099427515909 263213606699081142659233)
                  ·
                    rfl

theorem cell22_2306730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_2306730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306730 prefixEnd_2306730 := by exact prefixLift 2306730
  have htrace : WordTrace (prefixWord ++ tailWord_2306730) baseStart_2306730 baseEnd_2306730 := by
    simpa [prefixWord, tailWord_2306730, baseEnd_2306730] using wordTrace_append hprefix tailTrace_2306730
  have hstable : (prefixWord ++ tailWord_2306730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306730).length < 2 ^ (prefixWord ++ tailWord_2306730).sum := by decide
  have hdescent : baseEnd_2306730 < baseStart_2306730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306752 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_2306752 : Nat := 118140960795 + 2306752 * 2 ^ 59
def prefixEnd_2306752 : Nat := 4983230072969 + 3 ^ 40 * 2306752 * 2
def baseEnd_2306752 : Nat := 263216117048947567975877

theorem tailTrace_2306752 : CollatzResearch.WordTrace tailWord_2306752 prefixEnd_2306752 263216117048947567975877 := by
  unfold tailWord_2306752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067078669519470360901255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56089438226025960481201673 42067078669519470360901255)
  ·
    refine ⟨63100618004279205541351883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42067078669519470360901255 63100618004279205541351883)
    ·
      refine ⟨94650927006418808312027825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63100618004279205541351883 94650927006418808312027825)
      ·
        refine ⟨70988195254814106234020869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94650927006418808312027825 70988195254814106234020869)
        ·
          refine ⟨13310286610277644918878913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70988195254814106234020869 13310286610277644918878913)
          ·
            refine ⟨9982714957708233689159185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13310286610277644918878913 9982714957708233689159185)
            ·
              refine ⟨7487036218281175266869389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9982714957708233689159185 7487036218281175266869389)
              ·
                refine ⟨2807638581855440725076021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487036218281175266869389 2807638581855440725076021)
                ·
                  refine ⟨263216117048947567975877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807638581855440725076021 263216117048947567975877)
                  ·
                    rfl

theorem cell22_2306752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_2306752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306752 prefixEnd_2306752 := by exact prefixLift 2306752
  have htrace : WordTrace (prefixWord ++ tailWord_2306752) baseStart_2306752 baseEnd_2306752 := by
    simpa [prefixWord, tailWord_2306752, baseEnd_2306752] using wordTrace_append hprefix tailTrace_2306752
  have hstable : (prefixWord ++ tailWord_2306752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306752).length < 2 ^ (prefixWord ++ tailWord_2306752).sum := by decide
  have hdescent : baseEnd_2306752 < baseStart_2306752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306758 : List Nat := [6, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2306758 : Nat := 118140960795 + 2306758 * 2 ^ 59
def prefixEnd_2306758 : Nat := 4983230072969 + 3 ^ 40 * 2306758 * 2
def baseEnd_2306758 : Nat := 87738933896606743141957

theorem tailTrace_2306758 : CollatzResearch.WordTrace tailWord_2306758 prefixEnd_2306758 87738933896606743141957 := by
  unfold tailWord_2306758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629199255531787617078779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56089584118011469164347285 2629199255531787617078779)
  ·
    refine ⟨3943798883297681425618169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629199255531787617078779 3943798883297681425618169)
    ·
      refine ⟨2957849162473261069213627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3943798883297681425618169 2957849162473261069213627)
      ·
        refine ⟨4436773743709891603820441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957849162473261069213627 4436773743709891603820441)
        ·
          refine ⟨3327580307782418702865331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436773743709891603820441 3327580307782418702865331)
          ·
            refine ⟨4991370461673628054297997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327580307782418702865331 4991370461673628054297997)
            ·
              refine ⟨1871763923127610520361749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4991370461673628054297997 1871763923127610520361749)
              ·
                refine ⟨87738933896606743141957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1871763923127610520361749 87738933896606743141957)
                ·
                  rfl

theorem cell22_2306758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2306758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306758 prefixEnd_2306758 := by exact prefixLift 2306758
  have htrace : WordTrace (prefixWord ++ tailWord_2306758) baseStart_2306758 baseEnd_2306758 := by
    simpa [prefixWord, tailWord_2306758, baseEnd_2306758] using wordTrace_append hprefix tailTrace_2306758
  have hstable : (prefixWord ++ tailWord_2306758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306758).length < 2 ^ (prefixWord ++ tailWord_2306758).sum := by decide
  have hdescent : baseEnd_2306758 < baseStart_2306758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306814 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2306814 : Nat := 118140960795 + 2306814 * 2 ^ 59
def prefixEnd_2306814 : Nat := 4983230072969 + 3 ^ 40 * 2306814 * 2
def baseEnd_2306814 : Nat := 263223191671298402959147

theorem tailTrace_2306814 : CollatzResearch.WordTrace tailWord_2306814 prefixEnd_2306814 263223191671298402959147 := by
  unfold tailWord_2306814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517052333101790663819937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56090945776542883540372997 10517052333101790663819937)
  ·
    refine ⟨7887789249826342997864953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10517052333101790663819937 7887789249826342997864953)
    ·
      refine ⟨5915841937369757248398715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7887789249826342997864953 5915841937369757248398715)
      ·
        refine ⟨8873762906054635872598073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915841937369757248398715 8873762906054635872598073)
        ·
          refine ⟨6655322179540976904448555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8873762906054635872598073 6655322179540976904448555)
          ·
            refine ⟨9982983269311465356672833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655322179540976904448555 9982983269311465356672833)
            ·
              refine ⟨7487237451983599017504625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9982983269311465356672833 7487237451983599017504625)
              ·
                refine ⟨5615428088987699263128469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487237451983599017504625 5615428088987699263128469)
                ·
                  refine ⟨263223191671298402959147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5615428088987699263128469 263223191671298402959147)
                  ·
                    rfl

theorem cell22_2306814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2306814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306814 prefixEnd_2306814 := by exact prefixLift 2306814
  have htrace : WordTrace (prefixWord ++ tailWord_2306814) baseStart_2306814 baseEnd_2306814 := by
    simpa [prefixWord, tailWord_2306814, baseEnd_2306814] using wordTrace_append hprefix tailTrace_2306814
  have hstable : (prefixWord ++ tailWord_2306814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306814).length < 2 ^ (prefixWord ++ tailWord_2306814).sum := by decide
  have hdescent : baseEnd_2306814 < baseStart_2306814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306827 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_2306827 : Nat := 118140960795 + 2306827 * 2 ^ 59
def prefixEnd_2306827 : Nat := 4983230072969 + 3 ^ 40 * 2306827 * 2
def baseEnd_2306827 : Nat := 789674025179567508302401

theorem tailTrace_2306827 : CollatzResearch.WordTrace tailWord_2306827 prefixEnd_2306827 789674025179567508302401 := by
  unfold tailWord_2306827
  simp only [CollatzResearch.WordTrace]
  refine ⟨84136892813767228530782735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56091261875844819020521823 84136892813767228530782735)
  ·
    refine ⟨126205339220650842796174103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84136892813767228530782735 126205339220650842796174103)
    ·
      refine ⟨189308008830976264194261155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126205339220650842796174103 189308008830976264194261155)
      ·
        refine ⟨283962013246464396291391733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189308008830976264194261155 283962013246464396291391733)
        ·
          refine ⟨26621438741856037152317975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283962013246464396291391733 26621438741856037152317975)
          ·
            refine ⟨39932158112784055728476963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26621438741856037152317975 39932158112784055728476963)
            ·
              refine ⟨59898237169176083592715445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39932158112784055728476963 59898237169176083592715445)
              ·
                refine ⟨5615459734610257836817073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59898237169176083592715445 5615459734610257836817073)
                ·
                  refine ⟨4211594800957693377612805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615459734610257836817073 4211594800957693377612805)
                  ·
                    refine ⟨789674025179567508302401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211594800957693377612805 789674025179567508302401)
                    ·
                      rfl

theorem cell22_2306827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_2306827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306827 prefixEnd_2306827 := by exact prefixLift 2306827
  have htrace : WordTrace (prefixWord ++ tailWord_2306827) baseStart_2306827 baseEnd_2306827 := by
    simpa [prefixWord, tailWord_2306827, baseEnd_2306827] using wordTrace_append hprefix tailTrace_2306827
  have hstable : (prefixWord ++ tailWord_2306827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306827).length < 2 ^ (prefixWord ++ tailWord_2306827).sum := by decide
  have hdescent : baseEnd_2306827 < baseStart_2306827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306844 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2306844 : Nat := 118140960795 + 2306844 * 2 ^ 59
def prefixEnd_2306844 : Nat := 4983230072969 + 3 ^ 40 * 2306844 * 2
def baseEnd_2306844 : Nat := 789679844626985130627349

theorem tailTrace_2306844 : CollatzResearch.WordTrace tailWord_2306844 prefixEnd_2306844 789679844626985130627349 := by
  unfold tailWord_2306844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42068756427352820217075793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56091675236470426956101057 42068756427352820217075793)
  ·
    refine ⟨31551567320514615162806845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42068756427352820217075793 31551567320514615162806845)
    ·
      refine ⟨11831837745192980686052567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31551567320514615162806845 11831837745192980686052567)
      ·
        refine ⟨17747756617789471029078851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11831837745192980686052567 17747756617789471029078851)
        ·
          refine ⟨26621634926684206543618277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17747756617789471029078851 26621634926684206543618277)
          ·
            refine ⟨4991556548753288726928427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26621634926684206543618277 4991556548753288726928427)
            ·
              refine ⟨7487334823129933090392641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991556548753288726928427 7487334823129933090392641)
              ·
                refine ⟨5615501117347449817794481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487334823129933090392641 5615501117347449817794481)
                ·
                  refine ⟨4211625838010587363345861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615501117347449817794481 4211625838010587363345861)
                  ·
                    refine ⟨789679844626985130627349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211625838010587363345861 789679844626985130627349)
                    ·
                      rfl

theorem cell22_2306844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2306844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306844 prefixEnd_2306844 := by exact prefixLift 2306844
  have htrace : WordTrace (prefixWord ++ tailWord_2306844) baseStart_2306844 baseEnd_2306844 := by
    simpa [prefixWord, tailWord_2306844, baseEnd_2306844] using wordTrace_append hprefix tailTrace_2306844
  have hstable : (prefixWord ++ tailWord_2306844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306844).length < 2 ^ (prefixWord ++ tailWord_2306844).sum := by decide
  have hdescent : baseEnd_2306844 < baseStart_2306844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306919 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2306919 : Nat := 118140960795 + 2306919 * 2 ^ 59
def prefixEnd_2306919 : Nat := 4983230072969 + 3 ^ 40 * 2306919 * 2
def baseEnd_2306919 : Nat := 789705518659709935002119

theorem tailTrace_2306919 : CollatzResearch.WordTrace tailWord_2306919 prefixEnd_2306919 789705518659709935002119 := by
  unfold tailWord_2306919
  simp only [CollatzResearch.WordTrace]
  refine ⟨84140248329433928243131811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56093498886289285495421207 84140248329433928243131811)
  ·
    refine ⟨126210372494150892364697717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84140248329433928243131811 126210372494150892364697717)
    ·
      refine ⟨11832222421326646159190411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126210372494150892364697717 11832222421326646159190411)
      ·
        refine ⟨17748333631989969238785617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11832222421326646159190411 17748333631989969238785617)
        ·
          refine ⟨13311250223992476929089213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17748333631989969238785617 13311250223992476929089213)
          ·
            refine ⟨4991718833997178848408455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13311250223992476929089213 4991718833997178848408455)
            ·
              refine ⟨7487578250995768272612683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991718833997178848408455 7487578250995768272612683)
              ·
                refine ⟨11231367376493652408919025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487578250995768272612683 11231367376493652408919025)
                ·
                  refine ⟨8423525532370239306689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11231367376493652408919025 8423525532370239306689269)
                  ·
                    refine ⟨789705518659709935002119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8423525532370239306689269 789705518659709935002119)
                    ·
                      rfl

theorem cell22_2306919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2306919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306919 prefixEnd_2306919 := by exact prefixLift 2306919
  have htrace : WordTrace (prefixWord ++ tailWord_2306919) baseStart_2306919 baseEnd_2306919 := by
    simpa [prefixWord, tailWord_2306919, baseEnd_2306919] using wordTrace_append hprefix tailTrace_2306919
  have hstable : (prefixWord ++ tailWord_2306919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306919).length < 2 ^ (prefixWord ++ tailWord_2306919).sum := by decide
  have hdescent : baseEnd_2306919 < baseStart_2306919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306942 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2306942 : Nat := 118140960795 + 2306942 * 2 ^ 59
def prefixEnd_2306942 : Nat := 4983230072969 + 3 ^ 40 * 2306942 * 2
def baseEnd_2306942 : Nat := 789713392029745541677049

theorem tailTrace_2306942 : CollatzResearch.WordTrace tailWord_2306942 prefixEnd_2306942 789713392029745541677049 := by
  unfold tailWord_2306942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517635901043825396402385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56094058138900402114146053 10517635901043825396402385)
  ·
    refine ⟨7888226925782869047301789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10517635901043825396402385 7888226925782869047301789)
    ·
      refine ⟨2958085097168575892738171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7888226925782869047301789 2958085097168575892738171)
      ·
        refine ⟨4437127645752863839107257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958085097168575892738171 4437127645752863839107257)
        ·
          refine ⟨3327845734314647879330443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437127645752863839107257 3327845734314647879330443)
          ·
            refine ⟨4991768601471971818995665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327845734314647879330443 4991768601471971818995665)
            ·
              refine ⟨3743826451103978864246749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991768601471971818995665 3743826451103978864246749)
              ·
                refine ⟨1403934919163992074092531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743826451103978864246749 1403934919163992074092531)
                ·
                  refine ⟨2105902378745988111138797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403934919163992074092531 2105902378745988111138797)
                  ·
                    refine ⟨789713392029745541677049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2105902378745988111138797 789713392029745541677049)
                    ·
                      rfl

theorem cell22_2306942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2306942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306942 prefixEnd_2306942 := by exact prefixLift 2306942
  have htrace : WordTrace (prefixWord ++ tailWord_2306942) baseStart_2306942 baseEnd_2306942 := by
    simpa [prefixWord, tailWord_2306942, baseEnd_2306942] using wordTrace_append hprefix tailTrace_2306942
  have hstable : (prefixWord ++ tailWord_2306942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306942).length < 2 ^ (prefixWord ++ tailWord_2306942).sum := by decide
  have hdescent : baseEnd_2306942 < baseStart_2306942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2306951 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2306951 : Nat := 118140960795 + 2306951 * 2 ^ 59
def prefixEnd_2306951 : Nat := 4983230072969 + 3 ^ 40 * 2306951 * 2
def baseEnd_2306951 : Nat := 789716472913672518202021

theorem tailTrace_2306951 : CollatzResearch.WordTrace tailWord_2306951 prefixEnd_2306951 789716472913672518202021 := by
  unfold tailWord_2306951
  simp only [CollatzResearch.WordTrace]
  refine ⟨84141415465317997708296707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56094276976878665138864471 84141415465317997708296707)
  ·
    refine ⟨126212123197976996562445061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84141415465317997708296707 126212123197976996562445061)
    ·
      refine ⟨23664773099620686855458449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126212123197976996562445061 23664773099620686855458449)
      ·
        refine ⟨17748579824715515141593837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23664773099620686855458449 17748579824715515141593837)
        ·
          refine ⟨6655717434268318178097689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17748579824715515141593837 6655717434268318178097689)
          ·
            refine ⟨4991788075701238633573267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6655717434268318178097689 4991788075701238633573267)
            ·
              refine ⟨7487682113551857950359901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991788075701238633573267 7487682113551857950359901)
              ·
                refine ⟨2807880792581946731384963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487682113551857950359901 2807880792581946731384963)
                ·
                  refine ⟨4211821188872920097077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807880792581946731384963 4211821188872920097077445)
                  ·
                    refine ⟨789716472913672518202021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211821188872920097077445 789716472913672518202021)
                    ·
                      rfl

theorem cell22_2306951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2306951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2306951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2306951 prefixEnd_2306951 := by exact prefixLift 2306951
  have htrace : WordTrace (prefixWord ++ tailWord_2306951) baseStart_2306951 baseEnd_2306951 := by
    simpa [prefixWord, tailWord_2306951, baseEnd_2306951] using wordTrace_append hprefix tailTrace_2306951
  have hstable : (prefixWord ++ tailWord_2306951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2306951).length < 2 ^ (prefixWord ++ tailWord_2306951).sum := by decide
  have hdescent : baseEnd_2306951 < baseStart_2306951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2306951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307086 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2307086 : Nat := 118140960795 + 2307086 * 2 ^ 59
def prefixEnd_2307086 : Nat := 4983230072969 + 3 ^ 40 * 2307086 * 2
def baseEnd_2307086 : Nat := 789762686172577166076607

theorem tailTrace_2307086 : CollatzResearch.WordTrace tailWord_2307086 prefixEnd_2307086 789762686172577166076607 := by
  unfold tailWord_2307086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10518292414978614470557639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56097559546552610509640741 10518292414978614470557639)
  ·
    refine ⟨15777438622467921705836459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10518292414978614470557639 15777438622467921705836459)
    ·
      refine ⟨23666157933701882558754689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15777438622467921705836459 23666157933701882558754689)
      ·
        refine ⟨17749618450276411919066017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23666157933701882558754689 17749618450276411919066017)
        ·
          refine ⟨13312213837707308939299513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17749618450276411919066017 13312213837707308939299513)
          ·
            refine ⟨9984160378280481704474635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13312213837707308939299513 9984160378280481704474635)
            ·
              refine ⟨14976240567420722556711953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984160378280481704474635 14976240567420722556711953)
              ·
                refine ⟨11232180425565541917533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14976240567420722556711953 11232180425565541917533965)
                ·
                  refine ⟨4212067659587078219075237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11232180425565541917533965 4212067659587078219075237)
                  ·
                    refine ⟨789762686172577166076607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212067659587078219075237 789762686172577166076607)
                    ·
                      rfl

theorem cell22_2307086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2307086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307086 prefixEnd_2307086 := by exact prefixLift 2307086
  have htrace : WordTrace (prefixWord ++ tailWord_2307086) baseStart_2307086 baseEnd_2307086 := by
    simpa [prefixWord, tailWord_2307086, baseEnd_2307086] using wordTrace_append hprefix tailTrace_2307086
  have hstable : (prefixWord ++ tailWord_2307086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307086).length < 2 ^ (prefixWord ++ tailWord_2307086).sum := by decide
  have hdescent : baseEnd_2307086 < baseStart_2307086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307116 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_2307116 : Nat := 118140960795 + 2307116 * 2 ^ 59
def prefixEnd_2307116 : Nat := 4983230072969 + 3 ^ 40 * 2307116 * 2
def baseEnd_2307116 : Nat := 789772955785667087826515

theorem tailTrace_2307116 : CollatzResearch.WordTrace tailWord_2307116 prefixEnd_2307116 789772955785667087826515 := by
  unfold tailWord_2307116
  simp only [CollatzResearch.WordTrace]
  refine ⟨42073716754860115444026601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56098289006480153925368801 42073716754860115444026601)
  ·
    refine ⟨31555287566145086583019951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42073716754860115444026601 31555287566145086583019951)
    ·
      refine ⟨47332931349217629874529927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31555287566145086583019951 47332931349217629874529927)
      ·
        refine ⟨70999397023826444811794891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47332931349217629874529927 70999397023826444811794891)
        ·
          refine ⟨106499095535739667217692337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70999397023826444811794891 106499095535739667217692337)
          ·
            refine ⟨79874321651804750413269253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106499095535739667217692337 79874321651804750413269253)
            ·
              refine ⟨14976435309713390702487985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79874321651804750413269253 14976435309713390702487985)
              ·
                refine ⟨11232326482285043026865989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14976435309713390702487985 11232326482285043026865989)
                ·
                  refine ⟨2106061215428445567537373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11232326482285043026865989 2106061215428445567537373)
                  ·
                    refine ⟨789772955785667087826515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106061215428445567537373 789772955785667087826515)
                    ·
                      rfl

theorem cell22_2307116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_2307116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307116 prefixEnd_2307116 := by exact prefixLift 2307116
  have htrace : WordTrace (prefixWord ++ tailWord_2307116) baseStart_2307116 baseEnd_2307116 := by
    simpa [prefixWord, tailWord_2307116, baseEnd_2307116] using wordTrace_append hprefix tailTrace_2307116
  have hstable : (prefixWord ++ tailWord_2307116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307116).length < 2 ^ (prefixWord ++ tailWord_2307116).sum := by decide
  have hdescent : baseEnd_2307116 < baseStart_2307116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307133 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_2307133 : Nat := 118140960795 + 2307133 * 2 ^ 59
def prefixEnd_2307133 : Nat := 4983230072969 + 3 ^ 40 * 2307133 * 2
def baseEnd_2307133 : Nat := 789778775233084710151463

theorem tailTrace_2307133 : CollatzResearch.WordTrace tailWord_2307133 prefixEnd_2307133 789778775233084710151463 := by
  unfold tailWord_2307133
  simp only [CollatzResearch.WordTrace]
  refine ⟨84148053550658642791422053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56098702367105761860948035 84148053550658642791422053)
  ·
    refine ⟨15777760040748495523391635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84148053550658642791422053 15777760040748495523391635)
    ·
      refine ⟨23666640061122743285087453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15777760040748495523391635 23666640061122743285087453)
      ·
        refine ⟨8874990022921028731907795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23666640061122743285087453 8874990022921028731907795)
        ·
          refine ⟨13312485034381543097861693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874990022921028731907795 13312485034381543097861693)
          ·
            refine ⟨4992181887893078661698135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13312485034381543097861693 4992181887893078661698135)
            ·
              refine ⟨7488272831839617992547203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992181887893078661698135 7488272831839617992547203)
              ·
                refine ⟨11232409247759426988820805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7488272831839617992547203 11232409247759426988820805)
                ·
                  refine ⟨2106076733954892560403901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11232409247759426988820805 2106076733954892560403901)
                  ·
                    refine ⟨789778775233084710151463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106076733954892560403901 789778775233084710151463)
                    ·
                      rfl

theorem cell22_2307133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_2307133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307133 prefixEnd_2307133 := by exact prefixLift 2307133
  have htrace : WordTrace (prefixWord ++ tailWord_2307133) baseStart_2307133 baseEnd_2307133 := by
    simpa [prefixWord, tailWord_2307133, baseEnd_2307133] using wordTrace_append hprefix tailTrace_2307133
  have hstable : (prefixWord ++ tailWord_2307133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307133).length < 2 ^ (prefixWord ++ tailWord_2307133).sum := by decide
  have hdescent : baseEnd_2307133 < baseStart_2307133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307150 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_2307150 : Nat := 118140960795 + 2307150 * 2 ^ 59
def prefixEnd_2307150 : Nat := 4983230072969 + 3 ^ 40 * 2307150 * 2
def baseEnd_2307150 : Nat := 789784594680502332476411

theorem tailTrace_2307150 : CollatzResearch.WordTrace tailWord_2307150 prefixEnd_2307150 789784594680502332476411 := by
  unfold tailWord_2307150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10518584198949631836848863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56099115727731369796527269 10518584198949631836848863)
  ·
    refine ⟨15777876298424447755273295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10518584198949631836848863 15777876298424447755273295)
    ·
      refine ⟨23666814447636671632909943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15777876298424447755273295 23666814447636671632909943)
      ·
        refine ⟨35500221671455007449364915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23666814447636671632909943 35500221671455007449364915)
        ·
          refine ⟨53250332507182511174047373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35500221671455007449364915 53250332507182511174047373)
          ·
            refine ⟨19968874690193441690267765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53250332507182511174047373 19968874690193441690267765)
            ·
              refine ⟨1872082002205635158462603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19968874690193441690267765 1872082002205635158462603)
              ·
                refine ⟨2808123003308452737693905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872082002205635158462603 2808123003308452737693905)
                ·
                  refine ⟨2106092252481339553270429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808123003308452737693905 2106092252481339553270429)
                  ·
                    refine ⟨789784594680502332476411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106092252481339553270429 789784594680502332476411)
                    ·
                      rfl

theorem cell22_2307150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_2307150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307150 prefixEnd_2307150 := by exact prefixLift 2307150
  have htrace : WordTrace (prefixWord ++ tailWord_2307150) baseStart_2307150 baseEnd_2307150 := by
    simpa [prefixWord, tailWord_2307150, baseEnd_2307150] using wordTrace_append hprefix tailTrace_2307150
  have hstable : (prefixWord ++ tailWord_2307150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307150).length < 2 ^ (prefixWord ++ tailWord_2307150).sum := by decide
  have hdescent : baseEnd_2307150 < baseStart_2307150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307161 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_2307161 : Nat := 118140960795 + 2307161 * 2 ^ 59
def prefixEnd_2307161 : Nat := 4983230072969 + 3 ^ 40 * 2307161 * 2
def baseEnd_2307161 : Nat := 789788360205301970451377

theorem tailTrace_2307161 : CollatzResearch.WordTrace tailWord_2307161 prefixEnd_2307161 789788360205301970451377 := by
  unfold tailWord_2307161
  simp only [CollatzResearch.WordTrace]
  refine ⟨84149074794557203573441337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56099383196371469048960891 84149074794557203573441337)
  ·
    refine ⟨63111806095917902680081003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84149074794557203573441337 63111806095917902680081003)
    ·
      refine ⟨94667709143876854020121505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63111806095917902680081003 94667709143876854020121505)
      ·
        refine ⟨71000781857907640515091129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94667709143876854020121505 71000781857907640515091129)
        ·
          refine ⟨53250586393430730386318347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71000781857907640515091129 53250586393430730386318347)
          ·
            refine ⟨79875879590146095579477521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53250586393430730386318347 79875879590146095579477521)
            ·
              refine ⟨59906909692609571684608141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79875879590146095579477521 59906909692609571684608141)
              ·
                refine ⟨22465091134728589381728053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59906909692609571684608141 22465091134728589381728053)
                ·
                  refine ⟨2106102293880805254537005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22465091134728589381728053 2106102293880805254537005)
                  ·
                    refine ⟨789788360205301970451377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106102293880805254537005 789788360205301970451377)
                    ·
                      rfl

theorem cell22_2307161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_2307161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307161 prefixEnd_2307161 := by exact prefixLift 2307161
  have htrace : WordTrace (prefixWord ++ tailWord_2307161) baseStart_2307161 baseEnd_2307161 := by
    simpa [prefixWord, tailWord_2307161, baseEnd_2307161] using wordTrace_append hprefix tailTrace_2307161
  have hstable : (prefixWord ++ tailWord_2307161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307161).length < 2 ^ (prefixWord ++ tailWord_2307161).sum := by decide
  have hdescent : baseEnd_2307161 < baseStart_2307161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307191 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 5]
def baseStart_2307191 : Nat := 118140960795 + 2307191 * 2 ^ 59
def prefixEnd_2307191 : Nat := 4983230072969 + 3 ^ 40 * 2307191 * 2
def baseEnd_2307191 : Nat := 263266209939463964067095

theorem tailTrace_2307191 : CollatzResearch.WordTrace tailWord_2307191 prefixEnd_2307191 263266209939463964067095 := by
  unfold tailWord_2307191
  simp only [CollatzResearch.WordTrace]
  refine ⟨84150168984448518697033427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56100112656299012464688951 84150168984448518697033427)
  ·
    refine ⟨126225253476672778045550141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84150168984448518697033427 126225253476672778045550141)
    ·
      refine ⟨47334470053752291767081303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126225253476672778045550141 47334470053752291767081303)
      ·
        refine ⟨71001705080628437650621955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47334470053752291767081303 71001705080628437650621955)
        ·
          refine ⟨106502557620942656475932933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71001705080628437650621955 106502557620942656475932933)
          ·
            refine ⟨19969229553926748089237425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106502557620942656475932933 19969229553926748089237425)
            ·
              refine ⟨14976922165445061066928069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19969229553926748089237425 14976922165445061066928069)
              ·
                refine ⟨2808172906020948950049013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14976922165445061066928069 2808172906020948950049013)
                ·
                  refine ⟨263266209939463964067095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808172906020948950049013 263266209939463964067095)
                  ·
                    rfl

theorem cell22_2307191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].length) (baseStart_2307191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307191 prefixEnd_2307191 := by exact prefixLift 2307191
  have htrace : WordTrace (prefixWord ++ tailWord_2307191) baseStart_2307191 baseEnd_2307191 := by
    simpa [prefixWord, tailWord_2307191, baseEnd_2307191] using wordTrace_append hprefix tailTrace_2307191
  have hstable : (prefixWord ++ tailWord_2307191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307191).length < 2 ^ (prefixWord ++ tailWord_2307191).sum := by decide
  have hdescent : baseEnd_2307191 < baseStart_2307191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307364 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_2307364 : Nat := 118140960795 + 2307364 * 2 ^ 59
def prefixEnd_2307364 : Nat := 4983230072969 + 3 ^ 40 * 2307364 * 2
def baseEnd_2307364 : Nat := 789857851253877107625755

theorem tailTrace_2307364 : CollatzResearch.WordTrace tailWord_2307364 prefixEnd_2307364 789857851253877107625755 := by
  unfold tailWord_2307364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42078239406410884621540573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56104319208547846162054097 42078239406410884621540573)
  ·
    refine ⟨15779339777404081733077715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42078239406410884621540573 15779339777404081733077715)
    ·
      refine ⟨23669009666106122599616573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15779339777404081733077715 23669009666106122599616573)
      ·
        refine ⟨8875878624789795974856215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23669009666106122599616573 8875878624789795974856215)
        ·
          refine ⟨13313817937184693962284323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875878624789795974856215 13313817937184693962284323)
          ·
            refine ⟨19970726905777040943426485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313817937184693962284323 19970726905777040943426485)
            ·
              refine ⟨1872255647416597588446233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19970726905777040943426485 1872255647416597588446233)
              ·
                refine ⟨1404191735562448191334675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872255647416597588446233 1404191735562448191334675)
                ·
                  refine ⟨2106287603343672287002013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404191735562448191334675 2106287603343672287002013)
                  ·
                    refine ⟨789857851253877107625755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106287603343672287002013 789857851253877107625755)
                    ·
                      rfl

theorem cell22_2307364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_2307364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307364 prefixEnd_2307364 := by exact prefixLift 2307364
  have htrace : WordTrace (prefixWord ++ tailWord_2307364) baseStart_2307364 baseEnd_2307364 := by
    simpa [prefixWord, tailWord_2307364, baseEnd_2307364] using wordTrace_append hprefix tailTrace_2307364
  have hstable : (prefixWord ++ tailWord_2307364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307364).length < 2 ^ (prefixWord ++ tailWord_2307364).sum := by decide
  have hdescent : baseEnd_2307364 < baseStart_2307364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307371 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 12]
def baseStart_2307371 : Nat := 118140960795 + 2307371 * 2 ^ 59
def prefixEnd_2307371 : Nat := 4983230072969 + 3 ^ 40 * 2307371 * 2
def baseEnd_2307371 : Nat := 263286749165643807566911

theorem tailTrace_2307371 : CollatzResearch.WordTrace tailWord_2307371 prefixEnd_2307371 263286749165643807566911 := by
  unfold tailWord_2307371
  simp only [CollatzResearch.WordTrace]
  refine ⟨84156734123796409438585967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56104489415864272959057311 84156734123796409438585967)
  ·
    refine ⟨126235101185694614157878951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84156734123796409438585967 126235101185694614157878951)
    ·
      refine ⟨189352651778541921236818427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126235101185694614157878951 189352651778541921236818427)
      ·
        refine ⟨284028977667812881855227641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189352651778541921236818427 284028977667812881855227641)
        ·
          refine ⟨213021733250859661391420731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284028977667812881855227641 213021733250859661391420731)
          ·
            refine ⟨319532599876289492087131097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213021733250859661391420731 319532599876289492087131097)
            ·
              refine ⟨239649449907217119065348323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319532599876289492087131097 239649449907217119065348323)
              ·
                refine ⟨359474174860825678598022485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239649449907217119065348323 359474174860825678598022485)
                ·
                  refine ⟨263286749165643807566911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 359474174860825678598022485 263286749165643807566911)
                  ·
                    rfl

theorem cell22_2307371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_2307371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307371 prefixEnd_2307371 := by exact prefixLift 2307371
  have htrace : WordTrace (prefixWord ++ tailWord_2307371) baseStart_2307371 baseEnd_2307371 := by
    simpa [prefixWord, tailWord_2307371, baseEnd_2307371] using wordTrace_append hprefix tailTrace_2307371
  have hstable : (prefixWord ++ tailWord_2307371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307371).length < 2 ^ (prefixWord ++ tailWord_2307371).sum := by decide
  have hdescent : baseEnd_2307371 < baseStart_2307371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307377 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 5]
def baseStart_2307377 : Nat := 118140960795 + 2307377 * 2 ^ 59
def prefixEnd_2307377 : Nat := 4983230072969 + 3 ^ 40 * 2307377 * 2
def baseEnd_2307377 : Nat := 263287433806516469016905

theorem tailTrace_2307377 : CollatzResearch.WordTrace tailWord_2307377 prefixEnd_2307377 263287433806516469016905 := by
  unfold tailWord_2307377
  simp only [CollatzResearch.WordTrace]
  refine ⟨84156952961774672463304385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56104635307849781642202923 84156952961774672463304385)
  ·
    refine ⟨63117714721331004347478289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84156952961774672463304385 63117714721331004347478289)
    ·
      refine ⟨47338286040998253260608717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63117714721331004347478289 47338286040998253260608717)
      ·
        refine ⟨17751857265374344972728269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47338286040998253260608717 17751857265374344972728269)
        ·
          refine ⟨6656946474515379364773101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17751857265374344972728269 6656946474515379364773101)
          ·
            refine ⟨2496354927943267261789913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6656946474515379364773101 2496354927943267261789913)
            ·
              refine ⟨1872266195957450446342435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496354927943267261789913 1872266195957450446342435)
              ·
                refine ⟨2808399293936175669513653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872266195957450446342435 2808399293936175669513653)
                ·
                  refine ⟨263287433806516469016905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808399293936175669513653 263287433806516469016905)
                  ·
                    rfl

theorem cell22_2307377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_2307377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307377 prefixEnd_2307377 := by exact prefixLift 2307377
  have htrace : WordTrace (prefixWord ++ tailWord_2307377) baseStart_2307377 baseEnd_2307377 := by
    simpa [prefixWord, tailWord_2307377, baseEnd_2307377] using wordTrace_append hprefix tailTrace_2307377
  have hstable : (prefixWord ++ tailWord_2307377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307377).length < 2 ^ (prefixWord ++ tailWord_2307377).sum := by decide
  have hdescent : baseEnd_2307377 < baseStart_2307377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307390 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2307390 : Nat := 118140960795 + 2307390 * 2 ^ 59
def prefixEnd_2307390 : Nat := 4983230072969 + 3 ^ 40 * 2307390 * 2
def baseEnd_2307390 : Nat := 789866751585221706475675

theorem tailTrace_2307390 : CollatzResearch.WordTrace tailWord_2307390 prefixEnd_2307390 789866751585221706475675 := by
  unfold tailWord_2307390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519678388840946960440953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56104951407151717122351749 10519678388840946960440953)
  ·
    refine ⟨7889758791630710220330715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10519678388840946960440953 7889758791630710220330715)
    ·
      refine ⟨11834638187446065330496073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7889758791630710220330715 11834638187446065330496073)
      ·
        refine ⟨8875978640584548997872055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11834638187446065330496073 8875978640584548997872055)
        ·
          refine ⟨13313967960876823496808083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875978640584548997872055 13313967960876823496808083)
          ·
            refine ⟨19970951941315235245212125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313967960876823496808083 19970951941315235245212125)
            ·
              refine ⟨7489106977993213216954547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19970951941315235245212125 7489106977993213216954547)
              ·
                refine ⟨11233660466989819825431821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7489106977993213216954547 11233660466989819825431821)
                ·
                  refine ⟨4212622675121182434536933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11233660466989819825431821 4212622675121182434536933)
                  ·
                    refine ⟨789866751585221706475675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212622675121182434536933 789866751585221706475675)
                    ·
                      rfl

theorem cell22_2307390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2307390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307390 prefixEnd_2307390 := by exact prefixLift 2307390
  have htrace : WordTrace (prefixWord ++ tailWord_2307390) baseStart_2307390 baseEnd_2307390 := by
    simpa [prefixWord, tailWord_2307390, baseEnd_2307390] using wordTrace_append hprefix tailTrace_2307390
  have hstable : (prefixWord ++ tailWord_2307390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307390).length < 2 ^ (prefixWord ++ tailWord_2307390).sum := by decide
  have hdescent : baseEnd_2307390 < baseStart_2307390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307437 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_2307437 : Nat := 118140960795 + 2307437 * 2 ^ 59
def prefixEnd_2307437 : Nat := 4983230072969 + 3 ^ 40 * 2307437 * 2
def baseEnd_2307437 : Nat := 789882840645729250550531

theorem tailTrace_2307437 : CollatzResearch.WordTrace tailWord_2307437 prefixEnd_2307437 789882840645729250550531 := by
  unfold tailWord_2307437
  simp only [CollatzResearch.WordTrace]
  refine ⟨84159141341557302710488565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56106094227704868473659043 84159141341557302710488565)
  ·
    refine ⟨7889919500770997129108303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84159141341557302710488565 7889919500770997129108303)
    ·
      refine ⟨11834879251156495693662455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7889919500770997129108303 11834879251156495693662455)
      ·
        refine ⟨17752318876734743540493683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834879251156495693662455 17752318876734743540493683)
        ·
          refine ⟨26628478315102115310740525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17752318876734743540493683 26628478315102115310740525)
          ·
            refine ⟨9985679368163293241527697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26628478315102115310740525 9985679368163293241527697)
            ·
              refine ⟨7489259526122469931145773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9985679368163293241527697 7489259526122469931145773)
              ·
                refine ⟨2808472322295926224179665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7489259526122469931145773 2808472322295926224179665)
                ·
                  refine ⟨2106354241721944668134749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808472322295926224179665 2106354241721944668134749)
                  ·
                    refine ⟨789882840645729250550531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106354241721944668134749 789882840645729250550531)
                    ·
                      rfl

theorem cell22_2307437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_2307437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307437 prefixEnd_2307437 := by exact prefixLift 2307437
  have htrace : WordTrace (prefixWord ++ tailWord_2307437) baseStart_2307437 baseEnd_2307437 := by
    simpa [prefixWord, tailWord_2307437, baseEnd_2307437] using wordTrace_append hprefix tailTrace_2307437
  have hstable : (prefixWord ++ tailWord_2307437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307437).length < 2 ^ (prefixWord ++ tailWord_2307437).sum := by decide
  have hdescent : baseEnd_2307437 < baseStart_2307437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307482 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_2307482 : Nat := 118140960795 + 2307482 * 2 ^ 59
def prefixEnd_2307482 : Nat := 4983230072969 + 3 ^ 40 * 2307482 * 2
def baseEnd_2307482 : Nat := 789898245065364133175393

theorem tailTrace_2307482 : CollatzResearch.WordTrace tailWord_2307482 prefixEnd_2307482 789898245065364133175393 := by
  unfold tailWord_2307482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21040195656598568848969175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56107188417596183597251133 21040195656598568848969175)
  ·
    refine ⟨31560293484897853273453763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21040195656598568848969175 31560293484897853273453763)
    ·
      refine ⟨47340440227346779910180645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31560293484897853273453763 47340440227346779910180645)
      ·
        refine ⟨8876332542627521233158871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47340440227346779910180645 8876332542627521233158871)
        ·
          refine ⟨13314498813941281849738307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876332542627521233158871 13314498813941281849738307)
          ·
            refine ⟨19971748220911922774607461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13314498813941281849738307 19971748220911922774607461)
            ·
              refine ⟨3744702791420985520238899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19971748220911922774607461 3744702791420985520238899)
              ·
                refine ⟨5617054187131478280358349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744702791420985520238899 5617054187131478280358349)
                ·
                  refine ⟨2106395320174304355134381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5617054187131478280358349 2106395320174304355134381)
                  ·
                    refine ⟨789898245065364133175393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106395320174304355134381 789898245065364133175393)
                    ·
                      rfl

theorem cell22_2307482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_2307482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307482 prefixEnd_2307482 := by exact prefixLift 2307482
  have htrace : WordTrace (prefixWord ++ tailWord_2307482) baseStart_2307482 baseEnd_2307482 := by
    simpa [prefixWord, tailWord_2307482, baseEnd_2307482] using wordTrace_append hprefix tailTrace_2307482
  have hstable : (prefixWord ++ tailWord_2307482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307482).length < 2 ^ (prefixWord ++ tailWord_2307482).sum := by decide
  have hdescent : baseEnd_2307482 < baseStart_2307482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307493 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2307493 : Nat := 118140960795 + 2307493 * 2 ^ 59
def prefixEnd_2307493 : Nat := 4983230072969 + 3 ^ 40 * 2307493 * 2
def baseEnd_2307493 : Nat := 789902010590163771150359

theorem tailTrace_2307493 : CollatzResearch.WordTrace tailWord_2307493 prefixEnd_2307493 789902010590163771150359 := by
  unfold tailWord_2307493
  simp only [CollatzResearch.WordTrace]
  refine ⟨84161183829354424274527133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56107455886236282849684755 84161183829354424274527133)
  ·
    refine ⟨31560443936007909102947675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84161183829354424274527133 31560443936007909102947675)
    ·
      refine ⟨47340665904011863654421513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31560443936007909102947675 47340665904011863654421513)
      ·
        refine ⟨35505499428008897740816135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47340665904011863654421513 35505499428008897740816135)
        ·
          refine ⟨53258249142013346611224203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35505499428008897740816135 53258249142013346611224203)
          ·
            refine ⟨79887373713020019916836305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53258249142013346611224203 79887373713020019916836305)
            ·
              refine ⟨59915530284765014937627229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79887373713020019916836305 59915530284765014937627229)
              ·
                refine ⟨22468323856786880601610211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59915530284765014937627229 22468323856786880601610211)
                ·
                  refine ⟨33702485785180320902415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22468323856786880601610211 33702485785180320902415317)
                  ·
                    refine ⟨789902010590163771150359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33702485785180320902415317 789902010590163771150359)
                    ·
                      rfl

theorem cell22_2307493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2307493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307493 prefixEnd_2307493 := by exact prefixLift 2307493
  have htrace : WordTrace (prefixWord ++ tailWord_2307493) baseStart_2307493 baseEnd_2307493 := by
    simpa [prefixWord, tailWord_2307493, baseEnd_2307493] using wordTrace_append hprefix tailTrace_2307493
  have hstable : (prefixWord ++ tailWord_2307493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307493).length < 2 ^ (prefixWord ++ tailWord_2307493).sum := by decide
  have hdescent : baseEnd_2307493 < baseStart_2307493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307523 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 8]
def baseStart_2307523 : Nat := 118140960795 + 2307523 * 2 ^ 59
def prefixEnd_2307523 : Nat := 4983230072969 + 3 ^ 40 * 2307523 * 2
def baseEnd_2307523 : Nat := 263304093401084564300089

theorem tailTrace_2307523 : CollatzResearch.WordTrace tailWord_2307523 prefixEnd_2307523 263304093401084564300089 := by
  unfold tailWord_2307523
  simp only [CollatzResearch.WordTrace]
  refine ⟨84162278019245739398119223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56108185346163826265412815 84162278019245739398119223)
  ·
    refine ⟨126243417028868609097178835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84162278019245739398119223 126243417028868609097178835)
    ·
      refine ⟨189365125543302913645768253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126243417028868609097178835 189365125543302913645768253)
      ·
        refine ⟨71011922078738592617163095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189365125543302913645768253 71011922078738592617163095)
        ·
          refine ⟨106517883118107888925744643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71011922078738592617163095 106517883118107888925744643)
          ·
            refine ⟨159776824677161833388616965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106517883118107888925744643 159776824677161833388616965)
            ·
              refine ⟨29958154626967843760365681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159776824677161833388616965 29958154626967843760365681)
              ·
                refine ⟨22468615970225882820274261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29958154626967843760365681 22468615970225882820274261)
                ·
                  refine ⟨263304093401084564300089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22468615970225882820274261 263304093401084564300089)
                  ·
                    rfl

theorem cell22_2307523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_2307523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307523 prefixEnd_2307523 := by exact prefixLift 2307523
  have htrace : WordTrace (prefixWord ++ tailWord_2307523) baseStart_2307523 baseEnd_2307523 := by
    simpa [prefixWord, tailWord_2307523, baseEnd_2307523] using wordTrace_append hprefix tailTrace_2307523
  have hstable : (prefixWord ++ tailWord_2307523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307523).length < 2 ^ (prefixWord ++ tailWord_2307523).sum := by decide
  have hdescent : baseEnd_2307523 < baseStart_2307523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307559 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2307559 : Nat := 118140960795 + 2307559 * 2 ^ 59
def prefixEnd_2307559 : Nat := 4983230072969 + 3 ^ 40 * 2307559 * 2
def baseEnd_2307559 : Nat := 789924603738961599000157

theorem tailTrace_2307559 : CollatzResearch.WordTrace tailWord_2307559 prefixEnd_2307559 789924603738961599000157 := by
  unfold tailWord_2307559
  simp only [CollatzResearch.WordTrace]
  refine ⟨84163591047115317546429731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56109060698076878364286487 84163591047115317546429731)
  ·
    refine ⟨126245386570672976319644597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84163591047115317546429731 126245386570672976319644597)
    ·
      refine ⟨11835504991000591529966681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126245386570672976319644597 11835504991000591529966681)
      ·
        refine ⟨8876628743250443647475011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11835504991000591529966681 8876628743250443647475011)
        ·
          refine ⟨13314943114875665471212517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876628743250443647475011 13314943114875665471212517)
          ·
            refine ⟨2496551834039187275852347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13314943114875665471212517 2496551834039187275852347)
            ·
              refine ⟨3744827751058780913778521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496551834039187275852347 3744827751058780913778521)
              ·
                refine ⟨2808620813294085685333891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744827751058780913778521 2808620813294085685333891)
                ·
                  refine ⟨4212931219941128528000837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808620813294085685333891 4212931219941128528000837)
                  ·
                    refine ⟨789924603738961599000157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4212931219941128528000837 789924603738961599000157)
                    ·
                      rfl

theorem cell22_2307559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2307559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307559 prefixEnd_2307559 := by exact prefixLift 2307559
  have htrace : WordTrace (prefixWord ++ tailWord_2307559) baseStart_2307559 baseEnd_2307559 := by
    simpa [prefixWord, tailWord_2307559, baseEnd_2307559] using wordTrace_append hprefix tailTrace_2307559
  have hstable : (prefixWord ++ tailWord_2307559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307559).length < 2 ^ (prefixWord ++ tailWord_2307559).sum := by decide
  have hdescent : baseEnd_2307559 < baseStart_2307559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307585 : List Nat := [1, 2, 4, 1, 4, 10]
def baseStart_2307585 : Nat := 118140960795 + 2307585 * 2 ^ 59
def prefixEnd_2307585 : Nat := 4983230072969 + 3 ^ 40 * 2307585 * 2
def baseEnd_2307585 : Nat := 9752265482349459232717

theorem tailTrace_2307585 : CollatzResearch.WordTrace tailWord_2307585 prefixEnd_2307585 9752265482349459232717 := by
  unfold tailWord_2307585
  simp only [CollatzResearch.WordTrace]
  refine ⟨84164539345021123986876209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56109692896680749324584139 84164539345021123986876209)
  ·
    refine ⟨63123404508765842990157157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84164539345021123986876209 63123404508765842990157157)
    ·
      refine ⟨11835638345393595560654467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63123404508765842990157157 11835638345393595560654467)
      ·
        refine ⟨17753457518090393340981701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11835638345393595560654467 17753457518090393340981701)
        ·
          refine ⟨3328773284641948751434069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17753457518090393340981701 3328773284641948751434069)
          ·
            refine ⟨9752265482349459232717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3328773284641948751434069 9752265482349459232717)
            ·
              rfl

theorem cell22_2307585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 10].length) (baseStart_2307585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307585 prefixEnd_2307585 := by exact prefixLift 2307585
  have htrace : WordTrace (prefixWord ++ tailWord_2307585) baseStart_2307585 baseEnd_2307585 := by
    simpa [prefixWord, tailWord_2307585, baseEnd_2307585] using wordTrace_append hprefix tailTrace_2307585
  have hstable : (prefixWord ++ tailWord_2307585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307585).length < 2 ^ (prefixWord ++ tailWord_2307585).sum := by decide
  have hdescent : baseEnd_2307585 < baseStart_2307585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307591 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 4]
def baseStart_2307591 : Nat := 118140960795 + 2307591 * 2 ^ 59
def prefixEnd_2307591 : Nat := 4983230072969 + 3 ^ 40 * 2307591 * 2
def baseEnd_2307591 : Nat := 263311852664308060733353

theorem tailTrace_2307591 : CollatzResearch.WordTrace tailWord_2307591 prefixEnd_2307591 263311852664308060733353 := by
  unfold tailWord_2307591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84164758182999387011594627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56109838788666258007729751 84164758182999387011594627)
  ·
    refine ⟨126247137274499080517391941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84164758182999387011594627 126247137274499080517391941)
    ·
      refine ⟨23671338238968577597010989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126247137274499080517391941 23671338238968577597010989)
      ·
        refine ⟨8876751839613216598879121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23671338238968577597010989 8876751839613216598879121)
        ·
          refine ⟨6657563879709912449159341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8876751839613216598879121 6657563879709912449159341)
          ·
            refine ⟨2496586454891217168434753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6657563879709912449159341 2496586454891217168434753)
            ·
              refine ⟨1872439841168412876326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496586454891217168434753 1872439841168412876326065)
              ·
                refine ⟨1404329880876309657244549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872439841168412876326065 1404329880876309657244549)
                ·
                  refine ⟨263311852664308060733353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404329880876309657244549 263311852664308060733353)
                  ·
                    rfl

theorem cell22_2307591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 4].length) (baseStart_2307591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307591 prefixEnd_2307591 := by exact prefixLift 2307591
  have htrace : WordTrace (prefixWord ++ tailWord_2307591) baseStart_2307591 baseEnd_2307591 := by
    simpa [prefixWord, tailWord_2307591, baseEnd_2307591] using wordTrace_append hprefix tailTrace_2307591
  have hstable : (prefixWord ++ tailWord_2307591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307591).length < 2 ^ (prefixWord ++ tailWord_2307591).sum := by decide
  have hdescent : baseEnd_2307591 < baseStart_2307591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307617 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2307617 : Nat := 118140960795 + 2307617 * 2 ^ 59
def prefixEnd_2307617 : Nat := 4983230072969 + 3 ^ 40 * 2307617 * 2
def baseEnd_2307617 : Nat := 789944458324268781049979

theorem tailTrace_2307617 : CollatzResearch.WordTrace tailWord_2307617 prefixEnd_2307617 789944458324268781049979 := by
  unfold tailWord_2307617
  simp only [CollatzResearch.WordTrace]
  refine ⟨84165706480905193452041105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56110470987270128968027403 84165706480905193452041105)
  ·
    refine ⟨63124279860678895089030829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84165706480905193452041105 63124279860678895089030829)
    ·
      refine ⟨23671604947754585658386561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63124279860678895089030829 23671604947754585658386561)
      ·
        refine ⟨17753703710815939243789921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23671604947754585658386561 17753703710815939243789921)
        ·
          refine ⟨13315277783111954432842441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17753703710815939243789921 13315277783111954432842441)
          ·
            refine ⟨9986458337333965824631831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13315277783111954432842441 9986458337333965824631831)
            ·
              refine ⟨14979687506000948736947747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9986458337333965824631831 14979687506000948736947747)
              ·
                refine ⟨22469531259001423105421621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14979687506000948736947747 22469531259001423105421621)
                ·
                  refine ⟨2106518555531383416133277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22469531259001423105421621 2106518555531383416133277)
                  ·
                    refine ⟨789944458324268781049979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106518555531383416133277 789944458324268781049979)
                    ·
                      rfl

theorem cell22_2307617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2307617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307617 prefixEnd_2307617 := by exact prefixLift 2307617
  have htrace : WordTrace (prefixWord ++ tailWord_2307617) baseStart_2307617 baseEnd_2307617 := by
    simpa [prefixWord, tailWord_2307617, baseEnd_2307617] using wordTrace_append hprefix tailTrace_2307617
  have hstable : (prefixWord ++ tailWord_2307617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307617).length < 2 ^ (prefixWord ++ tailWord_2307617).sum := by decide
  have hdescent : baseEnd_2307617 < baseStart_2307617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307647 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 5]
def baseStart_2307647 : Nat := 118140960795 + 2307647 * 2 ^ 59
def prefixEnd_2307647 : Nat := 4983230072969 + 3 ^ 40 * 2307647 * 2
def baseEnd_2307647 : Nat := 263318242645786234266629

theorem tailTrace_2307647 : CollatzResearch.WordTrace tailWord_2307647 prefixEnd_2307647 263318242645786234266629 := by
  unfold tailWord_2307647
  simp only [CollatzResearch.WordTrace]
  refine ⟨84166800670796508575633195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56111200447197672383755463 84166800670796508575633195)
  ·
    refine ⟨126250201006194762863449793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84166800670796508575633195 126250201006194762863449793)
    ·
      refine ⟨94687650754646072147587345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126250201006194762863449793 94687650754646072147587345)
      ·
        refine ⟨71015738065984554110690509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94687650754646072147587345 71015738065984554110690509)
        ·
          refine ⟨26630901774744207791508941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71015738065984554110690509 26630901774744207791508941)
          ·
            refine ⟨9986588165529077921815853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26630901774744207791508941 9986588165529077921815853)
            ·
              refine ⟨3744970562073404220680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9986588165529077921815853 3744970562073404220680945)
              ·
                refine ⟨2808727921555053165510709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744970562073404220680945 2808727921555053165510709)
                ·
                  refine ⟨263318242645786234266629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808727921555053165510709 263318242645786234266629)
                  ·
                    rfl

theorem cell22_2307647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].length) (baseStart_2307647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307647 prefixEnd_2307647 := by exact prefixLift 2307647
  have htrace : WordTrace (prefixWord ++ tailWord_2307647) baseStart_2307647 baseEnd_2307647 := by
    simpa [prefixWord, tailWord_2307647, baseEnd_2307647] using wordTrace_append hprefix tailTrace_2307647
  have hstable : (prefixWord ++ tailWord_2307647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307647).length < 2 ^ (prefixWord ++ tailWord_2307647).sum := by decide
  have hdescent : baseEnd_2307647 < baseStart_2307647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307670 : List Nat := [5, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2307670 : Nat := 118140960795 + 2307670 * 2 ^ 59
def prefixEnd_2307670 : Nat := 4983230072969 + 3 ^ 40 * 2307670 * 2
def baseEnd_2307670 : Nat := 87773622367488256608313

theorem tailTrace_2307670 : CollatzResearch.WordTrace tailWord_2307670 prefixEnd_2307670 87773622367488256608313 := by
  unfold tailWord_2307670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260477471857073968982529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56111759699808789002480309 5260477471857073968982529)
  ·
    refine ⟨3945358103892805476736897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5260477471857073968982529 3945358103892805476736897)
    ·
      refine ⟨2959018577919604107552673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3945358103892805476736897 2959018577919604107552673)
      ·
        refine ⟨2219263933439703080664505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959018577919604107552673 2219263933439703080664505)
        ·
          refine ⟨1664447950079777310498379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219263933439703080664505 1664447950079777310498379)
          ·
            refine ⟨2496671925119665965747569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664447950079777310498379 2496671925119665965747569)
            ·
              refine ⟨1872503943839749474310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496671925119665965747569 1872503943839749474310677)
              ·
                refine ⟨87773622367488256608313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1872503943839749474310677 87773622367488256608313)
                ·
                  rfl

theorem cell22_2307670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2307670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307670 prefixEnd_2307670 := by exact prefixLift 2307670
  have htrace : WordTrace (prefixWord ++ tailWord_2307670) baseStart_2307670 baseEnd_2307670 := by
    simpa [prefixWord, tailWord_2307670, baseEnd_2307670] using wordTrace_append hprefix tailTrace_2307670
  have hstable : (prefixWord ++ tailWord_2307670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307670).length < 2 ^ (prefixWord ++ tailWord_2307670).sum := by decide
  have hdescent : baseEnd_2307670 < baseStart_2307670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307707 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 4, 3]
def baseStart_2307707 : Nat := 118140960795 + 2307707 * 2 ^ 59
def prefixEnd_2307707 : Nat := 4983230072969 + 3 ^ 40 * 2307707 * 2
def baseEnd_2307707 : Nat := 789975267163538546299703

theorem tailTrace_2307707 : CollatzResearch.WordTrace tailWord_2307707 prefixEnd_2307707 789975267163538546299703 := by
  unfold tailWord_2307707
  simp only [CollatzResearch.WordTrace]
  refine ⟨84168989050579138822817375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56112659367052759215211583 84168989050579138822817375)
  ·
    refine ⟨126253483575868708234226063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84168989050579138822817375 126253483575868708234226063)
    ·
      refine ⟨189380225363803062351339095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126253483575868708234226063 189380225363803062351339095)
      ·
        refine ⟨284070338045704593527008643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189380225363803062351339095 284070338045704593527008643)
        ·
          refine ⟨426105507068556890290512965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284070338045704593527008643 426105507068556890290512965)
          ·
            refine ⟨79894782575354416929471181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 426105507068556890290512965 79894782575354416929471181)
            ·
              refine ⟨29960543465757906348551693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79894782575354416929471181 29960543465757906348551693)
              ·
                refine ⟨11235203799659214880706885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29960543465757906348551693 11235203799659214880706885)
                ·
                  refine ⟨2106600712436102790132541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11235203799659214880706885 2106600712436102790132541)
                  ·
                    refine ⟨789975267163538546299703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106600712436102790132541 789975267163538546299703)
                    ·
                      rfl

theorem cell22_2307707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].length) (baseStart_2307707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307707 prefixEnd_2307707 := by exact prefixLift 2307707
  have htrace : WordTrace (prefixWord ++ tailWord_2307707) baseStart_2307707 baseEnd_2307707 := by
    simpa [prefixWord, tailWord_2307707, baseEnd_2307707] using wordTrace_append hprefix tailTrace_2307707
  have hstable : (prefixWord ++ tailWord_2307707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307707).length < 2 ^ (prefixWord ++ tailWord_2307707).sum := by decide
  have hdescent : baseEnd_2307707 < baseStart_2307707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307709 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 6]
def baseStart_2307709 : Nat := 118140960795 + 2307709 * 2 ^ 59
def prefixEnd_2307709 : Nat := 4983230072969 + 3 ^ 40 * 2307709 * 2
def baseEnd_2307709 : Nat := 263325317268137069249899

theorem tailTrace_2307709 : CollatzResearch.WordTrace tailWord_2307709 prefixEnd_2307709 263325317268137069249899 := by
  unfold tailWord_2307709
  simp only [CollatzResearch.WordTrace]
  refine ⟨84169061996571893164390181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56112707997714595442926787 84169061996571893164390181)
  ·
    refine ⟨15781699124357229968323159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84169061996571893164390181 15781699124357229968323159)
    ·
      refine ⟨23672548686535844952484739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15781699124357229968323159 23672548686535844952484739)
      ·
        refine ⟨35508823029803767428727109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23672548686535844952484739 35508823029803767428727109)
        ·
          refine ⟨6657904318088206392886333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35508823029803767428727109 6657904318088206392886333)
          ·
            refine ⟨2496714119283077397332375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6657904318088206392886333 2496714119283077397332375)
            ·
              refine ⟨3745071178924616095998563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496714119283077397332375 3745071178924616095998563)
              ·
                refine ⟨5617606768386924143997845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3745071178924616095998563 5617606768386924143997845)
                ·
                  refine ⟨263325317268137069249899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5617606768386924143997845 263325317268137069249899)
                  ·
                    rfl

theorem cell22_2307709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_2307709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307709 prefixEnd_2307709 := by exact prefixLift 2307709
  have htrace : WordTrace (prefixWord ++ tailWord_2307709) baseStart_2307709 baseEnd_2307709 := by
    simpa [prefixWord, tailWord_2307709, baseEnd_2307709] using wordTrace_append hprefix tailTrace_2307709
  have hstable : (prefixWord ++ tailWord_2307709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307709).length < 2 ^ (prefixWord ++ tailWord_2307709).sum := by decide
  have hdescent : baseEnd_2307709 < baseStart_2307709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307724 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_2307724 : Nat := 118140960795 + 2307724 * 2 ^ 59
def prefixEnd_2307724 : Nat := 4983230072969 + 3 ^ 40 * 2307724 * 2
def baseEnd_2307724 : Nat := 789981086610956168624651

theorem tailTrace_2307724 : CollatzResearch.WordTrace tailWord_2307724 prefixEnd_2307724 789981086610956168624651 := by
  unfold tailWord_2307724
  simp only [CollatzResearch.WordTrace]
  refine ⟨42084804545758775363093113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56113072727678367150790817 42084804545758775363093113)
  ·
    refine ⟨31563603409319081522319835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42084804545758775363093113 31563603409319081522319835)
    ·
      refine ⟨47345405113978622283479753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31563603409319081522319835 47345405113978622283479753)
      ·
        refine ⟨35509053835483966712609815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47345405113978622283479753 35509053835483966712609815)
        ·
          refine ⟨53263580753225950068914723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35509053835483966712609815 53263580753225950068914723)
          ·
            refine ⟨79895371129838925103372085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53263580753225950068914723 79895371129838925103372085)
            ·
              refine ⟨7490191043422399228441133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79895371129838925103372085 7490191043422399228441133)
              ·
                refine ⟨2808821641283399710665425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7490191043422399228441133 2808821641283399710665425)
                ·
                  refine ⟨2106616230962549782999069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2808821641283399710665425 2106616230962549782999069)
                  ·
                    refine ⟨789981086610956168624651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106616230962549782999069 789981086610956168624651)
                    ·
                      rfl

theorem cell22_2307724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_2307724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307724 prefixEnd_2307724 := by exact prefixLift 2307724
  have htrace : WordTrace (prefixWord ++ tailWord_2307724) baseStart_2307724 baseEnd_2307724 := by
    simpa [prefixWord, tailWord_2307724, baseEnd_2307724] using wordTrace_append hprefix tailTrace_2307724
  have hstable : (prefixWord ++ tailWord_2307724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307724).length < 2 ^ (prefixWord ++ tailWord_2307724).sum := by decide
  have hdescent : baseEnd_2307724 < baseStart_2307724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307767 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2307767 : Nat := 118140960795 + 2307767 * 2 ^ 59
def prefixEnd_2307767 : Nat := 4983230072969 + 3 ^ 40 * 2307767 * 2
def baseEnd_2307767 : Nat := 789995806389718389799519

theorem tailTrace_2307767 : CollatzResearch.WordTrace tailWord_2307767 prefixEnd_2307767 789995806389718389799519 := by
  unfold tailWord_2307767
  simp only [CollatzResearch.WordTrace]
  refine ⟨84171177430361769070001555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56114118286907846046667703 84171177430361769070001555)
  ·
    refine ⟨126256766145542653605002333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84171177430361769070001555 126256766145542653605002333)
    ·
      refine ⟨47346287304578495101875875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126256766145542653605002333 47346287304578495101875875)
      ·
        refine ⟨71019430956867742652813813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47346287304578495101875875 71019430956867742652813813)
        ·
          refine ⟨6658071652206350873701295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71019430956867742652813813 6658071652206350873701295)
          ·
            refine ⟨9987107478309526310551943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658071652206350873701295 9987107478309526310551943)
            ·
              refine ⟨14980661217464289465827915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9987107478309526310551943 14980661217464289465827915)
              ·
                refine ⟨22470991826196434198741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14980661217464289465827915 22470991826196434198741873)
                ·
                  refine ⟨16853243869647325649056405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22470991826196434198741873 16853243869647325649056405)
                  ·
                    refine ⟨789995806389718389799519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16853243869647325649056405 789995806389718389799519)
                    ·
                      rfl

theorem cell22_2307767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2307767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307767 prefixEnd_2307767 := by exact prefixLift 2307767
  have htrace : WordTrace (prefixWord ++ tailWord_2307767) baseStart_2307767 baseEnd_2307767 := by
    simpa [prefixWord, tailWord_2307767, baseEnd_2307767] using wordTrace_append hprefix tailTrace_2307767
  have hstable : (prefixWord ++ tailWord_2307767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307767).length < 2 ^ (prefixWord ++ tailWord_2307767).sum := by decide
  have hdescent : baseEnd_2307767 < baseStart_2307767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307786 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_2307786 : Nat := 118140960795 + 2307786 * 2 ^ 59
def prefixEnd_2307786 : Nat := 4983230072969 + 3 ^ 40 * 2307786 * 2
def baseEnd_2307786 : Nat := 790002310478008673574461

theorem tailTrace_2307786 : CollatzResearch.WordTrace tailWord_2307786 prefixEnd_2307786 790002310478008673574461 := by
  unfold tailWord_2307786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042967604323233828735803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56114580278195290209962141 21042967604323233828735803)
  ·
    refine ⟨31564451406484850743103705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21042967604323233828735803 31564451406484850743103705)
    ·
      refine ⟨23673338554863638057327779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31564451406484850743103705 23673338554863638057327779)
      ·
        refine ⟨35510007832295457085991669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23673338554863638057327779 35510007832295457085991669)
        ·
          refine ⟨3329063234277699101811719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35510007832295457085991669 3329063234277699101811719)
          ·
            refine ⟨4993594851416548652717579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329063234277699101811719 4993594851416548652717579)
            ·
              refine ⟨7490392277124822979076369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993594851416548652717579 7490392277124822979076369)
              ·
                refine ⟨5617794207843617234307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7490392277124822979076369 5617794207843617234307277)
                ·
                  refine ⟨2106672827941356462865229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5617794207843617234307277 2106672827941356462865229)
                  ·
                    refine ⟨790002310478008673574461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106672827941356462865229 790002310478008673574461)
                    ·
                      rfl

theorem cell22_2307786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_2307786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307786 prefixEnd_2307786 := by exact prefixLift 2307786
  have htrace : WordTrace (prefixWord ++ tailWord_2307786) baseStart_2307786 baseEnd_2307786 := by
    simpa [prefixWord, tailWord_2307786, baseEnd_2307786] using wordTrace_append hprefix tailTrace_2307786
  have hstable : (prefixWord ++ tailWord_2307786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307786).length < 2 ^ (prefixWord ++ tailWord_2307786).sum := by decide
  have hdescent : baseEnd_2307786 < baseStart_2307786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307816 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_2307816 : Nat := 118140960795 + 2307816 * 2 ^ 59
def prefixEnd_2307816 : Nat := 4983230072969 + 3 ^ 40 * 2307816 * 2
def baseEnd_2307816 : Nat := 263337526697032865108123

theorem tailTrace_2307816 : CollatzResearch.WordTrace tailWord_2307816 prefixEnd_2307816 263337526697032865108123 := by
  unfold tailWord_2307816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42086482303592125219267651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56115309738122833625690201 42086482303592125219267651)
  ·
    refine ⟨63129723455388187828901477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42086482303592125219267651 63129723455388187828901477)
    ·
      refine ⟨11836823147885285217919027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63129723455388187828901477 11836823147885285217919027)
      ·
        refine ⟨17755234721827927826878541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11836823147885285217919027 17755234721827927826878541)
        ·
          refine ⟨6658213020685472935079453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17755234721827927826878541 6658213020685472935079453)
          ·
            refine ⟨2496829882757052350654795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6658213020685472935079453 2496829882757052350654795)
            ·
              refine ⟨3745244824135578525982193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496829882757052350654795 3745244824135578525982193)
              ·
                refine ⟨2808933618101683894486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745244824135578525982193 2808933618101683894486645)
                ·
                  refine ⟨263337526697032865108123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808933618101683894486645 263337526697032865108123)
                  ·
                    rfl

theorem cell22_2307816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_2307816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307816 prefixEnd_2307816 := by exact prefixLift 2307816
  have htrace : WordTrace (prefixWord ++ tailWord_2307816) baseStart_2307816 baseEnd_2307816 := by
    simpa [prefixWord, tailWord_2307816, baseEnd_2307816] using wordTrace_append hprefix tailTrace_2307816
  have hstable : (prefixWord ++ tailWord_2307816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307816).length < 2 ^ (prefixWord ++ tailWord_2307816).sum := by decide
  have hdescent : baseEnd_2307816 < baseStart_2307816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307827 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 6]
def baseStart_2307827 : Nat := 118140960795 + 2307827 * 2 ^ 59
def prefixEnd_2307827 : Nat := 4983230072969 + 3 ^ 40 * 2307827 * 2
def baseEnd_2307827 : Nat := 263338781871966077766445

theorem tailTrace_2307827 : CollatzResearch.WordTrace tailWord_2307827 prefixEnd_2307827 263338781871966077766445 := by
  unfold tailWord_2307827
  simp only [CollatzResearch.WordTrace]
  refine ⟨84173365810144399317185735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56115577206762932878123823 84173365810144399317185735)
  ·
    refine ⟨126260048715216598975778603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84173365810144399317185735 126260048715216598975778603)
    ·
      refine ⟨189390073072824898463667905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126260048715216598975778603 189390073072824898463667905)
      ·
        refine ⟨142042554804618673847750929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189390073072824898463667905 142042554804618673847750929)
        ·
          refine ⟨106531916103464005385813197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142042554804618673847750929 106531916103464005385813197)
          ·
            refine ⟨39949468538799002019679949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106531916103464005385813197 39949468538799002019679949)
            ·
              refine ⟨14981050702049625757379981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39949468538799002019679949 14981050702049625757379981)
              ·
                refine ⟨5617894013268609659017493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14981050702049625757379981 5617894013268609659017493)
                ·
                  refine ⟨263338781871966077766445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5617894013268609659017493 263338781871966077766445)
                  ·
                    rfl

theorem cell22_2307827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_2307827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307827 prefixEnd_2307827 := by exact prefixLift 2307827
  have htrace : WordTrace (prefixWord ++ tailWord_2307827) baseStart_2307827 baseEnd_2307827 := by
    simpa [prefixWord, tailWord_2307827, baseEnd_2307827] using wordTrace_append hprefix tailTrace_2307827
  have hstable : (prefixWord ++ tailWord_2307827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307827).length < 2 ^ (prefixWord ++ tailWord_2307827).sum := by decide
  have hdescent : baseEnd_2307827 < baseStart_2307827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307844 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_2307844 : Nat := 118140960795 + 2307844 * 2 ^ 59
def prefixEnd_2307844 : Nat := 4983230072969 + 3 ^ 40 * 2307844 * 2
def baseEnd_2307844 : Nat := 263340721687771951874761

theorem tailTrace_2307844 : CollatzResearch.WordTrace tailWord_2307844 prefixEnd_2307844 263340721687771951874761 := by
  unfold tailWord_2307844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42086992925541405610277293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56115990567388540813703057 42086992925541405610277293)
  ·
    refine ⟨15782622347078027103853985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42086992925541405610277293 15782622347078027103853985)
    ·
      refine ⟨11836966760308520327890489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15782622347078027103853985 11836966760308520327890489)
      ·
        refine ⟨8877725070231390245917867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11836966760308520327890489 8877725070231390245917867)
        ·
          refine ⟨13316587605347085368876801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877725070231390245917867 13316587605347085368876801)
          ·
            refine ⟨9987440704010314026657601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13316587605347085368876801 9987440704010314026657601)
            ·
              refine ⟨7490580528007735519993201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9987440704010314026657601 7490580528007735519993201)
              ·
                refine ⟨5617935396005801639994901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7490580528007735519993201 5617935396005801639994901)
                ·
                  refine ⟨263340721687771951874761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5617935396005801639994901 263340721687771951874761)
                  ·
                    rfl

theorem cell22_2307844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_2307844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307844 prefixEnd_2307844 := by exact prefixLift 2307844
  have htrace : WordTrace (prefixWord ++ tailWord_2307844) baseStart_2307844 baseEnd_2307844 := by
    simpa [prefixWord, tailWord_2307844, baseEnd_2307844] using wordTrace_append hprefix tailTrace_2307844
  have hstable : (prefixWord ++ tailWord_2307844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307844).length < 2 ^ (prefixWord ++ tailWord_2307844).sum := by decide
  have hdescent : baseEnd_2307844 < baseStart_2307844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307861 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2307861 : Nat := 118140960795 + 2307861 * 2 ^ 59
def prefixEnd_2307861 : Nat := 4983230072969 + 3 ^ 40 * 2307861 * 2
def baseEnd_2307861 : Nat := 263342661503577825983077

theorem tailTrace_2307861 : CollatzResearch.WordTrace tailWord_2307861 prefixEnd_2307861 263342661503577825983077 := by
  unfold tailWord_2307861
  simp only [CollatzResearch.WordTrace]
  refine ⟨84174605892021223123923437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56116403928014148749282291 84174605892021223123923437)
  ·
    refine ⟨31565477209507958671471289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84174605892021223123923437 31565477209507958671471289)
    ·
      refine ⟨23674107907130969003603467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31565477209507958671471289 23674107907130969003603467)
      ·
        refine ⟨35511161860696453505405201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23674107907130969003603467 35511161860696453505405201)
        ·
          refine ⟨26633371395522340129053901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35511161860696453505405201 26633371395522340129053901)
          ·
            refine ⟨9987514273320877548395213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26633371395522340129053901 9987514273320877548395213)
            ·
              refine ⟨3745317852495329080648205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9987514273320877548395213 3745317852495329080648205)
              ·
                refine ⟨1404494194685748405243077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745317852495329080648205 1404494194685748405243077)
                ·
                  refine ⟨263342661503577825983077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404494194685748405243077 263342661503577825983077)
                  ·
                    rfl

theorem cell22_2307861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2307861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307861 prefixEnd_2307861 := by exact prefixLift 2307861
  have htrace : WordTrace (prefixWord ++ tailWord_2307861) baseStart_2307861 baseEnd_2307861 := by
    simpa [prefixWord, tailWord_2307861, baseEnd_2307861] using wordTrace_append hprefix tailTrace_2307861
  have hstable : (prefixWord ++ tailWord_2307861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307861).length < 2 ^ (prefixWord ++ tailWord_2307861).sum := by decide
  have hdescent : baseEnd_2307861 < baseStart_2307861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307876 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_2307876 : Nat := 118140960795 + 2307876 * 2 ^ 59
def prefixEnd_2307876 : Nat := 4983230072969 + 3 ^ 40 * 2307876 * 2
def baseEnd_2307876 : Nat := 790033119317278438824185

theorem tailTrace_2307876 : CollatzResearch.WordTrace tailWord_2307876 prefixEnd_2307876 790033119317278438824185 := by
  unfold tailWord_2307876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42087576493483440342859741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56116768657977920457146321 42087576493483440342859741)
  ·
    refine ⟨15782841185056290128572403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42087576493483440342859741 15782841185056290128572403)
    ·
      refine ⟨23674261777584435192858605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782841185056290128572403 23674261777584435192858605)
      ·
        refine ⟨8877848166594163197321977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23674261777584435192858605 8877848166594163197321977)
        ·
          refine ⟨6658386124945622397991483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877848166594163197321977 6658386124945622397991483)
          ·
            refine ⟨9987579187418433596987225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658386124945622397991483 9987579187418433596987225)
            ·
              refine ⟨7490684390563825197740419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9987579187418433596987225 7490684390563825197740419)
              ·
                refine ⟨11236026585845737796610629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7490684390563825197740419 11236026585845737796610629)
                ·
                  refine ⟨2106754984846075836864493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11236026585845737796610629 2106754984846075836864493)
                  ·
                    refine ⟨790033119317278438824185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106754984846075836864493 790033119317278438824185)
                    ·
                      rfl

theorem cell22_2307876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_2307876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307876 prefixEnd_2307876 := by exact prefixLift 2307876
  have htrace : WordTrace (prefixWord ++ tailWord_2307876) baseStart_2307876 baseEnd_2307876 := by
    simpa [prefixWord, tailWord_2307876, baseEnd_2307876] using wordTrace_append hprefix tailTrace_2307876
  have hstable : (prefixWord ++ tailWord_2307876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307876).length < 2 ^ (prefixWord ++ tailWord_2307876).sum := by decide
  have hdescent : baseEnd_2307876 < baseStart_2307876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307889 : List Nat := [1, 2, 2, 3, 2, 3, 2, 7]
def baseStart_2307889 : Nat := 118140960795 + 2307889 * 2 ^ 59
def prefixEnd_2307889 : Nat := 4983230072969 + 3 ^ 40 * 2307889 * 2
def baseEnd_2307889 : Nat := 87781952164772304249905

theorem tailTrace_2307889 : CollatzResearch.WordTrace tailWord_2307889 prefixEnd_2307889 87781952164772304249905 := by
  unfold tailWord_2307889
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175627135919783905942721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56117084757279855937295147 84175627135919783905942721)
  ·
    refine ⟨63131720351939837929457041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84175627135919783905942721 63131720351939837929457041)
    ·
      refine ⟨47348790263954878447092781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63131720351939837929457041 47348790263954878447092781)
      ·
        refine ⟨17755796348983079417659793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47348790263954878447092781 17755796348983079417659793)
        ·
          refine ⟨13316847261737309563244845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17755796348983079417659793 13316847261737309563244845)
          ·
            refine ⟨4993817723151491086216817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13316847261737309563244845 4993817723151491086216817)
            ·
              refine ⟨3745363292363618314662613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4993817723151491086216817 3745363292363618314662613)
              ·
                refine ⟨87781952164772304249905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3745363292363618314662613 87781952164772304249905)
                ·
                  rfl

theorem cell22_2307889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 7].length) (baseStart_2307889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307889 prefixEnd_2307889 := by exact prefixLift 2307889
  have htrace : WordTrace (prefixWord ++ tailWord_2307889) baseStart_2307889 baseEnd_2307889 := by
    simpa [prefixWord, tailWord_2307889, baseEnd_2307889] using wordTrace_append hprefix tailTrace_2307889
  have hstable : (prefixWord ++ tailWord_2307889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307889).length < 2 ^ (prefixWord ++ tailWord_2307889).sum := by decide
  have hdescent : baseEnd_2307889 < baseStart_2307889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307893 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2307893 : Nat := 118140960795 + 2307893 * 2 ^ 59
def prefixEnd_2307893 : Nat := 4983230072969 + 3 ^ 40 * 2307893 * 2
def baseEnd_2307893 : Nat := 790038938764696061149133

theorem tailTrace_2307893 : CollatzResearch.WordTrace tailWord_2307893 prefixEnd_2307893 790038938764696061149133 := by
  unfold tailWord_2307893
  simp only [CollatzResearch.WordTrace]
  refine ⟨84175773027905292589088333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56117182018603528392725555 84175773027905292589088333)
  ·
    refine ⟨31565914885464484720908125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84175773027905292589088333 31565914885464484720908125)
    ·
      refine ⟨11837218082049181770340547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31565914885464484720908125 11837218082049181770340547)
      ·
        refine ⟨17755827123073772655510821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837218082049181770340547 17755827123073772655510821)
        ·
          refine ⟨3329217585576332372908279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17755827123073772655510821 3329217585576332372908279)
          ·
            refine ⟨4993826378364498559362419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329217585576332372908279 4993826378364498559362419)
            ·
              refine ⟨7490739567546747839043629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993826378364498559362419 7490739567546747839043629)
              ·
                refine ⟨2809027337830030439641361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7490739567546747839043629 2809027337830030439641361)
                ·
                  refine ⟨2106770503372522829731021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809027337830030439641361 2106770503372522829731021)
                  ·
                    refine ⟨790038938764696061149133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106770503372522829731021 790038938764696061149133)
                    ·
                      rfl

theorem cell22_2307893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2307893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307893 prefixEnd_2307893 := by exact prefixLift 2307893
  have htrace : WordTrace (prefixWord ++ tailWord_2307893) baseStart_2307893 baseEnd_2307893 := by
    simpa [prefixWord, tailWord_2307893, baseEnd_2307893] using wordTrace_append hprefix tailTrace_2307893
  have hstable : (prefixWord ++ tailWord_2307893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307893).length < 2 ^ (prefixWord ++ tailWord_2307893).sum := by decide
  have hdescent : baseEnd_2307893 < baseStart_2307893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307949 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2307949 : Nat := 118140960795 + 2307949 * 2 ^ 59
def prefixEnd_2307949 : Nat := 4983230072969 + 3 ^ 40 * 2307949 * 2
def baseEnd_2307949 : Nat := 790058108709130581748961

theorem tailTrace_2307949 : CollatzResearch.WordTrace tailWord_2307949 prefixEnd_2307949 790058108709130581748961 := by
  unfold tailWord_2307949
  simp only [CollatzResearch.WordTrace]
  refine ⟨84177815515702414153126901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56118543677134942768751267 84177815515702414153126901)
  ·
    refine ⟨7891670204597101326855647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84177815515702414153126901 7891670204597101326855647)
    ·
      refine ⟨11837505306895651990283471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891670204597101326855647 11837505306895651990283471)
      ·
        refine ⟨17756257960343477985425207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837505306895651990283471 17756257960343477985425207)
        ·
          refine ⟨26634386940515216978137811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17756257960343477985425207 26634386940515216978137811)
          ·
            refine ⟨39951580410772825467206717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26634386940515216978137811 39951580410772825467206717)
            ·
              refine ⟨14981842654039809550202519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39951580410772825467206717 14981842654039809550202519)
              ·
                refine ⟨22472763981059714325303779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14981842654039809550202519 22472763981059714325303779)
                ·
                  refine ⟨33709145971589571487955669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22472763981059714325303779 33709145971589571487955669)
                  ·
                    refine ⟨790058108709130581748961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33709145971589571487955669 790058108709130581748961)
                    ·
                      rfl

theorem cell22_2307949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2307949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307949 prefixEnd_2307949 := by exact prefixLift 2307949
  have htrace : WordTrace (prefixWord ++ tailWord_2307949) baseStart_2307949 baseEnd_2307949 := by
    simpa [prefixWord, tailWord_2307949, baseEnd_2307949] using wordTrace_append hprefix tailTrace_2307949
  have hstable : (prefixWord ++ tailWord_2307949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307949).length < 2 ^ (prefixWord ++ tailWord_2307949).sum := by decide
  have hdescent : baseEnd_2307949 < baseStart_2307949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2307996 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_2307996 : Nat := 118140960795 + 2307996 * 2 ^ 59
def prefixEnd_2307996 : Nat := 4983230072969 + 3 ^ 40 * 2307996 * 2
def baseEnd_2307996 : Nat := 263358065923212708607939

theorem tailTrace_2307996 : CollatzResearch.WordTrace tailWord_2307996 prefixEnd_2307996 263358065923212708607939 := by
  unfold tailWord_2307996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42089764873266070590043921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56119686497688094120058561 42089764873266070590043921)
  ·
    refine ⟨31567323654949552942532941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42089764873266070590043921 31567323654949552942532941)
    ·
      refine ⟨11837746370606082353449853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31567323654949552942532941 11837746370606082353449853)
      ·
        refine ⟨4439154888977280882543695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11837746370606082353449853 4439154888977280882543695)
        ·
          refine ⟨6658732333465921323815543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439154888977280882543695 6658732333465921323815543)
          ·
            refine ⟨9988098500198881985723315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658732333465921323815543 9988098500198881985723315)
            ·
              refine ⟨14982147750298322978584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9988098500198881985723315 14982147750298322978584973)
              ·
                refine ⟨5618305406361871116969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14982147750298322978584973 5618305406361871116969365)
                ·
                  refine ⟨263358065923212708607939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5618305406361871116969365 263358065923212708607939)
                  ·
                    rfl

theorem cell22_2307996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_2307996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2307996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2307996 prefixEnd_2307996 := by exact prefixLift 2307996
  have htrace : WordTrace (prefixWord ++ tailWord_2307996) baseStart_2307996 baseEnd_2307996 := by
    simpa [prefixWord, tailWord_2307996, baseEnd_2307996] using wordTrace_append hprefix tailTrace_2307996
  have hstable : (prefixWord ++ tailWord_2307996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2307996).length < 2 ^ (prefixWord ++ tailWord_2307996).sum := by decide
  have hdescent : baseEnd_2307996 < baseStart_2307996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2307996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308009 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_2308009 : Nat := 118140960795 + 2308009 * 2 ^ 59
def prefixEnd_2308009 : Nat := 4983230072969 + 3 ^ 40 * 2308009 * 2
def baseEnd_2308009 : Nat := 790078647935310425248777

theorem tailTrace_2308009 : CollatzResearch.WordTrace tailWord_2308009 prefixEnd_2308009 790078647935310425248777 := by
  unfold tailWord_2308009
  simp only [CollatzResearch.WordTrace]
  refine ⟨84180003895485044400311081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56120002596990029600207387 84180003895485044400311081)
  ·
    refine ⟨63135002921613783300233311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84180003895485044400311081 63135002921613783300233311)
    ·
      refine ⟨94702504382420674950349967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63135002921613783300233311 94702504382420674950349967)
      ·
        refine ⟨142053756573631012425524951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94702504382420674950349967 142053756573631012425524951)
        ·
          refine ⟨213080634860446518638287427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142053756573631012425524951 213080634860446518638287427)
          ·
            refine ⟨319620952290669777957431141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213080634860446518638287427 319620952290669777957431141)
            ·
              refine ⟨59928928554500583367018339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319620952290669777957431141 59928928554500583367018339)
              ·
                refine ⟨89893392831750875050527509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59928928554500583367018339 89893392831750875050527509)
                ·
                  refine ⟨4213752788988322267993477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89893392831750875050527509 4213752788988322267993477)
                  ·
                    refine ⟨790078647935310425248777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4213752788988322267993477 790078647935310425248777)
                    ·
                      rfl

theorem cell22_2308009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_2308009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308009 prefixEnd_2308009 := by exact prefixLift 2308009
  have htrace : WordTrace (prefixWord ++ tailWord_2308009) baseStart_2308009 baseEnd_2308009 := by
    simpa [prefixWord, tailWord_2308009, baseEnd_2308009] using wordTrace_append hprefix tailTrace_2308009
  have hstable : (prefixWord ++ tailWord_2308009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308009).length < 2 ^ (prefixWord ++ tailWord_2308009).sum := by decide
  have hdescent : baseEnd_2308009 < baseStart_2308009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308024 : List Nat := [2, 1, 2, 1, 2, 3, 3, 8]
def baseStart_2308024 : Nat := 118140960795 + 2308024 * 2 ^ 59
def prefixEnd_2308024 : Nat := 4983230072969 + 3 ^ 40 * 2308024 * 2
def baseEnd_2308024 : Nat := 87787086971317265124859

theorem tailTrace_2308024 : CollatzResearch.WordTrace tailWord_2308024 prefixEnd_2308024 87787086971317265124859 := by
  unfold tailWord_2308024
  simp only [CollatzResearch.WordTrace]
  refine ⟨42090275495215350981053563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56120367326953801308071417 42090275495215350981053563)
  ·
    refine ⟨63135413242823026471580345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42090275495215350981053563 63135413242823026471580345)
    ·
      refine ⟨47351559932117269853685259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63135413242823026471580345 47351559932117269853685259)
      ·
        refine ⟨71027339898175904780527889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47351559932117269853685259 71027339898175904780527889)
        ·
          refine ⟨53270504923631928585395917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71027339898175904780527889 53270504923631928585395917)
          ·
            refine ⟨19976439346361973219523469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53270504923631928585395917 19976439346361973219523469)
            ·
              refine ⟨7491164754885739957321301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19976439346361973219523469 7491164754885739957321301)
              ·
                refine ⟨87787086971317265124859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7491164754885739957321301 87787086971317265124859)
                ·
                  rfl

theorem cell22_2308024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_2308024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308024 prefixEnd_2308024 := by exact prefixLift 2308024
  have htrace : WordTrace (prefixWord ++ tailWord_2308024) baseStart_2308024 baseEnd_2308024 := by
    simpa [prefixWord, tailWord_2308024, baseEnd_2308024] using wordTrace_append hprefix tailTrace_2308024
  have hstable : (prefixWord ++ tailWord_2308024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308024).length < 2 ^ (prefixWord ++ tailWord_2308024).sum := by decide
  have hdescent : baseEnd_2308024 < baseStart_2308024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308030 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2308030 : Nat := 118140960795 + 2308030 * 2 ^ 59
def prefixEnd_2308030 : Nat := 4983230072969 + 3 ^ 40 * 2308030 * 2
def baseEnd_2308030 : Nat := 263361945554824456824571

theorem tailTrace_2308030 : CollatzResearch.WordTrace tailWord_2308030 prefixEnd_2308030 263361945554824456824571 := by
  unfold tailWord_2308030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522596228551120623353193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56120513218939309991217029 10522596228551120623353193)
  ·
    refine ⟨7891947171413340467514895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10522596228551120623353193 7891947171413340467514895)
    ·
      refine ⟨11837920757120010701272343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891947171413340467514895 11837920757120010701272343)
      ·
        refine ⟨17756881135680016051908515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11837920757120010701272343 17756881135680016051908515)
        ·
          refine ⟨26635321703520024077862773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17756881135680016051908515 26635321703520024077862773)
          ·
            refine ⟨2497061409705002257299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26635321703520024077862773 2497061409705002257299635)
            ·
              refine ⟨3745592114557503385949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497061409705002257299635 3745592114557503385949453)
              ·
                refine ⟨1404597042959063769731045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745592114557503385949453 1404597042959063769731045)
                ·
                  refine ⟨263361945554824456824571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404597042959063769731045 263361945554824456824571)
                  ·
                    rfl

theorem cell22_2308030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2308030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308030 prefixEnd_2308030 := by exact prefixLift 2308030
  have htrace : WordTrace (prefixWord ++ tailWord_2308030) baseStart_2308030 baseEnd_2308030 := by
    simpa [prefixWord, tailWord_2308030, baseEnd_2308030] using wordTrace_append hprefix tailTrace_2308030
  have hstable : (prefixWord ++ tailWord_2308030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308030).length < 2 ^ (prefixWord ++ tailWord_2308030).sum := by decide
  have hdescent : baseEnd_2308030 < baseStart_2308030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308103 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 5]
def baseStart_2308103 : Nat := 118140960795 + 2308103 * 2 ^ 59
def prefixEnd_2308103 : Nat := 4983230072969 + 3 ^ 40 * 2308103 * 2
def baseEnd_2308103 : Nat := 263370275352108504466163

theorem tailTrace_2308103 : CollatzResearch.WordTrace tailWord_2308103 prefixEnd_2308103 263370275352108504466163 := by
  unfold tailWord_2308103
  simp only [CollatzResearch.WordTrace]
  refine ⟨84183432357144498454232963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56122288238096332302821975 84183432357144498454232963)
  ·
    refine ⟨126275148535716747681349445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84183432357144498454232963 126275148535716747681349445)
    ·
      refine ⟨23676590350446890190253021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126275148535716747681349445 23676590350446890190253021)
      ·
        refine ⟨8878721381417583821344883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23676590350446890190253021 8878721381417583821344883)
        ·
          refine ⟨13318082072126375732017325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8878721381417583821344883 13318082072126375732017325)
          ·
            refine ⟨4994280777047390899506497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13318082072126375732017325 4994280777047390899506497)
            ·
              refine ⟨3745710582785543174629873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994280777047390899506497 3745710582785543174629873)
              ·
                refine ⟨2809282937089157380972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3745710582785543174629873 2809282937089157380972405)
                ·
                  refine ⟨263370275352108504466163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2809282937089157380972405 263370275352108504466163)
                  ·
                    rfl

theorem cell22_2308103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].length) (baseStart_2308103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308103 prefixEnd_2308103 := by exact prefixLift 2308103
  have htrace : WordTrace (prefixWord ++ tailWord_2308103) baseStart_2308103 baseEnd_2308103 := by
    simpa [prefixWord, tailWord_2308103, baseEnd_2308103] using wordTrace_append hprefix tailTrace_2308103
  have hstable : (prefixWord ++ tailWord_2308103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308103).length < 2 ^ (prefixWord ++ tailWord_2308103).sum := by decide
  have hdescent : baseEnd_2308103 < baseStart_2308103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308109 : List Nat := [1, 7, 1, 2, 2, 1, 1, 7]
def baseStart_2308109 : Nat := 118140960795 + 2308109 * 2 ^ 59
def prefixEnd_2308109 : Nat := 4983230072969 + 3 ^ 40 * 2308109 * 2
def baseEnd_2308109 : Nat := 87790319997660388638719

theorem tailTrace_2308109 : CollatzResearch.WordTrace tailWord_2308109 prefixEnd_2308109 87790319997660388638719 := by
  unfold tailWord_2308109
  simp only [CollatzResearch.WordTrace]
  refine ⟨84183651195122761478951381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56122434130081840985967587 84183651195122761478951381)
  ·
    refine ⟨1973054324885689722162923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84183651195122761478951381 1973054324885689722162923)
    ·
      refine ⟨2959581487328534583244385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973054324885689722162923 2959581487328534583244385)
      ·
        refine ⟨2219686115496400937433289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959581487328534583244385 2219686115496400937433289)
        ·
          refine ⟨1664764586622300703074967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219686115496400937433289 1664764586622300703074967)
          ·
            refine ⟨2497146879933451054612451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664764586622300703074967 2497146879933451054612451)
            ·
              refine ⟨3745720319900176581918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497146879933451054612451 3745720319900176581918677)
              ·
                refine ⟨87790319997660388638719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3745720319900176581918677 87790319997660388638719)
                ·
                  rfl

theorem cell22_2308109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 7].length) (baseStart_2308109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308109 prefixEnd_2308109 := by exact prefixLift 2308109
  have htrace : WordTrace (prefixWord ++ tailWord_2308109) baseStart_2308109 baseEnd_2308109 := by
    simpa [prefixWord, tailWord_2308109, baseEnd_2308109] using wordTrace_append hprefix tailTrace_2308109
  have hstable : (prefixWord ++ tailWord_2308109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308109).length < 2 ^ (prefixWord ++ tailWord_2308109).sum := by decide
  have hdescent : baseEnd_2308109 < baseStart_2308109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308131 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 6]
def baseStart_2308131 : Nat := 118140960795 + 2308131 * 2 ^ 59
def prefixEnd_2308131 : Nat := 4983230072969 + 3 ^ 40 * 2308131 * 2
def baseEnd_2308131 : Nat := 263373470342847591232801

theorem tailTrace_2308131 : CollatzResearch.WordTrace tailWord_2308131 prefixEnd_2308131 263373470342847591232801 := by
  unfold tailWord_2308131
  simp only [CollatzResearch.WordTrace]
  refine ⟨84184453601043059236252247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56122969067362039490834831 84184453601043059236252247)
  ·
    refine ⟨126276680401564588854378371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84184453601043059236252247 126276680401564588854378371)
    ·
      refine ⟨189415020602346883281567557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126276680401564588854378371 189415020602346883281567557)
      ·
        refine ⟨35515316362940040615293917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189415020602346883281567557 35515316362940040615293917)
        ·
          refine ⟨13318243636102515230735219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35515316362940040615293917 13318243636102515230735219)
          ·
            refine ⟨19977365454153772846102829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13318243636102515230735219 19977365454153772846102829)
            ·
              refine ⟨7491512045307664817288561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19977365454153772846102829 7491512045307664817288561)
              ·
                refine ⟨5618634033980748612966421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7491512045307664817288561 5618634033980748612966421)
                ·
                  refine ⟨263373470342847591232801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5618634033980748612966421 263373470342847591232801)
                  ·
                    rfl

theorem cell22_2308131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_2308131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308131 prefixEnd_2308131 := by exact prefixLift 2308131
  have htrace : WordTrace (prefixWord ++ tailWord_2308131) baseStart_2308131 baseEnd_2308131 := by
    simpa [prefixWord, tailWord_2308131, baseEnd_2308131] using wordTrace_append hprefix tailTrace_2308131
  have hstable : (prefixWord ++ tailWord_2308131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308131).length < 2 ^ (prefixWord ++ tailWord_2308131).sum := by decide
  have hdescent : baseEnd_2308131 < baseStart_2308131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308150 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2308150 : Nat := 118140960795 + 2308150 * 2 ^ 59
def prefixEnd_2308150 : Nat := 4983230072969 + 3 ^ 40 * 2308150 * 2
def baseEnd_2308150 : Nat := 790126915116833057473345

theorem tailTrace_2308150 : CollatzResearch.WordTrace tailWord_2308150 prefixEnd_2308150 790126915116833057473345 := by
  unfold tailWord_2308150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261571661748389092574619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56123431058649483654129269 5261571661748389092574619)
  ·
    refine ⟨7892357492622583638861929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5261571661748389092574619 7892357492622583638861929)
    ·
      refine ⟨5919268119466937729146447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7892357492622583638861929 5919268119466937729146447)
      ·
        refine ⟨8878902179200406593719671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919268119466937729146447 8878902179200406593719671)
        ·
          refine ⟨13318353268800609890579507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8878902179200406593719671 13318353268800609890579507)
          ·
            refine ⟨19977529903200914835869261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13318353268800609890579507 19977529903200914835869261)
            ·
              refine ⟨7491573713700343063450973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19977529903200914835869261 7491573713700343063450973)
              ·
                refine ⟨2809340142637628648794115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7491573713700343063450973 2809340142637628648794115)
                ·
                  refine ⟨4214010213956442973191173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2809340142637628648794115 4214010213956442973191173)
                  ·
                    refine ⟨790126915116833057473345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214010213956442973191173 790126915116833057473345)
                    ·
                      rfl

theorem cell22_2308150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2308150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308150 prefixEnd_2308150 := by exact prefixLift 2308150
  have htrace : WordTrace (prefixWord ++ tailWord_2308150) baseStart_2308150 baseEnd_2308150 := by
    simpa [prefixWord, tailWord_2308150, baseEnd_2308150] using wordTrace_append hprefix tailTrace_2308150
  have hstable : (prefixWord ++ tailWord_2308150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308150).length < 2 ^ (prefixWord ++ tailWord_2308150).sum := by decide
  have hdescent : baseEnd_2308150 < baseStart_2308150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308163 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 2, 3]
def baseStart_2308163 : Nat := 118140960795 + 2308163 * 2 ^ 59
def prefixEnd_2308163 : Nat := 4983230072969 + 3 ^ 40 * 2308163 * 2
def baseEnd_2308163 : Nat := 790131365282505356898305

theorem tailTrace_2308163 : CollatzResearch.WordTrace tailWord_2308163 prefixEnd_2308163 790131365282505356898305 := by
  unfold tailWord_2308163
  simp only [CollatzResearch.WordTrace]
  refine ⟨84185620736927128701417143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56123747157951419134278095 84185620736927128701417143)
  ·
    refine ⟨126278431105390693052125715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84185620736927128701417143 126278431105390693052125715)
    ·
      refine ⟨189417646658086039578188573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126278431105390693052125715 189417646658086039578188573)
      ·
        refine ⟨71031617496782264841820715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189417646658086039578188573 71031617496782264841820715)
        ·
          refine ⟨106547426245173397262731073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71031617496782264841820715 106547426245173397262731073)
          ·
            refine ⟨79910569683880047947048305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106547426245173397262731073 79910569683880047947048305)
            ·
              refine ⟨59932927262910035960286229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79910569683880047947048305 59932927262910035960286229)
              ·
                refine ⟨2809355965448907935638417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59932927262910035960286229 2809355965448907935638417)
                ·
                  refine ⟨2107016974086680951728813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809355965448907935638417 2107016974086680951728813)
                  ·
                    refine ⟨790131365282505356898305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107016974086680951728813 790131365282505356898305)
                    ·
                      rfl

theorem cell22_2308163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].length) (baseStart_2308163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308163 prefixEnd_2308163 := by exact prefixLift 2308163
  have htrace : WordTrace (prefixWord ++ tailWord_2308163) baseStart_2308163 baseEnd_2308163 := by
    simpa [prefixWord, tailWord_2308163, baseEnd_2308163] using wordTrace_append hprefix tailTrace_2308163
  have hstable : (prefixWord ++ tailWord_2308163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308163).length < 2 ^ (prefixWord ++ tailWord_2308163).sum := by decide
  have hdescent : baseEnd_2308163 < baseStart_2308163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308317 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2308317 : Nat := 118140960795 + 2308317 * 2 ^ 59
def prefixEnd_2308317 : Nat := 4983230072969 + 3 ^ 40 * 2308317 * 2
def baseEnd_2308317 : Nat := 263394694209900096182611

theorem tailTrace_2308317 : CollatzResearch.WordTrace tailWord_2308317 prefixEnd_2308317 263394694209900096182611 := by
  unfold tailWord_2308317
  simp only [CollatzResearch.WordTrace]
  refine ⟨84191237578369213002523205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56127491718912808668348803 84191237578369213002523205)
  ·
    refine ⟨15785857045944227437973101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84191237578369213002523205 15785857045944227437973101)
    ·
      refine ⟨5919696392229085289239913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15785857045944227437973101 5919696392229085289239913)
      ·
        refine ⟨4439772294171813966929935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5919696392229085289239913 4439772294171813966929935)
        ·
          refine ⟨6659658441257720950394903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439772294171813966929935 6659658441257720950394903)
          ·
            refine ⟨9989487661886581425592355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6659658441257720950394903 9989487661886581425592355)
            ·
              refine ⟨14984231492829872138388533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9989487661886581425592355 14984231492829872138388533)
              ·
                refine ⟨1404771702452800512973925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14984231492829872138388533 1404771702452800512973925)
                ·
                  refine ⟨263394694209900096182611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404771702452800512973925 263394694209900096182611)
                  ·
                    rfl

theorem cell22_2308317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2308317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308317 prefixEnd_2308317 := by exact prefixLift 2308317
  have htrace : WordTrace (prefixWord ++ tailWord_2308317) baseStart_2308317 baseEnd_2308317 := by
    simpa [prefixWord, tailWord_2308317, baseEnd_2308317] using wordTrace_append hprefix tailTrace_2308317
  have hstable : (prefixWord ++ tailWord_2308317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308317).length < 2 ^ (prefixWord ++ tailWord_2308317).sum := by decide
  have hdescent : baseEnd_2308317 < baseStart_2308317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308328 : List Nat := [2, 1, 4, 1, 2, 3, 9]
def baseStart_2308328 : Nat := 118140960795 + 2308328 * 2 ^ 59
def prefixEnd_2308328 : Nat := 4983230072969 + 3 ^ 40 * 2308328 * 2
def baseEnd_2308328 : Nat := 29266216598314812093437

theorem tailTrace_2308328 : CollatzResearch.WordTrace tailWord_2308328 prefixEnd_2308328 29266216598314812093437 := by
  unfold tailWord_2308328
  simp only [CollatzResearch.WordTrace]
  refine ⟨42095819390664680940586819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56127759187552907920782425 42095819390664680940586819)
  ·
    refine ⟨63143729085997021410880229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42095819390664680940586819 63143729085997021410880229)
    ·
      refine ⟨11839449203624441514540043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63143729085997021410880229 11839449203624441514540043)
      ·
        refine ⟨17759173805436662271810065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11839449203624441514540043 17759173805436662271810065)
        ·
          refine ⟨13319380354077496703857549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17759173805436662271810065 13319380354077496703857549)
          ·
            refine ⟨4994767632779061263946581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13319380354077496703857549 4994767632779061263946581)
            ·
              refine ⟨29266216598314812093437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4994767632779061263946581 29266216598314812093437)
              ·
                rfl

theorem cell22_2308328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 9].length) (baseStart_2308328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308328 prefixEnd_2308328 := by exact prefixLift 2308328
  have htrace : WordTrace (prefixWord ++ tailWord_2308328) baseStart_2308328 baseEnd_2308328 := by
    simpa [prefixWord, tailWord_2308328, baseEnd_2308328] using wordTrace_append hprefix tailTrace_2308328
  have hstable : (prefixWord ++ tailWord_2308328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308328).length < 2 ^ (prefixWord ++ tailWord_2308328).sum := by decide
  have hdescent : baseEnd_2308328 < baseStart_2308328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308373 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 7]
def baseStart_2308373 : Nat := 118140960795 + 2308373 * 2 ^ 59
def prefixEnd_2308373 : Nat := 4983230072969 + 3 ^ 40 * 2308373 * 2
def baseEnd_2308373 : Nat := 263401084191378269715887

theorem tailTrace_2308373 : CollatzResearch.WordTrace tailWord_2308373 prefixEnd_2308373 263401084191378269715887 := by
  unfold tailWord_2308373
  simp only [CollatzResearch.WordTrace]
  refine ⟨84193280066166334566561773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56128853377444223044374515 84193280066166334566561773)
  ·
    refine ⟨31572480024812375462460665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84193280066166334566561773 31572480024812375462460665)
    ·
      refine ⟨23679360018609281596845499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31572480024812375462460665 23679360018609281596845499)
      ·
        refine ⟨35519040027913922395268249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23679360018609281596845499 35519040027913922395268249)
        ·
          refine ⟨26639280020935441796451187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35519040027913922395268249 26639280020935441796451187)
          ·
            refine ⟨39958920031403162694676781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26639280020935441796451187 39958920031403162694676781)
            ·
              refine ⟨14984595011776186010503793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39958920031403162694676781 14984595011776186010503793)
              ·
                refine ⟨11238446258832139507877845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14984595011776186010503793 11238446258832139507877845)
                ·
                  refine ⟨263401084191378269715887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11238446258832139507877845 263401084191378269715887)
                  ·
                    rfl

theorem cell22_2308373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_2308373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308373 prefixEnd_2308373 := by exact prefixLift 2308373
  have htrace : WordTrace (prefixWord ++ tailWord_2308373) baseStart_2308373 baseEnd_2308373 := by
    simpa [prefixWord, tailWord_2308373, baseEnd_2308373] using wordTrace_append hprefix tailTrace_2308373
  have hstable : (prefixWord ++ tailWord_2308373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308373).length < 2 ^ (prefixWord ++ tailWord_2308373).sum := by decide
  have hdescent : baseEnd_2308373 < baseStart_2308373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308452 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_2308452 : Nat := 118140960795 + 2308452 * 2 ^ 59
def prefixEnd_2308452 : Nat := 4983230072969 + 3 ^ 40 * 2308452 * 2
def baseEnd_2308452 : Nat := 263410098629534978807473

theorem tailTrace_2308452 : CollatzResearch.WordTrace tailWord_2308452 prefixEnd_2308452 263410098629534978807473 := by
  unfold tailWord_2308452
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098080716440065529343805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56130774288586754039125073 42098080716440065529343805)
  ·
    refine ⟨15786780268665024573503927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42098080716440065529343805 15786780268665024573503927)
    ·
      refine ⟨23680170402997536860255891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15786780268665024573503927 23680170402997536860255891)
      ·
        refine ⟨35520255604496305290383837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23680170402997536860255891 35520255604496305290383837)
        ·
          refine ⟨13320095851686114483893939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35520255604496305290383837 13320095851686114483893939)
          ·
            refine ⟨19980143777529171725840909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13320095851686114483893939 19980143777529171725840909)
            ·
              refine ⟨7492553916573439397190341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19980143777529171725840909 7492553916573439397190341)
              ·
                refine ⟨1404853859357519886973189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7492553916573439397190341 1404853859357519886973189)
                ·
                  refine ⟨263410098629534978807473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404853859357519886973189 263410098629534978807473)
                  ·
                    rfl

theorem cell22_2308452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_2308452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308452 prefixEnd_2308452 := by exact prefixLift 2308452
  have htrace : WordTrace (prefixWord ++ tailWord_2308452) baseStart_2308452 baseEnd_2308452 := by
    simpa [prefixWord, tailWord_2308452, baseEnd_2308452] using wordTrace_append hprefix tailTrace_2308452
  have hstable : (prefixWord ++ tailWord_2308452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308452).length < 2 ^ (prefixWord ++ tailWord_2308452).sum := by decide
  have hdescent : baseEnd_2308452 < baseStart_2308452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308463 : List Nat := [1, 1, 2, 1, 3, 1, 2, 11]
def baseStart_2308463 : Nat := 118140960795 + 2308463 * 2 ^ 59
def prefixEnd_2308463 : Nat := 4983230072969 + 3 ^ 40 * 2308463 * 2
def baseEnd_2308463 : Nat := 87803784601489397155265

theorem tailTrace_2308463 : CollatzResearch.WordTrace tailWord_2308463 prefixEnd_2308463 87803784601489397155265 := by
  unfold tailWord_2308463
  simp only [CollatzResearch.WordTrace]
  refine ⟨84196562635840279937338043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56131041757226853291558695 84196562635840279937338043)
  ·
    refine ⟨126294843953760419906007065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84196562635840279937338043 126294843953760419906007065)
    ·
      refine ⟨94721132965320314929505299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126294843953760419906007065 94721132965320314929505299)
      ·
        refine ⟨142081699447980472394257949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94721132965320314929505299 142081699447980472394257949)
        ·
          refine ⟨53280637292992677147846731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142081699447980472394257949 53280637292992677147846731)
          ·
            refine ⟨79920955939489015721770097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53280637292992677147846731 79920955939489015721770097)
            ·
              refine ⟨59940716954616761791327573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79920955939489015721770097 59940716954616761791327573)
              ·
                refine ⟨87803784601489397155265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59940716954616761791327573 87803784601489397155265)
                ·
                  rfl

theorem cell22_2308463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 11].length) (baseStart_2308463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308463 prefixEnd_2308463 := by exact prefixLift 2308463
  have htrace : WordTrace (prefixWord ++ tailWord_2308463) baseStart_2308463 baseEnd_2308463 := by
    simpa [prefixWord, tailWord_2308463, baseEnd_2308463] using wordTrace_append hprefix tailTrace_2308463
  have hstable : (prefixWord ++ tailWord_2308463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308463).length < 2 ^ (prefixWord ++ tailWord_2308463).sum := by decide
  have hdescent : baseEnd_2308463 < baseStart_2308463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308512 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_2308512 : Nat := 118140960795 + 2308512 * 2 ^ 59
def prefixEnd_2308512 : Nat := 4983230072969 + 3 ^ 40 * 2308512 * 2
def baseEnd_2308512 : Nat := 790250835114784779922235

theorem tailTrace_2308512 : CollatzResearch.WordTrace tailWord_2308512 prefixEnd_2308512 790250835114784779922235 := by
  unfold tailWord_2308512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42099174906331380652935895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56132233208441840870581193 42099174906331380652935895)
  ·
    refine ⟨63148762359497070979403843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42099174906331380652935895 63148762359497070979403843)
    ·
      refine ⟨94723143539245606469105765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63148762359497070979403843 94723143539245606469105765)
      ·
        refine ⟨17760589413608551212957331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94723143539245606469105765 17760589413608551212957331)
        ·
          refine ⟨26640884120412826819435997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17760589413608551212957331 26640884120412826819435997)
          ·
            refine ⟨9990331545154810057288499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26640884120412826819435997 9990331545154810057288499)
            ·
              refine ⟨14985497317732215085932749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990331545154810057288499 14985497317732215085932749)
              ·
                refine ⟨5619561494149580657224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14985497317732215085932749 5619561494149580657224781)
                ·
                  refine ⟨2107335560306092746459293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5619561494149580657224781 2107335560306092746459293)
                  ·
                    refine ⟨790250835114784779922235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107335560306092746459293 790250835114784779922235)
                    ·
                      rfl

theorem cell22_2308512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_2308512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308512 prefixEnd_2308512 := by exact prefixLift 2308512
  have htrace : WordTrace (prefixWord ++ tailWord_2308512) baseStart_2308512 baseEnd_2308512 := by
    simpa [prefixWord, tailWord_2308512, baseEnd_2308512] using wordTrace_append hprefix tailTrace_2308512
  have hstable : (prefixWord ++ tailWord_2308512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308512).length < 2 ^ (prefixWord ++ tailWord_2308512).sum := by decide
  have hdescent : baseEnd_2308512 < baseStart_2308512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_2308555 : Nat := 118140960795 + 2308555 * 2 ^ 59
def prefixEnd_2308555 : Nat := 4983230072969 + 3 ^ 40 * 2308555 * 2
def baseEnd_2308555 : Nat := 790265554893547001097103

theorem tailTrace_2308555 : CollatzResearch.WordTrace tailWord_2308555 prefixEnd_2308555 790265554893547001097103 := by
  unfold tailWord_2308555
  simp only [CollatzResearch.WordTrace]
  refine ⟨84199918151506979649687119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56133278767671319766458079 84199918151506979649687119)
  ·
    refine ⟨126299877227260469474530679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84199918151506979649687119 126299877227260469474530679)
    ·
      refine ⟨189449815840890704211796019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126299877227260469474530679 189449815840890704211796019)
      ·
        refine ⟨284174723761336056317694029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189449815840890704211796019 284174723761336056317694029)
        ·
          refine ⟨106565521410501021119135261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284174723761336056317694029 106565521410501021119135261)
          ·
            refine ⟨39962070528937882919675723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106565521410501021119135261 39962070528937882919675723)
            ·
              refine ⟨59943105793406824379513585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39962070528937882919675723 59943105793406824379513585)
              ·
                refine ⟨44957329345055118284635189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59943105793406824379513585 44957329345055118284635189)
                ·
                  refine ⟨4214749626098917339184549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44957329345055118284635189 4214749626098917339184549)
                  ·
                    refine ⟨790265554893547001097103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214749626098917339184549 790265554893547001097103)
                    ·
                      rfl

theorem cell22_2308555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_2308555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308555 prefixEnd_2308555 := by exact prefixLift 2308555
  have htrace : WordTrace (prefixWord ++ tailWord_2308555) baseStart_2308555 baseEnd_2308555 := by
    simpa [prefixWord, tailWord_2308555, baseEnd_2308555] using wordTrace_append hprefix tailTrace_2308555
  have hstable : (prefixWord ++ tailWord_2308555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308555).length < 2 ^ (prefixWord ++ tailWord_2308555).sum := by decide
  have hdescent : baseEnd_2308555 < baseStart_2308555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308589 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2308589 : Nat := 118140960795 + 2308589 * 2 ^ 59
def prefixEnd_2308589 : Nat := 4983230072969 + 3 ^ 40 * 2308589 * 2
def baseEnd_2308589 : Nat := 790277193788382245746999

theorem tailTrace_2308589 : CollatzResearch.WordTrace tailWord_2308589 prefixEnd_2308589 790277193788382245746999 := by
  unfold tailWord_2308589
  simp only [CollatzResearch.WordTrace]
  refine ⟨84201158233383803456424821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56134105488922535637616547 84201158233383803456424821)
  ·
    refine ⟨7893858584379731574039827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84201158233383803456424821 7893858584379731574039827)
    ·
      refine ⟨11840787876569597361059741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893858584379731574039827 11840787876569597361059741)
      ·
        refine ⟨4440295453713599010397403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11840787876569597361059741 4440295453713599010397403)
        ·
          refine ⟨6660443180570398515596105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440295453713599010397403 6660443180570398515596105)
          ·
            refine ⟨4995332385427798886697079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6660443180570398515596105 4995332385427798886697079)
            ·
              refine ⟨7492998578141698330045619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995332385427798886697079 7492998578141698330045619)
              ·
                refine ⟨11239497867212547495068429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492998578141698330045619 11239497867212547495068429)
                ·
                  refine ⟨4214811700204705310650661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11239497867212547495068429 4214811700204705310650661)
                  ·
                    refine ⟨790277193788382245746999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4214811700204705310650661 790277193788382245746999)
                    ·
                      rfl

theorem cell22_2308589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2308589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308589 prefixEnd_2308589 := by exact prefixLift 2308589
  have htrace : WordTrace (prefixWord ++ tailWord_2308589) baseStart_2308589 baseEnd_2308589 := by
    simpa [prefixWord, tailWord_2308589, baseEnd_2308589] using wordTrace_append hprefix tailTrace_2308589
  have hstable : (prefixWord ++ tailWord_2308589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308589).length < 2 ^ (prefixWord ++ tailWord_2308589).sum := by decide
  have hdescent : baseEnd_2308589 < baseStart_2308589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308602 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_2308602 : Nat := 118140960795 + 2308602 * 2 ^ 59
def prefixEnd_2308602 : Nat := 4983230072969 + 3 ^ 40 * 2308602 * 2
def baseEnd_2308602 : Nat := 790281643954054545171959

theorem tailTrace_2308602 : CollatzResearch.WordTrace tailWord_2308602 prefixEnd_2308602 790281643954054545171959 := by
  unfold tailWord_2308602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050408095584176669162015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56134421588224471117765373 21050408095584176669162015)
  ·
    refine ⟨31575612143376265003743023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21050408095584176669162015 31575612143376265003743023)
    ·
      refine ⟨47363418215064397505614535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31575612143376265003743023 47363418215064397505614535)
      ·
        refine ⟨71045127322596596258421803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47363418215064397505614535 71045127322596596258421803)
        ·
          refine ⟨106567690983894894387632705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71045127322596596258421803 106567690983894894387632705)
          ·
            refine ⟨79925768237921170790724529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106567690983894894387632705 79925768237921170790724529)
            ·
              refine ⟨59944326178440878093043397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79925768237921170790724529 59944326178440878093043397)
              ·
                refine ⟨11239561158457664642445637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59944326178440878093043397 11239561158457664642445637)
                ·
                  refine ⟨2107417717210812120458557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11239561158457664642445637 2107417717210812120458557)
                  ·
                    refine ⟨790281643954054545171959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107417717210812120458557 790281643954054545171959)
                    ·
                      rfl

theorem cell22_2308602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_2308602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308602 prefixEnd_2308602 := by exact prefixLift 2308602
  have htrace : WordTrace (prefixWord ++ tailWord_2308602) baseStart_2308602 baseEnd_2308602 := by
    simpa [prefixWord, tailWord_2308602, baseEnd_2308602] using wordTrace_append hprefix tailTrace_2308602
  have hstable : (prefixWord ++ tailWord_2308602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308602).length < 2 ^ (prefixWord ++ tailWord_2308602).sum := by decide
  have hdescent : baseEnd_2308602 < baseStart_2308602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308614 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2308614 : Nat := 118140960795 + 2308614 * 2 ^ 59
def prefixEnd_2308614 : Nat := 4983230072969 + 3 ^ 40 * 2308614 * 2
def baseEnd_2308614 : Nat := 790285751799290513871923

theorem tailTrace_2308614 : CollatzResearch.WordTrace tailWord_2308614 prefixEnd_2308614 790285751799290513871923 := by
  unfold tailWord_2308614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631314689321663522690153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56134713372195488484056597 2631314689321663522690153)
  ·
    refine ⟨1973486016991247642017615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2631314689321663522690153 1973486016991247642017615)
    ·
      refine ⟨2960229025486871463026423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973486016991247642017615 2960229025486871463026423)
      ·
        refine ⟨4440343538230307194539635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960229025486871463026423 4440343538230307194539635)
        ·
          refine ⟨6660515307345460791809453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440343538230307194539635 6660515307345460791809453)
          ·
            refine ⟨2497693240254547796928545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6660515307345460791809453 2497693240254547796928545)
            ·
              refine ⟨1873269930190910847696409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497693240254547796928545 1873269930190910847696409)
              ·
                refine ⟨1404952447643183135772307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873269930190910847696409 1404952447643183135772307)
                ·
                  refine ⟨2107428671464774703658461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404952447643183135772307 2107428671464774703658461)
                  ·
                    refine ⟨790285751799290513871923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107428671464774703658461 790285751799290513871923)
                    ·
                      rfl

theorem cell22_2308614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2308614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308614 prefixEnd_2308614 := by exact prefixLift 2308614
  have htrace : WordTrace (prefixWord ++ tailWord_2308614) baseStart_2308614 baseEnd_2308614 := by
    simpa [prefixWord, tailWord_2308614, baseEnd_2308614] using wordTrace_append hprefix tailTrace_2308614
  have hstable : (prefixWord ++ tailWord_2308614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308614).length < 2 ^ (prefixWord ++ tailWord_2308614).sum := by decide
  have hdescent : baseEnd_2308614 < baseStart_2308614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308615 : List Nat := [1, 1, 4, 3, 13]
def baseStart_2308615 : Nat := 118140960795 + 2308615 * 2 ^ 59
def prefixEnd_2308615 : Nat := 4983230072969 + 3 ^ 40 * 2308615 * 2
def baseEnd_2308615 : Nat := 3252206148640851212333

theorem tailTrace_2308615 : CollatzResearch.WordTrace tailWord_2308615 prefixEnd_2308615 3252206148640851212333 := by
  unfold tailWord_2308615
  simp only [CollatzResearch.WordTrace]
  refine ⟨84202106531289609896871299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56134737687526406597914199 84202106531289609896871299)
  ·
    refine ⟨126303159796934414845306949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84202106531289609896871299 126303159796934414845306949)
    ·
      refine ⟨23681842461925202783495053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126303159796934414845306949 23681842461925202783495053)
      ·
        refine ⟨8880690923221951043810645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23681842461925202783495053 8880690923221951043810645)
        ·
          refine ⟨3252206148640851212333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8880690923221951043810645 3252206148640851212333)
          ·
            rfl

theorem cell22_2308615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 13].length) (baseStart_2308615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308615 prefixEnd_2308615 := by exact prefixLift 2308615
  have htrace : WordTrace (prefixWord ++ tailWord_2308615) baseStart_2308615 baseEnd_2308615 := by
    simpa [prefixWord, tailWord_2308615, baseEnd_2308615] using wordTrace_append hprefix tailTrace_2308615
  have hstable : (prefixWord ++ tailWord_2308615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308615).length < 2 ^ (prefixWord ++ tailWord_2308615).sum := by decide
  have hdescent : baseEnd_2308615 < baseStart_2308615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308619 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 2, 3]
def baseStart_2308619 : Nat := 118140960795 + 2308619 * 2 ^ 59
def prefixEnd_2308619 : Nat := 4983230072969 + 3 ^ 40 * 2308619 * 2
def baseEnd_2308619 : Nat := 790287463401472167496907

theorem tailTrace_2308619 : CollatzResearch.WordTrace tailWord_2308619 prefixEnd_2308619 790287463401472167496907 := by
  unfold tailWord_2308619
  simp only [CollatzResearch.WordTrace]
  refine ⟨84202252423275118580016911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56134834948850079053344607 84202252423275118580016911)
  ·
    refine ⟨126303378634912677870025367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84202252423275118580016911 126303378634912677870025367)
    ·
      refine ⟨189455067952369016805038051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126303378634912677870025367 189455067952369016805038051)
      ·
        refine ⟨284182601928553525207557077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189455067952369016805038051 284182601928553525207557077)
        ·
          refine ⟨6660529732700473247052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 284182601928553525207557077 6660529732700473247052119)
          ·
            refine ⟨9990794599050709870578179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660529732700473247052119 9990794599050709870578179)
            ·
              refine ⟨14986191898576064805867269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9990794599050709870578179 14986191898576064805867269)
              ·
                refine ⟨2809910980983012151100113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14986191898576064805867269 2809910980983012151100113)
                ·
                  refine ⟨2107433235737259113325085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809910980983012151100113 2107433235737259113325085)
                  ·
                    refine ⟨790287463401472167496907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107433235737259113325085 790287463401472167496907)
                    ·
                      rfl

theorem cell22_2308619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].length) (baseStart_2308619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308619 prefixEnd_2308619 := by exact prefixLift 2308619
  have htrace : WordTrace (prefixWord ++ tailWord_2308619) baseStart_2308619 baseEnd_2308619 := by
    simpa [prefixWord, tailWord_2308619, baseEnd_2308619] using wordTrace_append hprefix tailTrace_2308619
  have hstable : (prefixWord ++ tailWord_2308619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308619).length < 2 ^ (prefixWord ++ tailWord_2308619).sum := by decide
  have hdescent : baseEnd_2308619 < baseStart_2308619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308632 : List Nat := [2, 1, 2, 3, 3, 1, 3, 7]
def baseStart_2308632 : Nat := 118140960795 + 2308632 * 2 ^ 59
def prefixEnd_2308632 : Nat := 4983230072969 + 3 ^ 40 * 2308632 * 2
def baseEnd_2308632 : Nat := 87810212618571607435763

theorem tailTrace_2308632 : CollatzResearch.WordTrace tailWord_2308632 prefixEnd_2308632 87810212618571607435763 := by
  unfold tailWord_2308632
  simp only [CollatzResearch.WordTrace]
  refine ⟨42101363286114010900120075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56135151048152014533493433 42101363286114010900120075)
  ·
    refine ⟨63152044929171016350180113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42101363286114010900120075 63152044929171016350180113)
    ·
      refine ⟨47364033696878262262635085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63152044929171016350180113 47364033696878262262635085)
      ·
        refine ⟨17761512636329348348488157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47364033696878262262635085 17761512636329348348488157)
        ·
          refine ⟨6660567238623505630683059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17761512636329348348488157 6660567238623505630683059)
          ·
            refine ⟨9990850857935258446024589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660567238623505630683059 9990850857935258446024589)
            ·
              refine ⟨3746569071725721917259221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9990850857935258446024589 3746569071725721917259221)
              ·
                refine ⟨87810212618571607435763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3746569071725721917259221 87810212618571607435763)
                ·
                  rfl

theorem cell22_2308632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_2308632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308632 prefixEnd_2308632 := by exact prefixLift 2308632
  have htrace : WordTrace (prefixWord ++ tailWord_2308632) baseStart_2308632 baseEnd_2308632 := by
    simpa [prefixWord, tailWord_2308632, baseEnd_2308632] using wordTrace_append hprefix tailTrace_2308632
  have hstable : (prefixWord ++ tailWord_2308632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308632).length < 2 ^ (prefixWord ++ tailWord_2308632).sum := by decide
  have hdescent : baseEnd_2308632 < baseStart_2308632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308670 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2308670 : Nat := 118140960795 + 2308670 * 2 ^ 59
def prefixEnd_2308670 : Nat := 4983230072969 + 3 ^ 40 * 2308670 * 2
def baseEnd_2308670 : Nat := 790304921743725034471751

theorem tailTrace_2308670 : CollatzResearch.WordTrace tailWord_2308670 prefixEnd_2308670 790304921743725034471751 := by
  unfold tailWord_2308670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525514068261294286265433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56136075030726902860082309 10525514068261294286265433)
  ·
    refine ⟨7894135551195970714699075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10525514068261294286265433 7894135551195970714699075)
    ·
      refine ⟨11841203326793956072048613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7894135551195970714699075 11841203326793956072048613)
      ·
        refine ⟨2220225623773866763509115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11841203326793956072048613 2220225623773866763509115)
        ·
          refine ⟨3330338435660800145263673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220225623773866763509115 3330338435660800145263673)
          ·
            refine ⟨2497753826745600108947755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3330338435660800145263673 2497753826745600108947755)
            ·
              refine ⟨3746630740118400163421633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497753826745600108947755 3746630740118400163421633)
              ·
                refine ⟨2809973055088800122566225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746630740118400163421633 2809973055088800122566225)
                ·
                  refine ⟨2107479791316600091924669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2809973055088800122566225 2107479791316600091924669)
                  ·
                    refine ⟨790304921743725034471751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107479791316600091924669 790304921743725034471751)
                    ·
                      rfl

theorem cell22_2308670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2308670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308670 prefixEnd_2308670 := by exact prefixLift 2308670
  have htrace : WordTrace (prefixWord ++ tailWord_2308670) baseStart_2308670 baseEnd_2308670 := by
    simpa [prefixWord, tailWord_2308670, baseEnd_2308670] using wordTrace_append hprefix tailTrace_2308670
  have hstable : (prefixWord ++ tailWord_2308670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308670).length < 2 ^ (prefixWord ++ tailWord_2308670).sum := by decide
  have hdescent : baseEnd_2308670 < baseStart_2308670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308677 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 7]
def baseStart_2308677 : Nat := 118140960795 + 2308677 * 2 ^ 59
def prefixEnd_2308677 : Nat := 4983230072969 + 3 ^ 40 * 2308677 * 2
def baseEnd_2308677 : Nat := 263435772662259783182243

theorem tailTrace_2308677 : CollatzResearch.WordTrace tailWord_2308677 prefixEnd_2308677 263435772662259783182243 := by
  unfold tailWord_2308677
  simp only [CollatzResearch.WordTrace]
  refine ⟨84204367857064994485628285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56136245238043329657085523 84204367857064994485628285)
  ·
    refine ⟨31576637946399372932110607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84204367857064994485628285 31576637946399372932110607)
    ·
      refine ⟨47364956919599059398165911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31576637946399372932110607 47364956919599059398165911)
      ·
        refine ⟨71047435379398589097248867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47364956919599059398165911 71047435379398589097248867)
        ·
          refine ⟨106571153069097883645873301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71047435379398589097248867 106571153069097883645873301)
          ·
            refine ⟨4995522800113963295900311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106571153069097883645873301 4995522800113963295900311)
            ·
              refine ⟨7493284200170944943850467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995522800113963295900311 7493284200170944943850467)
              ·
                refine ⟨11239926300256417415775701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7493284200170944943850467 11239926300256417415775701)
                ·
                  refine ⟨263435772662259783182243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11239926300256417415775701 263435772662259783182243)
                  ·
                    rfl

theorem cell22_2308677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_2308677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308677 prefixEnd_2308677 := by exact prefixLift 2308677
  have htrace : WordTrace (prefixWord ++ tailWord_2308677) baseStart_2308677 baseEnd_2308677 := by
    simpa [prefixWord, tailWord_2308677, baseEnd_2308677] using wordTrace_append hprefix tailTrace_2308677
  have hstable : (prefixWord ++ tailWord_2308677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308677).length < 2 ^ (prefixWord ++ tailWord_2308677).sum := by decide
  have hdescent : baseEnd_2308677 < baseStart_2308677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308739 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 4]
def baseStart_2308739 : Nat := 118140960795 + 2308739 * 2 ^ 59
def prefixEnd_2308739 : Nat := 4983230072969 + 3 ^ 40 * 2308739 * 2
def baseEnd_2308739 : Nat := 263442847284610618165513

theorem tailTrace_2308739 : CollatzResearch.WordTrace tailWord_2308739 prefixEnd_2308739 263442847284610618165513 := by
  unfold tailWord_2308739
  simp only [CollatzResearch.WordTrace]
  refine ⟨84206629182840379074385271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56137752788560252716256847 84206629182840379074385271)
  ·
    refine ⟨126309943774260568611577907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84206629182840379074385271 126309943774260568611577907)
    ·
      refine ⟨189464915661390852917366861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126309943774260568611577907 189464915661390852917366861)
      ·
        refine ⟨71049343373021569844012573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189464915661390852917366861 71049343373021569844012573)
        ·
          refine ⟨26643503764883088691504715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71049343373021569844012573 26643503764883088691504715)
          ·
            refine ⟨39965255647324633037257073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26643503764883088691504715 39965255647324633037257073)
            ·
              refine ⟨29973941735493474777942805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39965255647324633037257073 29973941735493474777942805)
              ·
                refine ⟨1405028518851256630216069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29973941735493474777942805 1405028518851256630216069)
                ·
                  refine ⟨263442847284610618165513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405028518851256630216069 263442847284610618165513)
                  ·
                    rfl

theorem cell22_2308739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 4].length) (baseStart_2308739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308739 prefixEnd_2308739 := by exact prefixLift 2308739
  have htrace : WordTrace (prefixWord ++ tailWord_2308739) baseStart_2308739 baseEnd_2308739 := by
    simpa [prefixWord, tailWord_2308739, baseEnd_2308739] using wordTrace_append hprefix tailTrace_2308739
  have hstable : (prefixWord ++ tailWord_2308739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308739).length < 2 ^ (prefixWord ++ tailWord_2308739).sum := by decide
  have hdescent : baseEnd_2308739 < baseStart_2308739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308775 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2308775 : Nat := 118140960795 + 2308775 * 2 ^ 59
def prefixEnd_2308775 : Nat := 4983230072969 + 3 ^ 40 * 2308775 * 2
def baseEnd_2308775 : Nat := 790340865389539760596429

theorem tailTrace_2308775 : CollatzResearch.WordTrace tailWord_2308775 prefixEnd_2308775 790340865389539760596429 := by
  unfold tailWord_2308775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84207942210709957222695779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56138628140473304815130519 84207942210709957222695779)
  ·
    refine ⟨126311913316064935834043669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84207942210709957222695779 126311913316064935834043669)
    ·
      refine ⟨5920870936690543867220797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126311913316064935834043669 5920870936690543867220797)
      ·
        refine ⟨2220326601258953950207799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5920870936690543867220797 2220326601258953950207799)
        ·
          refine ⟨3330489901888430925311699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220326601258953950207799 3330489901888430925311699)
          ·
            refine ⟨4995734852832646387967549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330489901888430925311699 4995734852832646387967549)
            ·
              refine ⟨1873400569812242395487831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4995734852832646387967549 1873400569812242395487831)
              ·
                refine ⟨2810100854718363593231747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873400569812242395487831 2810100854718363593231747)
                ·
                  refine ⟨4215151282077545389847621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810100854718363593231747 4215151282077545389847621)
                  ·
                    refine ⟨790340865389539760596429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215151282077545389847621 790340865389539760596429)
                    ·
                      rfl

theorem cell22_2308775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2308775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308775 prefixEnd_2308775 := by exact prefixLift 2308775
  have htrace : WordTrace (prefixWord ++ tailWord_2308775) baseStart_2308775 baseEnd_2308775 := by
    simpa [prefixWord, tailWord_2308775, baseEnd_2308775] using wordTrace_append hprefix tailTrace_2308775
  have hstable : (prefixWord ++ tailWord_2308775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308775).length < 2 ^ (prefixWord ++ tailWord_2308775).sum := by decide
  have hdescent : baseEnd_2308775 < baseStart_2308775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308790 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_2308790 : Nat := 118140960795 + 2308790 * 2 ^ 59
def prefixEnd_2308790 : Nat := 4983230072969 + 3 ^ 40 * 2308790 * 2
def baseEnd_2308790 : Nat := 263448666732028240490461

theorem tailTrace_2308790 : CollatzResearch.WordTrace tailWord_2308790 prefixEnd_2308790 263448666732028240490461 := by
  unfold tailWord_2308790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263030581603475924030739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56138992870437076522994549 5263030581603475924030739)
  ·
    refine ⟨7894545872405213886046109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5263030581603475924030739 7894545872405213886046109)
    ·
      refine ⟨2960454702151955207267291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7894545872405213886046109 2960454702151955207267291)
      ·
        refine ⟨4440682053227932810900937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960454702151955207267291 4440682053227932810900937)
        ·
          refine ⟨3330511539920949608175703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4440682053227932810900937 3330511539920949608175703)
          ·
            refine ⟨4995767309881424412263555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330511539920949608175703 4995767309881424412263555)
            ·
              refine ⟨7493650964822136618395333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995767309881424412263555 7493650964822136618395333)
              ·
                refine ⟨1405059555904150615949125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7493650964822136618395333 1405059555904150615949125)
                ·
                  refine ⟨263448666732028240490461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405059555904150615949125 263448666732028240490461)
                  ·
                    rfl

theorem cell22_2308790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_2308790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308790 prefixEnd_2308790 := by exact prefixLift 2308790
  have htrace : WordTrace (prefixWord ++ tailWord_2308790) baseStart_2308790 baseEnd_2308790 := by
    simpa [prefixWord, tailWord_2308790, baseEnd_2308790] using wordTrace_append hprefix tailTrace_2308790
  have hstable : (prefixWord ++ tailWord_2308790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308790).length < 2 ^ (prefixWord ++ tailWord_2308790).sum := by decide
  have hdescent : baseEnd_2308790 < baseStart_2308790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308820 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2308820 : Nat := 118140960795 + 2308820 * 2 ^ 59
def prefixEnd_2308820 : Nat := 4983230072969 + 3 ^ 40 * 2308820 * 2
def baseEnd_2308820 : Nat := 790356269809174643221291

theorem tailTrace_2308820 : CollatzResearch.WordTrace tailWord_2308820 prefixEnd_2308820 790356269809174643221291 := by
  unfold tailWord_2308820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42104791747773464954041957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56139722330364619938722609 42104791747773464954041957)
  ·
    refine ⟨7894648452707524678882867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42104791747773464954041957 7894648452707524678882867)
    ·
      refine ⟨11841972679061287018324301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7894648452707524678882867 11841972679061287018324301)
      ·
        refine ⟨4440739754647982631871613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11841972679061287018324301 4440739754647982631871613)
        ·
          refine ⟨1665277407992993486951855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4440739754647982631871613 1665277407992993486951855)
          ·
            refine ⟨2497916111989490230427783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665277407992993486951855 2497916111989490230427783)
            ·
              refine ⟨3746874167984235345641675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497916111989490230427783 3746874167984235345641675)
              ·
                refine ⟨5620311251976353018462513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746874167984235345641675 5620311251976353018462513)
                ·
                  refine ⟨4215233438982264763846885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5620311251976353018462513 4215233438982264763846885)
                  ·
                    refine ⟨790356269809174643221291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215233438982264763846885 790356269809174643221291)
                    ·
                      rfl

theorem cell22_2308820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2308820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308820 prefixEnd_2308820 := by exact prefixLift 2308820
  have htrace : WordTrace (prefixWord ++ tailWord_2308820) baseStart_2308820 baseEnd_2308820 := by
    simpa [prefixWord, tailWord_2308820, baseEnd_2308820] using wordTrace_append hprefix tailTrace_2308820
  have hstable : (prefixWord ++ tailWord_2308820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308820).length < 2 ^ (prefixWord ++ tailWord_2308820).sum := by decide
  have hdescent : baseEnd_2308820 < baseStart_2308820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308833 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2308833 : Nat := 118140960795 + 2308833 * 2 ^ 59
def prefixEnd_2308833 : Nat := 4983230072969 + 3 ^ 40 * 2308833 * 2
def baseEnd_2308833 : Nat := 790360719974846942646251

theorem tailTrace_2308833 : CollatzResearch.WordTrace tailWord_2308833 prefixEnd_2308833 790360719974846942646251 := by
  unfold tailWord_2308833
  simp only [CollatzResearch.WordTrace]
  refine ⟨84210057644499833128307153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56140038429666555418871435 84210057644499833128307153)
  ·
    refine ⟨63157543233374874846230365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84210057644499833128307153 63157543233374874846230365)
    ·
      refine ⟨23684078712515578067336387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63157543233374874846230365 23684078712515578067336387)
      ·
        refine ⟨35526118068773367101004581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684078712515578067336387 35526118068773367101004581)
        ·
          refine ⟨6661147137895006331438359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35526118068773367101004581 6661147137895006331438359)
          ·
            refine ⟨9991720706842509497157539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661147137895006331438359 9991720706842509497157539)
            ·
              refine ⟨14987581060263764245736309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9991720706842509497157539 14987581060263764245736309)
              ·
                refine ⟨1405085724399727898037779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14987581060263764245736309 1405085724399727898037779)
                ·
                  refine ⟨2107628586599591847056669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405085724399727898037779 2107628586599591847056669)
                  ·
                    refine ⟨790360719974846942646251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107628586599591847056669 790360719974846942646251)
                    ·
                      rfl

theorem cell22_2308833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2308833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308833 prefixEnd_2308833 := by exact prefixLift 2308833
  have htrace : WordTrace (prefixWord ++ tailWord_2308833) baseStart_2308833 baseEnd_2308833 := by
    simpa [prefixWord, tailWord_2308833, baseEnd_2308833] using wordTrace_append hprefix tailTrace_2308833
  have hstable : (prefixWord ++ tailWord_2308833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308833).length < 2 ^ (prefixWord ++ tailWord_2308833).sum := by decide
  have hdescent : baseEnd_2308833 < baseStart_2308833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308846 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2308846 : Nat := 118140960795 + 2308846 * 2 ^ 59
def prefixEnd_2308846 : Nat := 4983230072969 + 3 ^ 40 * 2308846 * 2
def baseEnd_2308846 : Nat := 263455056713506414023737

theorem tailTrace_2308846 : CollatzResearch.WordTrace tailWord_2308846 prefixEnd_2308846 263455056713506414023737 := by
  unfold tailWord_2308846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526316474181592043566299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56140354528968490899020261 10526316474181592043566299)
  ·
    refine ⟨15789474711272388065349449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526316474181592043566299 15789474711272388065349449)
    ·
      refine ⟨11842106033454291049012087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15789474711272388065349449 11842106033454291049012087)
      ·
        refine ⟨17763159050181436573518131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842106033454291049012087 17763159050181436573518131)
        ·
          refine ⟨26644738575272154860277197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17763159050181436573518131 26644738575272154860277197)
          ·
            refine ⟨9991776965727058072603949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26644738575272154860277197 9991776965727058072603949)
            ·
              refine ⟨3746916362147646777226481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9991776965727058072603949 3746916362147646777226481)
              ·
                refine ⟨2810187271610735082919861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746916362147646777226481 2810187271610735082919861)
                ·
                  refine ⟨263455056713506414023737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810187271610735082919861 263455056713506414023737)
                  ·
                    rfl

theorem cell22_2308846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2308846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308846 prefixEnd_2308846 := by exact prefixLift 2308846
  have htrace : WordTrace (prefixWord ++ tailWord_2308846) baseStart_2308846 baseEnd_2308846 := by
    simpa [prefixWord, tailWord_2308846, baseEnd_2308846] using wordTrace_append hprefix tailTrace_2308846
  have hstable : (prefixWord ++ tailWord_2308846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308846).length < 2 ^ (prefixWord ++ tailWord_2308846).sum := by decide
  have hdescent : baseEnd_2308846 < baseStart_2308846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308874 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_2308874 : Nat := 118140960795 + 2308874 * 2 ^ 59
def prefixEnd_2308874 : Nat := 4983230072969 + 3 ^ 40 * 2308874 * 2
def baseEnd_2308874 : Nat := 263458251704245500790375

theorem tailTrace_2308874 : CollatzResearch.WordTrace tailWord_2308874 prefixEnd_2308874 263458251704245500790375 := by
  unfold tailWord_2308874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21052888259337824282637419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56141035358234198087033117 21052888259337824282637419)
  ·
    refine ⟨31579332389006736423956129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21052888259337824282637419 31579332389006736423956129)
    ·
      refine ⟨23684499291755052317967097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31579332389006736423956129 23684499291755052317967097)
      ·
        refine ⟨17763374468816289238475323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23684499291755052317967097 17763374468816289238475323)
        ·
          refine ⟨26645061703224433857712985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17763374468816289238475323 26645061703224433857712985)
          ·
            refine ⟨19983796277418325393284739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26645061703224433857712985 19983796277418325393284739)
            ·
              refine ⟨29975694416127488089927109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19983796277418325393284739 29975694416127488089927109)
              ·
                refine ⟨5620442703023904016861333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29975694416127488089927109 5620442703023904016861333)
                ·
                  refine ⟨263458251704245500790375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5620442703023904016861333 263458251704245500790375)
                  ·
                    rfl

theorem cell22_2308874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_2308874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308874 prefixEnd_2308874 := by exact prefixLift 2308874
  have htrace : WordTrace (prefixWord ++ tailWord_2308874) baseStart_2308874 baseEnd_2308874 := by
    simpa [prefixWord, tailWord_2308874, baseEnd_2308874] using wordTrace_append hprefix tailTrace_2308874
  have hstable : (prefixWord ++ tailWord_2308874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308874).length < 2 ^ (prefixWord ++ tailWord_2308874).sum := by decide
  have hdescent : baseEnd_2308874 < baseStart_2308874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308908 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_2308908 : Nat := 118140960795 + 2308908 * 2 ^ 59
def prefixEnd_2308908 : Nat := 4983230072969 + 3 ^ 40 * 2308908 * 2
def baseEnd_2308908 : Nat := 263462131335857249007007

theorem tailTrace_2308908 : CollatzResearch.WordTrace tailWord_2308908 prefixEnd_2308908 263462131335857249007007 := by
  unfold tailWord_2308908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42106396559614060468643689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56141862079485413958191585 42106396559614060468643689)
  ·
    refine ⟨31579797419710545351482767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42106396559614060468643689 31579797419710545351482767)
    ·
      refine ⟨47369696129565818027224151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31579797419710545351482767 47369696129565818027224151)
      ·
        refine ⟨71054544194348727040836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47369696129565818027224151 71054544194348727040836227)
        ·
          refine ⟨106581816291523090561254341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71054544194348727040836227 106581816291523090561254341)
          ·
            refine ⟨19984090554660579480235189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106581816291523090561254341 19984090554660579480235189)
            ·
              refine ⟨1873508489499429326272049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19984090554660579480235189 1873508489499429326272049)
              ·
                refine ⟨1405131367124571994704037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873508489499429326272049 1405131367124571994704037)
                ·
                  refine ⟨263462131335857249007007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405131367124571994704037 263462131335857249007007)
                  ·
                    rfl

theorem cell22_2308908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_2308908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308908 prefixEnd_2308908 := by exact prefixLift 2308908
  have htrace : WordTrace (prefixWord ++ tailWord_2308908) baseStart_2308908 baseEnd_2308908 := by
    simpa [prefixWord, tailWord_2308908, baseEnd_2308908] using wordTrace_append hprefix tailTrace_2308908
  have hstable : (prefixWord ++ tailWord_2308908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308908).length < 2 ^ (prefixWord ++ tailWord_2308908).sum := by decide
  have hdescent : baseEnd_2308908 < baseStart_2308908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308919 : List Nat := [1, 1, 3, 1, 2, 1, 6, 7]
def baseStart_2308919 : Nat := 118140960795 + 2308919 * 2 ^ 59
def prefixEnd_2308919 : Nat := 4983230072969 + 3 ^ 40 * 2308919 * 2
def baseEnd_2308919 : Nat := 87821128836930153888443

theorem tailTrace_2308919 : CollatzResearch.WordTrace tailWord_2308919 prefixEnd_2308919 87821128836930153888443 := by
  unfold tailWord_2308919
  simp only [CollatzResearch.WordTrace]
  refine ⟨84213194322188269815937811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56142129548125513210625207 84213194322188269815937811)
  ·
    refine ⟨126319791483282404723906717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84213194322188269815937811 126319791483282404723906717)
    ·
      refine ⟨47369921806230901771465019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126319791483282404723906717 47369921806230901771465019)
      ·
        refine ⟨71054882709346352657197529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47369921806230901771465019 71054882709346352657197529)
        ·
          refine ⟨53291162032009764492898147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71054882709346352657197529 53291162032009764492898147)
          ·
            refine ⟨79936743048014646739347221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53291162032009764492898147 79936743048014646739347221)
            ·
              refine ⟨3747034830375686565906901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79936743048014646739347221 3747034830375686565906901)
              ·
                refine ⟨87821128836930153888443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3747034830375686565906901 87821128836930153888443)
                ·
                  rfl

theorem cell22_2308919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 7].length) (baseStart_2308919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308919 prefixEnd_2308919 := by exact prefixLift 2308919
  have htrace : WordTrace (prefixWord ++ tailWord_2308919) baseStart_2308919 baseEnd_2308919 := by
    simpa [prefixWord, tailWord_2308919, baseEnd_2308919] using wordTrace_append hprefix tailTrace_2308919
  have hstable : (prefixWord ++ tailWord_2308919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308919).length < 2 ^ (prefixWord ++ tailWord_2308919).sum := by decide
  have hdescent : baseEnd_2308919 < baseStart_2308919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2308979 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_2308979 : Nat := 118140960795 + 2308979 * 2 ^ 59
def prefixEnd_2308979 : Nat := 4983230072969 + 3 ^ 40 * 2308979 * 2
def baseEnd_2308979 : Nat := 790410698758551228495803

theorem tailTrace_2308979 : CollatzResearch.WordTrace tailWord_2308979 prefixEnd_2308979 790410698758551228495803 := by
  unfold tailWord_2308979
  simp only [CollatzResearch.WordTrace]
  refine ⟨84215382701970900063121991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56143588467980600042081327 84215382701970900063121991)
  ·
    refine ⟨126323074052956350094682987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84215382701970900063121991 126323074052956350094682987)
    ·
      refine ⟨189484611079434525142024481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126323074052956350094682987 189484611079434525142024481)
      ·
        refine ⟨142113458309575893856518361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189484611079434525142024481 142113458309575893856518361)
        ·
          refine ⟨106585093732181920392388771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142113458309575893856518361 106585093732181920392388771)
          ·
            refine ⟨159877640598272880588583157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106585093732181920392388771 159877640598272880588583157)
            ·
              refine ⟨14988528806088082555179671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159877640598272880588583157 14988528806088082555179671)
              ·
                refine ⟨22482793209132123832769507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14988528806088082555179671 22482793209132123832769507)
                ·
                  refine ⟨33724189813698185749154261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22482793209132123832769507 33724189813698185749154261)
                  ·
                    refine ⟨790410698758551228495803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33724189813698185749154261 790410698758551228495803)
                    ·
                      rfl

theorem cell22_2308979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_2308979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2308979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2308979 prefixEnd_2308979 := by exact prefixLift 2308979
  have htrace : WordTrace (prefixWord ++ tailWord_2308979) baseStart_2308979 baseEnd_2308979 := by
    simpa [prefixWord, tailWord_2308979, baseEnd_2308979] using wordTrace_append hprefix tailTrace_2308979
  have hstable : (prefixWord ++ tailWord_2308979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2308979).length < 2 ^ (prefixWord ++ tailWord_2308979).sum := by decide
  have hdescent : baseEnd_2308979 < baseStart_2308979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2308979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309002 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2309002 : Nat := 118140960795 + 2309002 * 2 ^ 59
def prefixEnd_2309002 : Nat := 4983230072969 + 3 ^ 40 * 2309002 * 2
def baseEnd_2309002 : Nat := 790418572128586835170733

theorem tailTrace_2309002 : CollatzResearch.WordTrace tailWord_2309002 prefixEnd_2309002 790418572128586835170733 := by
  unfold tailWord_2309002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054055395221893747802315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56144147720591716660806173 21054055395221893747802315)
  ·
    refine ⟨31581083092832840621703473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054055395221893747802315 31581083092832840621703473)
    ·
      refine ⟨23685812319624630466277605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31581083092832840621703473 23685812319624630466277605)
      ·
        refine ⟨4441089809929618212427051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23685812319624630466277605 4441089809929618212427051)
        ·
          refine ⟨6661634714894427318640577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441089809929618212427051 6661634714894427318640577)
          ·
            refine ⟨4996226036170820488980433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6661634714894427318640577 4996226036170820488980433)
            ·
              refine ⟨3747169527128115366735325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4996226036170820488980433 3747169527128115366735325)
              ·
                refine ⟨1405188572673043262525747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3747169527128115366735325 1405188572673043262525747)
                ·
                  refine ⟨2107782859009564893788621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405188572673043262525747 2107782859009564893788621)
                  ·
                    refine ⟨790418572128586835170733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2107782859009564893788621 790418572128586835170733)
                    ·
                      rfl

theorem cell22_2309002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2309002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309002 prefixEnd_2309002 := by exact prefixLift 2309002
  have htrace : WordTrace (prefixWord ++ tailWord_2309002) baseStart_2309002 baseEnd_2309002 := by
    simpa [prefixWord, tailWord_2309002, baseEnd_2309002] using wordTrace_append hprefix tailTrace_2309002
  have hstable : (prefixWord ++ tailWord_2309002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309002).length < 2 ^ (prefixWord ++ tailWord_2309002).sum := by decide
  have hdescent : baseEnd_2309002 < baseStart_2309002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309009 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 10]
def baseStart_2309009 : Nat := 118140960795 + 2309009 * 2 ^ 59
def prefixEnd_2309009 : Nat := 4983230072969 + 3 ^ 40 * 2309009 * 2
def baseEnd_2309009 : Nat := 263473656123880383415237

theorem tailTrace_2309009 : CollatzResearch.WordTrace tailWord_2309009 prefixEnd_2309009 263473656123880383415237 := by
  unfold tailWord_2309009
  simp only [CollatzResearch.WordTrace]
  refine ⟨84216476891862215186714081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56144317927908143457809387 84216476891862215186714081)
  ·
    refine ⟨63162357668896661390035561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84216476891862215186714081 63162357668896661390035561)
    ·
      refine ⟨47371768251672496042526671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63162357668896661390035561 47371768251672496042526671)
      ·
        refine ⟨71057652377508744063790007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47371768251672496042526671 71057652377508744063790007)
        ·
          refine ⟨106586478566263116095685011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71057652377508744063790007 106586478566263116095685011)
          ·
            refine ⟨159879717849394674143527517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106586478566263116095685011 159879717849394674143527517)
            ·
              refine ⟨59954894193523002803822819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159879717849394674143527517 59954894193523002803822819)
              ·
                refine ⟨89932341290284504205734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59954894193523002803822819 89932341290284504205734229)
                ·
                  refine ⟨263473656123880383415237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89932341290284504205734229 263473656123880383415237)
                  ·
                    rfl

theorem cell22_2309009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_2309009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309009 prefixEnd_2309009 := by exact prefixLift 2309009
  have htrace : WordTrace (prefixWord ++ tailWord_2309009) baseStart_2309009 baseEnd_2309009 := by
    simpa [prefixWord, tailWord_2309009, baseEnd_2309009] using wordTrace_append hprefix tailTrace_2309009
  have hstable : (prefixWord ++ tailWord_2309009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309009).length < 2 ^ (prefixWord ++ tailWord_2309009).sum := by decide
  have hdescent : baseEnd_2309009 < baseStart_2309009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309056 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_2309056 : Nat := 118140960795 + 2309056 * 2 ^ 59
def prefixEnd_2309056 : Nat := 4983230072969 + 3 ^ 40 * 2309056 * 2
def baseEnd_2309056 : Nat := 790437057432148694320567

theorem tailTrace_2309056 : CollatzResearch.WordTrace tailWord_2309056 prefixEnd_2309056 790437057432148694320567 := by
  unfold tailWord_2309056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42109095561345971106837511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56145460748461294809116681 42109095561345971106837511)
  ·
    refine ⟨63163643342018956660256267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42109095561345971106837511 63163643342018956660256267)
    ·
      refine ⟨94745465013028434990384401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63163643342018956660256267 94745465013028434990384401)
      ·
        refine ⟨71059098759771326242788301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94745465013028434990384401 71059098759771326242788301)
        ·
          refine ⟨26647162034914247341045613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71059098759771326242788301 26647162034914247341045613)
          ·
            refine ⟨9992685763092842752892105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26647162034914247341045613 9992685763092842752892105)
            ·
              refine ⟨7494514322319632064669079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9992685763092842752892105 7494514322319632064669079)
              ·
                refine ⟨11241771483479448097003619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7494514322319632064669079 11241771483479448097003619)
                ·
                  refine ⟨16862657225219172145505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11241771483479448097003619 16862657225219172145505429)
                  ·
                    refine ⟨790437057432148694320567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16862657225219172145505429 790437057432148694320567)
                    ·
                      rfl

theorem cell22_2309056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_2309056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309056 prefixEnd_2309056 := by exact prefixLift 2309056
  have htrace : WordTrace (prefixWord ++ tailWord_2309056) baseStart_2309056 baseEnd_2309056 := by
    simpa [prefixWord, tailWord_2309056, baseEnd_2309056] using wordTrace_append hprefix tailTrace_2309056
  have hstable : (prefixWord ++ tailWord_2309056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309056).length < 2 ^ (prefixWord ++ tailWord_2309056).sum := by decide
  have hdescent : baseEnd_2309056 < baseStart_2309056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309071 : List Nat := [1, 1, 2, 1, 1, 8, 8]
def baseStart_2309071 : Nat := 118140960795 + 2309071 * 2 ^ 59
def prefixEnd_2309071 : Nat := 4983230072969 + 3 ^ 40 * 2309071 * 2
def baseEnd_2309071 : Nat := 29275636749581246488723

theorem tailTrace_2309071 : CollatzResearch.WordTrace tailWord_2309071 prefixEnd_2309071 29275636749581246488723 := by
  unfold tailWord_2309071
  simp only [CollatzResearch.WordTrace]
  refine ⟨84218738217637599775471067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56145825478425066516980711 84218738217637599775471067)
  ·
    refine ⟨126328107326456399663206601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84218738217637599775471067 126328107326456399663206601)
    ·
      refine ⟨94746080494842299747404951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126328107326456399663206601 94746080494842299747404951)
      ·
        refine ⟨142119120742263449621107427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94746080494842299747404951 142119120742263449621107427)
        ·
          refine ⟨213178681113395174431661141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142119120742263449621107427 213178681113395174431661141)
          ·
            refine ⟨2498187669297599700371029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 213178681113395174431661141 2498187669297599700371029)
            ·
              refine ⟨29275636749581246488723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2498187669297599700371029 29275636749581246488723)
              ·
                rfl

theorem cell22_2309071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 8].length) (baseStart_2309071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309071 prefixEnd_2309071 := by exact prefixLift 2309071
  have htrace : WordTrace (prefixWord ++ tailWord_2309071) baseStart_2309071 baseEnd_2309071 := by
    simpa [prefixWord, tailWord_2309071, baseEnd_2309071] using wordTrace_append hprefix tailTrace_2309071
  have hstable : (prefixWord ++ tailWord_2309071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309071).length < 2 ^ (prefixWord ++ tailWord_2309071).sum := by decide
  have hdescent : baseEnd_2309071 < baseStart_2309071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309077 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 4]
def baseStart_2309077 : Nat := 118140960795 + 2309077 * 2 ^ 59
def prefixEnd_2309077 : Nat := 4983230072969 + 3 ^ 40 * 2309077 * 2
def baseEnd_2309077 : Nat := 263481415387103879848501

theorem tailTrace_2309077 : CollatzResearch.WordTrace tailWord_2309077 prefixEnd_2309077 263481415387103879848501 := by
  unfold tailWord_2309077
  simp only [CollatzResearch.WordTrace]
  refine ⟨84218957055615862800189485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56145971370410575200126323 84218957055615862800189485)
  ·
    refine ⟨31582108895855948550071057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84218957055615862800189485 31582108895855948550071057)
    ·
      refine ⟨23686581671891961412553293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31582108895855948550071057 23686581671891961412553293)
      ·
        refine ⟨8882468126959485529707485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23686581671891961412553293 8882468126959485529707485)
        ·
          refine ⟨3330925547609807073640307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8882468126959485529707485 3330925547609807073640307)
          ·
            refine ⟨4996388321414710610460461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330925547609807073640307 4996388321414710610460461)
            ·
              refine ⟨1873645620530516478922673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4996388321414710610460461 1873645620530516478922673)
              ·
                refine ⟨1405234215397887359192005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873645620530516478922673 1405234215397887359192005)
                ·
                  refine ⟨263481415387103879848501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405234215397887359192005 263481415387103879848501)
                  ·
                    rfl

theorem cell22_2309077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_2309077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309077 prefixEnd_2309077 := by exact prefixLift 2309077
  have htrace : WordTrace (prefixWord ++ tailWord_2309077) baseStart_2309077 baseEnd_2309077 := by
    simpa [prefixWord, tailWord_2309077, baseEnd_2309077] using wordTrace_append hprefix tailTrace_2309077
  have hstable : (prefixWord ++ tailWord_2309077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309077).length < 2 ^ (prefixWord ++ tailWord_2309077).sum := by decide
  have hdescent : baseEnd_2309077 < baseStart_2309077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309163 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 1, 4]
def baseStart_2309163 : Nat := 118140960795 + 2309163 * 2 ^ 59
def prefixEnd_2309163 : Nat := 4983230072969 + 3 ^ 40 * 2309163 * 2
def baseEnd_2309163 : Nat := 790473685718836081895239

theorem tailTrace_2309163 : CollatzResearch.WordTrace tailWord_2309163 prefixEnd_2309163 790473685718836081895239 := by
  unfold tailWord_2309163
  simp only [CollatzResearch.WordTrace]
  refine ⟨84222093733304299487820143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56148062488869532991880095 84222093733304299487820143)
  ·
    refine ⟨126333140599956449231730215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84222093733304299487820143 126333140599956449231730215)
    ·
      refine ⟨189499710899934673847595323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126333140599956449231730215 189499710899934673847595323)
      ·
        refine ⟨284249566349902010771392985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189499710899934673847595323 284249566349902010771392985)
        ·
          refine ⟨213187174762426508078544739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284249566349902010771392985 213187174762426508078544739)
          ·
            refine ⟨319780762143639762117817109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213187174762426508078544739 319780762143639762117817109)
            ·
              refine ⟨14989723225483113849272677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319780762143639762117817109 14989723225483113849272677)
              ·
                refine ⟨2810573104778083846738627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14989723225483113849272677 2810573104778083846738627)
                ·
                  refine ⟨4215859657167125770107941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810573104778083846738627 4215859657167125770107941)
                  ·
                    refine ⟨790473685718836081895239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215859657167125770107941 790473685718836081895239)
                    ·
                      rfl

theorem cell22_2309163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_2309163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309163 prefixEnd_2309163 := by exact prefixLift 2309163
  have htrace : WordTrace (prefixWord ++ tailWord_2309163) baseStart_2309163 baseEnd_2309163 := by
    simpa [prefixWord, tailWord_2309163, baseEnd_2309163] using wordTrace_append hprefix tailTrace_2309163
  have hstable : (prefixWord ++ tailWord_2309163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309163).length < 2 ^ (prefixWord ++ tailWord_2309163).sum := by decide
  have hdescent : baseEnd_2309163 < baseStart_2309163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309180 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_2309180 : Nat := 118140960795 + 2309180 * 2 ^ 59
def prefixEnd_2309180 : Nat := 4983230072969 + 3 ^ 40 * 2309180 * 2
def baseEnd_2309180 : Nat := 790479505166253704220187

theorem tailTrace_2309180 : CollatzResearch.WordTrace tailWord_2309180 prefixEnd_2309180 790479505166253704220187 := by
  unfold tailWord_2309180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42111356887121355695594497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56148475849495140927459329 42111356887121355695594497)
  ·
    refine ⟨31583517665341016771695873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42111356887121355695594497 31583517665341016771695873)
    ·
      refine ⟨23687638249005762578771905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31583517665341016771695873 23687638249005762578771905)
      ·
        refine ⟨17765728686754321934078929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23687638249005762578771905 17765728686754321934078929)
        ·
          refine ⟨13324296515065741450559197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17765728686754321934078929 13324296515065741450559197)
          ·
            refine ⟨4996611193149653043959699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13324296515065741450559197 4996611193149653043959699)
            ·
              refine ⟨7494916789724479565939549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996611193149653043959699 7494916789724479565939549)
              ·
                refine ⟨2810593796146679837227331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7494916789724479565939549 2810593796146679837227331)
                ·
                  refine ⟨4215890694220019755840997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810593796146679837227331 4215890694220019755840997)
                  ·
                    refine ⟨790479505166253704220187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215890694220019755840997 790479505166253704220187)
                    ·
                      rfl

theorem cell22_2309180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_2309180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309180 prefixEnd_2309180 := by exact prefixLift 2309180
  have htrace : WordTrace (prefixWord ++ tailWord_2309180) baseStart_2309180 baseEnd_2309180 := by
    simpa [prefixWord, tailWord_2309180, baseEnd_2309180] using wordTrace_append hprefix tailTrace_2309180
  have hstable : (prefixWord ++ tailWord_2309180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309180).length < 2 ^ (prefixWord ++ tailWord_2309180).sum := by decide
  have hdescent : baseEnd_2309180 < baseStart_2309180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309214 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2309214 : Nat := 118140960795 + 2309214 * 2 ^ 59
def prefixEnd_2309214 : Nat := 4983230072969 + 3 ^ 40 * 2309214 * 2
def baseEnd_2309214 : Nat := 790491144061088948870083

theorem tailTrace_2309214 : CollatzResearch.WordTrace tailWord_2309214 prefixEnd_2309214 790491144061088948870083 := by
  unfold tailWord_2309214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10527994232014941899740837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56149302570746356798617797 10527994232014941899740837)
  ·
    refine ⟨1973998918502801606201407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10527994232014941899740837 1973998918502801606201407)
    ·
      refine ⟨2960998377754202409302111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973998918502801606201407 2960998377754202409302111)
      ·
        refine ⟨4441497566631303613953167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960998377754202409302111 4441497566631303613953167)
        ·
          refine ⟨6662246349946955420929751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441497566631303613953167 6662246349946955420929751)
          ·
            refine ⟨9993369524920433131394627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662246349946955420929751 9993369524920433131394627)
            ·
              refine ⟨14990054287380649697091941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9993369524920433131394627 14990054287380649697091941)
              ·
                refine ⟨2810635178883871818204739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14990054287380649697091941 2810635178883871818204739)
                ·
                  refine ⟨4215952768325807727307109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810635178883871818204739 4215952768325807727307109)
                  ·
                    refine ⟨790491144061088948870083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215952768325807727307109 790491144061088948870083)
                    ·
                      rfl

theorem cell22_2309214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2309214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309214 prefixEnd_2309214 := by exact prefixLift 2309214
  have htrace : WordTrace (prefixWord ++ tailWord_2309214) baseStart_2309214 baseEnd_2309214 := by
    simpa [prefixWord, tailWord_2309214, baseEnd_2309214] using wordTrace_append hprefix tailTrace_2309214
  have hstable : (prefixWord ++ tailWord_2309214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309214).length < 2 ^ (prefixWord ++ tailWord_2309214).sum := by decide
  have hdescent : baseEnd_2309214 < baseStart_2309214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309223 : List Nat := [1, 1, 5, 1, 1, 4, 1, 8]
def baseStart_2309223 : Nat := 118140960795 + 2309223 * 2 ^ 59
def prefixEnd_2309223 : Nat := 4983230072969 + 3 ^ 40 * 2309223 * 2
def baseEnd_2309223 : Nat := 87832691660557325043895

theorem tailTrace_2309223 : CollatzResearch.WordTrace tailWord_2309223 prefixEnd_2309223 87832691660557325043895 := by
  unfold tailWord_2309223
  simp only [CollatzResearch.WordTrace]
  refine ⟨84224282113086929735004323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56149521408724619823336215 84224282113086929735004323)
  ·
    refine ⟨126336423169630394602506485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84224282113086929735004323 126336423169630394602506485)
    ·
      refine ⟨11844039672152849493984983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126336423169630394602506485 11844039672152849493984983)
      ·
        refine ⟨17766059508229274240977475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11844039672152849493984983 17766059508229274240977475)
        ·
          refine ⟨26649089262343911361466213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17766059508229274240977475 26649089262343911361466213)
          ·
            refine ⟨4996704236689483380274915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26649089262343911361466213 4996704236689483380274915)
            ·
              refine ⟨7495056355034225070412373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4996704236689483380274915 7495056355034225070412373)
              ·
                refine ⟨87832691660557325043895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7495056355034225070412373 87832691660557325043895)
                ·
                  rfl

theorem cell22_2309223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 8].length) (baseStart_2309223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309223 prefixEnd_2309223 := by exact prefixLift 2309223
  have htrace : WordTrace (prefixWord ++ tailWord_2309223) baseStart_2309223 baseEnd_2309223 := by
    simpa [prefixWord, tailWord_2309223, baseEnd_2309223] using wordTrace_append hprefix tailTrace_2309223
  have hstable : (prefixWord ++ tailWord_2309223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309223).length < 2 ^ (prefixWord ++ tailWord_2309223).sum := by decide
  have hdescent : baseEnd_2309223 < baseStart_2309223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309246 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2309246 : Nat := 118140960795 + 2309246 * 2 ^ 59
def prefixEnd_2309246 : Nat := 4983230072969 + 3 ^ 40 * 2309246 * 2
def baseEnd_2309246 : Nat := 263500699438350510689995

theorem tailTrace_2309246 : CollatzResearch.WordTrace tailWord_2309246 prefixEnd_2309246 263500699438350510689995 := by
  unfold tailWord_2309246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528140124000450582886449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56150080661335736442061061 10528140124000450582886449)
  ·
    refine ⟨7896105093000337937164837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10528140124000450582886449 7896105093000337937164837)
    ·
      refine ⟨1480519704937563363218407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7896105093000337937164837 1480519704937563363218407)
      ·
        refine ⟨2220779557406345044827611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480519704937563363218407 2220779557406345044827611)
        ·
          refine ⟨3331169336109517567241417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220779557406345044827611 3331169336109517567241417)
          ·
            refine ⟨2498377002082138175431063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331169336109517567241417 2498377002082138175431063)
            ·
              refine ⟨3747565503123207263146595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498377002082138175431063 3747565503123207263146595)
              ·
                refine ⟨5621348254684810894719893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747565503123207263146595 5621348254684810894719893)
                ·
                  refine ⟨263500699438350510689995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5621348254684810894719893 263500699438350510689995)
                  ·
                    rfl

theorem cell22_2309246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2309246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309246 prefixEnd_2309246 := by exact prefixLift 2309246
  have htrace : WordTrace (prefixWord ++ tailWord_2309246) baseStart_2309246 baseEnd_2309246 := by
    simpa [prefixWord, tailWord_2309246, baseEnd_2309246] using wordTrace_append hprefix tailTrace_2309246
  have hstable : (prefixWord ++ tailWord_2309246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309246).length < 2 ^ (prefixWord ++ tailWord_2309246).sum := by decide
  have hdescent : baseEnd_2309246 < baseStart_2309246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309330 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_2309330 : Nat := 118140960795 + 2309330 * 2 ^ 59
def prefixEnd_2309330 : Nat := 4983230072969 + 3 ^ 40 * 2309330 * 2
def baseEnd_2309330 : Nat := 263510284410567770989909

theorem tailTrace_2309330 : CollatzResearch.WordTrace tailWord_2309330 prefixEnd_2309330 263510284410567770989909 := by
  unfold tailWord_2309330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057046180924821752287361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56152123149132858006099629 21057046180924821752287361)
  ·
    refine ⟨15792784635693616314215521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21057046180924821752287361 15792784635693616314215521)
    ·
      refine ⟨11844588476770212235661641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15792784635693616314215521 11844588476770212235661641)
      ·
        refine ⟨8883441357577659176746231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11844588476770212235661641 8883441357577659176746231)
        ·
          refine ⟨13325162036366488765119347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883441357577659176746231 13325162036366488765119347)
          ·
            refine ⟨19987743054549733147679021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13325162036366488765119347 19987743054549733147679021)
            ·
              refine ⟨7495403645456149930379633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19987743054549733147679021 7495403645456149930379633)
              ·
                refine ⟨5621552734092112447784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7495403645456149930379633 5621552734092112447784725)
                ·
                  refine ⟨263510284410567770989909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5621552734092112447784725 263510284410567770989909)
                  ·
                    rfl

theorem cell22_2309330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_2309330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309330 prefixEnd_2309330 := by exact prefixLift 2309330
  have htrace : WordTrace (prefixWord ++ tailWord_2309330) baseStart_2309330 baseEnd_2309330 := by
    simpa [prefixWord, tailWord_2309330, baseEnd_2309330] using wordTrace_append hprefix tailTrace_2309330
  have hstable : (prefixWord ++ tailWord_2309330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309330).length < 2 ^ (prefixWord ++ tailWord_2309330).sum := by decide
  have hdescent : baseEnd_2309330 < baseStart_2309330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309345 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2309345 : Nat := 118140960795 + 2309345 * 2 ^ 59
def prefixEnd_2309345 : Nat := 4983230072969 + 3 ^ 40 * 2309345 * 2
def baseEnd_2309345 : Nat := 790535988038248273844681

theorem tailTrace_2309345 : CollatzResearch.WordTrace tailWord_2309345 prefixEnd_2309345 790535988038248273844681 := by
  unfold tailWord_2309345
  simp only [CollatzResearch.WordTrace]
  refine ⟨84228731818644944570945489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56152487879096629713963659 84228731818644944570945489)
  ·
    refine ⟨63171548863983708428209117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84228731818644944570945489 63171548863983708428209117)
    ·
      refine ⟨23689330823993890660578419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63171548863983708428209117 23689330823993890660578419)
      ·
        refine ⟨35533996235990835990867629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23689330823993890660578419 35533996235990835990867629)
        ·
          refine ⟨13325248588496563496575361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35533996235990835990867629 13325248588496563496575361)
          ·
            refine ⟨9993936441372422622431521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13325248588496563496575361 9993936441372422622431521)
            ·
              refine ⟨7495452331029316966823641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9993936441372422622431521 7495452331029316966823641)
              ·
                refine ⟨5621589248271987725117731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7495452331029316966823641 5621589248271987725117731)
                ·
                  refine ⟨8432383872407981587676597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621589248271987725117731 8432383872407981587676597)
                  ·
                    refine ⟨790535988038248273844681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8432383872407981587676597 790535988038248273844681)
                    ·
                      rfl

theorem cell22_2309345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2309345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309345 prefixEnd_2309345 := by exact prefixLift 2309345
  have htrace : WordTrace (prefixWord ++ tailWord_2309345) baseStart_2309345 baseEnd_2309345 := by
    simpa [prefixWord, tailWord_2309345, baseEnd_2309345] using wordTrace_append hprefix tailTrace_2309345
  have hstable : (prefixWord ++ tailWord_2309345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309345).length < 2 ^ (prefixWord ++ tailWord_2309345).sum := by decide
  have hdescent : baseEnd_2309345 < baseStart_2309345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309379 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 2, 3]
def baseStart_2309379 : Nat := 118140960795 + 2309379 * 2 ^ 59
def prefixEnd_2309379 : Nat := 4983230072969 + 3 ^ 40 * 2309379 * 2
def baseEnd_2309379 : Nat := 790547626933083518494577

theorem tailTrace_2309379 : CollatzResearch.WordTrace tailWord_2309379 prefixEnd_2309379 790547626933083518494577 := by
  unfold tailWord_2309379
  simp only [CollatzResearch.WordTrace]
  refine ⟨84229971900521768377683191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56153314600347845585122127 84229971900521768377683191)
  ·
    refine ⟨126344957850782652566524787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84229971900521768377683191 126344957850782652566524787)
    ·
      refine ⟨189517436776173978849787181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126344957850782652566524787 189517436776173978849787181)
      ·
        refine ⟨71069038791065242068670193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189517436776173978849787181 71069038791065242068670193)
        ·
          refine ⟨53301779093298931551502645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71069038791065242068670193 53301779093298931551502645)
          ·
            refine ⟨4997041789996774832953373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53301779093298931551502645 4997041789996774832953373)
            ·
              refine ⟨1873890671248790562357515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4997041789996774832953373 1873890671248790562357515)
              ·
                refine ⟨2810836006873185843536273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873890671248790562357515 2810836006873185843536273)
                ·
                  refine ⟨2108127005154889382652205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810836006873185843536273 2108127005154889382652205)
                  ·
                    refine ⟨790547626933083518494577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108127005154889382652205 790547626933083518494577)
                    ·
                      rfl

theorem cell22_2309379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 3].length) (baseStart_2309379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309379 prefixEnd_2309379 := by exact prefixLift 2309379
  have htrace : WordTrace (prefixWord ++ tailWord_2309379) baseStart_2309379 baseEnd_2309379 := by
    simpa [prefixWord, tailWord_2309379, baseEnd_2309379] using wordTrace_append hprefix tailTrace_2309379
  have hstable : (prefixWord ++ tailWord_2309379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309379).length < 2 ^ (prefixWord ++ tailWord_2309379).sum := by decide
  have hdescent : baseEnd_2309379 < baseStart_2309379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309420 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_2309420 : Nat := 118140960795 + 2309420 * 2 ^ 59
def prefixEnd_2309420 : Nat := 4983230072969 + 3 ^ 40 * 2309420 * 2
def baseEnd_2309420 : Nat := 263520554023657692739817

theorem tailTrace_2309420 : CollatzResearch.WordTrace tailWord_2309420 prefixEnd_2309420 263520554023657692739817 := by
  unfold tailWord_2309420
  simp only [CollatzResearch.WordTrace]
  refine ⟨42115733646686616189962857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56154311528915488253283809 42115733646686616189962857)
  ·
    refine ⟨31586800235014962142472143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42115733646686616189962857 31586800235014962142472143)
    ·
      refine ⟨47380200352522443213708215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31586800235014962142472143 47380200352522443213708215)
      ·
        refine ⟨71070300528783664820562323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47380200352522443213708215 71070300528783664820562323)
        ·
          refine ⟨106605450793175497230843485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71070300528783664820562323 106605450793175497230843485)
          ·
            refine ⟨39977044047440811461566307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106605450793175497230843485 39977044047440811461566307)
            ·
              refine ⟨59965566071161217192349461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39977044047440811461566307 59965566071161217192349461)
              ·
                refine ⟨2810885909585682055891381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59965566071161217192349461 2810885909585682055891381)
                ·
                  refine ⟨263520554023657692739817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810885909585682055891381 263520554023657692739817)
                  ·
                    rfl

theorem cell22_2309420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_2309420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309420 prefixEnd_2309420 := by exact prefixLift 2309420
  have htrace : WordTrace (prefixWord ++ tailWord_2309420) baseStart_2309420 baseEnd_2309420 := by
    simpa [prefixWord, tailWord_2309420, baseEnd_2309420] using wordTrace_append hprefix tailTrace_2309420
  have hstable : (prefixWord ++ tailWord_2309420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309420).length < 2 ^ (prefixWord ++ tailWord_2309420).sum := by decide
  have hdescent : baseEnd_2309420 < baseStart_2309420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309430 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2309430 : Nat := 118140960795 + 2309430 * 2 ^ 59
def prefixEnd_2309430 : Nat := 4983230072969 + 3 ^ 40 * 2309430 * 2
def baseEnd_2309430 : Nat := 790565085275336385469421

theorem tailTrace_2309430 : CollatzResearch.WordTrace tailWord_2309430 prefixEnd_2309430 790565085275336385469421 := by
  unfold tailWord_2309430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264489501458562755486859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56154554682224669391859829 5264489501458562755486859)
  ·
    refine ⟨7896734252187844133230289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5264489501458562755486859 7896734252187844133230289)
    ·
      refine ⟨5922550689140883099922717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7896734252187844133230289 5922550689140883099922717)
      ·
        refine ⟨2220956508427831162471019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5922550689140883099922717 2220956508427831162471019)
        ·
          refine ⟨3331434762641746743706529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220956508427831162471019 3331434762641746743706529)
          ·
            refine ⟨2498576071981310057779897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331434762641746743706529 2498576071981310057779897)
            ·
              refine ⟨1873932053985982543334923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498576071981310057779897 1873932053985982543334923)
              ·
                refine ⟨2810898080978973815002385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873932053985982543334923 2810898080978973815002385)
                ·
                  refine ⟨2108173560734230361251789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810898080978973815002385 2108173560734230361251789)
                  ·
                    refine ⟨790565085275336385469421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108173560734230361251789 790565085275336385469421)
                    ·
                      rfl

theorem cell22_2309430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2309430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309430 prefixEnd_2309430 := by exact prefixLift 2309430
  have htrace : WordTrace (prefixWord ++ tailWord_2309430) baseStart_2309430 baseEnd_2309430 := by
    simpa [prefixWord, tailWord_2309430, baseEnd_2309430] using wordTrace_append hprefix tailTrace_2309430
  have hstable : (prefixWord ++ tailWord_2309430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309430).length < 2 ^ (prefixWord ++ tailWord_2309430).sum := by decide
  have hdescent : baseEnd_2309430 < baseStart_2309430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309495 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2309495 : Nat := 118140960795 + 2309495 * 2 ^ 59
def prefixEnd_2309495 : Nat := 4983230072969 + 3 ^ 40 * 2309495 * 2
def baseEnd_2309495 : Nat := 790587336103697882594221

theorem tailTrace_2309495 : CollatzResearch.WordTrace tailWord_2309495 prefixEnd_2309495 790587336103697882594221 := by
  unfold tailWord_2309495
  simp only [CollatzResearch.WordTrace]
  refine ⟨84234202768101520188905939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56156135178734346792603959 84234202768101520188905939)
  ·
    refine ⟨126351304152152280283358909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84234202768101520188905939 126351304152152280283358909)
    ·
      refine ⟨47381739057057105106259591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126351304152152280283358909 47381739057057105106259591)
      ·
        refine ⟨71072608585585657659389387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47381739057057105106259591 71072608585585657659389387)
        ·
          refine ⟨106608912878378486489084081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71072608585585657659389387 106608912878378486489084081)
          ·
            refine ⟨79956684658783864866813061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106608912878378486489084081 79956684658783864866813061)
            ·
              refine ⟨14991878373521974662527449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79956684658783864866813061 14991878373521974662527449)
              ·
                refine ⟨11243908780141480996895587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14991878373521974662527449 11243908780141480996895587)
                ·
                  refine ⟨16865863170212221495343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11243908780141480996895587 16865863170212221495343381)
                  ·
                    refine ⟨790587336103697882594221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16865863170212221495343381 790587336103697882594221)
                    ·
                      rfl

theorem cell22_2309495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2309495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309495 prefixEnd_2309495 := by exact prefixLift 2309495
  have htrace : WordTrace (prefixWord ++ tailWord_2309495) baseStart_2309495 baseEnd_2309495 := by
    simpa [prefixWord, tailWord_2309495, baseEnd_2309495] using wordTrace_append hprefix tailTrace_2309495
  have hstable : (prefixWord ++ tailWord_2309495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309495).length < 2 ^ (prefixWord ++ tailWord_2309495).sum := by decide
  have hdescent : baseEnd_2309495 < baseStart_2309495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309512 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2309512 : Nat := 118140960795 + 2309512 * 2 ^ 59
def prefixEnd_2309512 : Nat := 4983230072969 + 3 ^ 40 * 2309512 * 2
def baseEnd_2309512 : Nat := 790593155551115504919169

theorem tailTrace_2309512 : CollatzResearch.WordTrace tailWord_2309512 prefixEnd_2309512 790593155551115504919169 := by
  unfold tailWord_2309512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42117411404519966046137395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56156548539359954728183193 42117411404519966046137395)
  ·
    refine ⟨63176117106779949069206093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42117411404519966046137395 63176117106779949069206093)
    ·
      refine ⟨23691043915042480900952285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63176117106779949069206093 23691043915042480900952285)
      ·
        refine ⟨8884141468140930337857107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23691043915042480900952285 8884141468140930337857107)
        ·
          refine ⟨13326212202211395506785661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8884141468140930337857107 13326212202211395506785661)
          ·
            refine ⟨4997329575829273315044623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13326212202211395506785661 4997329575829273315044623)
            ·
              refine ⟨7495994363743909972566935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997329575829273315044623 7495994363743909972566935)
              ·
                refine ⟨11243991545615864958850403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7495994363743909972566935 11243991545615864958850403)
                ·
                  refine ⟨16865987318423797438275605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11243991545615864958850403 16865987318423797438275605)
                  ·
                    refine ⟨790593155551115504919169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16865987318423797438275605 790593155551115504919169)
                    ·
                      rfl

theorem cell22_2309512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2309512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309512 prefixEnd_2309512 := by exact prefixLift 2309512
  have htrace : WordTrace (prefixWord ++ tailWord_2309512) baseStart_2309512 baseEnd_2309512 := by
    simpa [prefixWord, tailWord_2309512, baseEnd_2309512] using wordTrace_append hprefix tailTrace_2309512
  have hstable : (prefixWord ++ tailWord_2309512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309512).length < 2 ^ (prefixWord ++ tailWord_2309512).sum := by decide
  have hdescent : baseEnd_2309512 < baseStart_2309512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309518 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2309518 : Nat := 118140960795 + 2309518 * 2 ^ 59
def prefixEnd_2309518 : Nat := 4983230072969 + 3 ^ 40 * 2309518 * 2
def baseEnd_2309518 : Nat := 790595209473733489269151

theorem tailTrace_2309518 : CollatzResearch.WordTrace tailWord_2309518 prefixEnd_2309518 790595209473733489269151 := by
  unfold tailWord_2309518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529380205877274389624151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56156694431345463411328805 10529380205877274389624151)
  ·
    refine ⟨15794070308815911584436227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10529380205877274389624151 15794070308815911584436227)
    ·
      refine ⟨23691105463223867376654341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15794070308815911584436227 23691105463223867376654341)
      ·
        refine ⟨4442082274354475133122689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23691105463223867376654341 4442082274354475133122689)
        ·
          refine ⟨3331561705765856349842017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4442082274354475133122689 3331561705765856349842017)
          ·
            refine ⟨2498671279324392262381513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331561705765856349842017 2498671279324392262381513)
            ·
              refine ⟨1874003459493294196786135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498671279324392262381513 1874003459493294196786135)
              ·
                refine ⟨2811005189239941295179203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874003459493294196786135 2811005189239941295179203)
                ·
                  refine ⟨4216507783859911942768805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811005189239941295179203 4216507783859911942768805)
                  ·
                    refine ⟨790595209473733489269151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216507783859911942768805 790595209473733489269151)
                    ·
                      rfl

theorem cell22_2309518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2309518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309518 prefixEnd_2309518 := by exact prefixLift 2309518
  have htrace : WordTrace (prefixWord ++ tailWord_2309518) baseStart_2309518 baseEnd_2309518 := by
    simpa [prefixWord, tailWord_2309518, baseEnd_2309518] using wordTrace_append hprefix tailTrace_2309518
  have hstable : (prefixWord ++ tailWord_2309518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309518).length < 2 ^ (prefixWord ++ tailWord_2309518).sum := by decide
  have hdescent : baseEnd_2309518 < baseStart_2309518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309561 : List Nat := [1, 2, 1, 4, 5, 1, 2, 6]
def baseStart_2309561 : Nat := 118140960795 + 2309561 * 2 ^ 59
def prefixEnd_2309561 : Nat := 4983230072969 + 3 ^ 40 * 2309561 * 2
def baseEnd_2309561 : Nat := 87845547694721745604891

theorem tailTrace_2309561 : CollatzResearch.WordTrace tailWord_2309561 prefixEnd_2309561 87845547694721745604891 := by
  unfold tailWord_2309561
  simp only [CollatzResearch.WordTrace]
  refine ⟨84236609985862413460808537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56157739990574942307205691 84236609985862413460808537)
  ·
    refine ⟨63177457489396810095606403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84236609985862413460808537 63177457489396810095606403)
    ·
      refine ⟨94766186234095215143409605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63177457489396810095606403 94766186234095215143409605)
      ·
        refine ⟨17768659918892852839389301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94766186234095215143409605 17768659918892852839389301)
        ·
          refine ⟨1665811867396204953692747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17768659918892852839389301 1665811867396204953692747)
          ·
            refine ⟨2498717801094307430539121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665811867396204953692747 2498717801094307430539121)
            ·
              refine ⟨1874038350820730572904341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498717801094307430539121 1874038350820730572904341)
              ·
                refine ⟨87845547694721745604891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1874038350820730572904341 87845547694721745604891)
                ·
                  rfl

theorem cell22_2309561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 6].length) (baseStart_2309561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309561 prefixEnd_2309561 := by exact prefixLift 2309561
  have htrace : WordTrace (prefixWord ++ tailWord_2309561) baseStart_2309561 baseEnd_2309561 := by
    simpa [prefixWord, tailWord_2309561, baseEnd_2309561] using wordTrace_append hprefix tailTrace_2309561
  have hstable : (prefixWord ++ tailWord_2309561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309561).length < 2 ^ (prefixWord ++ tailWord_2309561).sum := by decide
  have hdescent : baseEnd_2309561 < baseStart_2309561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309593 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_2309593 : Nat := 118140960795 + 2309593 * 2 ^ 59
def prefixEnd_2309593 : Nat := 4983230072969 + 3 ^ 40 * 2309593 * 2
def baseEnd_2309593 : Nat := 790620883506458293643921

theorem tailTrace_2309593 : CollatzResearch.WordTrace tailWord_2309593 prefixEnd_2309593 790620883506458293643921 := by
  unfold tailWord_2309593
  simp only [CollatzResearch.WordTrace]
  refine ⟨84237777121746482925973433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56158518081164321950648955 84237777121746482925973433)
  ·
    refine ⟨63178332841309862194480075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84237777121746482925973433 63178332841309862194480075)
    ·
      refine ⟨94767499261964793291720113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63178332841309862194480075 94767499261964793291720113)
      ·
        refine ⟨71075624446473594968790085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94767499261964793291720113 71075624446473594968790085)
        ·
          refine ⟨13326679583713799056648141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71075624446473594968790085 13326679583713799056648141)
          ·
            refine ⟨4997504843892674646243053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13326679583713799056648141 4997504843892674646243053)
            ·
              refine ⟨1874064316459752992341145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4997504843892674646243053 1874064316459752992341145)
              ·
                refine ⟨1405548237344814744255859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874064316459752992341145 1405548237344814744255859)
                ·
                  refine ⟨2108322356017222116383789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405548237344814744255859 2108322356017222116383789)
                  ·
                    refine ⟨790620883506458293643921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108322356017222116383789 790620883506458293643921)
                    ·
                      rfl

theorem cell22_2309593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_2309593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309593 prefixEnd_2309593 := by exact prefixLift 2309593
  have htrace : WordTrace (prefixWord ++ tailWord_2309593) baseStart_2309593 baseEnd_2309593 := by
    simpa [prefixWord, tailWord_2309593, baseEnd_2309593] using wordTrace_append hprefix tailTrace_2309593
  have hstable : (prefixWord ++ tailWord_2309593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309593).length < 2 ^ (prefixWord ++ tailWord_2309593).sum := by decide
  have hdescent : baseEnd_2309593 < baseStart_2309593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309651 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 4]
def baseStart_2309651 : Nat := 118140960795 + 2309651 * 2 ^ 59
def prefixEnd_2309651 : Nat := 4983230072969 + 3 ^ 40 * 2309651 * 2
def baseEnd_2309651 : Nat := 263546912697255158564581

theorem tailTrace_2309651 : CollatzResearch.WordTrace tailWord_2309651 prefixEnd_2309651 263546912697255158564581 := by
  unfold tailWord_2309651
  simp only [CollatzResearch.WordTrace]
  refine ⟨84239892555536358831584807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56159928370357572554389871 84239892555536358831584807)
  ·
    refine ⟨126359838833304538247377211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84239892555536358831584807 126359838833304538247377211)
    ·
      refine ⟨189539758249956807371065817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126359838833304538247377211 189539758249956807371065817)
      ·
        refine ⟨142154818687467605528299363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189539758249956807371065817 142154818687467605528299363)
        ·
          refine ⟨213232228031201408292449045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142154818687467605528299363 213232228031201408292449045)
          ·
            refine ⟨9995260688962566013708549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213232228031201408292449045 9995260688962566013708549)
            ·
              refine ⟨1874111379180481127570353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9995260688962566013708549 1874111379180481127570353)
              ·
                refine ⟨1405583534385360845677765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874111379180481127570353 1405583534385360845677765)
                ·
                  refine ⟨263546912697255158564581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405583534385360845677765 263546912697255158564581)
                  ·
                    rfl

theorem cell22_2309651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 4].length) (baseStart_2309651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309651 prefixEnd_2309651 := by exact prefixLift 2309651
  have htrace : WordTrace (prefixWord ++ tailWord_2309651) baseStart_2309651 baseEnd_2309651 := by
    simpa [prefixWord, tailWord_2309651, baseEnd_2309651] using wordTrace_append hprefix tailTrace_2309651
  have hstable : (prefixWord ++ tailWord_2309651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309651).length < 2 ^ (prefixWord ++ tailWord_2309651).sum := by decide
  have hdescent : baseEnd_2309651 < baseStart_2309651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309666 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2309666 : Nat := 118140960795 + 2309666 * 2 ^ 59
def prefixEnd_2309666 : Nat := 4983230072969 + 3 ^ 40 * 2309666 * 2
def baseEnd_2309666 : Nat := 790645872898310436568697

theorem tailTrace_2309666 : CollatzResearch.WordTrace tailWord_2309666 prefixEnd_2309666 790645872898310436568697 := by
  unfold tailWord_2309666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060109912620504098345213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56160293100321344262253901 21060109912620504098345213)
  ·
    refine ⟨7897541217232689036879455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21060109912620504098345213 7897541217232689036879455)
    ·
      refine ⟨11846311825849033555319183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897541217232689036879455 11846311825849033555319183)
      ·
        refine ⟨17769467738773550332978775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846311825849033555319183 17769467738773550332978775)
        ·
          refine ⟨26654201608160325499468163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17769467738773550332978775 26654201608160325499468163)
          ·
            refine ⟨39981302412240488249202245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26654201608160325499468163 39981302412240488249202245)
            ·
              refine ⟨7496494202295091546725421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39981302412240488249202245 7496494202295091546725421)
              ·
                refine ⟨2811185325860659330022033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7496494202295091546725421 2811185325860659330022033)
                ·
                  refine ⟨2108388994395494497516525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811185325860659330022033 2108388994395494497516525)
                  ·
                    refine ⟨790645872898310436568697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108388994395494497516525 790645872898310436568697)
                    ·
                      rfl

theorem cell22_2309666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2309666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309666 prefixEnd_2309666 := by exact prefixLift 2309666
  have htrace : WordTrace (prefixWord ++ tailWord_2309666) baseStart_2309666 baseEnd_2309666 := by
    simpa [prefixWord, tailWord_2309666, baseEnd_2309666] using wordTrace_append hprefix tailTrace_2309666
  have hstable : (prefixWord ++ tailWord_2309666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309666).length < 2 ^ (prefixWord ++ tailWord_2309666).sum := by decide
  have hdescent : baseEnd_2309666 < baseStart_2309666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309769 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 6]
def baseStart_2309769 : Nat := 118140960795 + 2309769 * 2 ^ 59
def prefixEnd_2309769 : Nat := 4983230072969 + 3 ^ 40 * 2309769 * 2
def baseEnd_2309769 : Nat := 263560377301084167081127

theorem tailTrace_2309769 : CollatzResearch.WordTrace tailWord_2309769 prefixEnd_2309769 263560377301084167081127 := by
  unfold tailWord_2309769
  simp only [CollatzResearch.WordTrace]
  refine ⟨84244196369108864984380361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56162797579405909989586907 84244196369108864984380361)
  ·
    refine ⟨63183147276831648738285271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84244196369108864984380361 63183147276831648738285271)
    ·
      refine ⟨94774720915247473107427907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63183147276831648738285271 94774720915247473107427907)
      ·
        refine ⟨142162081372871209661141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94774720915247473107427907 142162081372871209661141861)
        ·
          refine ⟨26655390257413351811464099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142162081372871209661141861 26655390257413351811464099)
          ·
            refine ⟨39983085386120027717196149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26655390257413351811464099 39983085386120027717196149)
            ·
              refine ⟨3748414254948752598487139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39983085386120027717196149 3748414254948752598487139)
              ·
                refine ⟨5622621382423128897730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748414254948752598487139 5622621382423128897730709)
                ·
                  refine ⟨263560377301084167081127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5622621382423128897730709 263560377301084167081127)
                  ·
                    rfl

theorem cell22_2309769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_2309769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309769 prefixEnd_2309769 := by exact prefixLift 2309769
  have htrace : WordTrace (prefixWord ++ tailWord_2309769) baseStart_2309769 baseEnd_2309769 := by
    simpa [prefixWord, tailWord_2309769, baseEnd_2309769] using wordTrace_append hprefix tailTrace_2309769
  have hstable : (prefixWord ++ tailWord_2309769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309769).length < 2 ^ (prefixWord ++ tailWord_2309769).sum := by decide
  have hdescent : baseEnd_2309769 < baseStart_2309769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309818 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_2309818 : Nat := 118140960795 + 2309818 * 2 ^ 59
def prefixEnd_2309818 : Nat := 4983230072969 + 3 ^ 40 * 2309818 * 2
def baseEnd_2309818 : Nat := 790697905604632706768231

theorem tailTrace_2309818 : CollatzResearch.WordTrace tailWord_2309818 prefixEnd_2309818 790697905604632706768231 := by
  unfold tailWord_2309818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21061495886482836588228527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56163989030620897568609405 21061495886482836588228527)
  ·
    refine ⟨31592243829724254882342791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21061495886482836588228527 31592243829724254882342791)
    ·
      refine ⟨47388365744586382323514187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31592243829724254882342791 47388365744586382323514187)
      ·
        refine ⟨71082548616879573485271281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47388365744586382323514187 71082548616879573485271281)
        ·
          refine ⟨53311911462659680113953461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71082548616879573485271281 53311911462659680113953461)
          ·
            refine ⟨4997991699624345010683137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53311911462659680113953461 4997991699624345010683137)
            ·
              refine ⟨3748493774718258758012353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4997991699624345010683137 3748493774718258758012353)
              ·
                refine ⟨2811370331038694068509265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748493774718258758012353 2811370331038694068509265)
                ·
                  refine ⟨2108527748279020551381949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811370331038694068509265 2108527748279020551381949)
                  ·
                    refine ⟨790697905604632706768231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108527748279020551381949 790697905604632706768231)
                    ·
                      rfl

theorem cell22_2309818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_2309818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309818 prefixEnd_2309818 := by exact prefixLift 2309818
  have htrace : WordTrace (prefixWord ++ tailWord_2309818) baseStart_2309818 baseEnd_2309818 := by
    simpa [prefixWord, tailWord_2309818, baseEnd_2309818] using wordTrace_append hprefix tailTrace_2309818
  have hstable : (prefixWord ++ tailWord_2309818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309818).length < 2 ^ (prefixWord ++ tailWord_2309818).sum := by decide
  have hdescent : baseEnd_2309818 < baseStart_2309818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309820 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_2309820 : Nat := 118140960795 + 2309820 * 2 ^ 59
def prefixEnd_2309820 : Nat := 4983230072969 + 3 ^ 40 * 2309820 * 2
def baseEnd_2309820 : Nat := 263566196748501789406075

theorem tailTrace_2309820 : CollatzResearch.WordTrace tailWord_2309820 prefixEnd_2309820 263566196748501789406075 := by
  unfold tailWord_2309820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42123028245962050347243457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56164037661282733796324609 42123028245962050347243457)
  ·
    refine ⟨31592271184471537760432593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42123028245962050347243457 31592271184471537760432593)
    ·
      refine ⟨23694203388353653320324445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31592271184471537760432593 23694203388353653320324445)
      ·
        refine ⟨8885326270632619995121667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23694203388353653320324445 8885326270632619995121667)
        ·
          refine ⟨13327989405948929992682501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8885326270632619995121667 13327989405948929992682501)
          ·
            refine ⟨2498998013615424373627969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13327989405948929992682501 2498998013615424373627969)
            ·
              refine ⟨1874248510211568280220977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498998013615424373627969 1874248510211568280220977)
              ·
                refine ⟨1405686382658676210165733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874248510211568280220977 1405686382658676210165733)
                ·
                  refine ⟨263566196748501789406075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405686382658676210165733 263566196748501789406075)
                  ·
                    rfl

theorem cell22_2309820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_2309820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309820 prefixEnd_2309820 := by exact prefixLift 2309820
  have htrace : WordTrace (prefixWord ++ tailWord_2309820) baseStart_2309820 baseEnd_2309820 := by
    simpa [prefixWord, tailWord_2309820, baseEnd_2309820] using wordTrace_append hprefix tailTrace_2309820
  have hstable : (prefixWord ++ tailWord_2309820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309820).length < 2 ^ (prefixWord ++ tailWord_2309820).sum := by decide
  have hdescent : baseEnd_2309820 < baseStart_2309820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309938 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_2309938 : Nat := 118140960795 + 2309938 * 2 ^ 59
def prefixEnd_2309938 : Nat := 4983230072969 + 3 ^ 40 * 2309938 * 2
def baseEnd_2309938 : Nat := 263579661352330797922621

theorem tailTrace_2309938 : CollatzResearch.WordTrace tailWord_2309938 prefixEnd_2309938 263579661352330797922621 := by
  unfold tailWord_2309938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062590076374151711820617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56166906870331071231521645 21062590076374151711820617)
  ·
    refine ⟨15796942557280613783865463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21062590076374151711820617 15796942557280613783865463)
    ·
      refine ⟨23695413835920920675798195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15796942557280613783865463 23695413835920920675798195)
      ·
        refine ⟨35543120753881381013697293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23695413835920920675798195 35543120753881381013697293)
        ·
          refine ⟨13328670282705517880136485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35543120753881381013697293 13328670282705517880136485)
          ·
            refine ⟨2499125678007284602525591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13328670282705517880136485 2499125678007284602525591)
            ·
              refine ⟨3748688517010926903788387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499125678007284602525591 3748688517010926903788387)
              ·
                refine ⟨5623032775516390355682581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748688517010926903788387 5623032775516390355682581)
                ·
                  refine ⟨263579661352330797922621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5623032775516390355682581 263579661352330797922621)
                  ·
                    rfl

theorem cell22_2309938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_2309938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309938 prefixEnd_2309938 := by exact prefixLift 2309938
  have htrace : WordTrace (prefixWord ++ tailWord_2309938) baseStart_2309938 baseEnd_2309938 := by
    simpa [prefixWord, tailWord_2309938, baseEnd_2309938] using wordTrace_append hprefix tailTrace_2309938
  have hstable : (prefixWord ++ tailWord_2309938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309938).length < 2 ^ (prefixWord ++ tailWord_2309938).sum := by decide
  have hdescent : baseEnd_2309938 < baseStart_2309938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2309996 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_2309996 : Nat := 118140960795 + 2309996 * 2 ^ 59
def prefixEnd_2309996 : Nat := 4983230072969 + 3 ^ 40 * 2309996 * 2
def baseEnd_2309996 : Nat := 790758838642299575817685

theorem tailTrace_2309996 : CollatzResearch.WordTrace tailWord_2309996 prefixEnd_2309996 790758838642299575817685 := by
  unfold tailWord_2309996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126237869643241376446921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56168317159524321835262561 42126237869643241376446921)
  ·
    refine ⟨31594678402232431032335191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42126237869643241376446921 31594678402232431032335191)
    ·
      refine ⟨47392017603348646548502787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31594678402232431032335191 47392017603348646548502787)
      ·
        refine ⟨71088026405022969822754181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47392017603348646548502787 71088026405022969822754181)
        ·
          refine ⟨13329004950941806841766409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71088026405022969822754181 13329004950941806841766409)
          ·
            refine ⟨9996753713206355131324807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13329004950941806841766409 9996753713206355131324807)
            ·
              refine ⟨14995130569809532696987211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996753713206355131324807 14995130569809532696987211)
              ·
                refine ⟨22492695854714299045480817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14995130569809532696987211 22492695854714299045480817)
                ·
                  refine ⟨16869521891035724284110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22492695854714299045480817 16869521891035724284110613)
                  ·
                    refine ⟨790758838642299575817685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16869521891035724284110613 790758838642299575817685)
                    ·
                      rfl

theorem cell22_2309996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_2309996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2309996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2309996 prefixEnd_2309996 := by exact prefixLift 2309996
  have htrace : WordTrace (prefixWord ++ tailWord_2309996) baseStart_2309996 baseEnd_2309996 := by
    simpa [prefixWord, tailWord_2309996, baseEnd_2309996] using wordTrace_append hprefix tailTrace_2309996
  have hstable : (prefixWord ++ tailWord_2309996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2309996).length < 2 ^ (prefixWord ++ tailWord_2309996).sum := by decide
  have hdescent : baseEnd_2309996 < baseStart_2309996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2309996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310038 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2310038 : Nat := 118140960795 + 2310038 * 2 ^ 59
def prefixEnd_2310038 : Nat := 4983230072969 + 3 ^ 40 * 2310038 * 2
def baseEnd_2310038 : Nat := 790773216100625466267557

theorem tailTrace_2310038 : CollatzResearch.WordTrace tailWord_2310038 prefixEnd_2310038 790773216100625466267557 := by
  unfold tailWord_2310038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265875475320895245370173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56169338403422882617281845 5265875475320895245370173)
  ·
    refine ⟨1974703303245335717013815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5265875475320895245370173 1974703303245335717013815)
    ·
      refine ⟨2962054954868003575520723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974703303245335717013815 2962054954868003575520723)
      ·
        refine ⟨4443082432302005363281085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962054954868003575520723 4443082432302005363281085)
        ·
          refine ⟨1666155912113252011230407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4443082432302005363281085 1666155912113252011230407)
          ·
            refine ⟨2499233868169878016845611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666155912113252011230407 2499233868169878016845611)
            ·
              refine ⟨3748850802254817025268417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499233868169878016845611 3748850802254817025268417)
              ·
                refine ⟨2811638101691112768951313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748850802254817025268417 2811638101691112768951313)
                ·
                  refine ⟨2108728576268334576713485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811638101691112768951313 2108728576268334576713485)
                  ·
                    refine ⟨790773216100625466267557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108728576268334576713485 790773216100625466267557)
                    ·
                      rfl

theorem cell22_2310038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2310038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310038 prefixEnd_2310038 := by exact prefixLift 2310038
  have htrace : WordTrace (prefixWord ++ tailWord_2310038) baseStart_2310038 baseEnd_2310038 := by
    simpa [prefixWord, tailWord_2310038, baseEnd_2310038] using wordTrace_append hprefix tailTrace_2310038
  have hstable : (prefixWord ++ tailWord_2310038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310038).length < 2 ^ (prefixWord ++ tailWord_2310038).sum := by decide
  have hdescent : baseEnd_2310038 < baseStart_2310038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310045 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2310045 : Nat := 118140960795 + 2310045 * 2 ^ 59
def prefixEnd_2310045 : Nat := 4983230072969 + 3 ^ 40 * 2310045 * 2
def baseEnd_2310045 : Nat := 263591870781226593780845

theorem tailTrace_2310045 : CollatzResearch.WordTrace tailWord_2310045 prefixEnd_2310045 263591870781226593780845 := by
  unfold tailWord_2310045
  simp only [CollatzResearch.WordTrace]
  refine ⟨84254262916108964121427589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56169508610739309414285059 84254262916108964121427589)
  ·
    refine ⟨15797674296770430772767673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84254262916108964121427589 15797674296770430772767673)
    ·
      refine ⟨11848255722577823079575755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15797674296770430772767673 11848255722577823079575755)
      ·
        refine ⟨17772383583866734619363633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11848255722577823079575755 17772383583866734619363633)
        ·
          refine ⟨13329287687900050964522725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17772383583866734619363633 13329287687900050964522725)
          ·
            refine ⟨2499241441481259555848011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13329287687900050964522725 2499241441481259555848011)
            ·
              refine ⟨3748862162221889333772017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499241441481259555848011 3748862162221889333772017)
              ·
                refine ⟨2811646621666417000329013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748862162221889333772017 2811646621666417000329013)
                ·
                  refine ⟨263591870781226593780845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811646621666417000329013 263591870781226593780845)
                  ·
                    rfl

theorem cell22_2310045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2310045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310045 prefixEnd_2310045 := by exact prefixLift 2310045
  have htrace : WordTrace (prefixWord ++ tailWord_2310045) baseStart_2310045 baseEnd_2310045 := by
    simpa [prefixWord, tailWord_2310045, baseEnd_2310045] using wordTrace_append hprefix tailTrace_2310045
  have hstable : (prefixWord ++ tailWord_2310045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310045).length < 2 ^ (prefixWord ++ tailWord_2310045).sum := by decide
  have hdescent : baseEnd_2310045 < baseStart_2310045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310090 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_2310090 : Nat := 118140960795 + 2310090 * 2 ^ 59
def prefixEnd_2310090 : Nat := 4983230072969 + 3 ^ 40 * 2310090 * 2
def baseEnd_2310090 : Nat := 263597005587771554655799

theorem tailTrace_2310090 : CollatzResearch.WordTrace tailWord_2310090 prefixEnd_2310090 263597005587771554655799 := by
  unfold tailWord_2310090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063976050236484201703931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56170602800630624537877149 21063976050236484201703931)
  ·
    refine ⟨31595964075354726302555897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21063976050236484201703931 31595964075354726302555897)
    ·
      refine ⟨23696973056516044726916923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31595964075354726302555897 23696973056516044726916923)
      ·
        refine ⟨35545459584774067090375385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23696973056516044726916923 35545459584774067090375385)
        ·
          refine ⟨26659094688580550317781539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35545459584774067090375385 26659094688580550317781539)
          ·
            refine ⟨39988642032870825476672309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26659094688580550317781539 39988642032870825476672309)
            ·
              refine ⟨3748935190581639888438029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39988642032870825476672309 3748935190581639888438029)
              ·
                refine ⟨1405850696468114958164261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3748935190581639888438029 1405850696468114958164261)
                ·
                  refine ⟨263597005587771554655799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405850696468114958164261 263597005587771554655799)
                  ·
                    rfl

theorem cell22_2310090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_2310090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310090 prefixEnd_2310090 := by exact prefixLift 2310090
  have htrace : WordTrace (prefixWord ++ tailWord_2310090) baseStart_2310090 baseEnd_2310090 := by
    simpa [prefixWord, tailWord_2310090, baseEnd_2310090] using wordTrace_append hprefix tailTrace_2310090
  have hstable : (prefixWord ++ tailWord_2310090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310090).length < 2 ^ (prefixWord ++ tailWord_2310090).sum := by decide
  have hdescent : baseEnd_2310090 < baseStart_2310090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310103 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2310103 : Nat := 118140960795 + 2310103 * 2 ^ 59
def prefixEnd_2310103 : Nat := 4983230072969 + 3 ^ 40 * 2310103 * 2
def baseEnd_2310103 : Nat := 790795466928986963392357

theorem tailTrace_2310103 : CollatzResearch.WordTrace tailWord_2310103 prefixEnd_2310103 790795466928986963392357 := by
  unfold tailWord_2310103
  simp only [CollatzResearch.WordTrace]
  refine ⟨84256378349898840027038963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56170918899932560018025975 84256378349898840027038963)
  ·
    refine ⟨126384567524848260040558445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84256378349898840027038963 126384567524848260040558445)
    ·
      refine ⟨47394212821818097515209417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126384567524848260040558445 47394212821818097515209417)
      ·
        refine ⟨35545659616363573136407063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47394212821818097515209417 35545659616363573136407063)
        ·
          refine ⟨53318489424545359704610595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35545659616363573136407063 53318489424545359704610595)
          ·
            refine ⟨79977734136818039556915893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53318489424545359704610595 79977734136818039556915893)
            ·
              refine ⟨7497912575326691208460865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79977734136818039556915893 7497912575326691208460865)
              ·
                refine ⟨5623434431495018406345649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7497912575326691208460865 5623434431495018406345649)
                ·
                  refine ⟨4217575823621263804759237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5623434431495018406345649 4217575823621263804759237)
                  ·
                    refine ⟨790795466928986963392357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4217575823621263804759237 790795466928986963392357)
                    ·
                      rfl

theorem cell22_2310103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2310103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310103 prefixEnd_2310103 := by exact prefixLift 2310103
  have htrace : WordTrace (prefixWord ++ tailWord_2310103) baseStart_2310103 baseEnd_2310103 := by
    simpa [prefixWord, tailWord_2310103, baseEnd_2310103] using wordTrace_append hprefix tailTrace_2310103
  have hstable : (prefixWord ++ tailWord_2310103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310103).length < 2 ^ (prefixWord ++ tailWord_2310103).sum := by decide
  have hdescent : baseEnd_2310103 < baseStart_2310103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310163 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 5]
def baseStart_2310163 : Nat := 118140960795 + 2310163 * 2 ^ 59
def prefixEnd_2310163 : Nat := 4983230072969 + 3 ^ 40 * 2310163 * 2
def baseEnd_2310163 : Nat := 263605335385055602297391

theorem tailTrace_2310163 : CollatzResearch.WordTrace tailWord_2310163 prefixEnd_2310163 263605335385055602297391 := by
  unfold tailWord_2310163
  simp only [CollatzResearch.WordTrace]
  refine ⟨84258566729681470274223143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56172377819787646849482095 84258566729681470274223143)
  ·
    refine ⟨126387850094522205411334715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84258566729681470274223143 126387850094522205411334715)
    ·
      refine ⟨189581775141783308117002073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126387850094522205411334715 189581775141783308117002073)
      ·
        refine ⟨142186331356337481087751555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189581775141783308117002073 142186331356337481087751555)
        ·
          refine ⟨213279497034506221631627333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142186331356337481087751555 213279497034506221631627333)
          ·
            refine ⟨39989905693969916555930125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213279497034506221631627333 39989905693969916555930125)
            ·
              refine ⟨14996214635238718708473797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39989905693969916555930125 14996214635238718708473797)
              ·
                refine ⟨2811790244107259757838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14996214635238718708473797 2811790244107259757838837)
                ·
                  refine ⟨263605335385055602297391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811790244107259757838837 263605335385055602297391)
                  ·
                    rfl

theorem cell22_2310163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].length) (baseStart_2310163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310163 prefixEnd_2310163 := by exact prefixLift 2310163
  have htrace : WordTrace (prefixWord ++ tailWord_2310163) baseStart_2310163 baseEnd_2310163 := by
    simpa [prefixWord, tailWord_2310163, baseEnd_2310163] using wordTrace_append hprefix tailTrace_2310163
  have hstable : (prefixWord ++ tailWord_2310163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310163).length < 2 ^ (prefixWord ++ tailWord_2310163).sum := by decide
  have hdescent : baseEnd_2310163 < baseStart_2310163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310184 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2310184 : Nat := 118140960795 + 2310184 * 2 ^ 59
def prefixEnd_2310184 : Nat := 4983230072969 + 3 ^ 40 * 2310184 * 2
def baseEnd_2310184 : Nat := 790823194884329752117109

theorem tailTrace_2310184 : CollatzResearch.WordTrace tailWord_2310184 prefixEnd_2310184 790823194884329752117109 := by
  unfold tailWord_2310184
  simp only [CollatzResearch.WordTrace]
  refine ⟨42129666331302695430368803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56172888441736927240491737 42129666331302695430368803)
  ·
    refine ⟨63194499496954043145553205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42129666331302695430368803 63194499496954043145553205)
    ·
      refine ⟨5924484327839441544895613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63194499496954043145553205 5924484327839441544895613)
      ·
        refine ⟨2221681622939790579335855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5924484327839441544895613 2221681622939790579335855)
        ·
          refine ⟨3332522434409685869003783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221681622939790579335855 3332522434409685869003783)
          ·
            refine ⟨4998783651614528803505675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332522434409685869003783 4998783651614528803505675)
            ·
              refine ⟨7498175477421793205258513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998783651614528803505675 7498175477421793205258513)
              ·
                refine ⟨5623631608066344903943885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7498175477421793205258513 5623631608066344903943885)
                ·
                  refine ⟨2108861853024879338978957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5623631608066344903943885 2108861853024879338978957)
                  ·
                    refine ⟨790823194884329752117109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2108861853024879338978957 790823194884329752117109)
                    ·
                      rfl

theorem cell22_2310184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2310184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310184 prefixEnd_2310184 := by exact prefixLift 2310184
  have htrace : WordTrace (prefixWord ++ tailWord_2310184) baseStart_2310184 baseEnd_2310184 := by
    simpa [prefixWord, tailWord_2310184, baseEnd_2310184] using wordTrace_append hprefix tailTrace_2310184
  have hstable : (prefixWord ++ tailWord_2310184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310184).length < 2 ^ (prefixWord ++ tailWord_2310184).sum := by decide
  have hdescent : baseEnd_2310184 < baseStart_2310184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310240 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_2310240 : Nat := 118140960795 + 2310240 * 2 ^ 59
def prefixEnd_2310240 : Nat := 4983230072969 + 3 ^ 40 * 2310240 * 2
def baseEnd_2310240 : Nat := 790842364828764272716937

theorem tailTrace_2310240 : CollatzResearch.WordTrace tailWord_2310240 prefixEnd_2310240 790842364828764272716937 := by
  unfold tailWord_2310240
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130687575201256212388087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56174250100268341616517449 42130687575201256212388087)
  ·
    refine ⟨63196031362801884318582131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42130687575201256212388087 63196031362801884318582131)
    ·
      refine ⟨94794047044202826477873197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63196031362801884318582131 94794047044202826477873197)
      ·
        refine ⟨35547767641576059929202449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94794047044202826477873197 35547767641576059929202449)
        ·
          refine ⟨26660825731182044946901837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35547767641576059929202449 26660825731182044946901837)
          ·
            refine ⟨9997809649193266855088189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26660825731182044946901837 9997809649193266855088189)
            ·
              refine ⟨3749178618447475070658071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9997809649193266855088189 3749178618447475070658071)
              ·
                refine ⟨5623767927671212605987107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749178618447475070658071 5623767927671212605987107)
                ·
                  refine ⟨8435651891506818908980661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623767927671212605987107 8435651891506818908980661)
                  ·
                    refine ⟨790842364828764272716937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8435651891506818908980661 790842364828764272716937)
                    ·
                      rfl

theorem cell22_2310240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_2310240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310240 prefixEnd_2310240 := by exact prefixLift 2310240
  have htrace : WordTrace (prefixWord ++ tailWord_2310240) baseStart_2310240 baseEnd_2310240 := by
    simpa [prefixWord, tailWord_2310240, baseEnd_2310240] using wordTrace_append hprefix tailTrace_2310240
  have hstable : (prefixWord ++ tailWord_2310240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310240).length < 2 ^ (prefixWord ++ tailWord_2310240).sum := by decide
  have hdescent : baseEnd_2310240 < baseStart_2310240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310336 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_2310336 : Nat := 118140960795 + 2310336 * 2 ^ 59
def prefixEnd_2310336 : Nat := 4983230072969 + 3 ^ 40 * 2310336 * 2
def baseEnd_2310336 : Nat := 790875227590652022316643

theorem tailTrace_2310336 : CollatzResearch.WordTrace tailWord_2310336 prefixEnd_2310336 790875227590652022316643 := by
  unfold tailWord_2310336
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132438279027360410135431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56176584372036480546847241 42132438279027360410135431)
  ·
    refine ⟨63198657418541040615203147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42132438279027360410135431 63198657418541040615203147)
    ·
      refine ⟨94797986127811560922804721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63198657418541040615203147 94797986127811560922804721)
      ·
        refine ⟨71098489595858670692103541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94797986127811560922804721 71098489595858670692103541)
        ·
          refine ⟨6665483399611750377384707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71098489595858670692103541 6665483399611750377384707)
          ·
            refine ⟨9998225099417625566077061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6665483399611750377384707 9998225099417625566077061)
            ·
              refine ⟨1874667206140804793639449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9998225099417625566077061 1874667206140804793639449)
              ·
                refine ⟨1406000404605603595229587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874667206140804793639449 1406000404605603595229587)
                ·
                  refine ⟨2109000606908405392844381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406000404605603595229587 2109000606908405392844381)
                  ·
                    refine ⟨790875227590652022316643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109000606908405392844381 790875227590652022316643)
                    ·
                      rfl

theorem cell22_2310336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_2310336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310336 prefixEnd_2310336 := by exact prefixLift 2310336
  have htrace : WordTrace (prefixWord ++ tailWord_2310336) baseStart_2310336 baseEnd_2310336 := by
    simpa [prefixWord, tailWord_2310336, baseEnd_2310336] using wordTrace_append hprefix tailTrace_2310336
  have hstable : (prefixWord ++ tailWord_2310336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310336).length < 2 ^ (prefixWord ++ tailWord_2310336).sum := by decide
  have hdescent : baseEnd_2310336 < baseStart_2310336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310360 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_2310360 : Nat := 118140960795 + 2310360 * 2 ^ 59
def prefixEnd_2310360 : Nat := 4983230072969 + 3 ^ 40 * 2310360 * 2
def baseEnd_2310360 : Nat := 263627814427041319905523

theorem tailTrace_2310360 : CollatzResearch.WordTrace tailWord_2310360 prefixEnd_2310360 263627814427041319905523 := by
  unfold tailWord_2310360
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132875954983886459572267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56177167939978515279429689 42132875954983886459572267)
  ·
    refine ⟨63199313932475829689358401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42132875954983886459572267 63199313932475829689358401)
    ·
      refine ⟨47399485449356872267018801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63199313932475829689358401 47399485449356872267018801)
      ·
        refine ⟨35549614087017654200264101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47399485449356872267018801 35549614087017654200264101)
        ·
          refine ⟨6665552641315810162549519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35549614087017654200264101 6665552641315810162549519)
          ·
            refine ⟨9998328961973715243824279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6665552641315810162549519 9998328961973715243824279)
            ·
              refine ⟨14997493442960572865736419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9998328961973715243824279 14997493442960572865736419)
              ·
                refine ⟨22496240164440859298604629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14997493442960572865736419 22496240164440859298604629)
                ·
                  refine ⟨263627814427041319905523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22496240164440859298604629 263627814427041319905523)
                  ·
                    rfl

theorem cell22_2310360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_2310360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310360 prefixEnd_2310360 := by exact prefixLift 2310360
  have htrace : WordTrace (prefixWord ++ tailWord_2310360) baseStart_2310360 baseEnd_2310360 := by
    simpa [prefixWord, tailWord_2310360, baseEnd_2310360] using wordTrace_append hprefix tailTrace_2310360
  have hstable : (prefixWord ++ tailWord_2310360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310360).length < 2 ^ (prefixWord ++ tailWord_2310360).sum := by decide
  have hdescent : baseEnd_2310360 < baseStart_2310360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310529 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 6]
def baseStart_2310529 : Nat := 118140960795 + 2310529 * 2 ^ 59
def prefixEnd_2310529 : Nat := 4983230072969 + 3 ^ 40 * 2310529 * 2
def baseEnd_2310529 : Nat := 263647098478287950747017

theorem tailTrace_2310529 : CollatzResearch.WordTrace tailWord_2310529 prefixEnd_2310529 263647098478287950747017 := by
  unfold tailWord_2310529
  simp only [CollatzResearch.WordTrace]
  refine ⟨84271915846355514782046641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56181277230903676521364427 84271915846355514782046641)
  ·
    refine ⟨63203936884766636086534981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84271915846355514782046641 63203936884766636086534981)
    ·
      refine ⟨11850738165893744266225309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63203936884766636086534981 11850738165893744266225309)
      ·
        refine ⟨4444026812210154099834491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11850738165893744266225309 4444026812210154099834491)
        ·
          refine ⟨6666040218315231149751737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444026812210154099834491 6666040218315231149751737)
          ·
            refine ⟨4999530163736423362313803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6666040218315231149751737 4999530163736423362313803)
            ·
              refine ⟨7499295245604635043470705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999530163736423362313803 7499295245604635043470705)
              ·
                refine ⟨5624471434203476282603029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499295245604635043470705 5624471434203476282603029)
                ·
                  refine ⟨263647098478287950747017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5624471434203476282603029 263647098478287950747017)
                  ·
                    rfl

theorem cell22_2310529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_2310529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310529 prefixEnd_2310529 := by exact prefixLift 2310529
  have htrace : WordTrace (prefixWord ++ tailWord_2310529) baseStart_2310529 baseEnd_2310529 := by
    simpa [prefixWord, tailWord_2310529, baseEnd_2310529] using wordTrace_append hprefix tailTrace_2310529
  have hstable : (prefixWord ++ tailWord_2310529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310529).length < 2 ^ (prefixWord ++ tailWord_2310529).sum := by decide
  have hdescent : baseEnd_2310529 < baseStart_2310529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310602 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_2310602 : Nat := 118140960795 + 2310602 * 2 ^ 59
def prefixEnd_2310602 : Nat := 4983230072969 + 3 ^ 40 * 2310602 * 2
def baseEnd_2310602 : Nat := 263655428275571998388609

theorem tailTrace_2310602 : CollatzResearch.WordTrace tailWord_2310602 prefixEnd_2310602 263655428275571998388609 := by
  unfold tailWord_2310602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21068644593772762062363515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56183052250060698832969373 21068644593772762062363515)
  ·
    refine ⟨31602966890659143093545273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21068644593772762062363515 31602966890659143093545273)
    ·
      refine ⟨23702225167994357320158955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31602966890659143093545273 23702225167994357320158955)
      ·
        refine ⟨35553337751991535980238433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23702225167994357320158955 35553337751991535980238433)
        ·
          refine ⟨26665003313993651985178825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35553337751991535980238433 26665003313993651985178825)
          ·
            refine ⟨19998752485495238988884119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26665003313993651985178825 19998752485495238988884119)
            ·
              refine ⟨29998128728242858483326179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19998752485495238988884119 29998128728242858483326179)
              ·
                refine ⟨44997193092364287724989269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29998128728242858483326179 44997193092364287724989269)
                ·
                  refine ⟨263655428275571998388609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44997193092364287724989269 263655428275571998388609)
                  ·
                    rfl

theorem cell22_2310602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_2310602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310602 prefixEnd_2310602 := by exact prefixLift 2310602
  have htrace : WordTrace (prefixWord ++ tailWord_2310602) baseStart_2310602 baseEnd_2310602 := by
    simpa [prefixWord, tailWord_2310602, baseEnd_2310602] using wordTrace_append hprefix tailTrace_2310602
  have hstable : (prefixWord ++ tailWord_2310602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310602).length < 2 ^ (prefixWord ++ tailWord_2310602).sum := by decide
  have hdescent : baseEnd_2310602 < baseStart_2310602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310696 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2310696 : Nat := 118140960795 + 2310696 * 2 ^ 59
def prefixEnd_2310696 : Nat := 4983230072969 + 3 ^ 40 * 2310696 * 2
def baseEnd_2310696 : Nat := 790998462947731083315539

theorem tailTrace_2310696 : CollatzResearch.WordTrace tailWord_2310696 prefixEnd_2310696 790998462947731083315539 := by
  unfold tailWord_2310696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42139003418375251151687971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56185337891167001535583961 42139003418375251151687971)
  ·
    refine ⟨63208505127562876727531957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42139003418375251151687971 63208505127562876727531957)
    ·
      refine ⟨5925797355709019693206121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63208505127562876727531957 5925797355709019693206121)
      ·
        refine ⟨4444348016781764769904591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5925797355709019693206121 4444348016781764769904591)
        ·
          refine ⟨6666522025172647154856887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444348016781764769904591 6666522025172647154856887)
          ·
            refine ⟨9999783037758970732285331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6666522025172647154856887 9999783037758970732285331)
            ·
              refine ⟨14999674556638456098427997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9999783037758970732285331 14999674556638456098427997)
              ·
                refine ⟨5624877958739421036910499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14999674556638456098427997 5624877958739421036910499)
                ·
                  refine ⟨8437316938109131555365749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624877958739421036910499 8437316938109131555365749)
                  ·
                    refine ⟨790998462947731083315539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8437316938109131555365749 790998462947731083315539)
                    ·
                      rfl

theorem cell22_2310696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2310696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310696 prefixEnd_2310696 := by exact prefixLift 2310696
  have htrace : WordTrace (prefixWord ++ tailWord_2310696) baseStart_2310696 baseEnd_2310696 := by
    simpa [prefixWord, tailWord_2310696, baseEnd_2310696] using wordTrace_append hprefix tailTrace_2310696
  have hstable : (prefixWord ++ tailWord_2310696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310696).length < 2 ^ (prefixWord ++ tailWord_2310696).sum := by decide
  have hdescent : baseEnd_2310696 < baseStart_2310696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310741 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_2310741 : Nat := 118140960795 + 2310741 * 2 ^ 59
def prefixEnd_2310741 : Nat := 4983230072969 + 3 ^ 40 * 2310741 * 2
def baseEnd_2310741 : Nat := 791013867367365965940401

theorem tailTrace_2310741 : CollatzResearch.WordTrace tailWord_2310741 prefixEnd_2310741 791013867367365965940401 := by
  unfold tailWord_2310741
  simp only [CollatzResearch.WordTrace]
  refine ⟨84279648121587474988764077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56186432081058316659176051 84279648121587474988764077)
  ·
    refine ⟨31604868045595303120786529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84279648121587474988764077 31604868045595303120786529)
    ·
      refine ⟨23703651034196477340589897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31604868045595303120786529 23703651034196477340589897)
      ·
        refine ⟨17777738275647358005442423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23703651034196477340589897 17777738275647358005442423)
        ·
          refine ⟨26666607413471037008163635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17777738275647358005442423 26666607413471037008163635)
          ·
            refine ⟨39999911120206555512245453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26666607413471037008163635 39999911120206555512245453)
            ·
              refine ⟨14999966670077458317092045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39999911120206555512245453 14999966670077458317092045)
              ·
                refine ⟨5624987501279046868909517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14999966670077458317092045 5624987501279046868909517)
                ·
                  refine ⟨2109370312979642575841069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5624987501279046868909517 2109370312979642575841069)
                  ·
                    refine ⟨791013867367365965940401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109370312979642575841069 791013867367365965940401)
                    ·
                      rfl

theorem cell22_2310741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_2310741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310741 prefixEnd_2310741 := by exact prefixLift 2310741
  have htrace : WordTrace (prefixWord ++ tailWord_2310741) baseStart_2310741 baseEnd_2310741 := by
    simpa [prefixWord, tailWord_2310741, baseEnd_2310741] using wordTrace_append hprefix tailTrace_2310741
  have hstable : (prefixWord ++ tailWord_2310741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310741).length < 2 ^ (prefixWord ++ tailWord_2310741).sum := by decide
  have hdescent : baseEnd_2310741 < baseStart_2310741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310760 : List Nat := [2, 1, 4, 3, 3, 1, 2, 6]
def baseStart_2310760 : Nat := 118140960795 + 2310760 * 2 ^ 59
def prefixEnd_2310760 : Nat := 4983230072969 + 3 ^ 40 * 2310760 * 2
def baseEnd_2310760 : Nat := 87891152383961805523927

theorem tailTrace_2310760 : CollatzResearch.WordTrace tailWord_2310760 prefixEnd_2310760 87891152383961805523927 := by
  unfold tailWord_2310760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42140170554259320616852867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56186894072345760822470489 42140170554259320616852867)
  ·
    refine ⟨63210255831388980925279301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42140170554259320616852867 63210255831388980925279301)
    ·
      refine ⟨11851922968385433923489869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63210255831388980925279301 11851922968385433923489869)
      ·
        refine ⟨4444471113144537721308701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11851922968385433923489869 4444471113144537721308701)
        ·
          refine ⟨1666676667429201645490763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4444471113144537721308701 1666676667429201645490763)
          ·
            refine ⟨2500015001143802468236145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666676667429201645490763 2500015001143802468236145)
            ·
              refine ⟨1875011250857851851177109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500015001143802468236145 1875011250857851851177109)
              ·
                refine ⟨87891152383961805523927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875011250857851851177109 87891152383961805523927)
                ·
                  rfl

theorem cell22_2310760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_2310760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310760 prefixEnd_2310760 := by exact prefixLift 2310760
  have htrace : WordTrace (prefixWord ++ tailWord_2310760) baseStart_2310760 baseEnd_2310760 := by
    simpa [prefixWord, tailWord_2310760, baseEnd_2310760] using wordTrace_append hprefix tailTrace_2310760
  have hstable : (prefixWord ++ tailWord_2310760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310760).length < 2 ^ (prefixWord ++ tailWord_2310760).sum := by decide
  have hdescent : baseEnd_2310760 < baseStart_2310760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310831 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_2310831 : Nat := 118140960795 + 2310831 * 2 ^ 59
def prefixEnd_2310831 : Nat := 4983230072969 + 3 ^ 40 * 2310831 * 2
def baseEnd_2310831 : Nat := 791044676206635731190125

theorem tailTrace_2310831 : CollatzResearch.WordTrace tailWord_2310831 prefixEnd_2310831 791044676206635731190125 := by
  unfold tailWord_2310831
  simp only [CollatzResearch.WordTrace]
  refine ⟨84282930691261420359540347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56188620460840946906360231 84282930691261420359540347)
  ·
    refine ⟨126424396036892130539310521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84282930691261420359540347 126424396036892130539310521)
    ·
      refine ⟨94818297027669097904482891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126424396036892130539310521 94818297027669097904482891)
      ·
        refine ⟨142227445541503646856724337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94818297027669097904482891 142227445541503646856724337)
        ·
          refine ⟨106670584156127735142543253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142227445541503646856724337 106670584156127735142543253)
          ·
            refine ⟨5000183632318487584806715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106670584156127735142543253 5000183632318487584806715)
            ·
              refine ⟨7500275448477731377210073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000183632318487584806715 7500275448477731377210073)
              ·
                refine ⟨5625206586358298532907555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7500275448477731377210073 5625206586358298532907555)
                ·
                  refine ⟨8437809879537447799361333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625206586358298532907555 8437809879537447799361333)
                  ·
                    refine ⟨791044676206635731190125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8437809879537447799361333 791044676206635731190125)
                    ·
                      rfl

theorem cell22_2310831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_2310831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310831 prefixEnd_2310831 := by exact prefixLift 2310831
  have htrace : WordTrace (prefixWord ++ tailWord_2310831) baseStart_2310831 baseEnd_2310831 := by
    simpa [prefixWord, tailWord_2310831, baseEnd_2310831] using wordTrace_append hprefix tailTrace_2310831
  have hstable : (prefixWord ++ tailWord_2310831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310831).length < 2 ^ (prefixWord ++ tailWord_2310831).sum := by decide
  have hdescent : baseEnd_2310831 < baseStart_2310831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
