import V185TrunkScan23Chunk0639

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3784841 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 4, 2]
def baseStart_3784841 : Nat := 118140960795 + 3784841 * 2 ^ 59
def prefixEnd_3784841 : Nat := 4983230072969 + 3 ^ 40 * 3784841 * 2
def baseEnd_3784841 : Nat := 1943442633843731525881339

theorem tailTrace_3784841 : CollatzResearch.WordTrace tailWord_3784841 prefixEnd_3784841 1943442633843731525881339 := by
  unfold tailWord_3784841
  simp only [CollatzResearch.WordTrace]
  refine ⟨138044492081174931225426377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92029661387449954150284251 138044492081174931225426377)
  ·
    refine ⟨103533369060881198419069783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138044492081174931225426377 103533369060881198419069783)
    ·
      refine ⟨155300053591321797628604675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103533369060881198419069783 155300053591321797628604675)
      ·
        refine ⟨232950080386982696442907013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155300053591321797628604675 232950080386982696442907013)
        ·
          refine ⟨43678140072559255583045065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232950080386982696442907013 43678140072559255583045065)
          ·
            refine ⟨32758605054419441687283799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43678140072559255583045065 32758605054419441687283799)
            ·
              refine ⟨49137907581629162530925699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32758605054419441687283799 49137907581629162530925699)
              ·
                refine ⟨73706861372443743796388549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49137907581629162530925699 73706861372443743796388549)
                ·
                  refine ⟨13820036507333201961822853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73706861372443743796388549 13820036507333201961822853)
                  ·
                    refine ⟨2591256845124975367841785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13820036507333201961822853 2591256845124975367841785)
                    ·
                      refine ⟨1943442633843731525881339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591256845124975367841785 1943442633843731525881339)
                      ·
                        rfl

theorem cell23_3784841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4, 2].length) (baseStart_3784841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784841 prefixEnd_3784841 := by exact prefixLift 3784841
  have htrace : WordTrace (prefixWord ++ tailWord_3784841) baseStart_3784841 baseEnd_3784841 := by
    simpa [prefixWord, tailWord_3784841, baseEnd_3784841] using wordTrace_append hprefix tailTrace_3784841
  have hstable : (prefixWord ++ tailWord_3784841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784841).length < 2 ^ (prefixWord ++ tailWord_3784841).sum := by decide
  have hdescent : baseEnd_3784841 < baseStart_3784841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784861 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3784861 : Nat := 118140960795 + 3784861 * 2 ^ 59
def prefixEnd_3784861 : Nat := 4983230072969 + 3 ^ 40 * 3784861 * 2
def baseEnd_3784861 : Nat := 1943452903456821447631247

theorem tailTrace_3784861 : CollatzResearch.WordTrace tailWord_3784861 prefixEnd_3784861 1943452903456821447631247 := by
  unfold tailWord_3784861
  simp only [CollatzResearch.WordTrace]
  refine ⟨138045221541102474641154437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92030147694068316427436291 138045221541102474641154437)
  ·
    refine ⟨25883479038956713995216457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138045221541102474641154437 25883479038956713995216457)
    ·
      refine ⟨19412609279217535496412343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25883479038956713995216457 19412609279217535496412343)
      ·
        refine ⟨29118913918826303244618515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19412609279217535496412343 29118913918826303244618515)
        ·
          refine ⟨43678370878239454866927773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29118913918826303244618515 43678370878239454866927773)
          ·
            refine ⟨16379389079339795575097915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43678370878239454866927773 16379389079339795575097915)
            ·
              refine ⟨24569083619009693362646873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16379389079339795575097915 24569083619009693362646873)
              ·
                refine ⟨18426812714257270021985155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24569083619009693362646873 18426812714257270021985155)
                ·
                  refine ⟨27640219071385905032977733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18426812714257270021985155 27640219071385905032977733)
                  ·
                    refine ⟨5182541075884857193683325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27640219071385905032977733 5182541075884857193683325)
                    ·
                      refine ⟨1943452903456821447631247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182541075884857193683325 1943452903456821447631247)
                      ·
                        rfl

theorem cell23_3784861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3784861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784861 prefixEnd_3784861 := by exact prefixLift 3784861
  have htrace : WordTrace (prefixWord ++ tailWord_3784861) baseStart_3784861 baseEnd_3784861 := by
    simpa [prefixWord, tailWord_3784861, baseEnd_3784861] using wordTrace_append hprefix tailTrace_3784861
  have hstable : (prefixWord ++ tailWord_3784861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784861).length < 2 ^ (prefixWord ++ tailWord_3784861).sum := by decide
  have hdescent : baseEnd_3784861 < baseStart_3784861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784904 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_3784904 : Nat := 118140960795 + 3784904 * 2 ^ 59
def prefixEnd_3784904 : Nat := 4983230072969 + 3 ^ 40 * 3784904 * 2
def baseEnd_3784904 : Nat := 1943474983124964779393549

theorem tailTrace_3784904 : CollatzResearch.WordTrace tailWord_3784904 prefixEnd_3784904 1943474983124964779393549 := by
  unfold tailWord_3784904
  simp only [CollatzResearch.WordTrace]
  refine ⟨69023394939973346492484883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92031193253297795323313177 69023394939973346492484883)
  ·
    refine ⟨103535092409960019738727325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69023394939973346492484883 103535092409960019738727325)
    ·
      refine ⟨38825659653735007402022747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103535092409960019738727325 38825659653735007402022747)
      ·
        refine ⟨58238489480602511103034121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38825659653735007402022747 58238489480602511103034121)
        ·
          refine ⟨43678867110451883327275591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58238489480602511103034121 43678867110451883327275591)
          ·
            refine ⟨65518300665677824990913387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43678867110451883327275591 65518300665677824990913387)
            ·
              refine ⟨98277450998516737486370081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65518300665677824990913387 98277450998516737486370081)
              ·
                refine ⟨73708088248887553114777561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98277450998516737486370081 73708088248887553114777561)
                ·
                  refine ⟨55281066186665664836083171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73708088248887553114777561 55281066186665664836083171)
                  ·
                    refine ⟨82921599279998497254124757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55281066186665664836083171 82921599279998497254124757)
                    ·
                      refine ⟨1943474983124964779393549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82921599279998497254124757 1943474983124964779393549)
                      ·
                        rfl

theorem cell23_3784904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3784904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784904 prefixEnd_3784904 := by exact prefixLift 3784904
  have htrace : WordTrace (prefixWord ++ tailWord_3784904) baseStart_3784904 baseEnd_3784904 := by
    simpa [prefixWord, tailWord_3784904, baseEnd_3784904] using wordTrace_append hprefix tailTrace_3784904
  have hstable : (prefixWord ++ tailWord_3784904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784904).length < 2 ^ (prefixWord ++ tailWord_3784904).sum := by decide
  have hdescent : baseEnd_3784904 < baseStart_3784904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784935 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3784935 : Nat := 118140960795 + 3784935 * 2 ^ 59
def prefixEnd_3784935 : Nat := 4983230072969 + 3 ^ 40 * 3784935 * 2
def baseEnd_3784935 : Nat := 1943490901025254158105907

theorem tailTrace_3784935 : CollatzResearch.WordTrace tailWord_3784935 prefixEnd_3784935 1943490901025254158105907 := by
  unfold tailWord_3784935
  simp only [CollatzResearch.WordTrace]
  refine ⟨138047920542834385279348259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92031947028556256852898839 138047920542834385279348259)
  ·
    refine ⟨207071880814251577919022389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138047920542834385279348259 207071880814251577919022389)
    ·
      refine ⟨19412988826336085429908349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207071880814251577919022389 19412988826336085429908349)
      ·
        refine ⟨7279870809876032036215631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19412988826336085429908349 7279870809876032036215631)
        ·
          refine ⟨10919806214814048054323447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279870809876032036215631 10919806214814048054323447)
          ·
            refine ⟨16379709322221072081485171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919806214814048054323447 16379709322221072081485171)
            ·
              refine ⟨24569563983331608122227757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16379709322221072081485171 24569563983331608122227757)
              ·
                refine ⟨9213586493749353045835409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24569563983331608122227757 9213586493749353045835409)
                ·
                  refine ⟨6910189870312014784376557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213586493749353045835409 6910189870312014784376557)
                  ·
                    refine ⟨2591321201367005544141209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6910189870312014784376557 2591321201367005544141209)
                    ·
                      refine ⟨1943490901025254158105907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591321201367005544141209 1943490901025254158105907)
                      ·
                        rfl

theorem cell23_3784935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3784935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784935 prefixEnd_3784935 := by exact prefixLift 3784935
  have htrace : WordTrace (prefixWord ++ tailWord_3784935) baseStart_3784935 baseEnd_3784935 := by
    simpa [prefixWord, tailWord_3784935, baseEnd_3784935] using wordTrace_append hprefix tailTrace_3784935
  have hstable : (prefixWord ++ tailWord_3784935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784935).length < 2 ^ (prefixWord ++ tailWord_3784935).sum := by decide
  have hdescent : baseEnd_3784935 < baseStart_3784935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784951 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_3784951 : Nat := 118140960795 + 3784951 * 2 ^ 59
def prefixEnd_3784951 : Nat := 4983230072969 + 3 ^ 40 * 3784951 * 2
def baseEnd_3784951 : Nat := 1943499116715726095505833

theorem tailTrace_3784951 : CollatzResearch.WordTrace tailWord_3784951 prefixEnd_3784951 1943499116715726095505833 := by
  unfold tailWord_3784951
  simp only [CollatzResearch.WordTrace]
  refine ⟨138048504110776420011930707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92032336073850946674620471 138048504110776420011930707)
  ·
    refine ⟨207072756166164630017896061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138048504110776420011930707 207072756166164630017896061)
    ·
      refine ⟨77652283562311736256711023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207072756166164630017896061 77652283562311736256711023)
      ·
        refine ⟨116478425343467604385066535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77652283562311736256711023 116478425343467604385066535)
        ·
          refine ⟨174717638015201406577599803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116478425343467604385066535 174717638015201406577599803)
          ·
            refine ⟨262076457022802109866399705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174717638015201406577599803 262076457022802109866399705)
            ·
              refine ⟨196557342767101582399799779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262076457022802109866399705 196557342767101582399799779)
              ·
                refine ⟨294836014150652373599699669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196557342767101582399799779 294836014150652373599699669)
                ·
                  refine ⟨6910219081655915006242961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 294836014150652373599699669 6910219081655915006242961)
                  ·
                    refine ⟨5182664311241936254682221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910219081655915006242961 5182664311241936254682221)
                    ·
                      refine ⟨1943499116715726095505833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182664311241936254682221 1943499116715726095505833)
                      ·
                        rfl

theorem cell23_3784951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_3784951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784951 prefixEnd_3784951 := by exact prefixLift 3784951
  have htrace : WordTrace (prefixWord ++ tailWord_3784951) baseStart_3784951 baseEnd_3784951 := by
    simpa [prefixWord, tailWord_3784951, baseEnd_3784951] using wordTrace_append hprefix tailTrace_3784951
  have hstable : (prefixWord ++ tailWord_3784951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784951).length < 2 ^ (prefixWord ++ tailWord_3784951).sum := by decide
  have hdescent : baseEnd_3784951 < baseStart_3784951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784954 : List Nat := [3, 1, 1, 1, 1, 16]
def baseStart_3784954 : Nat := 118140960795 + 3784954 * 2 ^ 59
def prefixEnd_3784954 : Nat := 4983230072969 + 3 ^ 40 * 3784954 * 2
def baseEnd_3784954 : Nat := 7997945091183907752133

theorem tailTrace_3784954 : CollatzResearch.WordTrace tailWord_3784954 prefixEnd_3784954 7997945091183907752133 := by
  unfold tailWord_3784954
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512153382441387881072479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92032409019843701016193277 34512153382441387881072479)
  ·
    refine ⟨51768230073662081821608719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34512153382441387881072479 51768230073662081821608719)
    ·
      refine ⟨77652345110493122732413079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51768230073662081821608719 77652345110493122732413079)
      ·
        refine ⟨116478517665739684098619619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77652345110493122732413079 116478517665739684098619619)
        ·
          refine ⟨174717776498609526147929429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116478517665739684098619619 174717776498609526147929429)
          ·
            refine ⟨7997945091183907752133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 174717776498609526147929429 7997945091183907752133)
            ·
              rfl

theorem cell23_3784954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 16].length) (baseStart_3784954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784954 prefixEnd_3784954 := by exact prefixLift 3784954
  have htrace : WordTrace (prefixWord ++ tailWord_3784954) baseStart_3784954 baseEnd_3784954 := by
    simpa [prefixWord, tailWord_3784954, baseEnd_3784954] using wordTrace_append hprefix tailTrace_3784954
  have hstable : (prefixWord ++ tailWord_3784954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784954).length < 2 ^ (prefixWord ++ tailWord_3784954).sum := by decide
  have hdescent : baseEnd_3784954 < baseStart_3784954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784961 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3784961 : Nat := 118140960795 + 3784961 * 2 ^ 59
def prefixEnd_3784961 : Nat := 4983230072969 + 3 ^ 40 * 3784961 * 2
def baseEnd_3784961 : Nat := 1943504251522271056380787

theorem tailTrace_3784961 : CollatzResearch.WordTrace tailWord_3784961 prefixEnd_3784961 1943504251522271056380787 := by
  unfold tailWord_3784961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138048868840740191719794737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92032579227160127813196491 138048868840740191719794737)
  ·
    refine ⟨103536651630555143789846053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138048868840740191719794737 103536651630555143789846053)
    ·
      refine ⟨19413122180729089460596135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103536651630555143789846053 19413122180729089460596135)
      ·
        refine ⟨29119683271093634190894203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413122180729089460596135 29119683271093634190894203)
        ·
          refine ⟨43679524906640451286341305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119683271093634190894203 43679524906640451286341305)
          ·
            refine ⟨32759643679980338464755979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43679524906640451286341305 32759643679980338464755979)
            ·
              refine ⟨49139465519970507697133969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32759643679980338464755979 49139465519970507697133969)
              ·
                refine ⟨36854599139977880772850477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49139465519970507697133969 36854599139977880772850477)
                ·
                  refine ⟨13820474677491705289818929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36854599139977880772850477 13820474677491705289818929)
                  ·
                    refine ⟨10365356008118778967364197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13820474677491705289818929 10365356008118778967364197)
                    ·
                      refine ⟨1943504251522271056380787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10365356008118778967364197 1943504251522271056380787)
                      ·
                        rfl

theorem cell23_3784961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3784961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784961 prefixEnd_3784961 := by exact prefixLift 3784961
  have htrace : WordTrace (prefixWord ++ tailWord_3784961) baseStart_3784961 baseEnd_3784961 := by
    simpa [prefixWord, tailWord_3784961, baseEnd_3784961] using wordTrace_append hprefix tailTrace_3784961
  have hstable : (prefixWord ++ tailWord_3784961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784961).length < 2 ^ (prefixWord ++ tailWord_3784961).sum := by decide
  have hdescent : baseEnd_3784961 < baseStart_3784961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784968 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3784968 : Nat := 118140960795 + 3784968 * 2 ^ 59
def prefixEnd_3784968 : Nat := 4983230072969 + 3 ^ 40 * 3784968 * 2
def baseEnd_3784968 : Nat := 1943507845886852528993255

theorem tailTrace_3784968 : CollatzResearch.WordTrace tailWord_3784968 prefixEnd_3784968 1943507845886852528993255 := by
  unfold tailWord_3784968
  simp only [CollatzResearch.WordTrace]
  refine ⟨69024562075857415957649779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92032749434476554610199705 69024562075857415957649779)
  ·
    refine ⟨103536843113786123936474669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69024562075857415957649779 103536843113786123936474669)
    ·
      refine ⟨38826316167669796476178001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103536843113786123936474669 38826316167669796476178001)
      ·
        refine ⟨29119737125752347357133501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38826316167669796476178001 29119737125752347357133501)
        ·
          refine ⟨10919901422157130258925063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29119737125752347357133501 10919901422157130258925063)
          ·
            refine ⟨16379852133235695388387595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919901422157130258925063 16379852133235695388387595)
            ·
              refine ⟨24569778199853543082581393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16379852133235695388387595 24569778199853543082581393)
              ·
                refine ⟨18427333649890157311936045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24569778199853543082581393 18427333649890157311936045)
                ·
                  refine ⟨6910250118708808991976017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18427333649890157311936045 6910250118708808991976017)
                  ·
                    refine ⟨5182687589031606743982013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910250118708808991976017 5182687589031606743982013)
                    ·
                      refine ⟨1943507845886852528993255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182687589031606743982013 1943507845886852528993255)
                      ·
                        rfl

theorem cell23_3784968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3784968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784968 prefixEnd_3784968 := by exact prefixLift 3784968
  have htrace : WordTrace (prefixWord ++ tailWord_3784968) baseStart_3784968 baseEnd_3784968 := by
    simpa [prefixWord, tailWord_3784968, baseEnd_3784968] using wordTrace_append hprefix tailTrace_3784968
  have hstable : (prefixWord ++ tailWord_3784968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784968).length < 2 ^ (prefixWord ++ tailWord_3784968).sum := by decide
  have hdescent : baseEnd_3784968 < baseStart_3784968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784999 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3784999 : Nat := 118140960795 + 3784999 * 2 ^ 59
def prefixEnd_3784999 : Nat := 4983230072969 + 3 ^ 40 * 3784999 * 2
def baseEnd_3784999 : Nat := 1943523763787141907705613

theorem tailTrace_3784999 : CollatzResearch.WordTrace tailWord_3784999 prefixEnd_3784999 1943523763787141907705613 := by
  unfold tailWord_3784999
  simp only [CollatzResearch.WordTrace]
  refine ⟨138050254814602524209678051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92033503209735016139785367 138050254814602524209678051)
  ·
    refine ⟨207075382221903786314517077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138050254814602524209678051 207075382221903786314517077)
    ·
      refine ⟨2426664635412934995873247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 207075382221903786314517077 2426664635412934995873247)
      ·
        refine ⟨3639996953119402493809871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426664635412934995873247 3639996953119402493809871)
        ·
          refine ⟨5459995429679103740714807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639996953119402493809871 5459995429679103740714807)
          ·
            refine ⟨8189993144518655611072211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459995429679103740714807 8189993144518655611072211)
            ·
              refine ⟨12284989716777983416608317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189993144518655611072211 12284989716777983416608317)
              ·
                refine ⟨4606871143791743781228119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12284989716777983416608317 4606871143791743781228119)
                ·
                  refine ⟨6910306715687615671842179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606871143791743781228119 6910306715687615671842179)
                  ·
                    refine ⟨10365460073531423507763269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910306715687615671842179 10365460073531423507763269)
                    ·
                      refine ⟨1943523763787141907705613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10365460073531423507763269 1943523763787141907705613)
                      ·
                        rfl

theorem cell23_3784999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3784999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784999 prefixEnd_3784999 := by exact prefixLift 3784999
  have htrace : WordTrace (prefixWord ++ tailWord_3784999) baseStart_3784999 baseEnd_3784999 := by
    simpa [prefixWord, tailWord_3784999, baseEnd_3784999] using wordTrace_append hprefix tailTrace_3784999
  have hstable : (prefixWord ++ tailWord_3784999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784999).length < 2 ^ (prefixWord ++ tailWord_3784999).sum := by decide
  have hdescent : baseEnd_3784999 < baseStart_3784999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785002 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3785002 : Nat := 118140960795 + 3785002 * 2 ^ 59
def prefixEnd_3785002 : Nat := 4983230072969 + 3 ^ 40 * 3785002 * 2
def baseEnd_3785002 : Nat := 1943525304229105395968099

theorem tailTrace_3785002 : CollatzResearch.WordTrace tailWord_3785002 prefixEnd_3785002 1943525304229105395968099 := by
  unfold tailWord_3785002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512591058397913930509315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92033576155727770481358173 34512591058397913930509315)
  ·
    refine ⟨51768886587596870895763973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34512591058397913930509315 51768886587596870895763973)
    ·
      refine ⟨9706666235174413292955745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51768886587596870895763973 9706666235174413292955745)
      ·
        refine ⟨7279999676380809969716809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9706666235174413292955745 7279999676380809969716809)
        ·
          refine ⟨5459999757285607477287607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7279999676380809969716809 5459999757285607477287607)
          ·
            refine ⟨8189999635928411215931411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459999757285607477287607 8189999635928411215931411)
            ·
              refine ⟨12284999453892616823897117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189999635928411215931411 12284999453892616823897117)
              ·
                refine ⟨4606874795209731308961419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12284999453892616823897117 4606874795209731308961419)
                ·
                  refine ⟨6910312192814596963442129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606874795209731308961419 6910312192814596963442129)
                  ·
                    refine ⟨5182734144610947722581597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6910312192814596963442129 5182734144610947722581597)
                    ·
                      refine ⟨1943525304229105395968099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182734144610947722581597 1943525304229105395968099)
                      ·
                        rfl

theorem cell23_3785002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3785002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785002 prefixEnd_3785002 := by exact prefixLift 3785002
  have htrace : WordTrace (prefixWord ++ tailWord_3785002) baseStart_3785002 baseEnd_3785002 := by
    simpa [prefixWord, tailWord_3785002, baseEnd_3785002] using wordTrace_append hprefix tailTrace_3785002
  have hstable : (prefixWord ++ tailWord_3785002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785002).length < 2 ^ (prefixWord ++ tailWord_3785002).sum := by decide
  have hdescent : baseEnd_3785002 < baseStart_3785002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785008 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2]
def baseStart_3785008 : Nat := 118140960795 + 3785008 * 2 ^ 59
def prefixEnd_3785008 : Nat := 4983230072969 + 3 ^ 40 * 3785008 * 2
def baseEnd_3785008 : Nat := 1943528385113032372493071

theorem tailTrace_3785008 : CollatzResearch.WordTrace tailWord_3785008 prefixEnd_3785008 1943528385113032372493071 := by
  unfold tailWord_3785008
  simp only [CollatzResearch.WordTrace]
  refine ⟨69025291535784959373377839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92033722047713279164503785 69025291535784959373377839)
  ·
    refine ⟨103537937303677439060066759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69025291535784959373377839 103537937303677439060066759)
    ·
      refine ⟨155306905955516158590100139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103537937303677439060066759 155306905955516158590100139)
      ·
        refine ⟨232960358933274237885150209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155306905955516158590100139 232960358933274237885150209)
        ·
          refine ⟨174720269199955678413862657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232960358933274237885150209 174720269199955678413862657)
          ·
            refine ⟨131040201899966758810396993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174720269199955678413862657 131040201899966758810396993)
            ·
              refine ⟨98280151424975069107797745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131040201899966758810396993 98280151424975069107797745)
              ·
                refine ⟨73710113568731301830848309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98280151424975069107797745 73710113568731301830848309)
                ·
                  refine ⟨6910323147068559546642029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73710113568731301830848309 6910323147068559546642029)
                  ·
                    refine ⟨2591371180150709829990761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6910323147068559546642029 2591371180150709829990761)
                    ·
                      refine ⟨1943528385113032372493071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591371180150709829990761 1943528385113032372493071)
                      ·
                        rfl

theorem cell23_3785008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2].length) (baseStart_3785008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785008 prefixEnd_3785008 := by exact prefixLift 3785008
  have htrace : WordTrace (prefixWord ++ tailWord_3785008) baseStart_3785008 baseEnd_3785008 := by
    simpa [prefixWord, tailWord_3785008, baseEnd_3785008] using wordTrace_append hprefix tailTrace_3785008
  have hstable : (prefixWord ++ tailWord_3785008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785008).length < 2 ^ (prefixWord ++ tailWord_3785008).sum := by decide
  have hdescent : baseEnd_3785008 < baseStart_3785008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785031 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3785031 : Nat := 118140960795 + 3785031 * 2 ^ 59
def prefixEnd_3785031 : Nat := 4983230072969 + 3 ^ 40 * 3785031 * 2
def baseEnd_3785031 : Nat := 647846731722695260835155

theorem tailTrace_3785031 : CollatzResearch.WordTrace tailWord_3785031 prefixEnd_3785031 647846731722695260835155 := by
  unfold tailWord_3785031
  simp only [CollatzResearch.WordTrace]
  refine ⟨138051421950486593674842947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92034281300324395783228631 138051421950486593674842947)
  ·
    refine ⟨207077132925729890512264421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138051421950486593674842947 207077132925729890512264421)
    ·
      refine ⟨38826962423574354471049579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207077132925729890512264421 38826962423574354471049579)
      ·
        refine ⟨58240443635361531706574369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38826962423574354471049579 58240443635361531706574369)
        ·
          refine ⟨43680332726521148779930777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58240443635361531706574369 43680332726521148779930777)
          ·
            refine ⟨32760249544890861584948083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43680332726521148779930777 32760249544890861584948083)
            ·
              refine ⟨49140374317336292377422125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32760249544890861584948083 49140374317336292377422125)
              ·
                refine ⟨18427640369001109641533297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49140374317336292377422125 18427640369001109641533297)
                ·
                  refine ⟨13820730276750832231149973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18427640369001109641533297 13820730276750832231149973)
                  ·
                    refine ⟨647846731722695260835155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13820730276750832231149973 647846731722695260835155)
                    ·
                      rfl

theorem cell23_3785031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3785031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785031 prefixEnd_3785031 := by exact prefixLift 3785031
  have htrace : WordTrace (prefixWord ++ tailWord_3785031) baseStart_3785031 baseEnd_3785031 := by
    simpa [prefixWord, tailWord_3785031, baseEnd_3785031] using wordTrace_append hprefix tailTrace_3785031
  have hstable : (prefixWord ++ tailWord_3785031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785031).length < 2 ^ (prefixWord ++ tailWord_3785031).sum := by decide
  have hdescent : baseEnd_3785031 < baseStart_3785031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785055 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 4, 2, 2]
def baseStart_3785055 : Nat := 118140960795 + 3785055 * 2 ^ 59
def prefixEnd_3785055 : Nat := 4983230072969 + 3 ^ 40 * 3785055 * 2
def baseEnd_3785055 : Nat := 1943552518703793688605355

theorem tailTrace_3785055 : CollatzResearch.WordTrace tailWord_3785055 prefixEnd_3785055 1943552518703793688605355 := by
  unfold tailWord_3785055
  simp only [CollatzResearch.WordTrace]
  refine ⟨138052297302399645773716619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92034864868266430515811079 138052297302399645773716619)
  ·
    refine ⟨207078445953599468660574929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138052297302399645773716619 207078445953599468660574929)
    ·
      refine ⟨155308834465199601495431197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207078445953599468660574929 155308834465199601495431197)
      ·
        refine ⟨58240812924449850560786699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155308834465199601495431197 58240812924449850560786699)
        ·
          refine ⟨87361219386674775841180049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58240812924449850560786699 87361219386674775841180049)
          ·
            refine ⟨65520914540006081880885037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87361219386674775841180049 65520914540006081880885037)
            ·
              refine ⟨24570342952502280705331889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65520914540006081880885037 24570342952502280705331889)
              ·
                refine ⟨18427757214376710528998917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24570342952502280705331889 18427757214376710528998917)
                ·
                  refine ⟨3455204477695633224187297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18427757214376710528998917 3455204477695633224187297)
                  ·
                    refine ⟨2591403358271724918140473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455204477695633224187297 2591403358271724918140473)
                    ·
                      refine ⟨1943552518703793688605355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591403358271724918140473 1943552518703793688605355)
                      ·
                        rfl

theorem cell23_3785055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_3785055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785055 prefixEnd_3785055 := by exact prefixLift 3785055
  have htrace : WordTrace (prefixWord ++ tailWord_3785055) baseStart_3785055 baseEnd_3785055 := by
    simpa [prefixWord, tailWord_3785055, baseEnd_3785055] using wordTrace_append hprefix tailTrace_3785055
  have hstable : (prefixWord ++ tailWord_3785055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785055).length < 2 ^ (prefixWord ++ tailWord_3785055).sum := by decide
  have hdescent : baseEnd_3785055 < baseStart_3785055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785058 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3785058 : Nat := 118140960795 + 3785058 * 2 ^ 59
def prefixEnd_3785058 : Nat := 4983230072969 + 3 ^ 40 * 3785058 * 2
def baseEnd_3785058 : Nat := 1943554059145757176867841

theorem tailTrace_3785058 : CollatzResearch.WordTrace tailWord_3785058 prefixEnd_3785058 1943554059145757176867841 := by
  unfold tailWord_3785058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34513101680347194321518957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92034937814259184857383885 34513101680347194321518957)
  ·
    refine ⟨12942413130130197870569609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34513101680347194321518957 12942413130130197870569609)
    ·
      refine ⟨9706809847597648402927207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12942413130130197870569609 9706809847597648402927207)
      ·
        refine ⟨14560214771396472604390811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706809847597648402927207 14560214771396472604390811)
        ·
          refine ⟨21840322157094708906586217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14560214771396472604390811 21840322157094708906586217)
          ·
            refine ⟨16380241617821031679939663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21840322157094708906586217 16380241617821031679939663)
            ·
              refine ⟨24570362426731547519909495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380241617821031679939663 24570362426731547519909495)
              ·
                refine ⟨36855543640097321279864243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24570362426731547519909495 36855543640097321279864243)
                ·
                  refine ⟨55283315460145981919796365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36855543640097321279864243 55283315460145981919796365)
                  ·
                    refine ⟨20731243297554743219923637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55283315460145981919796365 20731243297554743219923637)
                    ·
                      refine ⟨1943554059145757176867841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20731243297554743219923637 1943554059145757176867841)
                      ·
                        rfl

theorem cell23_3785058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3785058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785058 prefixEnd_3785058 := by exact prefixLift 3785058
  have htrace : WordTrace (prefixWord ++ tailWord_3785058) baseStart_3785058 baseEnd_3785058 := by
    simpa [prefixWord, tailWord_3785058, baseEnd_3785058] using wordTrace_append hprefix tailTrace_3785058
  have hstable : (prefixWord ++ tailWord_3785058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785058).length < 2 ^ (prefixWord ++ tailWord_3785058).sum := by decide
  have hdescent : baseEnd_3785058 < baseStart_3785058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785089 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3785089 : Nat := 118140960795 + 3785089 * 2 ^ 59
def prefixEnd_3785089 : Nat := 4983230072969 + 3 ^ 40 * 3785089 * 2
def baseEnd_3785089 : Nat := 1943569977046046555580199

theorem tailTrace_3785089 : CollatzResearch.WordTrace tailWord_3785089 prefixEnd_3785089 1943569977046046555580199 := by
  unfold tailWord_3785089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138053537384276469580454321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92035691589517646386969547 138053537384276469580454321)
  ·
    refine ⟨103540153038207352185340741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138053537384276469580454321 103540153038207352185340741)
    ·
      refine ⟨19413778694663878534751389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103540153038207352185340741 19413778694663878534751389)
      ·
        refine ⟨7280167010498954450531771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19413778694663878534751389 7280167010498954450531771)
        ·
          refine ⟨10920250515748431675797657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280167010498954450531771 10920250515748431675797657)
          ·
            refine ⟨8190187886811323756848243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10920250515748431675797657 8190187886811323756848243)
            ·
              refine ⟨12285281830216985635272365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190187886811323756848243 12285281830216985635272365)
              ·
                refine ⟨4606980686331369613227137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12285281830216985635272365 4606980686331369613227137)
                ·
                  refine ⟨3455235514748527209920353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4606980686331369613227137 3455235514748527209920353)
                  ·
                    refine ⟨2591426636061395407440265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455235514748527209920353 2591426636061395407440265)
                    ·
                      refine ⟨1943569977046046555580199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591426636061395407440265 1943569977046046555580199)
                      ·
                        rfl

theorem cell23_3785089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3785089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785089 prefixEnd_3785089 := by exact prefixLift 3785089
  have htrace : WordTrace (prefixWord ++ tailWord_3785089) baseStart_3785089 baseEnd_3785089 := by
    simpa [prefixWord, tailWord_3785089, baseEnd_3785089] using wordTrace_append hprefix tailTrace_3785089
  have hstable : (prefixWord ++ tailWord_3785089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785089).length < 2 ^ (prefixWord ++ tailWord_3785089).sum := by decide
  have hdescent : baseEnd_3785089 < baseStart_3785089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785110 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3785110 : Nat := 118140960795 + 3785110 * 2 ^ 59
def prefixEnd_3785110 : Nat := 4983230072969 + 3 ^ 40 * 3785110 * 2
def baseEnd_3785110 : Nat := 1943580760139790973417603

theorem tailTrace_3785110 : CollatzResearch.WordTrace tailWord_3785110 prefixEnd_3785110 1943580760139790973417603 := by
  unfold tailWord_3785110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628393957325024385435549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92036202211466926777979189 8628393957325024385435549)
  ·
    refine ⟨3235647733996884144538331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8628393957325024385435549 3235647733996884144538331)
    ·
      refine ⟨4853471600995326216807497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235647733996884144538331 4853471600995326216807497)
      ·
        refine ⟨3640103700746494662605623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853471600995326216807497 3640103700746494662605623)
        ·
          refine ⟨5460155551119741993908435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640103700746494662605623 5460155551119741993908435)
          ·
            refine ⟨8190233326679612990862653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460155551119741993908435 8190233326679612990862653)
            ·
              refine ⟨3071337497504854871573495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8190233326679612990862653 3071337497504854871573495)
              ·
                refine ⟨4607006246257282307360243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071337497504854871573495 4607006246257282307360243)
                ·
                  refine ⟨6910509369385923461040365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607006246257282307360243 6910509369385923461040365)
                  ·
                    refine ⟨2591441013519721297890137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6910509369385923461040365 2591441013519721297890137)
                    ·
                      refine ⟨1943580760139790973417603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591441013519721297890137 1943580760139790973417603)
                      ·
                        rfl

theorem cell23_3785110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3785110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785110 prefixEnd_3785110 := by exact prefixLift 3785110
  have htrace : WordTrace (prefixWord ++ tailWord_3785110) baseStart_3785110 baseEnd_3785110 := by
    simpa [prefixWord, tailWord_3785110, baseEnd_3785110] using wordTrace_append hprefix tailTrace_3785110
  have hstable : (prefixWord ++ tailWord_3785110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785110).length < 2 ^ (prefixWord ++ tailWord_3785110).sum := by decide
  have hdescent : baseEnd_3785110 < baseStart_3785110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785145 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3785145 : Nat := 118140960795 + 3785145 * 2 ^ 59
def prefixEnd_3785145 : Nat := 4983230072969 + 3 ^ 40 * 3785145 * 2
def baseEnd_3785145 : Nat := 1943598731962698336479941

theorem tailTrace_3785145 : CollatzResearch.WordTrace tailWord_3785145 prefixEnd_3785145 1943598731962698336479941 := by
  unfold tailWord_3785145
  simp only [CollatzResearch.WordTrace]
  refine ⟨138055579872073591144492889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92037053248049060762995259 138055579872073591144492889)
  ·
    refine ⟨103541684904055193358369667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138055579872073591144492889 103541684904055193358369667)
    ·
      refine ⟨155312527356082790037554501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103541684904055193358369667 155312527356082790037554501)
      ·
        refine ⟨29121098879265523132041469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155312527356082790037554501 29121098879265523132041469)
        ·
          refine ⟨10920412079724571174515551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29121098879265523132041469 10920412079724571174515551)
          ·
            refine ⟨16380618119586856761773327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920412079724571174515551 16380618119586856761773327)
            ·
              refine ⟨24570927179380285142659991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380618119586856761773327 24570927179380285142659991)
              ·
                refine ⟨36856390769070427713989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24570927179380285142659991 36856390769070427713989987)
                ·
                  refine ⟨55284586153605641570984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36856390769070427713989987 55284586153605641570984981)
                  ·
                    refine ⟨2591464975950264448639921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55284586153605641570984981 2591464975950264448639921)
                    ·
                      refine ⟨1943598731962698336479941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591464975950264448639921 1943598731962698336479941)
                      ·
                        rfl

theorem cell23_3785145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3785145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785145 prefixEnd_3785145 := by exact prefixLift 3785145
  have htrace : WordTrace (prefixWord ++ tailWord_3785145) baseStart_3785145 baseEnd_3785145 := by
    simpa [prefixWord, tailWord_3785145, baseEnd_3785145] using wordTrace_append hprefix tailTrace_3785145
  have hstable : (prefixWord ++ tailWord_3785145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785145).length < 2 ^ (prefixWord ++ tailWord_3785145).sum := by decide
  have hdescent : baseEnd_3785145 < baseStart_3785145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785151 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 12]
def baseStart_3785151 : Nat := 118140960795 + 3785151 * 2 ^ 59
def prefixEnd_3785151 : Nat := 4983230072969 + 3 ^ 40 * 3785151 * 2
def baseEnd_3785151 : Nat := 215955756982958368111657

theorem tailTrace_3785151 : CollatzResearch.WordTrace tailWord_3785151 prefixEnd_3785151 215955756982958368111657 := by
  unfold tailWord_3785151
  simp only [CollatzResearch.WordTrace]
  refine ⟨138055798710051854169211307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92037199140034569446140871 138055798710051854169211307)
  ·
    refine ⟨207083698065077781253816961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138055798710051854169211307 207083698065077781253816961)
    ·
      refine ⟨155312773548808335940362721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207083698065077781253816961 155312773548808335940362721)
      ·
        refine ⟨116484580161606251955272041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155312773548808335940362721 116484580161606251955272041)
        ·
          refine ⟨87363435121204688966454031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116484580161606251955272041 87363435121204688966454031)
          ·
            refine ⟨131045152681807033449681047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87363435121204688966454031 131045152681807033449681047)
            ·
              refine ⟨196567729022710550174521571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131045152681807033449681047 196567729022710550174521571)
              ·
                refine ⟨294851593534065825261782357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196567729022710550174521571 294851593534065825261782357)
                ·
                  refine ⟨215955756982958368111657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 294851593534065825261782357 215955756982958368111657)
                  ·
                    rfl

theorem cell23_3785151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 12].length) (baseStart_3785151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785151 prefixEnd_3785151 := by exact prefixLift 3785151
  have htrace : WordTrace (prefixWord ++ tailWord_3785151) baseStart_3785151 baseEnd_3785151 := by
    simpa [prefixWord, tailWord_3785151, baseEnd_3785151] using wordTrace_append hprefix tailTrace_3785151
  have hstable : (prefixWord ++ tailWord_3785151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785151).length < 2 ^ (prefixWord ++ tailWord_3785151).sum := by decide
  have hdescent : baseEnd_3785151 < baseStart_3785151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785215 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 1, 5]
def baseStart_3785215 : Nat := 118140960795 + 3785215 * 2 ^ 59
def prefixEnd_3785215 : Nat := 4983230072969 + 3 ^ 40 * 3785215 * 2
def baseEnd_3785215 : Nat := 647878225202837687534873

theorem tailTrace_3785215 : CollatzResearch.WordTrace tailWord_3785215 prefixEnd_3785215 647878225202837687534873 := by
  unfold tailWord_3785215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138058132981819993099541099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92038755321213328733027399 138058132981819993099541099)
  ·
    refine ⟨207087199472729989649311649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138058132981819993099541099 207087199472729989649311649)
    ·
      refine ⟨155315399604547492236983737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207087199472729989649311649 155315399604547492236983737)
      ·
        refine ⟨116486549703410619177737803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155315399604547492236983737 116486549703410619177737803)
        ·
          refine ⟨174729824555115928766606705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116486549703410619177737803 174729824555115928766606705)
          ·
            refine ⟨131047368416336946574955029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174729824555115928766606705 131047368416336946574955029)
            ·
              refine ⟨6142845394515794370701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131047368416336946574955029 6142845394515794370701017)
              ·
                refine ⟨4607134045886845778025763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6142845394515794370701017 4607134045886845778025763)
                ·
                  refine ⟨6910701068830268667038645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607134045886845778025763 6910701068830268667038645)
                  ·
                    refine ⟨647878225202837687534873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6910701068830268667038645 647878225202837687534873)
                    ·
                      rfl

theorem cell23_3785215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_3785215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785215 prefixEnd_3785215 := by exact prefixLift 3785215
  have htrace : WordTrace (prefixWord ++ tailWord_3785215) baseStart_3785215 baseEnd_3785215 := by
    simpa [prefixWord, tailWord_3785215, baseEnd_3785215] using wordTrace_append hprefix tailTrace_3785215
  have hstable : (prefixWord ++ tailWord_3785215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785215).length < 2 ^ (prefixWord ++ tailWord_3785215).sum := by decide
  have hdescent : baseEnd_3785215 < baseStart_3785215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785235 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 4]
def baseStart_3785235 : Nat := 118140960795 + 3785235 * 2 ^ 59
def prefixEnd_3785235 : Nat := 4983230072969 + 3 ^ 40 * 3785235 * 2
def baseEnd_3785235 : Nat := 1943644945221602984354527

theorem tailTrace_3785235 : CollatzResearch.WordTrace tailWord_3785235 prefixEnd_3785235 1943644945221602984354527 := by
  unfold tailWord_3785235
  simp only [CollatzResearch.WordTrace]
  refine ⟨138058862441747536515269159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92039241627831691010179439 138058862441747536515269159)
  ·
    refine ⟨207088293662621304772903739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138058862441747536515269159 207088293662621304772903739)
    ·
      refine ⟨310632440493931957159355609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207088293662621304772903739 310632440493931957159355609)
      ·
        refine ⟨232974330370448967869516707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310632440493931957159355609 232974330370448967869516707)
        ·
          refine ⟨349461495555673451804275061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232974330370448967869516707 349461495555673451804275061)
          ·
            refine ⟨32762015208344386106650787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349461495555673451804275061 32762015208344386106650787)
            ·
              refine ⟨49143022812516579159976181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32762015208344386106650787 49143022812516579159976181)
              ·
                refine ⟨4607158388673429296247767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49143022812516579159976181 4607158388673429296247767)
                ·
                  refine ⟨6910737583010143944371651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607158388673429296247767 6910737583010143944371651)
                  ·
                    refine ⟨10366106374515215916557477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910737583010143944371651 10366106374515215916557477)
                    ·
                      refine ⟨1943644945221602984354527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10366106374515215916557477 1943644945221602984354527)
                      ·
                        rfl

theorem cell23_3785235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_3785235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785235 prefixEnd_3785235 := by exact prefixLift 3785235
  have htrace : WordTrace (prefixWord ++ tailWord_3785235) baseStart_3785235 baseEnd_3785235 := by
    simpa [prefixWord, tailWord_3785235, baseEnd_3785235] using wordTrace_append hprefix tailTrace_3785235
  have hstable : (prefixWord ++ tailWord_3785235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785235).length < 2 ^ (prefixWord ++ tailWord_3785235).sum := by decide
  have hdescent : baseEnd_3785235 < baseStart_3785235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785285 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_3785285 : Nat := 118140960795 + 3785285 * 2 ^ 59
def prefixEnd_3785285 : Nat := 4983230072969 + 3 ^ 40 * 3785285 * 2
def baseEnd_3785285 : Nat := 1943670619254327788729297

theorem tailTrace_3785285 : CollatzResearch.WordTrace tailWord_3785285 prefixEnd_3785285 1943670619254327788729297 := by
  unfold tailWord_3785285
  simp only [CollatzResearch.WordTrace]
  refine ⟨138060686091566395054589309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92040457394377596703059539 138060686091566395054589309)
  ·
    refine ⟨51772757284337398145470991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138060686091566395054589309 51772757284337398145470991)
    ·
      refine ⟨77659135926506097218206487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51772757284337398145470991 77659135926506097218206487)
      ·
        refine ⟨116488703889759145827309731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77659135926506097218206487 116488703889759145827309731)
        ·
          refine ⟨174733055834638718740964597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116488703889759145827309731 174733055834638718740964597)
          ·
            refine ⟨16381223984497379881965431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174733055834638718740964597 16381223984497379881965431)
            ·
              refine ⟨24571835976746069822948147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16381223984497379881965431 24571835976746069822948147)
              ·
                refine ⟨36857753965119104734422221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24571835976746069822948147 36857753965119104734422221)
                ·
                  refine ⟨13821657736919664275408333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36857753965119104734422221 13821657736919664275408333)
                  ·
                    refine ⟨5183121651344874103278125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13821657736919664275408333 5183121651344874103278125)
                    ·
                      refine ⟨1943670619254327788729297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5183121651344874103278125 1943670619254327788729297)
                      ·
                        rfl

theorem cell23_3785285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_3785285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785285 prefixEnd_3785285 := by exact prefixLift 3785285
  have htrace : WordTrace (prefixWord ++ tailWord_3785285) baseStart_3785285 baseEnd_3785285 := by
    simpa [prefixWord, tailWord_3785285, baseEnd_3785285] using wordTrace_append hprefix tailTrace_3785285
  have hstable : (prefixWord ++ tailWord_3785285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785285).length < 2 ^ (prefixWord ++ tailWord_3785285).sum := by decide
  have hdescent : baseEnd_3785285 < baseStart_3785285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785288 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_3785288 : Nat := 118140960795 + 3785288 * 2 ^ 59
def prefixEnd_3785288 : Nat := 4983230072969 + 3 ^ 40 * 3785288 * 2
def baseEnd_3785288 : Nat := 647890719898763758997261

theorem tailTrace_3785288 : CollatzResearch.WordTrace tailWord_3785288 prefixEnd_3785288 647890719898763758997261 := by
  unfold tailWord_3785288
  simp only [CollatzResearch.WordTrace]
  refine ⟨69030397755277763283474259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92040530340370351044632345 69030397755277763283474259)
  ·
    refine ⟨103545596632916644925211389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69030397755277763283474259 103545596632916644925211389)
    ·
      refine ⟨38829598737343741846954271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103545596632916644925211389 38829598737343741846954271)
      ·
        refine ⟨58244398106015612770431407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829598737343741846954271 58244398106015612770431407)
        ·
          refine ⟨87366597159023419155647111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58244398106015612770431407 87366597159023419155647111)
          ·
            refine ⟨131049895738535128733470667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87366597159023419155647111 131049895738535128733470667)
            ·
              refine ⟨196574843607802693100206001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131049895738535128733470667 196574843607802693100206001)
              ·
                refine ⟨147431132705852019825154501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196574843607802693100206001 147431132705852019825154501)
                ·
                  refine ⟨27643337382347253717216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147431132705852019825154501 27643337382347253717216469)
                  ·
                    refine ⟨647890719898763758997261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27643337382347253717216469 647890719898763758997261)
                    ·
                      rfl

theorem cell23_3785288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_3785288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785288 prefixEnd_3785288 := by exact prefixLift 3785288
  have htrace : WordTrace (prefixWord ++ tailWord_3785288) baseStart_3785288 baseEnd_3785288 := by
    simpa [prefixWord, tailWord_3785288, baseEnd_3785288] using wordTrace_append hprefix tailTrace_3785288
  have hstable : (prefixWord ++ tailWord_3785288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785288).length < 2 ^ (prefixWord ++ tailWord_3785288).sum := by decide
  have hdescent : baseEnd_3785288 < baseStart_3785288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785312 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2]
def baseStart_3785312 : Nat := 118140960795 + 3785312 * 2 ^ 59
def prefixEnd_3785312 : Nat := 4983230072969 + 3 ^ 40 * 3785312 * 2
def baseEnd_3785312 : Nat := 1943684483231999183091673

theorem tailTrace_3785312 : CollatzResearch.WordTrace tailWord_3785312 prefixEnd_3785312 1943684483231999183091673 := by
  unfold tailWord_3785312
  simp only [CollatzResearch.WordTrace]
  refine ⟨69030835431234289332911095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92041113908312385777214793 69030835431234289332911095)
  ·
    refine ⟨103546253146851433999366643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69030835431234289332911095 103546253146851433999366643)
    ·
      refine ⟨155319379720277150999049965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103546253146851433999366643 155319379720277150999049965)
      ·
        refine ⟨58244767395103931624643737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155319379720277150999049965 58244767395103931624643737)
        ·
          refine ⟨43683575546327948718482803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58244767395103931624643737 43683575546327948718482803)
          ·
            refine ⟨65525363319491923077724205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43683575546327948718482803 65525363319491923077724205)
            ·
              refine ⟨24572011244809471154146577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65525363319491923077724205 24572011244809471154146577)
              ·
                refine ⟨18429008433607103365609933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24572011244809471154146577 18429008433607103365609933)
                ·
                  refine ⟨6910878162602663762103725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18429008433607103365609933 6910878162602663762103725)
                  ·
                    refine ⟨2591579310975998910788897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6910878162602663762103725 2591579310975998910788897)
                    ·
                      refine ⟨1943684483231999183091673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591579310975998910788897 1943684483231999183091673)
                      ·
                        rfl

theorem cell23_3785312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_3785312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785312 prefixEnd_3785312 := by exact prefixLift 3785312
  have htrace : WordTrace (prefixWord ++ tailWord_3785312) baseStart_3785312 baseEnd_3785312 := by
    simpa [prefixWord, tailWord_3785312, baseEnd_3785312] using wordTrace_append hprefix tailTrace_3785312
  have hstable : (prefixWord ++ tailWord_3785312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785312).length < 2 ^ (prefixWord ++ tailWord_3785312).sum := by decide
  have hdescent : baseEnd_3785312 < baseStart_3785312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785345 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3785345 : Nat := 118140960795 + 3785345 * 2 ^ 59
def prefixEnd_3785345 : Nat := 4983230072969 + 3 ^ 40 * 3785345 * 2
def baseEnd_3785345 : Nat := 1943701428093597553979021

theorem tailTrace_3785345 : CollatzResearch.WordTrace tailWord_3785345 prefixEnd_3785345 1943701428093597553979021 := by
  unfold tailWord_3785345
  simp only [CollatzResearch.WordTrace]
  refine ⟨138062874471349025301773489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92041916314232683534515659 138062874471349025301773489)
  ·
    refine ⟨103547155853511768976330117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138062874471349025301773489 103547155853511768976330117)
    ·
      refine ⟨19415091722533456683061897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103547155853511768976330117 19415091722533456683061897)
      ·
        refine ⟨14561318791900092512296423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19415091722533456683061897 14561318791900092512296423)
        ·
          refine ⟨21841978187850138768444635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561318791900092512296423 21841978187850138768444635)
          ·
            refine ⟨32762967281775208152666953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21841978187850138768444635 32762967281775208152666953)
            ·
              refine ⟨24572225461331406114500215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32762967281775208152666953 24572225461331406114500215)
              ·
                refine ⟨36858338191997109171750323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24572225461331406114500215 36858338191997109171750323)
                ·
                  refine ⟨55287507287995663757625485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36858338191997109171750323 55287507287995663757625485)
                  ·
                    refine ⟨20732815232998373909109557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55287507287995663757625485 20732815232998373909109557)
                    ·
                      refine ⟨1943701428093597553979021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20732815232998373909109557 1943701428093597553979021)
                      ·
                        rfl

theorem cell23_3785345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3785345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785345 prefixEnd_3785345 := by exact prefixLift 3785345
  have htrace : WordTrace (prefixWord ++ tailWord_3785345) baseStart_3785345 baseEnd_3785345 := by
    simpa [prefixWord, tailWord_3785345, baseEnd_3785345] using wordTrace_append hprefix tailTrace_3785345
  have hstable : (prefixWord ++ tailWord_3785345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785345).length < 2 ^ (prefixWord ++ tailWord_3785345).sum := by decide
  have hdescent : baseEnd_3785345 < baseStart_3785345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785372 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3785372 : Nat := 118140960795 + 3785372 * 2 ^ 59
def prefixEnd_3785372 : Nat := 4983230072969 + 3 ^ 40 * 3785372 * 2
def baseEnd_3785372 : Nat := 1943715292071268948341397

theorem tailTrace_3785372 : CollatzResearch.WordTrace tailWord_3785372 prefixEnd_3785372 1943715292071268948341397 := by
  unfold tailWord_3785372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69031929621125604456503185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92042572828167472608670913 69031929621125604456503185)
  ·
    refine ⟨51773947215844203342377389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69031929621125604456503185 51773947215844203342377389)
    ·
      refine ⟨19415230205941576253391521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51773947215844203342377389 19415230205941576253391521)
      ·
        refine ⟨14561422654456182190043641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19415230205941576253391521 14561422654456182190043641)
        ·
          refine ⟨10921066990842136642532731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14561422654456182190043641 10921066990842136642532731)
          ·
            refine ⟨16381600486263204963799097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921066990842136642532731 16381600486263204963799097)
            ·
              refine ⟨12286200364697403722849323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16381600486263204963799097 12286200364697403722849323)
              ·
                refine ⟨18429300547046105584273985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286200364697403722849323 18429300547046105584273985)
                ·
                  refine ⟨13821975410284579188205489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18429300547046105584273985 13821975410284579188205489)
                  ·
                    refine ⟨10366481557713434391154117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13821975410284579188205489 10366481557713434391154117)
                    ·
                      refine ⟨1943715292071268948341397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10366481557713434391154117 1943715292071268948341397)
                      ·
                        rfl

theorem cell23_3785372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3785372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785372 prefixEnd_3785372 := by exact prefixLift 3785372
  have htrace : WordTrace (prefixWord ++ tailWord_3785372) baseStart_3785372 baseEnd_3785372 := by
    simpa [prefixWord, tailWord_3785372, baseEnd_3785372] using wordTrace_append hprefix tailTrace_3785372
  have hstable : (prefixWord ++ tailWord_3785372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785372).length < 2 ^ (prefixWord ++ tailWord_3785372).sum := by decide
  have hdescent : baseEnd_3785372 < baseStart_3785372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785376 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2]
def baseStart_3785376 : Nat := 118140960795 + 3785376 * 2 ^ 59
def prefixEnd_3785376 : Nat := 4983230072969 + 3 ^ 40 * 3785376 * 2
def baseEnd_3785376 : Nat := 1943717345993886932691379

theorem tailTrace_3785376 : CollatzResearch.WordTrace tailWord_3785376 prefixEnd_3785376 1943717345993886932691379 := by
  unfold tailWord_3785376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69032002567118358798075991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92042670089491145064101321 69032002567118358798075991)
  ·
    refine ⟨103548003850677538197113987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69032002567118358798075991 103548003850677538197113987)
    ·
      refine ⟨155322005776016307295670981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103548003850677538197113987 155322005776016307295670981)
      ·
        refine ⟨29122876083003057617938309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155322005776016307295670981 29122876083003057617938309)
        ·
          refine ⟨5460539265563073303363433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29122876083003057617938309 5460539265563073303363433)
          ·
            refine ⟨4095404449172304977522575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5460539265563073303363433 4095404449172304977522575)
            ·
              refine ⟨6143106673758457466283863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095404449172304977522575 6143106673758457466283863)
              ·
                refine ⟨9214660010637686199425795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143106673758457466283863 9214660010637686199425795)
                ·
                  refine ⟨13821990015956529299138693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9214660010637686199425795 13821990015956529299138693)
                  ·
                    refine ⟨2591623127991849243588505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13821990015956529299138693 2591623127991849243588505)
                    ·
                      refine ⟨1943717345993886932691379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591623127991849243588505 1943717345993886932691379)
                      ·
                        rfl

theorem cell23_3785376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_3785376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785376 prefixEnd_3785376 := by exact prefixLift 3785376
  have htrace : WordTrace (prefixWord ++ tailWord_3785376) baseStart_3785376 baseEnd_3785376 := by
    simpa [prefixWord, tailWord_3785376, baseEnd_3785376] using wordTrace_append hprefix tailTrace_3785376
  have hstable : (prefixWord ++ tailWord_3785376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785376).length < 2 ^ (prefixWord ++ tailWord_3785376).sum := by decide
  have hdescent : baseEnd_3785376 < baseStart_3785376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785395 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 7]
def baseStart_3785395 : Nat := 118140960795 + 3785395 * 2 ^ 59
def prefixEnd_3785395 : Nat := 4983230072969 + 3 ^ 40 * 3785395 * 2
def baseEnd_3785395 : Nat := 647909034042107452784597

theorem tailTrace_3785395 : CollatzResearch.WordTrace tailWord_3785395 prefixEnd_3785395 647909034042107452784597 := by
  unfold tailWord_3785395
  simp only [CollatzResearch.WordTrace]
  refine ⟨138064698121167883841093639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92043132080778589227395759 138064698121167883841093639)
  ·
    refine ⟨207097047181751825761640459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138064698121167883841093639 207097047181751825761640459)
    ·
      refine ⟨310645570772627738642460689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207097047181751825761640459 310645570772627738642460689)
      ·
        refine ⟨232984178079470803981845517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310645570772627738642460689 232984178079470803981845517)
        ·
          refine ⟨87369066779801551493192069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232984178079470803981845517 87369066779801551493192069)
          ·
            refine ⟨16381700021212790904973513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87369066779801551493192069 16381700021212790904973513)
            ·
              refine ⟨12286275015909593178730135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16381700021212790904973513 12286275015909593178730135)
              ·
                refine ⟨18429412523864389768095203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286275015909593178730135 18429412523864389768095203)
                ·
                  refine ⟨27644118785796584652142805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18429412523864389768095203 27644118785796584652142805)
                  ·
                    refine ⟨647909034042107452784597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27644118785796584652142805 647909034042107452784597)
                    ·
                      rfl

theorem cell23_3785395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_3785395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785395 prefixEnd_3785395 := by exact prefixLift 3785395
  have htrace : WordTrace (prefixWord ++ tailWord_3785395) baseStart_3785395 baseEnd_3785395 := by
    simpa [prefixWord, tailWord_3785395, baseEnd_3785395] using wordTrace_append hprefix tailTrace_3785395
  have hstable : (prefixWord ++ tailWord_3785395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785395).length < 2 ^ (prefixWord ++ tailWord_3785395).sum := by decide
  have hdescent : baseEnd_3785395 < baseStart_3785395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785412 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3785412 : Nat := 118140960795 + 3785412 * 2 ^ 59
def prefixEnd_3785412 : Nat := 4983230072969 + 3 ^ 40 * 3785412 * 2
def baseEnd_3785412 : Nat := 647911943765816263947071

theorem tailTrace_3785412 : CollatzResearch.WordTrace tailWord_3785412 prefixEnd_3785412 647911943765816263947071 := by
  unfold tailWord_3785412
  simp only [CollatzResearch.WordTrace]
  refine ⟨69032659081053147872231245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92043545441404197162974993 69032659081053147872231245)
  ·
    refine ⟨25887247155394930452086717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69032659081053147872231245 25887247155394930452086717)
    ·
      refine ⟨9707717683273098919532519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25887247155394930452086717 9707717683273098919532519)
      ·
        refine ⟨14561576524909648379298779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707717683273098919532519 14561576524909648379298779)
        ·
          refine ⟨21842364787364472568948169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561576524909648379298779 21842364787364472568948169)
          ·
            refine ⟨16381773590523354426711127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21842364787364472568948169 16381773590523354426711127)
            ·
              refine ⟨24572660385785031640066691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16381773590523354426711127 24572660385785031640066691)
              ·
                refine ⟨36858990578677547460100037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24572660385785031640066691 36858990578677547460100037)
                ·
                  refine ⟨6911060733502040148768757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36858990578677547460100037 6911060733502040148768757)
                  ·
                    refine ⟨647911943765816263947071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6911060733502040148768757 647911943765816263947071)
                    ·
                      rfl

theorem cell23_3785412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3785412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785412 prefixEnd_3785412 := by exact prefixLift 3785412
  have htrace : WordTrace (prefixWord ++ tailWord_3785412) baseStart_3785412 baseEnd_3785412 := by
    simpa [prefixWord, tailWord_3785412, baseEnd_3785412] using wordTrace_append hprefix tailTrace_3785412
  have hstable : (prefixWord ++ tailWord_3785412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785412).length < 2 ^ (prefixWord ++ tailWord_3785412).sum := by decide
  have hdescent : baseEnd_3785412 < baseStart_3785412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785415 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3785415 : Nat := 118140960795 + 3785415 * 2 ^ 59
def prefixEnd_3785415 : Nat := 4983230072969 + 3 ^ 40 * 3785415 * 2
def baseEnd_3785415 : Nat := 1943737371739412280103699

theorem tailTrace_3785415 : CollatzResearch.WordTrace tailWord_3785415 prefixEnd_3785415 1943737371739412280103699 := by
  unfold tailWord_3785415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138065427581095427256821699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92043618387396951504547799 138065427581095427256821699)
  ·
    refine ⟨207098141371643140885232549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138065427581095427256821699 207098141371643140885232549)
    ·
      refine ⟨38830901507183088915981103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207098141371643140885232549 38830901507183088915981103)
      ·
        refine ⟨58246352260774633373971655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38830901507183088915981103 58246352260774633373971655)
        ·
          refine ⟨87369528391161950060957483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58246352260774633373971655 87369528391161950060957483)
          ·
            refine ⟨131054292586742925091436225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87369528391161950060957483 131054292586742925091436225)
            ·
              refine ⟨98290719440057193818577169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131054292586742925091436225 98290719440057193818577169)
              ·
                refine ⟨73718039580042895363932877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98290719440057193818577169 73718039580042895363932877)
                ·
                  refine ⟨27644264842516085761474829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73718039580042895363932877 27644264842516085761474829)
                  ·
                    refine ⟨10366599315943532160553061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27644264842516085761474829 10366599315943532160553061)
                    ·
                      refine ⟨1943737371739412280103699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10366599315943532160553061 1943737371739412280103699)
                      ·
                        rfl

theorem cell23_3785415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3785415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785415 prefixEnd_3785415 := by exact prefixLift 3785415
  have htrace : WordTrace (prefixWord ++ tailWord_3785415) baseStart_3785415 baseEnd_3785415 := by
    simpa [prefixWord, tailWord_3785415, baseEnd_3785415] using wordTrace_append hprefix tailTrace_3785415
  have hstable : (prefixWord ++ tailWord_3785415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785415).length < 2 ^ (prefixWord ++ tailWord_3785415).sum := by decide
  have hdescent : baseEnd_3785415 < baseStart_3785415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785422 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3785422 : Nat := 118140960795 + 3785422 * 2 ^ 59
def prefixEnd_3785422 : Nat := 4983230072969 + 3 ^ 40 * 3785422 * 2
def baseEnd_3785422 : Nat := 1943740966103993752716167

theorem tailTrace_3785422 : CollatzResearch.WordTrace tailWord_3785422 prefixEnd_3785422 1943740966103993752716167 := by
  unfold tailWord_3785422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258210361508758431540815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92043788594713378301551013 17258210361508758431540815)
  ·
    refine ⟨25887315542263137647311223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17258210361508758431540815 25887315542263137647311223)
    ·
      refine ⟨38830973313394706470966835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25887315542263137647311223 38830973313394706470966835)
      ·
        refine ⟨58246459970092059706450253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38830973313394706470966835 58246459970092059706450253)
        ·
          refine ⟨21842422488784522389918845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58246459970092059706450253 21842422488784522389918845)
          ·
            refine ⟨8190908433294195896219567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21842422488784522389918845 8190908433294195896219567)
            ·
              refine ⟨12286362649941293844329351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190908433294195896219567 12286362649941293844329351)
              ·
                refine ⟨18429543974911940766494027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286362649941293844329351 18429543974911940766494027)
                ·
                  refine ⟨27644315962367911149741041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18429543974911940766494027 27644315962367911149741041)
                  ·
                    refine ⟨20733236971775933362305781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27644315962367911149741041 20733236971775933362305781)
                    ·
                      refine ⟨1943740966103993752716167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20733236971775933362305781 1943740966103993752716167)
                      ·
                        rfl

theorem cell23_3785422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3785422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785422 prefixEnd_3785422 := by exact prefixLift 3785422
  have htrace : WordTrace (prefixWord ++ tailWord_3785422) baseStart_3785422 baseEnd_3785422 := by
    simpa [prefixWord, tailWord_3785422, baseEnd_3785422] using wordTrace_append hprefix tailTrace_3785422
  have hstable : (prefixWord ++ tailWord_3785422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785422).length < 2 ^ (prefixWord ++ tailWord_3785422).sum := by decide
  have hdescent : baseEnd_3785422 < baseStart_3785422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785459 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 1, 4]
def baseStart_3785459 : Nat := 118140960795 + 3785459 * 2 ^ 59
def prefixEnd_3785459 : Nat := 4983230072969 + 3 ^ 40 * 3785459 * 2
def baseEnd_3785459 : Nat := 647919988296070035984499

theorem tailTrace_3785459 : CollatzResearch.WordTrace tailWord_3785459 prefixEnd_3785459 647919988296070035984499 := by
  unfold tailWord_3785459
  simp only [CollatzResearch.WordTrace]
  refine ⟨138067032392936022771423431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92044688261957348514282287 138067032392936022771423431)
  ·
    refine ⟨207100548589404034157135147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138067032392936022771423431 207100548589404034157135147)
    ·
      refine ⟨310650822884106051235702721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207100548589404034157135147 310650822884106051235702721)
      ·
        refine ⟨232988117163079538426777041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310650822884106051235702721 232988117163079538426777041)
        ·
          refine ⟨174741087872309653820082781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232988117163079538426777041 174741087872309653820082781)
          ·
            refine ⟨65527907952116120182531043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174741087872309653820082781 65527907952116120182531043)
            ·
              refine ⟨98291861928174180273796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65527907952116120182531043 98291861928174180273796565)
              ·
                refine ⟨2303715513941582350167107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98291861928174180273796565 2303715513941582350167107)
                ·
                  refine ⟨3455573270912373525250661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303715513941582350167107 3455573270912373525250661)
                  ·
                    refine ⟨647919988296070035984499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455573270912373525250661 647919988296070035984499)
                    ·
                      rfl

theorem cell23_3785459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 4].length) (baseStart_3785459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785459 prefixEnd_3785459 := by exact prefixLift 3785459
  have htrace : WordTrace (prefixWord ++ tailWord_3785459) baseStart_3785459 baseEnd_3785459 := by
    simpa [prefixWord, tailWord_3785459, baseEnd_3785459] using wordTrace_append hprefix tailTrace_3785459
  have hstable : (prefixWord ++ tailWord_3785459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785459).length < 2 ^ (prefixWord ++ tailWord_3785459).sum := by decide
  have hdescent : baseEnd_3785459 < baseStart_3785459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785462 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3785462 : Nat := 118140960795 + 3785462 * 2 ^ 59
def prefixEnd_3785462 : Nat := 4983230072969 + 3 ^ 40 * 3785462 * 2
def baseEnd_3785462 : Nat := 1943761505330173596215983

theorem tailTrace_3785462 : CollatzResearch.WordTrace tailWord_3785462 prefixEnd_3785462 1943761505330173596215983 := by
  unfold tailWord_3785462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629196363245322142736415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92044761207950102855855093 8629196363245322142736415)
  ·
    refine ⟨12943794544867983214104623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8629196363245322142736415 12943794544867983214104623)
    ·
      refine ⟨19415691817301974821156935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12943794544867983214104623 19415691817301974821156935)
      ·
        refine ⟨29123537725952962231735403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19415691817301974821156935 29123537725952962231735403)
        ·
          refine ⟨43685306588929443347603105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29123537725952962231735403 43685306588929443347603105)
          ·
            refine ⟨32763979941697082510702329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43685306588929443347603105 32763979941697082510702329)
            ·
              refine ⟨24572984956272811883026747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32763979941697082510702329 24572984956272811883026747)
              ·
                refine ⟨36859477434409217824540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24572984956272811883026747 36859477434409217824540121)
                ·
                  refine ⟨27644608075806913368405091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36859477434409217824540121 27644608075806913368405091)
                  ·
                    refine ⟨41466912113710370052607637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27644608075806913368405091 41466912113710370052607637)
                    ·
                      refine ⟨1943761505330173596215983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41466912113710370052607637 1943761505330173596215983)
                      ·
                        rfl

theorem cell23_3785462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3785462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785462 prefixEnd_3785462 := by exact prefixLift 3785462
  have htrace : WordTrace (prefixWord ++ tailWord_3785462) baseStart_3785462 baseEnd_3785462 := by
    simpa [prefixWord, tailWord_3785462, baseEnd_3785462] using wordTrace_append hprefix tailTrace_3785462
  have hstable : (prefixWord ++ tailWord_3785462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785462).length < 2 ^ (prefixWord ++ tailWord_3785462).sum := by decide
  have hdescent : baseEnd_3785462 < baseStart_3785462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785475 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_3785475 : Nat := 118140960795 + 3785475 * 2 ^ 59
def prefixEnd_3785475 : Nat := 4983230072969 + 3 ^ 40 * 3785475 * 2
def baseEnd_3785475 : Nat := 1943768180578682045353423

theorem tailTrace_3785475 : CollatzResearch.WordTrace tailWord_3785475 prefixEnd_3785475 1943768180578682045353423 := by
  unfold tailWord_3785475
  simp only [CollatzResearch.WordTrace]
  refine ⟨138067615960878057504005879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92045077307252038336003919 138067615960878057504005879)
  ·
    refine ⟨207101423941317086256008819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138067615960878057504005879 207101423941317086256008819)
    ·
      refine ⟨310652135911975629384013229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207101423941317086256008819 310652135911975629384013229)
      ·
        refine ⟨116494550966990861019004961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310652135911975629384013229 116494550966990861019004961)
        ·
          refine ⟨87370913225243145764253721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116494550966990861019004961 87370913225243145764253721)
          ·
            refine ⟨65528184918932359323190291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87370913225243145764253721 65528184918932359323190291)
            ·
              refine ⟨98292277378398538984785437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65528184918932359323190291 98292277378398538984785437)
              ·
                refine ⟨36859604016899452119294539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98292277378398538984785437 36859604016899452119294539)
                ·
                  refine ⟨55289406025349178178941809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36859604016899452119294539 55289406025349178178941809)
                  ·
                    refine ⟨41467054519011883634206357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55289406025349178178941809 41467054519011883634206357)
                    ·
                      refine ⟨1943768180578682045353423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41467054519011883634206357 1943768180578682045353423)
                      ·
                        rfl

theorem cell23_3785475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_3785475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785475 prefixEnd_3785475 := by exact prefixLift 3785475
  have htrace : WordTrace (prefixWord ++ tailWord_3785475) baseStart_3785475 baseEnd_3785475 := by
    simpa [prefixWord, tailWord_3785475, baseEnd_3785475] using wordTrace_append hprefix tailTrace_3785475
  have hstable : (prefixWord ++ tailWord_3785475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785475).length < 2 ^ (prefixWord ++ tailWord_3785475).sum := by decide
  have hdescent : baseEnd_3785475 < baseStart_3785475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785476 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3785476 : Nat := 118140960795 + 3785476 * 2 ^ 59
def prefixEnd_3785476 : Nat := 4983230072969 + 3 ^ 40 * 3785476 * 2
def baseEnd_3785476 : Nat := 647922898019778847146973

theorem tailTrace_3785476 : CollatzResearch.WordTrace tailWord_3785476 prefixEnd_3785476 647922898019778847146973 := by
  unfold tailWord_3785476
  simp only [CollatzResearch.WordTrace]
  refine ⟨69033826216937217337396141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92045101622582956449861521 69033826216937217337396141)
  ·
    refine ⟨25887684831351456501523553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69033826216937217337396141 25887684831351456501523553)
    ·
      refine ⟨19415763623513592376142665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25887684831351456501523553 19415763623513592376142665)
      ·
        refine ⟨14561822717635194282106999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19415763623513592376142665 14561822717635194282106999)
        ·
          refine ⟨21842734076452791423160499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561822717635194282106999 21842734076452791423160499)
          ·
            refine ⟨32764101114679187134740749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21842734076452791423160499 32764101114679187134740749)
            ·
              refine ⟨12286537918004695175527781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32764101114679187134740749 12286537918004695175527781)
              ·
                refine ⟨2303725859625880345411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12286537918004695175527781 2303725859625880345411459)
                ·
                  refine ⟨3455588789438820518117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303725859625880345411459 3455588789438820518117189)
                  ·
                    refine ⟨647922898019778847146973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455588789438820518117189 647922898019778847146973)
                    ·
                      rfl

theorem cell23_3785476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3785476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785476 prefixEnd_3785476 := by exact prefixLift 3785476
  have htrace : WordTrace (prefixWord ++ tailWord_3785476) baseStart_3785476 baseEnd_3785476 := by
    simpa [prefixWord, tailWord_3785476, baseEnd_3785476] using wordTrace_append hprefix tailTrace_3785476
  have hstable : (prefixWord ++ tailWord_3785476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785476).length < 2 ^ (prefixWord ++ tailWord_3785476).sum := by decide
  have hdescent : baseEnd_3785476 < baseStart_3785476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785509 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_3785509 : Nat := 118140960795 + 3785509 * 2 ^ 59
def prefixEnd_3785509 : Nat := 4983230072969 + 3 ^ 40 * 3785509 * 2
def baseEnd_3785509 : Nat := 1943785638920934912328267

theorem tailTrace_3785509 : CollatzResearch.WordTrace tailWord_3785509 prefixEnd_3785509 1943785638920934912328267 := by
  unfold tailWord_3785509
  simp only [CollatzResearch.WordTrace]
  refine ⟨138068856042754881310743581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92045904028503254207162387 138068856042754881310743581)
  ·
    refine ⟨51775821016033080491528843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138068856042754881310743581 51775821016033080491528843)
    ·
      refine ⟨77663731524049620737293265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51775821016033080491528843 77663731524049620737293265)
      ·
        refine ⟨58247798643037215552969949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77663731524049620737293265 58247798643037215552969949)
        ·
          refine ⟨21842924491138955832363731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58247798643037215552969949 21842924491138955832363731)
          ·
            refine ⟨32764386736708433748545597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21842924491138955832363731 32764386736708433748545597)
            ·
              refine ⟨12286645026265662655704599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32764386736708433748545597 12286645026265662655704599)
              ·
                refine ⟨18429967539398493983556899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286645026265662655704599 18429967539398493983556899)
                ·
                  refine ⟨27644951309097740975335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18429967539398493983556899 27644951309097740975335349)
                  ·
                    refine ⟨2591714185227913216437689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27644951309097740975335349 2591714185227913216437689)
                    ·
                      refine ⟨1943785638920934912328267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591714185227913216437689 1943785638920934912328267)
                      ·
                        rfl

theorem cell23_3785509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_3785509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785509 prefixEnd_3785509 := by exact prefixLift 3785509
  have htrace : WordTrace (prefixWord ++ tailWord_3785509) baseStart_3785509 baseEnd_3785509 := by
    simpa [prefixWord, tailWord_3785509, baseEnd_3785509] using wordTrace_append hprefix tailTrace_3785509
  have hstable : (prefixWord ++ tailWord_3785509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785509).length < 2 ^ (prefixWord ++ tailWord_3785509).sum := by decide
  have hdescent : baseEnd_3785509 < baseStart_3785509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785533 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3785533 : Nat := 118140960795 + 3785533 * 2 ^ 59
def prefixEnd_3785533 : Nat := 4983230072969 + 3 ^ 40 * 3785533 * 2
def baseEnd_3785533 : Nat := 1943797962456642818428157

theorem tailTrace_3785533 : CollatzResearch.WordTrace tailWord_3785533 prefixEnd_3785533 1943797962456642818428157 := by
  unfold tailWord_3785533
  simp only [CollatzResearch.WordTrace]
  refine ⟨138069731394667933409617253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92046487596445288939744835 138069731394667933409617253)
  ·
    refine ⟨25888074636500237514303235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138069731394667933409617253 25888074636500237514303235)
    ·
      refine ⟨38832111954750356271454853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25888074636500237514303235 38832111954750356271454853)
      ·
        refine ⟨7281020991515691800897785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38832111954750356271454853 7281020991515691800897785)
        ·
          refine ⟨5460765743636768850673339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281020991515691800897785 5460765743636768850673339)
          ·
            refine ⟨8191148615455153276010009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460765743636768850673339 8191148615455153276010009)
            ·
              refine ⟨6143361461591364957007507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191148615455153276010009 6143361461591364957007507)
              ·
                refine ⟨9215042192387047435511261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143361461591364957007507 9215042192387047435511261)
                ·
                  refine ⟨3455640822145142788316723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9215042192387047435511261 3455640822145142788316723)
                  ·
                    refine ⟨5183461233217714182475085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3455640822145142788316723 5183461233217714182475085)
                    ·
                      refine ⟨1943797962456642818428157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5183461233217714182475085 1943797962456642818428157)
                      ·
                        rfl

theorem cell23_3785533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3785533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785533 prefixEnd_3785533 := by exact prefixLift 3785533
  have htrace : WordTrace (prefixWord ++ tailWord_3785533) baseStart_3785533 baseEnd_3785533 := by
    simpa [prefixWord, tailWord_3785533, baseEnd_3785533] using wordTrace_append hprefix tailTrace_3785533
  have hstable : (prefixWord ++ tailWord_3785533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785533).length < 2 ^ (prefixWord ++ tailWord_3785533).sum := by decide
  have hdescent : baseEnd_3785533 < baseStart_3785533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785562 : List Nat := [3, 1, 1, 2, 1, 5, 1, 9]
def baseStart_3785562 : Nat := 118140960795 + 3785562 * 2 ^ 59
def prefixEnd_3785562 : Nat := 4983230072969 + 3 ^ 40 * 3785562 * 2
def baseEnd_3785562 : Nat := 71993068644282340924649

theorem tailTrace_3785562 : CollatzResearch.WordTrace tailWord_3785562 prefixEnd_3785562 71993068644282340924649 := by
  unfold tailWord_3785562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517697277890717840605735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92047192741041914241615293 34517697277890717840605735)
  ·
    refine ⟨51776545916836076760908603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34517697277890717840605735 51776545916836076760908603)
    ·
      refine ⟨77664818875254115141362905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51776545916836076760908603 77664818875254115141362905)
      ·
        refine ⟨58248614156440586356022179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77664818875254115141362905 58248614156440586356022179)
        ·
          refine ⟨87372921234660879534033269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58248614156440586356022179 87372921234660879534033269)
          ·
            refine ⟨8191211365749457456315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87372921234660879534033269 8191211365749457456315619)
            ·
              refine ⟨12286817048624186184473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8191211365749457456315619 12286817048624186184473429)
              ·
                refine ⟨71993068644282340924649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12286817048624186184473429 71993068644282340924649)
                ·
                  rfl

theorem cell23_3785562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_3785562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785562 prefixEnd_3785562 := by exact prefixLift 3785562
  have htrace : WordTrace (prefixWord ++ tailWord_3785562) baseStart_3785562 baseEnd_3785562 := by
    simpa [prefixWord, tailWord_3785562, baseEnd_3785562] using wordTrace_append hprefix tailTrace_3785562
  have hstable : (prefixWord ++ tailWord_3785562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785562).length < 2 ^ (prefixWord ++ tailWord_3785562).sum := by decide
  have hdescent : baseEnd_3785562 < baseStart_3785562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785576 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3785576 : Nat := 118140960795 + 3785576 * 2 ^ 59
def prefixEnd_3785576 : Nat := 4983230072969 + 3 ^ 40 * 3785576 * 2
def baseEnd_3785576 : Nat := 1943820042124786150190459

theorem tailTrace_3785576 : CollatzResearch.WordTrace tailWord_3785576 prefixEnd_3785576 1943820042124786150190459 := by
  unfold tailWord_3785576
  simp only [CollatzResearch.WordTrace]
  refine ⟨69035649866756075876716291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92047533155674767835621721 69035649866756075876716291)
  ·
    refine ⟨103553474800134113815074437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69035649866756075876716291 103553474800134113815074437)
    ·
      refine ⟨19416276525025146340326457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103553474800134113815074437 19416276525025146340326457)
      ·
        refine ⟨14562207393768859755244843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19416276525025146340326457 14562207393768859755244843)
        ·
          refine ⟨21843311090653289632867265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14562207393768859755244843 21843311090653289632867265)
          ·
            refine ⟨16382483317989967224650449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21843311090653289632867265 16382483317989967224650449)
            ·
              refine ⟨12286862488492475418487837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16382483317989967224650449 12286862488492475418487837)
              ·
                refine ⟨4607573433184678281932939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12286862488492475418487837 4607573433184678281932939)
                ·
                  refine ⟨6911360149777017422899409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607573433184678281932939 6911360149777017422899409)
                  ·
                    refine ⟨5183520112332763067174557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911360149777017422899409 5183520112332763067174557)
                    ·
                      refine ⟨1943820042124786150190459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5183520112332763067174557 1943820042124786150190459)
                      ·
                        rfl

theorem cell23_3785576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3785576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785576 prefixEnd_3785576 := by exact prefixLift 3785576
  have htrace : WordTrace (prefixWord ++ tailWord_3785576) baseStart_3785576 baseEnd_3785576 := by
    simpa [prefixWord, tailWord_3785576, baseEnd_3785576] using wordTrace_append hprefix tailTrace_3785576
  have hstable : (prefixWord ++ tailWord_3785576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785576).length < 2 ^ (prefixWord ++ tailWord_3785576).sum := by decide
  have hdescent : baseEnd_3785576 < baseStart_3785576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785590 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3785590 : Nat := 118140960795 + 3785590 * 2 ^ 59
def prefixEnd_3785590 : Nat := 4983230072969 + 3 ^ 40 * 3785590 * 2
def baseEnd_3785590 : Nat := 1943827230853949095415395

theorem tailTrace_3785590 : CollatzResearch.WordTrace tailWord_3785590 prefixEnd_3785590 1943827230853949095415395 := by
  unfold tailWord_3785590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629488147216339509027639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92047873570307621429628149 8629488147216339509027639)
  ·
    refine ⟨12944232220824509263541459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8629488147216339509027639 12944232220824509263541459)
    ·
      refine ⟨19416348331236763895312189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944232220824509263541459 19416348331236763895312189)
      ·
        refine ⟨7281130624213786460742071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19416348331236763895312189 7281130624213786460742071)
        ·
          refine ⟨10921695936320679691113107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281130624213786460742071 10921695936320679691113107)
          ·
            refine ⟨16382543904481019536669661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921695936320679691113107 16382543904481019536669661)
            ·
              refine ⟨6143453964180382326251123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16382543904481019536669661 6143453964180382326251123)
              ·
                refine ⟨9215180946270573489376685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143453964180382326251123 9215180946270573489376685)
                ·
                  refine ⟨3455692854851465058516257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9215180946270573489376685 3455692854851465058516257)
                  ·
                    refine ⟨2591769641138598793887193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455692854851465058516257 2591769641138598793887193)
                    ·
                      refine ⟨1943827230853949095415395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591769641138598793887193 1943827230853949095415395)
                      ·
                        rfl

theorem cell23_3785590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3785590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785590 prefixEnd_3785590 := by exact prefixLift 3785590
  have htrace : WordTrace (prefixWord ++ tailWord_3785590) baseStart_3785590 baseEnd_3785590 := by
    simpa [prefixWord, tailWord_3785590, baseEnd_3785590] using wordTrace_append hprefix tailTrace_3785590
  have hstable : (prefixWord ++ tailWord_3785590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785590).length < 2 ^ (prefixWord ++ tailWord_3785590).sum := by decide
  have hdescent : baseEnd_3785590 < baseStart_3785590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785699 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 4, 5]
def baseStart_3785699 : Nat := 118140960795 + 3785699 * 2 ^ 59
def prefixEnd_3785699 : Nat := 4983230072969 + 3 ^ 40 * 3785699 * 2
def baseEnd_3785699 : Nat := 647961066748429722984131

theorem tailTrace_3785699 : CollatzResearch.WordTrace tailWord_3785699 prefixEnd_3785699 647961066748429722984131 := by
  unfold tailWord_3785699
  simp only [CollatzResearch.WordTrace]
  refine ⟨138075785912066543760160151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92050523941377695840106767 138075785912066543760160151)
  ·
    refine ⟨207113678868099815640240227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138075785912066543760160151 207113678868099815640240227)
    ·
      refine ⟨310670518302149723460360341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207113678868099815640240227 310670518302149723460360341)
      ·
        refine ⟨14562680545413268287204391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310670518302149723460360341 14562680545413268287204391)
        ·
          refine ⟨21844020818119902430806587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14562680545413268287204391 21844020818119902430806587)
          ·
            refine ⟨32766031227179853646209881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844020818119902430806587 32766031227179853646209881)
            ·
              refine ⟨24574523420384890234657411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32766031227179853646209881 24574523420384890234657411)
              ·
                refine ⟨36861785130577335351986117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24574523420384890234657411 36861785130577335351986117)
                ·
                  refine ⟨6911584711983250378497397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36861785130577335351986117 6911584711983250378497397)
                  ·
                    refine ⟨647961066748429722984131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6911584711983250378497397 647961066748429722984131)
                    ·
                      rfl

theorem cell23_3785699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].length) (baseStart_3785699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785699 prefixEnd_3785699 := by exact prefixLift 3785699
  have htrace : WordTrace (prefixWord ++ tailWord_3785699) baseStart_3785699 baseEnd_3785699 := by
    simpa [prefixWord, tailWord_3785699, baseEnd_3785699] using wordTrace_append hprefix tailTrace_3785699
  have hstable : (prefixWord ++ tailWord_3785699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785699).length < 2 ^ (prefixWord ++ tailWord_3785699).sum := by decide
  have hdescent : baseEnd_3785699 < baseStart_3785699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785714 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3785714 : Nat := 118140960795 + 3785714 * 2 ^ 59
def prefixEnd_3785714 : Nat := 4983230072969 + 3 ^ 40 * 3785714 * 2
def baseEnd_3785714 : Nat := 1943890902455106610264825

theorem tailTrace_3785714 : CollatzResearch.WordTrace tailWord_3785714 prefixEnd_3785714 1943890902455106610264825 := by
  unfold tailWord_3785714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519083251753050330489049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92050888671341467547970797 34519083251753050330489049)
  ·
    refine ⟨25889312438814787747866787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34519083251753050330489049 25889312438814787747866787)
    ·
      refine ⟨38833968658222181621800181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25889312438814787747866787 38833968658222181621800181)
      ·
        refine ⟨3640684561708329527043767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38833968658222181621800181 3640684561708329527043767)
        ·
          refine ⟨5461026842562494290565651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640684561708329527043767 5461026842562494290565651)
          ·
            refine ⟨8191540263843741435848477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461026842562494290565651 8191540263843741435848477)
            ·
              refine ⟨3071827598941403038443179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8191540263843741435848477 3071827598941403038443179)
              ·
                refine ⟨4607741398412104557664769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071827598941403038443179 4607741398412104557664769)
                ·
                  refine ⟨3455806048809078418248577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607741398412104557664769 3455806048809078418248577)
                  ·
                    refine ⟨2591854536606808813686433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455806048809078418248577 2591854536606808813686433)
                    ·
                      refine ⟨1943890902455106610264825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591854536606808813686433 1943890902455106610264825)
                      ·
                        rfl

theorem cell23_3785714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3785714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785714 prefixEnd_3785714 := by exact prefixLift 3785714
  have htrace : WordTrace (prefixWord ++ tailWord_3785714) baseStart_3785714 baseEnd_3785714 := by
    simpa [prefixWord, tailWord_3785714, baseEnd_3785714] using wordTrace_append hprefix tailTrace_3785714
  have hstable : (prefixWord ++ tailWord_3785714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785714).length < 2 ^ (prefixWord ++ tailWord_3785714).sum := by decide
  have hdescent : baseEnd_3785714 < baseStart_3785714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785759 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 8]
def baseStart_3785759 : Nat := 118140960795 + 3785759 * 2 ^ 59
def prefixEnd_3785759 : Nat := 4983230072969 + 3 ^ 40 * 3785759 * 2
def baseEnd_3785759 : Nat := 215990445453839881578013

theorem tailTrace_3785759 : CollatzResearch.WordTrace tailWord_3785759 prefixEnd_3785759 215990445453839881578013 := by
  unfold tailWord_3785759
  simp only [CollatzResearch.WordTrace]
  refine ⟨138077974291849174007344331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92051982861232782671562887 138077974291849174007344331)
  ·
    refine ⟨207116961437773761011016497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138077974291849174007344331 207116961437773761011016497)
    ·
      refine ⟨155337721078330320758262373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207116961437773761011016497 155337721078330320758262373)
      ·
        refine ⟨29125822702186935142174195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155337721078330320758262373 29125822702186935142174195)
        ·
          refine ⟨43688734053280402713261293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125822702186935142174195 43688734053280402713261293)
          ·
            refine ⟨16383275269980151017472985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43688734053280402713261293 16383275269980151017472985)
            ·
              refine ⟨12287456452485113263104739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16383275269980151017472985 12287456452485113263104739)
              ·
                refine ⟨18431184678727669894657109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12287456452485113263104739 18431184678727669894657109)
                ·
                  refine ⟨215990445453839881578013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18431184678727669894657109 215990445453839881578013)
                  ·
                    rfl

theorem cell23_3785759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 8].length) (baseStart_3785759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785759 prefixEnd_3785759 := by exact prefixLift 3785759
  have htrace : WordTrace (prefixWord ++ tailWord_3785759) baseStart_3785759 baseEnd_3785759 := by
    simpa [prefixWord, tailWord_3785759, baseEnd_3785759] using wordTrace_append hprefix tailTrace_3785759
  have hstable : (prefixWord ++ tailWord_3785759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785759).length < 2 ^ (prefixWord ++ tailWord_3785759).sum := by decide
  have hdescent : baseEnd_3785759 < baseStart_3785759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785763 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 3, 4]
def baseStart_3785763 : Nat := 118140960795 + 3785763 * 2 ^ 59
def prefixEnd_3785763 : Nat := 4983230072969 + 3 ^ 40 * 3785763 * 2
def baseEnd_3785763 : Nat := 647972021002392306184033

theorem tailTrace_3785763 : CollatzResearch.WordTrace tailWord_3785763 prefixEnd_3785763 647972021002392306184033 := by
  unfold tailWord_3785763
  simp only [CollatzResearch.WordTrace]
  refine ⟨138078120183834682690489943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92052080122556455126993295 138078120183834682690489943)
  ·
    refine ⟨207117180275752024035734915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138078120183834682690489943 207117180275752024035734915)
    ·
      refine ⟨310675770413628036053602373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207117180275752024035734915 310675770413628036053602373)
      ·
        refine ⟨58251706952555256760050445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310675770413628036053602373 58251706952555256760050445)
        ·
          refine ⟨21844390107208221285018917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58251706952555256760050445 21844390107208221285018917)
          ·
            refine ⟨4095823145101541490941047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21844390107208221285018917 4095823145101541490941047)
            ·
              refine ⟨6143734717652312236411571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095823145101541490941047 6143734717652312236411571)
              ·
                refine ⟨9215602076478468354617357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143734717652312236411571 9215602076478468354617357)
                ·
                  refine ⟨3455850778679425632981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9215602076478468354617357 3455850778679425632981509)
                  ·
                    refine ⟨647972021002392306184033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455850778679425632981509 647972021002392306184033)
                    ·
                      rfl

theorem cell23_3785763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 4].length) (baseStart_3785763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785763 prefixEnd_3785763 := by exact prefixLift 3785763
  have htrace : WordTrace (prefixWord ++ tailWord_3785763) baseStart_3785763 baseEnd_3785763 := by
    simpa [prefixWord, tailWord_3785763, baseEnd_3785763] using wordTrace_append hprefix tailTrace_3785763
  have hstable : (prefixWord ++ tailWord_3785763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785763).length < 2 ^ (prefixWord ++ tailWord_3785763).sum := by decide
  have hdescent : baseEnd_3785763 < baseStart_3785763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785790 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3785790 : Nat := 118140960795 + 3785790 * 2 ^ 59
def prefixEnd_3785790 : Nat := 4983230072969 + 3 ^ 40 * 3785790 * 2
def baseEnd_3785790 : Nat := 1943929926984848312914475

theorem tailTrace_3785790 : CollatzResearch.WordTrace tailWord_3785790 prefixEnd_3785790 1943929926984848312914475 := by
  unfold tailWord_3785790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259888119342108287715353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92052736636491244201148549 17259888119342108287715353)
  ·
    refine ⟨12944916089506581215786515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17259888119342108287715353 12944916089506581215786515)
    ·
      refine ⟨19417374134259871823679773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944916089506581215786515 19417374134259871823679773)
      ·
        refine ⟨7281515300347451933879915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19417374134259871823679773 7281515300347451933879915)
        ·
          refine ⟨10922272950521177900819873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281515300347451933879915 10922272950521177900819873)
          ·
            refine ⟨8191704712890883425614905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10922272950521177900819873 8191704712890883425614905)
            ·
              refine ⟨6143778534668162569211179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191704712890883425614905 6143778534668162569211179)
              ·
                refine ⟨9215667802002243853816769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143778534668162569211179 9215667802002243853816769)
                ·
                  refine ⟨6911750851501682890362577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215667802002243853816769 6911750851501682890362577)
                  ·
                    refine ⟨5183813138626262167771933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911750851501682890362577 5183813138626262167771933)
                    ·
                      refine ⟨1943929926984848312914475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5183813138626262167771933 1943929926984848312914475)
                      ·
                        rfl

theorem cell23_3785790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3785790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785790 prefixEnd_3785790 := by exact prefixLift 3785790
  have htrace : WordTrace (prefixWord ++ tailWord_3785790) baseStart_3785790 baseEnd_3785790 := by
    simpa [prefixWord, tailWord_3785790, baseEnd_3785790] using wordTrace_append hprefix tailTrace_3785790
  have hstable : (prefixWord ++ tailWord_3785790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785790).length < 2 ^ (prefixWord ++ tailWord_3785790).sum := by decide
  have hdescent : baseEnd_3785790 < baseStart_3785790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785813 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3785813 : Nat := 118140960795 + 3785813 * 2 ^ 59
def prefixEnd_3785813 : Nat := 4983230072969 + 3 ^ 40 * 3785813 * 2
def baseEnd_3785813 : Nat := 1943941737039901722926869

theorem tailTrace_3785813 : CollatzResearch.WordTrace tailWord_3785813 prefixEnd_3785813 1943941737039901722926869 := by
  unfold tailWord_3785813
  simp only [CollatzResearch.WordTrace]
  refine ⟨138079943833653541229810093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92053295889102360819873395 138079943833653541229810093)
  ·
    refine ⟨51779978937620077961178785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138079943833653541229810093 51779978937620077961178785)
    ·
      refine ⟨38834984203215058470884089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51779978937620077961178785 38834984203215058470884089)
      ·
        refine ⟨29126238152411293853163067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38834984203215058470884089 29126238152411293853163067)
        ·
          refine ⟨43689357228616940779744601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29126238152411293853163067 43689357228616940779744601)
          ·
            refine ⟨32767017921462705584808451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43689357228616940779744601 32767017921462705584808451)
            ·
              refine ⟨49150526882194058377212677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32767017921462705584808451 49150526882194058377212677)
              ·
                refine ⟨9215723790411385945727377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49150526882194058377212677 9215723790411385945727377)
                ·
                  refine ⟨6911792842808539459295533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215723790411385945727377 6911792842808539459295533)
                  ·
                    refine ⟨2591922316053202297235825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6911792842808539459295533 2591922316053202297235825)
                    ·
                      refine ⟨1943941737039901722926869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591922316053202297235825 1943941737039901722926869)
                      ·
                        rfl

theorem cell23_3785813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3785813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785813 prefixEnd_3785813 := by exact prefixLift 3785813
  have htrace : WordTrace (prefixWord ++ tailWord_3785813) baseStart_3785813 baseEnd_3785813 := by
    simpa [prefixWord, tailWord_3785813, baseEnd_3785813] using wordTrace_append hprefix tailTrace_3785813
  have hstable : (prefixWord ++ tailWord_3785813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785813).length < 2 ^ (prefixWord ++ tailWord_3785813).sum := by decide
  have hdescent : baseEnd_3785813 < baseStart_3785813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785814 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3785814 : Nat := 118140960795 + 3785814 * 2 ^ 59
def prefixEnd_3785814 : Nat := 4983230072969 + 3 ^ 40 * 3785814 * 2
def baseEnd_3785814 : Nat := 647980750173518739671455

theorem tailTrace_3785814 : CollatzResearch.WordTrace tailWord_3785814 prefixEnd_3785814 647980750173518739671455 := by
  unfold tailWord_3785814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629998769165619900037281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92053320204433278933730997 8629998769165619900037281)
  ·
    refine ⟨6472499076874214925027961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8629998769165619900037281 6472499076874214925027961)
    ·
      refine ⟨4854374307655661193770971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6472499076874214925027961 4854374307655661193770971)
      ·
        refine ⟨7281561461483491790656457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854374307655661193770971 7281561461483491790656457)
        ·
          refine ⟨5461171096112618842992343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281561461483491790656457 5461171096112618842992343)
          ·
            refine ⟨8191756644168928264488515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461171096112618842992343 8191756644168928264488515)
            ·
              refine ⟨12287634966253392396732773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8191756644168928264488515 12287634966253392396732773)
              ·
                refine ⟨2303931556172511074387395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12287634966253392396732773 2303931556172511074387395)
                ·
                  refine ⟨3455897334258766611581093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303931556172511074387395 3455897334258766611581093)
                  ·
                    refine ⟨647980750173518739671455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455897334258766611581093 647980750173518739671455)
                    ·
                      rfl

theorem cell23_3785814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3785814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785814 prefixEnd_3785814 := by exact prefixLift 3785814
  have htrace : WordTrace (prefixWord ++ tailWord_3785814) baseStart_3785814 baseEnd_3785814 := by
    simpa [prefixWord, tailWord_3785814, baseEnd_3785814] using wordTrace_append hprefix tailTrace_3785814
  have hstable : (prefixWord ++ tailWord_3785814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785814).length < 2 ^ (prefixWord ++ tailWord_3785814).sum := by decide
  have hdescent : baseEnd_3785814 < baseStart_3785814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785836 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_3785836 : Nat := 118140960795 + 3785836 * 2 ^ 59
def prefixEnd_3785836 : Nat := 4983230072969 + 3 ^ 40 * 3785836 * 2
def baseEnd_3785836 : Nat := 647984515698318377646421

theorem tailTrace_3785836 : CollatzResearch.WordTrace tailWord_3785836 prefixEnd_3785836 647984515698318377646421 := by
  unfold tailWord_3785836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040391356285108078948681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92053855141713477438598241 69040391356285108078948681)
  ·
    refine ⟨51780293517213831059211511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69040391356285108078948681 51780293517213831059211511)
    ·
      refine ⟨77670440275820746588817267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51780293517213831059211511 77670440275820746588817267)
      ·
        refine ⟨116505660413731119883225901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77670440275820746588817267 116505660413731119883225901)
        ·
          refine ⟨43689622655149169956209713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116505660413731119883225901 43689622655149169956209713)
          ·
            refine ⟨32767216991361877467157285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43689622655149169956209713 32767216991361877467157285)
            ·
              refine ⟨6143853185880352025091991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32767216991361877467157285 6143853185880352025091991)
              ·
                refine ⟨9215779778820528037637987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143853185880352025091991 9215779778820528037637987)
                ·
                  refine ⟨13823669668230792056456981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9215779778820528037637987 13823669668230792056456981)
                  ·
                    refine ⟨647984515698318377646421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13823669668230792056456981 647984515698318377646421)
                    ·
                      rfl

theorem cell23_3785836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_3785836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785836 prefixEnd_3785836 := by exact prefixLift 3785836
  have htrace : WordTrace (prefixWord ++ tailWord_3785836) baseStart_3785836 baseEnd_3785836 := by
    simpa [prefixWord, tailWord_3785836, baseEnd_3785836] using wordTrace_append hprefix tailTrace_3785836
  have hstable : (prefixWord ++ tailWord_3785836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785836).length < 2 ^ (prefixWord ++ tailWord_3785836).sum := by decide
  have hdescent : baseEnd_3785836 < baseStart_3785836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785856 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_3785856 : Nat := 118140960795 + 3785856 * 2 ^ 59
def prefixEnd_3785856 : Nat := 4983230072969 + 3 ^ 40 * 3785856 * 2
def baseEnd_3785856 : Nat := 1943963816708045054689171

theorem tailTrace_3785856 : CollatzResearch.WordTrace tailWord_3785856 prefixEnd_3785856 1943963816708045054689171 := by
  unfold tailWord_3785856
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040756086248879786812711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92054341448331839715750281 69040756086248879786812711)
  ·
    refine ⟨103561134129373319680219067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69040756086248879786812711 103561134129373319680219067)
    ·
      refine ⟨155341701194059979520328601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103561134129373319680219067 155341701194059979520328601)
      ·
        refine ⟨116506275895544984640246451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155341701194059979520328601 116506275895544984640246451)
        ·
          refine ⟨174759413843317476960369677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116506275895544984640246451 174759413843317476960369677)
          ·
            refine ⟨65534780191244053860138629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174759413843317476960369677 65534780191244053860138629)
            ·
              refine ⟨12287771285858260098775993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65534780191244053860138629 12287771285858260098775993)
              ·
                refine ⟨9215828464393695074081995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12287771285858260098775993 9215828464393695074081995)
                ·
                  refine ⟨13823742696590542611122993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9215828464393695074081995 13823742696590542611122993)
                  ·
                    refine ⟨10367807022442906958342245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13823742696590542611122993 10367807022442906958342245)
                    ·
                      refine ⟨1943963816708045054689171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10367807022442906958342245 1943963816708045054689171)
                      ·
                        rfl

theorem cell23_3785856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_3785856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785856 prefixEnd_3785856 := by exact prefixLift 3785856
  have htrace : WordTrace (prefixWord ++ tailWord_3785856) baseStart_3785856 baseEnd_3785856 := by
    simpa [prefixWord, tailWord_3785856, baseEnd_3785856] using wordTrace_append hprefix tailTrace_3785856
  have hstable : (prefixWord ++ tailWord_3785856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785856).length < 2 ^ (prefixWord ++ tailWord_3785856).sum := by decide
  have hdescent : baseEnd_3785856 < baseStart_3785856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785860 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3785860 : Nat := 118140960795 + 3785860 * 2 ^ 59
def prefixEnd_3785860 : Nat := 4983230072969 + 3 ^ 40 * 3785860 * 2
def baseEnd_3785860 : Nat := 1943965870630663039039153

theorem tailTrace_3785860 : CollatzResearch.WordTrace tailWord_3785860 prefixEnd_3785860 1943965870630663039039153 := by
  unfold tailWord_3785860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040829032241634128385517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92054438709655512171180689 69040829032241634128385517)
  ·
    refine ⟨25890310887090612798144569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69040829032241634128385517 25890310887090612798144569)
    ·
      refine ⟨19417733165317959598608427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25890310887090612798144569 19417733165317959598608427)
      ·
        refine ⟨29126599747976939397912641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19417733165317959598608427 29126599747976939397912641)
        ·
          refine ⟨21844949810982704548434481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29126599747976939397912641 21844949810982704548434481)
          ·
            refine ⟨16383712358237028411325861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21844949810982704548434481 16383712358237028411325861)
            ·
              refine ⟨3071946067169442827123599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16383712358237028411325861 3071946067169442827123599)
              ·
                refine ⟨4607919100754164240685399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071946067169442827123599 4607919100754164240685399)
                ·
                  refine ⟨6911878651131246361028099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607919100754164240685399 6911878651131246361028099)
                  ·
                    refine ⟨10367817976696869541542149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911878651131246361028099 10367817976696869541542149)
                    ·
                      refine ⟨1943965870630663039039153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10367817976696869541542149 1943965870630663039039153)
                      ·
                        rfl

theorem cell23_3785860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3785860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785860 prefixEnd_3785860 := by exact prefixLift 3785860
  have htrace : WordTrace (prefixWord ++ tailWord_3785860) baseStart_3785860 baseEnd_3785860 := by
    simpa [prefixWord, tailWord_3785860, baseEnd_3785860] using wordTrace_append hprefix tailTrace_3785860
  have hstable : (prefixWord ++ tailWord_3785860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785860).length < 2 ^ (prefixWord ++ tailWord_3785860).sum := by decide
  have hdescent : baseEnd_3785860 < baseStart_3785860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785870 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3785870 : Nat := 118140960795 + 3785870 * 2 ^ 59
def prefixEnd_3785870 : Nat := 4983230072969 + 3 ^ 40 * 3785870 * 2
def baseEnd_3785870 : Nat := 647990335145735999971369

theorem tailTrace_3785870 : CollatzResearch.WordTrace tailWord_3785870 prefixEnd_3785870 647990335145735999971369 := by
  unfold tailWord_3785870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17260252849305879995579383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92054681862964693309756709 17260252849305879995579383)
  ·
    refine ⟨25890379273958819993369075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17260252849305879995579383 25890379273958819993369075)
    ·
      refine ⟨38835568910938229990053613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25890379273958819993369075 38835568910938229990053613)
      ·
        refine ⟨14563338341601836246270105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38835568910938229990053613 14563338341601836246270105)
        ·
          refine ⟨10922503756201377184702579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14563338341601836246270105 10922503756201377184702579)
          ·
            refine ⟨16383755634302065777053869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922503756201377184702579 16383755634302065777053869)
            ·
              refine ⟨6143908362863274666395201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383755634302065777053869 6143908362863274666395201)
              ·
                refine ⟨4607931272147455999796401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6143908362863274666395201 4607931272147455999796401)
                ·
                  refine ⟨3455948454110591999847301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607931272147455999796401 3455948454110591999847301)
                  ·
                    refine ⟨647990335145735999971369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455948454110591999847301 647990335145735999971369)
                    ·
                      rfl

theorem cell23_3785870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3785870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785870 prefixEnd_3785870 := by exact prefixLift 3785870
  have htrace : WordTrace (prefixWord ++ tailWord_3785870) baseStart_3785870 baseEnd_3785870 := by
    simpa [prefixWord, tailWord_3785870, baseEnd_3785870] using wordTrace_append hprefix tailTrace_3785870
  have hstable : (prefixWord ++ tailWord_3785870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785870).length < 2 ^ (prefixWord ++ tailWord_3785870).sum := by decide
  have hdescent : baseEnd_3785870 < baseStart_3785870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785887 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 2, 4]
def baseStart_3785887 : Nat := 118140960795 + 3785887 * 2 ^ 59
def prefixEnd_3785887 : Nat := 4983230072969 + 3 ^ 40 * 3785887 * 2
def baseEnd_3785887 : Nat := 647993244869444811133843

theorem tailTrace_3785887 : CollatzResearch.WordTrace tailWord_3785887 prefixEnd_3785887 647993244869444811133843 := by
  unfold tailWord_3785887
  simp only [CollatzResearch.WordTrace]
  refine ⟨138082642835385451868003915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92055095223590301245335943 138082642835385451868003915)
  ·
    refine ⟨207123964253078177802005873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138082642835385451868003915 207123964253078177802005873)
    ·
      refine ⟨155342973189808633351504405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207123964253078177802005873 155342973189808633351504405)
      ·
        refine ⟨7281701868272279688351769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155342973189808633351504405 7281701868272279688351769)
        ·
          refine ⟨5461276401204209766263827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281701868272279688351769 5461276401204209766263827)
          ·
            refine ⟨8191914601806314649395741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461276401204209766263827 8191914601806314649395741)
            ·
              refine ⟨3071967975677367993523403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8191914601806314649395741 3071967975677367993523403)
              ·
                refine ⟨4607951963516051990285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071967975677367993523403 4607951963516051990285105)
                ·
                  refine ⟨3455963972637038992713829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607951963516051990285105 3455963972637038992713829)
                  ·
                    refine ⟨647993244869444811133843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455963972637038992713829 647993244869444811133843)
                    ·
                      rfl

theorem cell23_3785887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_3785887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785887 prefixEnd_3785887 := by exact prefixLift 3785887
  have htrace : WordTrace (prefixWord ++ tailWord_3785887) baseStart_3785887 baseEnd_3785887 := by
    simpa [prefixWord, tailWord_3785887, baseEnd_3785887] using wordTrace_append hprefix tailTrace_3785887
  have hstable : (prefixWord ++ tailWord_3785887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785887).length < 2 ^ (prefixWord ++ tailWord_3785887).sum := by decide
  have hdescent : baseEnd_3785887 < baseStart_3785887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785893 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3785893 : Nat := 118140960795 + 3785893 * 2 ^ 59
def prefixEnd_3785893 : Nat := 4983230072969 + 3 ^ 40 * 3785893 * 2
def baseEnd_3785893 : Nat := 1943982815492261409926501

theorem tailTrace_3785893 : CollatzResearch.WordTrace tailWord_3785893 prefixEnd_3785893 1943982815492261409926501 := by
  unfold tailWord_3785893
  simp only [CollatzResearch.WordTrace]
  refine ⟨138082861673363714892722333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92055241115575809928481555 138082861673363714892722333)
  ·
    refine ⟨51781073127511393084770875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138082861673363714892722333 51781073127511393084770875)
    ·
      refine ⟨77671609691267089627156313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51781073127511393084770875 77671609691267089627156313)
      ·
        refine ⟨58253707268450317220367235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77671609691267089627156313 58253707268450317220367235)
        ·
          refine ⟨87380560902675475830550853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58253707268450317220367235 87380560902675475830550853)
          ·
            refine ⟨16383855169251651718228285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87380560902675475830550853 16383855169251651718228285)
            ·
              refine ⟨6143945688469369394335607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383855169251651718228285 6143945688469369394335607)
              ·
                refine ⟨9215918532704054091503411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143945688469369394335607 9215918532704054091503411)
                ·
                  refine ⟨13823877799056081137255117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9215918532704054091503411 13823877799056081137255117)
                  ·
                    refine ⟨5183954174646030426470669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13823877799056081137255117 5183954174646030426470669)
                    ·
                      refine ⟨1943982815492261409926501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5183954174646030426470669 1943982815492261409926501)
                      ·
                        rfl

theorem cell23_3785893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3785893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785893 prefixEnd_3785893 := by exact prefixLift 3785893
  have htrace : WordTrace (prefixWord ++ tailWord_3785893) baseStart_3785893 baseEnd_3785893 := by
    simpa [prefixWord, tailWord_3785893, baseEnd_3785893] using wordTrace_append hprefix tailTrace_3785893
  have hstable : (prefixWord ++ tailWord_3785893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785893).length < 2 ^ (prefixWord ++ tailWord_3785893).sum := by decide
  have hdescent : baseEnd_3785893 < baseStart_3785893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785903 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 3, 3, 2]
def baseStart_3785903 : Nat := 118140960795 + 3785903 * 2 ^ 59
def prefixEnd_3785903 : Nat := 4983230072969 + 3 ^ 40 * 3785903 * 2
def baseEnd_3785903 : Nat := 1943987950298806370801455

theorem tailTrace_3785903 : CollatzResearch.WordTrace tailWord_3785903 prefixEnd_3785903 1943987950298806370801455 := by
  unfold tailWord_3785903
  simp only [CollatzResearch.WordTrace]
  refine ⟨138083226403327486600586363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92055484268884991067057575 138083226403327486600586363)
  ·
    refine ⟨207124839604991229900879545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138083226403327486600586363 207124839604991229900879545)
    ·
      refine ⟨155343629703743422425659659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207124839604991229900879545 155343629703743422425659659)
      ·
        refine ⟨233015444555615133638489489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155343629703743422425659659 233015444555615133638489489)
        ·
          refine ⟨174761583416711350228867117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233015444555615133638489489 174761583416711350228867117)
          ·
            refine ⟨65535593781266756335825169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174761583416711350228867117 65535593781266756335825169)
            ·
              refine ⟨49151695335950067251868877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65535593781266756335825169 49151695335950067251868877)
              ·
                refine ⟨18431885750981275219450829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49151695335950067251868877 18431885750981275219450829)
                ·
                  refine ⟨6911957156617978207294061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18431885750981275219450829 6911957156617978207294061)
                  ·
                    refine ⟨2591983933731741827735273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6911957156617978207294061 2591983933731741827735273)
                    ·
                      refine ⟨1943987950298806370801455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591983933731741827735273 1943987950298806370801455)
                      ·
                        rfl

theorem cell23_3785903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3, 2].length) (baseStart_3785903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785903 prefixEnd_3785903 := by exact prefixLift 3785903
  have htrace : WordTrace (prefixWord ++ tailWord_3785903) baseStart_3785903 baseEnd_3785903 := by
    simpa [prefixWord, tailWord_3785903, baseEnd_3785903] using wordTrace_append hprefix tailTrace_3785903
  have hstable : (prefixWord ++ tailWord_3785903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785903).length < 2 ^ (prefixWord ++ tailWord_3785903).sum := by decide
  have hdescent : baseEnd_3785903 < baseStart_3785903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785906 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3785906 : Nat := 118140960795 + 3785906 * 2 ^ 59
def prefixEnd_3785906 : Nat := 4983230072969 + 3 ^ 40 * 3785906 * 2
def baseEnd_3785906 : Nat := 1943989490740769859063941

theorem tailTrace_3785906 : CollatzResearch.WordTrace tailWord_3785906 prefixEnd_3785906 1943989490740769859063941 := by
  unfold tailWord_3785906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520833955579154528236393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92055557214877745408630381 34520833955579154528236393)
  ·
    refine ⟨25890625466684365896177295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34520833955579154528236393 25890625466684365896177295)
    ·
      refine ⟨38835938200026548844265943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25890625466684365896177295 38835938200026548844265943)
      ·
        refine ⟨58253907300039823266398915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38835938200026548844265943 58253907300039823266398915)
        ·
          refine ⟨87380860950059734899598373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58253907300039823266398915 87380860950059734899598373)
          ·
            refine ⟨16383911428136200293674695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87380860950059734899598373 16383911428136200293674695)
            ·
              refine ⟨24575867142204300440512043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383911428136200293674695 24575867142204300440512043)
              ·
                refine ⟨36863800713306450660768065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24575867142204300440512043 36863800713306450660768065)
                ·
                  refine ⟨27647850534979837995576049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36863800713306450660768065 27647850534979837995576049)
                  ·
                    refine ⟨20735887901234878496682037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27647850534979837995576049 20735887901234878496682037)
                    ·
                      refine ⟨1943989490740769859063941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20735887901234878496682037 1943989490740769859063941)
                      ·
                        rfl

theorem cell23_3785906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3785906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785906 prefixEnd_3785906 := by exact prefixLift 3785906
  have htrace : WordTrace (prefixWord ++ tailWord_3785906) baseStart_3785906 baseEnd_3785906 := by
    simpa [prefixWord, tailWord_3785906, baseEnd_3785906] using wordTrace_append hprefix tailTrace_3785906
  have hstable : (prefixWord ++ tailWord_3785906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785906).length < 2 ^ (prefixWord ++ tailWord_3785906).sum := by decide
  have hdescent : baseEnd_3785906 < baseStart_3785906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785944 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_3785944 : Nat := 118140960795 + 3785944 * 2 ^ 59
def prefixEnd_3785944 : Nat := 4983230072969 + 3 ^ 40 * 3785944 * 2
def baseEnd_3785944 : Nat := 1944009003005640710388767

theorem tailTrace_3785944 : CollatzResearch.WordTrace tailWord_3785944 prefixEnd_3785944 1944009003005640710388767 := by
  unfold tailWord_3785944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69042360898089475301414443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92056481197452633735219257 69042360898089475301414443)
  ·
    refine ⟨103563541347134212952121665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69042360898089475301414443 103563541347134212952121665)
    ·
      refine ⟨77672656010350659714091249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103563541347134212952121665 77672656010350659714091249)
      ·
        refine ⟨58254492007762994785568437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77672656010350659714091249 58254492007762994785568437)
        ·
          refine ⟨5461358625727780761147041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58254492007762994785568437 5461358625727780761147041)
          ·
            refine ⟨4096018969295835570860281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461358625727780761147041 4096018969295835570860281)
            ·
              refine ⟨3072014226971876678145211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096018969295835570860281 3072014226971876678145211)
              ·
                refine ⟨4608021340457815017217817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072014226971876678145211 4608021340457815017217817)
                ·
                  refine ⟨3456016005343361262913363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4608021340457815017217817 3456016005343361262913363)
                  ·
                    refine ⟨5184024008015041894370045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3456016005343361262913363 5184024008015041894370045)
                    ·
                      refine ⟨1944009003005640710388767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5184024008015041894370045 1944009003005640710388767)
                      ·
                        rfl

theorem cell23_3785944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_3785944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785944 prefixEnd_3785944 := by exact prefixLift 3785944
  have htrace : WordTrace (prefixWord ++ tailWord_3785944) baseStart_3785944 baseEnd_3785944 := by
    simpa [prefixWord, tailWord_3785944, baseEnd_3785944] using wordTrace_append hprefix tailTrace_3785944
  have hstable : (prefixWord ++ tailWord_3785944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785944).length < 2 ^ (prefixWord ++ tailWord_3785944).sum := by decide
  have hdescent : baseEnd_3785944 < baseStart_3785944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785946 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3785946 : Nat := 118140960795 + 3785946 * 2 ^ 59
def prefixEnd_3785946 : Nat := 4983230072969 + 3 ^ 40 * 3785946 * 2
def baseEnd_3785946 : Nat := 1944010029966949702563757

theorem tailTrace_3785946 : CollatzResearch.WordTrace tailWord_3785946 prefixEnd_3785946 1944010029966949702563757 := by
  unfold tailWord_3785946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34521198685542926236100423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92056529828114469962934461 34521198685542926236100423)
  ·
    refine ⟨51781798028314389354150635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34521198685542926236100423 51781798028314389354150635)
    ·
      refine ⟨77672697042471584031225953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51781798028314389354150635 77672697042471584031225953)
      ·
        refine ⟨58254522781853688023419465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77672697042471584031225953 58254522781853688023419465)
        ·
          refine ⟨43690892086390266017564599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58254522781853688023419465 43690892086390266017564599)
          ·
            refine ⟨65536338129585399026346899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43690892086390266017564599 65536338129585399026346899)
            ·
              refine ⟨98304507194378098539520349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65536338129585399026346899 98304507194378098539520349)
              ·
                refine ⟨36864190197891786952320131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98304507194378098539520349 36864190197891786952320131)
                ·
                  refine ⟨55296285296837680428480197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36864190197891786952320131 55296285296837680428480197)
                  ·
                    refine ⟨10368053493157065080340037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55296285296837680428480197 10368053493157065080340037)
                    ·
                      refine ⟨1944010029966949702563757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10368053493157065080340037 1944010029966949702563757)
                      ·
                        rfl

theorem cell23_3785946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3785946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785946 prefixEnd_3785946 := by exact prefixLift 3785946
  have htrace : WordTrace (prefixWord ++ tailWord_3785946) baseStart_3785946 baseEnd_3785946 := by
    simpa [prefixWord, tailWord_3785946, baseEnd_3785946] using wordTrace_append hprefix tailTrace_3785946
  have hstable : (prefixWord ++ tailWord_3785946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785946).length < 2 ^ (prefixWord ++ tailWord_3785946).sum := by decide
  have hdescent : baseEnd_3785946 < baseStart_3785946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785956 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 7]
def baseStart_3785956 : Nat := 118140960795 + 3785956 * 2 ^ 59
def prefixEnd_3785956 : Nat := 4983230072969 + 3 ^ 40 * 3785956 * 2
def baseEnd_3785956 : Nat := 216001684974832740382079

theorem tailTrace_3785956 : CollatzResearch.WordTrace tailWord_3785956 prefixEnd_3785956 216001684974832740382079 := by
  unfold tailWord_3785956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69042579736067738326132861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92056772981423651101510481 69042579736067738326132861)
  ·
    refine ⟨25890967401025401872299823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69042579736067738326132861 25890967401025401872299823)
    ·
      refine ⟨38836451101538102808449735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25890967401025401872299823 38836451101538102808449735)
      ·
        refine ⟨58254676652307154212674603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38836451101538102808449735 58254676652307154212674603)
        ·
          refine ⟨87382014978460731319011905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58254676652307154212674603 87382014978460731319011905)
          ·
            refine ⟨65536511233845548489258929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87382014978460731319011905 65536511233845548489258929)
            ·
              refine ⟨49152383425384161366944197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65536511233845548489258929 49152383425384161366944197)
              ·
                refine ⟨9216071892259530256302037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49152383425384161366944197 9216071892259530256302037)
                ·
                  refine ⟨216001684974832740382079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9216071892259530256302037 216001684974832740382079)
                  ·
                    rfl

theorem cell23_3785956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_3785956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785956 prefixEnd_3785956 := by exact prefixLift 3785956
  have htrace : WordTrace (prefixWord ++ tailWord_3785956) baseStart_3785956 baseEnd_3785956 := by
    simpa [prefixWord, tailWord_3785956, baseEnd_3785956] using wordTrace_append hprefix tailTrace_3785956
  have hstable : (prefixWord ++ tailWord_3785956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785956).length < 2 ^ (prefixWord ++ tailWord_3785956).sum := by decide
  have hdescent : baseEnd_3785956 < baseStart_3785956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785993 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 7, 2]
def baseStart_3785993 : Nat := 118140960795 + 3785993 * 2 ^ 59
def prefixEnd_3785993 : Nat := 4983230072969 + 3 ^ 40 * 3785993 * 2
def baseEnd_3785993 : Nat := 1944034163557711018676041

theorem tailTrace_3785993 : CollatzResearch.WordTrace tailWord_3785993 prefixEnd_3785993 1944034163557711018676041 := by
  unfold tailWord_3785993
  simp only [CollatzResearch.WordTrace]
  refine ⟨138086508973001431971362633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92057672648667621314241755 138086508973001431971362633)
  ·
    refine ⟨103564881729751073978521975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138086508973001431971362633 103564881729751073978521975)
    ·
      refine ⟨155347322594626610967782963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103564881729751073978521975 155347322594626610967782963)
      ·
        refine ⟨233020983891939916451674445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155347322594626610967782963 233020983891939916451674445)
        ·
          refine ⟨87382868959477468669377917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233020983891939916451674445 87382868959477468669377917)
          ·
            refine ⟨32768575859804050751016719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87382868959477468669377917 32768575859804050751016719)
            ·
              refine ⟨49152863789706076126525079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32768575859804050751016719 49152863789706076126525079)
              ·
                refine ⟨73729295684559114189787619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49152863789706076126525079 73729295684559114189787619)
                ·
                  refine ⟨110593943526838671284681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73729295684559114189787619 110593943526838671284681429)
                  ·
                    refine ⟨2592045551410281358234721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110593943526838671284681429 2592045551410281358234721)
                    ·
                      refine ⟨1944034163557711018676041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592045551410281358234721 1944034163557711018676041)
                      ·
                        rfl

theorem cell23_3785993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7, 2].length) (baseStart_3785993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3785993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3785993 prefixEnd_3785993 := by exact prefixLift 3785993
  have htrace : WordTrace (prefixWord ++ tailWord_3785993) baseStart_3785993 baseEnd_3785993 := by
    simpa [prefixWord, tailWord_3785993, baseEnd_3785993] using wordTrace_append hprefix tailTrace_3785993
  have hstable : (prefixWord ++ tailWord_3785993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785993).length < 2 ^ (prefixWord ++ tailWord_3785993).sum := by decide
  have hdescent : baseEnd_3785993 < baseStart_3785993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786084 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_3786084 : Nat := 118140960795 + 3786084 * 2 ^ 59
def prefixEnd_3786084 : Nat := 4983230072969 + 3 ^ 40 * 3786084 * 2
def baseEnd_3786084 : Nat := 648026963432423387546041

theorem tailTrace_3786084 : CollatzResearch.WordTrace tailWord_3786084 prefixEnd_3786084 648026963432423387546041 := by
  unfold tailWord_3786084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69044914007835877256462653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92059885343781169675283537 69044914007835877256462653)
  ·
    refine ⟨25891842752938453971173495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69044914007835877256462653 25891842752938453971173495)
    ·
      refine ⟨38837764129407680956760243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891842752938453971173495 38837764129407680956760243)
      ·
        refine ⟨58256646194111521435140365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837764129407680956760243 58256646194111521435140365)
        ·
          refine ⟨21846242322791820538177637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58256646194111521435140365 21846242322791820538177637)
          ·
            refine ⟨4096170435523466350908307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21846242322791820538177637 4096170435523466350908307)
            ·
              refine ⟨6144255653285199526362461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096170435523466350908307 6144255653285199526362461)
              ·
                refine ⟨2304095869981949822385923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6144255653285199526362461 2304095869981949822385923)
                ·
                  refine ⟨3456143804972924733578885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304095869981949822385923 3456143804972924733578885)
                  ·
                    refine ⟨648026963432423387546041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456143804972924733578885 648026963432423387546041)
                    ·
                      rfl

theorem cell23_3786084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_3786084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786084 prefixEnd_3786084 := by exact prefixLift 3786084
  have htrace : WordTrace (prefixWord ++ tailWord_3786084) baseStart_3786084 baseEnd_3786084 := by
    simpa [prefixWord, tailWord_3786084, baseEnd_3786084] using wordTrace_append hprefix tailTrace_3786084
  have hstable : (prefixWord ++ tailWord_3786084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786084).length < 2 ^ (prefixWord ++ tailWord_3786084).sum := by decide
  have hdescent : baseEnd_3786084 < baseStart_3786084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786094 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3786094 : Nat := 118140960795 + 3786094 * 2 ^ 59
def prefixEnd_3786094 : Nat := 4983230072969 + 3 ^ 40 * 3786094 * 2
def baseEnd_3786094 : Nat := 1944086025103815123513077

theorem tailTrace_3786094 : CollatzResearch.WordTrace tailWord_3786094 prefixEnd_3786094 1944086025103815123513077 := by
  unfold tailWord_3786094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17261274093204440777598667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92060128497090350813859557 17261274093204440777598667)
  ·
    refine ⟨25891911139806661166398001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17261274093204440777598667 25891911139806661166398001)
    ·
      refine ⟨19418933354854995874798501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25891911139806661166398001 19418933354854995874798501)
      ·
        refine ⟨3641050004035311726524719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19418933354854995874798501 3641050004035311726524719)
        ·
          refine ⟨5461575006052967589787079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641050004035311726524719 5461575006052967589787079)
          ·
            refine ⟨8192362509079451384680619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461575006052967589787079 8192362509079451384680619)
            ·
              refine ⟨12288543763619177077020929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192362509079451384680619 12288543763619177077020929)
              ·
                refine ⟨9216407822714382807765697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12288543763619177077020929 9216407822714382807765697)
                ·
                  refine ⟨6912305867035787105824273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216407822714382807765697 6912305867035787105824273)
                  ·
                    refine ⟨5184229400276840329368205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912305867035787105824273 5184229400276840329368205)
                    ·
                      refine ⟨1944086025103815123513077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5184229400276840329368205 1944086025103815123513077)
                      ·
                        rfl

theorem cell23_3786094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3786094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786094 prefixEnd_3786094 := by exact prefixLift 3786094
  have htrace : WordTrace (prefixWord ++ tailWord_3786094) baseStart_3786094 baseEnd_3786094 := by
    simpa [prefixWord, tailWord_3786094, baseEnd_3786094] using wordTrace_append hprefix tailTrace_3786094
  have hstable : (prefixWord ++ tailWord_3786094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786094).length < 2 ^ (prefixWord ++ tailWord_3786094).sum := by decide
  have hdescent : baseEnd_3786094 < baseStart_3786094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786101 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3786101 : Nat := 118140960795 + 3786101 * 2 ^ 59
def prefixEnd_3786101 : Nat := 4983230072969 + 3 ^ 40 * 3786101 * 2
def baseEnd_3786101 : Nat := 648029873156132198708515

theorem tailTrace_3786101 : CollatzResearch.WordTrace tailWord_3786101 prefixEnd_3786101 648029873156132198708515 := by
  unfold tailWord_3786101
  simp only [CollatzResearch.WordTrace]
  refine ⟨138090448056610166416294157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92060298704406777610862771 138090448056610166416294157)
  ·
    refine ⟨51783918021228812406110309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138090448056610166416294157 51783918021228812406110309)
    ·
      refine ⟨9709484628980402326145683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51783918021228812406110309 9709484628980402326145683)
      ·
        refine ⟨14564226943470603489218525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709484628980402326145683 14564226943470603489218525)
        ·
          refine ⟨5461585103801476308456947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14564226943470603489218525 5461585103801476308456947)
          ·
            refine ⟨8192377655702214462685421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461585103801476308456947 8192377655702214462685421)
            ·
              refine ⟨3072141620888330423507033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8192377655702214462685421 3072141620888330423507033)
              ·
                refine ⟨2304106215666247817630275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072141620888330423507033 2304106215666247817630275)
                ·
                  refine ⟨3456159323499371726445413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304106215666247817630275 3456159323499371726445413)
                  ·
                    refine ⟨648029873156132198708515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456159323499371726445413 648029873156132198708515)
                    ·
                      rfl

theorem cell23_3786101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3786101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786101 prefixEnd_3786101 := by exact prefixLift 3786101
  have htrace : WordTrace (prefixWord ++ tailWord_3786101) baseStart_3786101 baseEnd_3786101 := by
    simpa [prefixWord, tailWord_3786101, baseEnd_3786101] using wordTrace_append hprefix tailTrace_3786101
  have hstable : (prefixWord ++ tailWord_3786101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786101).length < 2 ^ (prefixWord ++ tailWord_3786101).sum := by decide
  have hdescent : baseEnd_3786101 < baseStart_3786101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786114 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3786114 : Nat := 118140960795 + 3786114 * 2 ^ 59
def prefixEnd_3786114 : Nat := 4983230072969 + 3 ^ 40 * 3786114 * 2
def baseEnd_3786114 : Nat := 216010699412989449473665

theorem tailTrace_3786114 : CollatzResearch.WordTrace tailWord_3786114 prefixEnd_3786114 216010699412989449473665 := by
  unfold tailWord_3786114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522730551390767409129349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92060614803708713091011597 34522730551390767409129349)
  ·
    refine ⟨6473011978385768889211753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34522730551390767409129349 6473011978385768889211753)
    ·
      refine ⟨4854758983789326666908815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6473011978385768889211753 4854758983789326666908815)
      ·
        refine ⟨7282138475683990000363223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854758983789326666908815 7282138475683990000363223)
        ·
          refine ⟨10923207713525985000544835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282138475683990000363223 10923207713525985000544835)
          ·
            refine ⟨16384811570288977500817253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923207713525985000544835 16384811570288977500817253)
            ·
              refine ⟨3072152169429183281403235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16384811570288977500817253 3072152169429183281403235)
              ·
                refine ⟨4608228254143774922104853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072152169429183281403235 4608228254143774922104853)
                ·
                  refine ⟨216010699412989449473665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4608228254143774922104853 216010699412989449473665)
                  ·
                    rfl

theorem cell23_3786114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3786114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786114 prefixEnd_3786114 := by exact prefixLift 3786114
  have htrace : WordTrace (prefixWord ++ tailWord_3786114) baseStart_3786114 baseEnd_3786114 := by
    simpa [prefixWord, tailWord_3786114, baseEnd_3786114] using wordTrace_append hprefix tailTrace_3786114
  have hstable : (prefixWord ++ tailWord_3786114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786114).length < 2 ^ (prefixWord ++ tailWord_3786114).sum := by decide
  have hdescent : baseEnd_3786114 < baseStart_3786114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786123 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 6]
def baseStart_3786123 : Nat := 118140960795 + 3786123 * 2 ^ 59
def prefixEnd_3786123 : Nat := 4983230072969 + 3 ^ 40 * 3786123 * 2
def baseEnd_3786123 : Nat := 648033638680931836683481

theorem tailTrace_3786123 : CollatzResearch.WordTrace tailWord_3786123 prefixEnd_3786123 648033638680931836683481 := by
  unfold tailWord_3786123
  simp only [CollatzResearch.WordTrace]
  refine ⟨138091250462530464173595023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92060833641686976115730015 138091250462530464173595023)
  ·
    refine ⟨207136875693795696260392535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138091250462530464173595023 207136875693795696260392535)
    ·
      refine ⟨310705313540693544390588803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207136875693795696260392535 310705313540693544390588803)
      ·
        refine ⟨466057970311040316585883205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310705313540693544390588803 466057970311040316585883205)
        ·
          refine ⟨87385869433320059359853101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466057970311040316585883205 87385869433320059359853101)
          ·
            refine ⟨32769701037495022259944913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87385869433320059359853101 32769701037495022259944913)
            ·
              refine ⟨24577275778121266694958685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32769701037495022259944913 24577275778121266694958685)
              ·
                refine ⟨9216478416795475010609507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24577275778121266694958685 9216478416795475010609507)
                ·
                  refine ⟨13824717625193212515914261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216478416795475010609507 13824717625193212515914261)
                  ·
                    refine ⟨648033638680931836683481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13824717625193212515914261 648033638680931836683481)
                    ·
                      rfl

theorem cell23_3786123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_3786123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786123 prefixEnd_3786123 := by exact prefixLift 3786123
  have htrace : WordTrace (prefixWord ++ tailWord_3786123) baseStart_3786123 baseEnd_3786123 := by
    simpa [prefixWord, tailWord_3786123, baseEnd_3786123] using wordTrace_append hprefix tailTrace_3786123
  have hstable : (prefixWord ++ tailWord_3786123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786123).length < 2 ^ (prefixWord ++ tailWord_3786123).sum := by decide
  have hdescent : baseEnd_3786123 < baseStart_3786123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786133 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3786133 : Nat := 118140960795 + 3786133 * 2 ^ 59
def prefixEnd_3786133 : Nat := 4983230072969 + 3 ^ 40 * 3786133 * 2
def baseEnd_3786133 : Nat := 1944106050849340470925397

theorem tailTrace_3786133 : CollatzResearch.WordTrace tailWord_3786133 prefixEnd_3786133 1944106050849340470925397 := by
  unfold tailWord_3786133
  simp only [CollatzResearch.WordTrace]
  refine ⟨138091615192494235881459053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92061076794996157254306035 138091615192494235881459053)
  ·
    refine ⟨51784355697185338455547145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138091615192494235881459053 51784355697185338455547145)
    ·
      refine ⟨38838266772889003841660359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51784355697185338455547145 38838266772889003841660359)
      ·
        refine ⟨58257400159333505762490539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38838266772889003841660359 58257400159333505762490539)
        ·
          refine ⟨87386100239000258643735809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58257400159333505762490539 87386100239000258643735809)
          ·
            refine ⟨65539575179250193982801857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87386100239000258643735809 65539575179250193982801857)
            ·
              refine ⟨49154681384437645487101393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65539575179250193982801857 49154681384437645487101393)
              ·
                refine ⟨36866011038328234115326045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49154681384437645487101393 36866011038328234115326045)
                ·
                  refine ⟨13824754139373087793247267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36866011038328234115326045 13824754139373087793247267)
                  ·
                    refine ⟨20737131209059631689870901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13824754139373087793247267 20737131209059631689870901)
                    ·
                      refine ⟨1944106050849340470925397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20737131209059631689870901 1944106050849340470925397)
                      ·
                        rfl

theorem cell23_3786133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3786133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786133 prefixEnd_3786133 := by exact prefixLift 3786133
  have htrace : WordTrace (prefixWord ++ tailWord_3786133) baseStart_3786133 baseEnd_3786133 := by
    simpa [prefixWord, tailWord_3786133, baseEnd_3786133] using wordTrace_append hprefix tailTrace_3786133
  have hstable : (prefixWord ++ tailWord_3786133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786133).length < 2 ^ (prefixWord ++ tailWord_3786133).sum := by decide
  have hdescent : baseEnd_3786133 < baseStart_3786133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786147 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 1, 1, 4]
def baseStart_3786147 : Nat := 118140960795 + 3786147 * 2 ^ 59
def prefixEnd_3786147 : Nat := 4983230072969 + 3 ^ 40 * 3786147 * 2
def baseEnd_3786147 : Nat := 1944113239578503416150333

theorem tailTrace_3786147 : CollatzResearch.WordTrace tailWord_3786147 prefixEnd_3786147 1944113239578503416150333 := by
  unfold tailWord_3786147
  simp only [CollatzResearch.WordTrace]
  refine ⟨138092125814443516272468695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92061417209629010848312463 138092125814443516272468695)
  ·
    refine ⟨207138188721665274408703043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138092125814443516272468695 207138188721665274408703043)
    ·
      refine ⟨310707283082497911613054565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207138188721665274408703043 310707283082497911613054565)
      ·
        refine ⟨58257615577968358427447731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310707283082497911613054565 58257615577968358427447731)
        ·
          refine ⟨87386423366952537641171597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58257615577968358427447731 87386423366952537641171597)
          ·
            refine ⟨32769908762607201615439349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87386423366952537641171597 32769908762607201615439349)
            ·
              refine ⟨3072178946494425151447439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32769908762607201615439349 3072178946494425151447439)
              ·
                refine ⟨4608268419741637727171159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072178946494425151447439 4608268419741637727171159)
                ·
                  refine ⟨6912402629612456590756739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608268419741637727171159 6912402629612456590756739)
                  ·
                    refine ⟨10368603944418684886135109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912402629612456590756739 10368603944418684886135109)
                    ·
                      refine ⟨1944113239578503416150333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10368603944418684886135109 1944113239578503416150333)
                      ·
                        rfl

theorem cell23_3786147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_3786147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786147 prefixEnd_3786147 := by exact prefixLift 3786147
  have htrace : WordTrace (prefixWord ++ tailWord_3786147) baseStart_3786147 baseEnd_3786147 := by
    simpa [prefixWord, tailWord_3786147, baseEnd_3786147] using wordTrace_append hprefix tailTrace_3786147
  have hstable : (prefixWord ++ tailWord_3786147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786147).length < 2 ^ (prefixWord ++ tailWord_3786147).sum := by decide
  have hdescent : baseEnd_3786147 < baseStart_3786147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786183 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3786183 : Nat := 118140960795 + 3786183 * 2 ^ 59
def prefixEnd_3786183 : Nat := 4983230072969 + 3 ^ 40 * 3786183 * 2
def baseEnd_3786183 : Nat := 648043908294021758433389

theorem tailTrace_3786183 : CollatzResearch.WordTrace tailWord_3786183 prefixEnd_3786183 648043908294021758433389 := by
  unfold tailWord_3786183
  simp only [CollatzResearch.WordTrace]
  refine ⟨138093438842313094420779203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92062292561542062947186135 138093438842313094420779203)
  ·
    refine ⟨207140158263469641631168805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138093438842313094420779203 207140158263469641631168805)
    ·
      refine ⟨38838779674400557805844151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207140158263469641631168805 38838779674400557805844151)
      ·
        refine ⟨58258169511600836708766227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38838779674400557805844151 58258169511600836708766227)
        ·
          refine ⟨87387254267401255063149341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58258169511600836708766227 87387254267401255063149341)
          ·
            refine ⟨32770220350275470648681003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87387254267401255063149341 32770220350275470648681003)
            ·
              refine ⟨49155330525413205973021505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32770220350275470648681003 49155330525413205973021505)
              ·
                refine ⟨36866497894059904479766129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49155330525413205973021505 36866497894059904479766129)
                ·
                  refine ⟨27649873420544928359824597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36866497894059904479766129 27649873420544928359824597)
                  ·
                    refine ⟨648043908294021758433389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27649873420544928359824597 648043908294021758433389)
                    ·
                      rfl

theorem cell23_3786183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3786183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786183 prefixEnd_3786183 := by exact prefixLift 3786183
  have htrace : WordTrace (prefixWord ++ tailWord_3786183) baseStart_3786183 baseEnd_3786183 := by
    simpa [prefixWord, tailWord_3786183, baseEnd_3786183] using wordTrace_append hprefix tailTrace_3786183
  have hstable : (prefixWord ++ tailWord_3786183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786183).length < 2 ^ (prefixWord ++ tailWord_3786183).sum := by decide
  have hdescent : baseEnd_3786183 < baseStart_3786183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786197 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3786197 : Nat := 118140960795 + 3786197 * 2 ^ 59
def prefixEnd_3786197 : Nat := 4983230072969 + 3 ^ 40 * 3786197 * 2
def baseEnd_3786197 : Nat := 1944138913611228220525103

theorem tailTrace_3786197 : CollatzResearch.WordTrace tailWord_3786197 prefixEnd_3786197 1944138913611228220525103 := by
  unfold tailWord_3786197
  simp only [CollatzResearch.WordTrace]
  refine ⟨138093949464262374811788845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92062632976174916541192563 138093949464262374811788845)
  ·
    refine ⟨51785231049098390554420817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138093949464262374811788845 51785231049098390554420817)
    ·
      refine ⟨38838923286823792915815613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51785231049098390554420817 38838923286823792915815613)
      ·
        refine ⟨14564596232558922343430855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38838923286823792915815613 14564596232558922343430855)
        ·
          refine ⟨21846894348838383515146283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564596232558922343430855 21846894348838383515146283)
          ·
            refine ⟨32770341523257575272719425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21846894348838383515146283 32770341523257575272719425)
            ·
              refine ⟨24577756142443181454539569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32770341523257575272719425 24577756142443181454539569)
              ·
                refine ⟨18433317106832386090904677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24577756142443181454539569 18433317106832386090904677)
                ·
                  refine ⟨3456246957531072392044627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18433317106832386090904677 3456246957531072392044627)
                  ·
                    refine ⟨5184370436296608588066941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3456246957531072392044627 5184370436296608588066941)
                    ·
                      refine ⟨1944138913611228220525103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5184370436296608588066941 1944138913611228220525103)
                      ·
                        rfl

theorem cell23_3786197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3786197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786197 prefixEnd_3786197 := by exact prefixLift 3786197
  have htrace : WordTrace (prefixWord ++ tailWord_3786197) baseStart_3786197 baseEnd_3786197 := by
    simpa [prefixWord, tailWord_3786197, baseEnd_3786197] using wordTrace_append hprefix tailTrace_3786197
  have hstable : (prefixWord ++ tailWord_3786197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786197).length < 2 ^ (prefixWord ++ tailWord_3786197).sum := by decide
  have hdescent : baseEnd_3786197 < baseStart_3786197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786198 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3786198 : Nat := 118140960795 + 3786198 * 2 ^ 59
def prefixEnd_3786198 : Nat := 4983230072969 + 3 ^ 40 * 3786198 * 2
def baseEnd_3786198 : Nat := 1944139427091882716612599

theorem tailTrace_3786198 : CollatzResearch.WordTrace tailWord_3786198 prefixEnd_3786198 1944139427091882716612599 := by
  unfold tailWord_3786198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630874121078671998910953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92062657291505834655050165 8630874121078671998910953)
  ·
    refine ⟨6473155590809003999183215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8630874121078671998910953 6473155590809003999183215)
    ·
      refine ⟨9709733386213505998774823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473155590809003999183215 9709733386213505998774823)
      ·
        refine ⟨14564600079320258998162235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709733386213505998774823 14564600079320258998162235)
        ·
          refine ⟨21846900118980388497243353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564600079320258998162235 21846900118980388497243353)
          ·
            refine ⟨16385175089235291372932515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21846900118980388497243353 16385175089235291372932515)
            ·
              refine ⟨24577762633852937059398773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385175089235291372932515 24577762633852937059398773)
              ·
                refine ⟨2304165246923712849318635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24577762633852937059398773 2304165246923712849318635)
                ·
                  refine ⟨3456247870385569273977953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304165246923712849318635 3456247870385569273977953)
                  ·
                    refine ⟨2592185902789176955483465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3456247870385569273977953 2592185902789176955483465)
                    ·
                      refine ⟨1944139427091882716612599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592185902789176955483465 1944139427091882716612599)
                      ·
                        rfl

theorem cell23_3786198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3786198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786198 prefixEnd_3786198 := by exact prefixLift 3786198
  have htrace : WordTrace (prefixWord ++ tailWord_3786198) baseStart_3786198 baseEnd_3786198 := by
    simpa [prefixWord, tailWord_3786198, baseEnd_3786198] using wordTrace_append hprefix tailTrace_3786198
  have hstable : (prefixWord ++ tailWord_3786198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786198).length < 2 ^ (prefixWord ++ tailWord_3786198).sum := by decide
  have hdescent : baseEnd_3786198 < baseStart_3786198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786241 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_3786241 : Nat := 118140960795 + 3786241 * 2 ^ 59
def prefixEnd_3786241 : Nat := 4983230072969 + 3 ^ 40 * 3786241 * 2
def baseEnd_3786241 : Nat := 1944161506760026048374901

theorem tailTrace_3786241 : CollatzResearch.WordTrace tailWord_3786241 prefixEnd_3786241 1944161506760026048374901 := by
  unfold tailWord_3786241
  simp only [CollatzResearch.WordTrace]
  refine ⟨138095554276102970326390577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92063702850735313550927051 138095554276102970326390577)
  ·
    refine ⟨103571665707077227744792933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138095554276102970326390577 103571665707077227744792933)
    ·
      refine ⟨19419687320076980202148675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103571665707077227744792933 19419687320076980202148675)
      ·
        refine ⟨29129530980115470303223013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19419687320076980202148675 29129530980115470303223013)
        ·
          refine ⟨5461787058771650681854315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29129530980115470303223013 5461787058771650681854315)
          ·
            refine ⟨8192680588157476022781473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461787058771650681854315 8192680588157476022781473)
            ·
              refine ⟨6144510441118107017086105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8192680588157476022781473 6144510441118107017086105)
              ·
                refine ⟨4608382830838580262814579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144510441118107017086105 4608382830838580262814579)
                ·
                  refine ⟨6912574246257870394221869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608382830838580262814579 6912574246257870394221869)
                  ·
                    refine ⟨2592215342346701397833201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6912574246257870394221869 2592215342346701397833201)
                    ·
                      refine ⟨1944161506760026048374901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592215342346701397833201 1944161506760026048374901)
                      ·
                        rfl

theorem cell23_3786241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_3786241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786241 prefixEnd_3786241 := by exact prefixLift 3786241
  have htrace : WordTrace (prefixWord ++ tailWord_3786241) baseStart_3786241 baseEnd_3786241 := by
    simpa [prefixWord, tailWord_3786241, baseEnd_3786241] using wordTrace_append hprefix tailTrace_3786241
  have hstable : (prefixWord ++ tailWord_3786241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786241).length < 2 ^ (prefixWord ++ tailWord_3786241).sum := by decide
  have hdescent : baseEnd_3786241 < baseStart_3786241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786243 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 9]
def baseStart_3786243 : Nat := 118140960795 + 3786243 * 2 ^ 59
def prefixEnd_3786243 : Nat := 4983230072969 + 3 ^ 40 * 3786243 * 2
def baseEnd_3786243 : Nat := 216018059302370560061099

theorem tailTrace_3786243 : CollatzResearch.WordTrace tailWord_3786243 prefixEnd_3786243 216018059302370560061099 := by
  unfold tailWord_3786243
  simp only [CollatzResearch.WordTrace]
  refine ⟨138095627222095724667963383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92063751481397149778642255 138095627222095724667963383)
  ·
    refine ⟨207143440833143587001945075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138095627222095724667963383 207143440833143587001945075)
    ·
      refine ⟨310715161249715380502917613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207143440833143587001945075 310715161249715380502917613)
      ·
        refine ⟨116518185468643267688594105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310715161249715380502917613 116518185468643267688594105)
        ·
          refine ⟨87388639101482450766445579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116518185468643267688594105 87388639101482450766445579)
          ·
            refine ⟨131082958652223676149668369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87388639101482450766445579 131082958652223676149668369)
            ·
              refine ⟨98312218989167757112251277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131082958652223676149668369 98312218989167757112251277)
              ·
                refine ⟨36867082120937908917094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98312218989167757112251277 36867082120937908917094229)
                ·
                  refine ⟨216018059302370560061099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36867082120937908917094229 216018059302370560061099)
                  ·
                    rfl

theorem cell23_3786243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 9].length) (baseStart_3786243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786243 prefixEnd_3786243 := by exact prefixLift 3786243
  have htrace : WordTrace (prefixWord ++ tailWord_3786243) baseStart_3786243 baseEnd_3786243 := by
    simpa [prefixWord, tailWord_3786243, baseEnd_3786243] using wordTrace_append hprefix tailTrace_3786243
  have hstable : (prefixWord ++ tailWord_3786243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786243).length < 2 ^ (prefixWord ++ tailWord_3786243).sum := by decide
  have hdescent : baseEnd_3786243 < baseStart_3786243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786290 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3786290 : Nat := 118140960795 + 3786290 * 2 ^ 59
def prefixEnd_3786290 : Nat := 4983230072969 + 3 ^ 40 * 3786290 * 2
def baseEnd_3786290 : Nat := 648062222437365452220725

theorem tailTrace_3786290 : CollatzResearch.WordTrace tailWord_3786290 prefixEnd_3786290 648062222437365452220725 := by
  unfold tailWord_3786290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524335363231362923731081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92064894301950301129949549 34524335363231362923731081)
  ·
    refine ⟨25893251522423522192798311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34524335363231362923731081 25893251522423522192798311)
    ·
      refine ⟨38839877283635283289197467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893251522423522192798311 38839877283635283289197467)
      ·
        refine ⟨58259815925452924933796201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38839877283635283289197467 58259815925452924933796201)
        ·
          refine ⟨43694861944089693700347151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58259815925452924933796201 43694861944089693700347151)
          ·
            refine ⟨65542292916134540550520727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43694861944089693700347151 65542292916134540550520727)
            ·
              refine ⟨98313439374201810825781091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65542292916134540550520727 98313439374201810825781091)
              ·
                refine ⟨147470159061302716238671637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98313439374201810825781091 147470159061302716238671637)
                ·
                  refine ⟨6912663705998564823687733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147470159061302716238671637 6912663705998564823687733)
                  ·
                    refine ⟨648062222437365452220725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6912663705998564823687733 648062222437365452220725)
                    ·
                      rfl

theorem cell23_3786290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3786290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786290 prefixEnd_3786290 := by exact prefixLift 3786290
  have htrace : WordTrace (prefixWord ++ tailWord_3786290) baseStart_3786290 baseEnd_3786290 := by
    simpa [prefixWord, tailWord_3786290, baseEnd_3786290] using wordTrace_append hprefix tailTrace_3786290
  have hstable : (prefixWord ++ tailWord_3786290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786290).length < 2 ^ (prefixWord ++ tailWord_3786290).sum := by decide
  have hdescent : baseEnd_3786290 < baseStart_3786290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786327 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3786327 : Nat := 118140960795 + 3786327 * 2 ^ 59
def prefixEnd_3786327 : Nat := 4983230072969 + 3 ^ 40 * 3786327 * 2
def baseEnd_3786327 : Nat := 1944205666096312711899505

theorem tailTrace_3786327 : CollatzResearch.WordTrace tailWord_3786327 prefixEnd_3786327 1944205666096312711899505 := by
  unfold tailWord_3786327
  simp only [CollatzResearch.WordTrace]
  refine ⟨138098690953791407014021235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92065793969194271342680823 138098690953791407014021235)
  ·
    refine ⟨207148036430687110521031853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138098690953791407014021235 207148036430687110521031853)
    ·
      refine ⟨77680513661507666445386945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207148036430687110521031853 77680513661507666445386945)
      ·
        refine ⟨58260385246130749834040209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77680513661507666445386945 58260385246130749834040209)
        ·
          refine ⟨43695288934598062375530157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58260385246130749834040209 43695288934598062375530157)
          ·
            refine ⟨16385733350474273390823809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43695288934598062375530157 16385733350474273390823809)
            ·
              refine ⟨12289300012855705043117857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16385733350474273390823809 12289300012855705043117857)
              ·
                refine ⟨9216975009641778782338393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12289300012855705043117857 9216975009641778782338393)
                ·
                  refine ⟨6912731257231334086753795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216975009641778782338393 6912731257231334086753795)
                  ·
                    refine ⟨10369096885847001130130693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912731257231334086753795 10369096885847001130130693)
                    ·
                      refine ⟨1944205666096312711899505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10369096885847001130130693 1944205666096312711899505)
                      ·
                        rfl

theorem cell23_3786327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3786327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786327 prefixEnd_3786327 := by exact prefixLift 3786327
  have htrace : WordTrace (prefixWord ++ tailWord_3786327) baseStart_3786327 baseEnd_3786327 := by
    simpa [prefixWord, tailWord_3786327, baseEnd_3786327] using wordTrace_append hprefix tailTrace_3786327
  have hstable : (prefixWord ++ tailWord_3786327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786327).length < 2 ^ (prefixWord ++ tailWord_3786327).sum := by decide
  have hdescent : baseEnd_3786327 < baseStart_3786327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786337 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3786337 : Nat := 118140960795 + 3786337 * 2 ^ 59
def prefixEnd_3786337 : Nat := 4983230072969 + 3 ^ 40 * 3786337 * 2
def baseEnd_3786337 : Nat := 648070266967619224258153

theorem tailTrace_3786337 : CollatzResearch.WordTrace tailWord_3786337 prefixEnd_3786337 648070266967619224258153 := by
  unfold tailWord_3786337
  simp only [CollatzResearch.WordTrace]
  refine ⟨138099055683755178721885265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92066037122503452481256843 138099055683755178721885265)
  ·
    refine ⟨103574291762816384041413949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138099055683755178721885265 103574291762816384041413949)
    ·
      refine ⟨38840359411056144015530231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103574291762816384041413949 38840359411056144015530231)
      ·
        refine ⟨58260539116584216023295347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38840359411056144015530231 58260539116584216023295347)
        ·
          refine ⟨87390808674876324034943021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58260539116584216023295347 87390808674876324034943021)
          ·
            refine ⟨32771553253078621513103633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87390808674876324034943021 32771553253078621513103633)
            ·
              refine ⟨24578664939808966134827725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32771553253078621513103633 24578664939808966134827725)
              ·
                refine ⟨9216999352428362300560397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24578664939808966134827725 9216999352428362300560397)
                ·
                  refine ⟨3456374757160635862710149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9216999352428362300560397 3456374757160635862710149)
                  ·
                    refine ⟨648070266967619224258153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456374757160635862710149 648070266967619224258153)
                    ·
                      rfl

theorem cell23_3786337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3786337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786337 prefixEnd_3786337 := by exact prefixLift 3786337
  have htrace : WordTrace (prefixWord ++ tailWord_3786337) baseStart_3786337 baseEnd_3786337 := by
    simpa [prefixWord, tailWord_3786337, baseEnd_3786337] using wordTrace_append hprefix tailTrace_3786337
  have hstable : (prefixWord ++ tailWord_3786337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786337).length < 2 ^ (prefixWord ++ tailWord_3786337).sum := by decide
  have hdescent : baseEnd_3786337 < baseStart_3786337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786344 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3786344 : Nat := 118140960795 + 3786344 * 2 ^ 59
def prefixEnd_3786344 : Nat := 4983230072969 + 3 ^ 40 * 3786344 * 2
def baseEnd_3786344 : Nat := 1944214395267439145386927

theorem tailTrace_3786344 : CollatzResearch.WordTrace tailWord_3786344 prefixEnd_3786344 1944214395267439145386927 := by
  unfold tailWord_3786344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69049655497364909458695043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92066207329819879278260057 69049655497364909458695043)
  ·
    refine ⟨103574483246047364188042565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69049655497364909458695043 103574483246047364188042565)
    ·
      refine ⟨19420215608633880785257981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103574483246047364188042565 19420215608633880785257981)
      ·
        refine ⟨7282580853237705294471743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19420215608633880785257981 7282580853237705294471743)
        ·
          refine ⟨10923871279856557941707615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282580853237705294471743 10923871279856557941707615)
          ·
            refine ⟨16385806919784836912561423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923871279856557941707615 16385806919784836912561423)
            ·
              refine ⟨24578710379677255368842135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385806919784836912561423 24578710379677255368842135)
              ·
                refine ⟨36868065569515883053263203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24578710379677255368842135 36868065569515883053263203)
                ·
                  refine ⟨55302098354273824579894805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36868065569515883053263203 55302098354273824579894805)
                  ·
                    refine ⟨2592285860356585527182569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55302098354273824579894805 2592285860356585527182569)
                    ·
                      refine ⟨1944214395267439145386927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592285860356585527182569 1944214395267439145386927)
                      ·
                        rfl

theorem cell23_3786344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3786344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786344 prefixEnd_3786344 := by exact prefixLift 3786344
  have htrace : WordTrace (prefixWord ++ tailWord_3786344) baseStart_3786344 baseEnd_3786344 := by
    simpa [prefixWord, tailWord_3786344, baseEnd_3786344] using wordTrace_append hprefix tailTrace_3786344
  have hstable : (prefixWord ++ tailWord_3786344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786344).length < 2 ^ (prefixWord ++ tailWord_3786344).sum := by decide
  have hdescent : baseEnd_3786344 < baseStart_3786344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786354 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3786354 : Nat := 118140960795 + 3786354 * 2 ^ 59
def prefixEnd_3786354 : Nat := 4983230072969 + 3 ^ 40 * 3786354 * 2
def baseEnd_3786354 : Nat := 648073176691328035420627

theorem tailTrace_3786354 : CollatzResearch.WordTrace tailWord_3786354 prefixEnd_3786354 648073176691328035420627 := by
  unfold tailWord_3786354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524918931173397656313529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92066450483129060416836077 34524918931173397656313529)
  ·
    refine ⟨25893689198380048242235147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34524918931173397656313529 25893689198380048242235147)
    ·
      refine ⟨38840533797570072363352721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893689198380048242235147 38840533797570072363352721)
      ·
        refine ⟨29130400348177554272514541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38840533797570072363352721 29130400348177554272514541)
        ·
          refine ⟨10923900130566582852192953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29130400348177554272514541 10923900130566582852192953)
          ·
            refine ⟨8192925097924937139144715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10923900130566582852192953 8192925097924937139144715)
            ·
              refine ⟨12289387646887405708717073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192925097924937139144715 12289387646887405708717073)
              ·
                refine ⟨9217040735165554281537805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12289387646887405708717073 9217040735165554281537805)
                ·
                  refine ⟨3456390275687082855576677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9217040735165554281537805 3456390275687082855576677)
                  ·
                    refine ⟨648073176691328035420627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456390275687082855576677 648073176691328035420627)
                    ·
                      rfl

theorem cell23_3786354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3786354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786354 prefixEnd_3786354 := by exact prefixLift 3786354
  have htrace : WordTrace (prefixWord ++ tailWord_3786354) baseStart_3786354 baseEnd_3786354 := by
    simpa [prefixWord, tailWord_3786354, baseEnd_3786354] using wordTrace_append hprefix tailTrace_3786354
  have hstable : (prefixWord ++ tailWord_3786354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786354).length < 2 ^ (prefixWord ++ tailWord_3786354).sum := by decide
  have hdescent : baseEnd_3786354 < baseStart_3786354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786387 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 5, 2]
def baseStart_3786387 : Nat := 118140960795 + 3786387 * 2 ^ 59
def prefixEnd_3786387 : Nat := 4983230072969 + 3 ^ 40 * 3786387 * 2
def baseEnd_3786387 : Nat := 1944236474935582477149229

theorem tailTrace_3786387 : CollatzResearch.WordTrace tailWord_3786387 prefixEnd_3786387 1944236474935582477149229 := by
  unfold tailWord_3786387
  simp only [CollatzResearch.WordTrace]
  refine ⟨138100879333574037261205415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92067252889049358174136943 138100879333574037261205415)
  ·
    refine ⟨207151319000361055891808123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138100879333574037261205415 207151319000361055891808123)
    ·
      refine ⟨310726978500541583837712185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207151319000361055891808123 310726978500541583837712185)
      ·
        refine ⟨233045233875406187878284139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310726978500541583837712185 233045233875406187878284139)
        ·
          refine ⟨349567850813109281817426209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233045233875406187878284139 349567850813109281817426209)
          ·
            refine ⟨262175888109831961363069657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349567850813109281817426209 262175888109831961363069657)
            ·
              refine ⟨196631916082373971022302243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262175888109831961363069657 196631916082373971022302243)
              ·
                refine ⟨294947874123560956533453365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196631916082373971022302243 294947874123560956533453365)
                ·
                  refine ⟨27651363199083839675011253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294947874123560956533453365 27651363199083839675011253)
                  ·
                    refine ⟨2592315299914109969532305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27651363199083839675011253 2592315299914109969532305)
                    ·
                      refine ⟨1944236474935582477149229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592315299914109969532305 1944236474935582477149229)
                      ·
                        rfl

theorem cell23_3786387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5, 2].length) (baseStart_3786387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786387 prefixEnd_3786387 := by exact prefixLift 3786387
  have htrace : WordTrace (prefixWord ++ tailWord_3786387) baseStart_3786387 baseEnd_3786387 := by
    simpa [prefixWord, tailWord_3786387, baseEnd_3786387] using wordTrace_append hprefix tailTrace_3786387
  have hstable : (prefixWord ++ tailWord_3786387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786387).length < 2 ^ (prefixWord ++ tailWord_3786387).sum := by decide
  have hdescent : baseEnd_3786387 < baseStart_3786387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786404 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_3786404 : Nat := 118140960795 + 3786404 * 2 ^ 59
def prefixEnd_3786404 : Nat := 4983230072969 + 3 ^ 40 * 3786404 * 2
def baseEnd_3786404 : Nat := 1944245204106708910636651

theorem tailTrace_3786404 : CollatzResearch.WordTrace tailWord_3786404 prefixEnd_3786404 1944245204106708910636651 := by
  unfold tailWord_3786404
  simp only [CollatzResearch.WordTrace]
  refine ⟨69050749687256224582287133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92067666249674966109716177 69050749687256224582287133)
  ·
    refine ⟨25894031132721084218357675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69050749687256224582287133 25894031132721084218357675)
    ·
      refine ⟨38841046699081626327536513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25894031132721084218357675 38841046699081626327536513)
      ·
        refine ⟨29130785024311219745652385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38841046699081626327536513 29130785024311219745652385)
        ·
          refine ⟨21848088768233414809239289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29130785024311219745652385 21848088768233414809239289)
          ·
            refine ⟨16386066576175061106929467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21848088768233414809239289 16386066576175061106929467)
            ·
              refine ⟨24579099864262591660394201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386066576175061106929467 24579099864262591660394201)
              ·
                refine ⟨18434324898196943745295651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24579099864262591660394201 18434324898196943745295651)
                ·
                  refine ⟨27651487347295415617943477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18434324898196943745295651 27651487347295415617943477)
                  ·
                    refine ⟨2592326938808945214182201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27651487347295415617943477 2592326938808945214182201)
                    ·
                      refine ⟨1944245204106708910636651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592326938808945214182201 1944245204106708910636651)
                      ·
                        rfl

theorem cell23_3786404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_3786404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786404 prefixEnd_3786404 := by exact prefixLift 3786404
  have htrace : WordTrace (prefixWord ++ tailWord_3786404) baseStart_3786404 baseEnd_3786404 := by
    simpa [prefixWord, tailWord_3786404, baseEnd_3786404] using wordTrace_append hprefix tailTrace_3786404
  have hstable : (prefixWord ++ tailWord_3786404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786404).length < 2 ^ (prefixWord ++ tailWord_3786404).sum := by decide
  have hdescent : baseEnd_3786404 < baseStart_3786404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786428 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3786428 : Nat := 118140960795 + 3786428 * 2 ^ 59
def prefixEnd_3786428 : Nat := 4983230072969 + 3 ^ 40 * 3786428 * 2
def baseEnd_3786428 : Nat := 1944257527642416816736541

theorem tailTrace_3786428 : CollatzResearch.WordTrace tailWord_3786428 prefixEnd_3786428 1944257527642416816736541 := by
  unfold tailWord_3786428
  simp only [CollatzResearch.WordTrace]
  refine ⟨69051187363212750631723969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92068249817617000842298625 69051187363212750631723969)
  ·
    refine ⟨51788390522409562973792977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69051187363212750631723969 51788390522409562973792977)
    ·
      refine ⟨38841292891807172230344733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51788390522409562973792977 38841292891807172230344733)
      ·
        refine ⟨14565484834427689586379275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38841292891807172230344733 14565484834427689586379275)
        ·
          refine ⟨21848227251641534379568913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14565484834427689586379275 21848227251641534379568913)
          ·
            refine ⟨16386170438731150784676685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21848227251641534379568913 16386170438731150784676685)
            ·
              refine ⟨6144813914524181544253757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16386170438731150784676685 6144813914524181544253757)
              ·
                refine ⟨2304305217946568079095159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6144813914524181544253757 2304305217946568079095159)
                ·
                  refine ⟨3456457826919852118642739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304305217946568079095159 3456457826919852118642739)
                  ·
                    refine ⟨5184686740379778177964109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3456457826919852118642739 5184686740379778177964109)
                    ·
                      refine ⟨1944257527642416816736541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5184686740379778177964109 1944257527642416816736541)
                      ·
                        rfl

theorem cell23_3786428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3786428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786428 prefixEnd_3786428 := by exact prefixLift 3786428
  have htrace : WordTrace (prefixWord ++ tailWord_3786428) baseStart_3786428 baseEnd_3786428 := by
    simpa [prefixWord, tailWord_3786428, baseEnd_3786428] using wordTrace_append hprefix tailTrace_3786428
  have hstable : (prefixWord ++ tailWord_3786428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786428).length < 2 ^ (prefixWord ++ tailWord_3786428).sum := by decide
  have hdescent : baseEnd_3786428 < baseStart_3786428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786445 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3786445 : Nat := 118140960795 + 3786445 * 2 ^ 59
def prefixEnd_3786445 : Nat := 4983230072969 + 3 ^ 40 * 3786445 * 2
def baseEnd_3786445 : Nat := 1944266256813543250223963

theorem tailTrace_3786445 : CollatzResearch.WordTrace tailWord_3786445 prefixEnd_3786445 1944266256813543250223963 := by
  unfold tailWord_3786445
  simp only [CollatzResearch.WordTrace]
  refine ⟨138102994767363913166816789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92068663178242608777877859 138102994767363913166816789)
  ·
    refine ⟨6473577879720183429694537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138102994767363913166816789 6473577879720183429694537)
    ·
      refine ⟨4855183409790137572270903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6473577879720183429694537 4855183409790137572270903)
      ·
        refine ⟨7282775114685206358406355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855183409790137572270903 7282775114685206358406355)
        ·
          refine ⟨10924162672027809537609533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282775114685206358406355 10924162672027809537609533)
          ·
            refine ⟨4096561002010428576603575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10924162672027809537609533 4096561002010428576603575)
            ·
              refine ⟨6144841503015642864905363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096561002010428576603575 6144841503015642864905363)
              ·
                refine ⟨9217262254523464297358045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144841503015642864905363 9217262254523464297358045)
                ·
                  refine ⟨3456473345446299111509267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9217262254523464297358045 3456473345446299111509267)
                  ·
                    refine ⟨5184710018169448667263901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3456473345446299111509267 5184710018169448667263901)
                    ·
                      refine ⟨1944266256813543250223963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5184710018169448667263901 1944266256813543250223963)
                      ·
                        rfl

theorem cell23_3786445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3786445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786445 prefixEnd_3786445 := by exact prefixLift 3786445
  have htrace : WordTrace (prefixWord ++ tailWord_3786445) baseStart_3786445 baseEnd_3786445 := by
    simpa [prefixWord, tailWord_3786445, baseEnd_3786445] using wordTrace_append hprefix tailTrace_3786445
  have hstable : (prefixWord ++ tailWord_3786445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786445).length < 2 ^ (prefixWord ++ tailWord_3786445).sum := by decide
  have hdescent : baseEnd_3786445 < baseStart_3786445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786457 : List Nat := [1, 2, 1, 2, 3, 4, 2, 8]
def baseStart_3786457 : Nat := 118140960795 + 3786457 * 2 ^ 59
def prefixEnd_3786457 : Nat := 4983230072969 + 3 ^ 40 * 3786457 * 2
def baseEnd_3786457 : Nat := 72010089577088785306441

theorem tailTrace_3786457 : CollatzResearch.WordTrace tailWord_3786457 prefixEnd_3786457 72010089577088785306441 := by
  unfold tailWord_3786457
  simp only [CollatzResearch.WordTrace]
  refine ⟨138103432443320439216253625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92068954962213626144169083 138103432443320439216253625)
  ·
    refine ⟨103577574332490329412190219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138103432443320439216253625 103577574332490329412190219)
    ·
      refine ⟨155366361498735494118285329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103577574332490329412190219 155366361498735494118285329)
      ·
        refine ⟨116524771124051620588713997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155366361498735494118285329 116524771124051620588713997)
        ·
          refine ⟨43696789171519357720767749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116524771124051620588713997 43696789171519357720767749)
          ·
            refine ⟨8193147969659879572643953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43696789171519357720767749 8193147969659879572643953)
            ·
              refine ⟨6144860977244909679482965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193147969659879572643953 6144860977244909679482965)
              ·
                refine ⟨72010089577088785306441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6144860977244909679482965 72010089577088785306441)
                ·
                  rfl

theorem cell23_3786457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 8].length) (baseStart_3786457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786457 prefixEnd_3786457 := by exact prefixLift 3786457
  have htrace : WordTrace (prefixWord ++ tailWord_3786457) baseStart_3786457 baseEnd_3786457 := by
    simpa [prefixWord, tailWord_3786457, baseEnd_3786457] using wordTrace_append hprefix tailTrace_3786457
  have hstable : (prefixWord ++ tailWord_3786457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786457).length < 2 ^ (prefixWord ++ tailWord_3786457).sum := by decide
  have hdescent : baseEnd_3786457 < baseStart_3786457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786497 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3786497 : Nat := 118140960795 + 3786497 * 2 ^ 59
def prefixEnd_3786497 : Nat := 4983230072969 + 3 ^ 40 * 3786497 * 2
def baseEnd_3786497 : Nat := 1944292957807577046773723

theorem tailTrace_3786497 : CollatzResearch.WordTrace tailWord_3786497 prefixEnd_3786497 1944292957807577046773723 := by
  unfold tailWord_3786497
  simp only [CollatzResearch.WordTrace]
  refine ⟨138104891363175526047709745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92069927575450350698473163 138104891363175526047709745)
  ·
    refine ⟨103578668522381644535782309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138104891363175526047709745 103578668522381644535782309)
    ·
      refine ⟨19421000347946558350459183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103578668522381644535782309 19421000347946558350459183)
      ·
        refine ⟨29131500521919837525688775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19421000347946558350459183 29131500521919837525688775)
        ·
          refine ⟨43697250782879756288533163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29131500521919837525688775 43697250782879756288533163)
          ·
            refine ⟨65545876174319634432799745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43697250782879756288533163 65545876174319634432799745)
            ·
              refine ⟨49159407130739725824599809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65545876174319634432799745 49159407130739725824599809)
              ·
                refine ⟨36869555348054794368449857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49159407130739725824599809 36869555348054794368449857)
                ·
                  refine ⟨27652166511041095776337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36869555348054794368449857 27652166511041095776337393)
                  ·
                    refine ⟨20739124883280821832253045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27652166511041095776337393 20739124883280821832253045)
                    ·
                      refine ⟨1944292957807577046773723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20739124883280821832253045 1944292957807577046773723)
                      ·
                        rfl

theorem cell23_3786497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3786497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786497 prefixEnd_3786497 := by exact prefixLift 3786497
  have htrace : WordTrace (prefixWord ++ tailWord_3786497) baseStart_3786497 baseEnd_3786497 := by
    simpa [prefixWord, tailWord_3786497, baseEnd_3786497] using wordTrace_append hprefix tailTrace_3786497
  have hstable : (prefixWord ++ tailWord_3786497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786497).length < 2 ^ (prefixWord ++ tailWord_3786497).sum := by decide
  have hdescent : baseEnd_3786497 < baseStart_3786497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786507 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_3786507 : Nat := 118140960795 + 3786507 * 2 ^ 59
def prefixEnd_3786507 : Nat := 4983230072969 + 3 ^ 40 * 3786507 * 2
def baseEnd_3786507 : Nat := 1944298092614122007648677

theorem tailTrace_3786507 : CollatzResearch.WordTrace tailWord_3786507 prefixEnd_3786507 1944298092614122007648677 := by
  unfold tailWord_3786507
  simp only [CollatzResearch.WordTrace]
  refine ⟨138105256093139297755573775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92070170728759531837049183 138105256093139297755573775)
  ·
    refine ⟨207157884139708946633360663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138105256093139297755573775 207157884139708946633360663)
    ·
      refine ⟨310736826209563419950040995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207157884139708946633360663 310736826209563419950040995)
      ·
        refine ⟨466105239314345129925061493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310736826209563419950040995 466105239314345129925061493)
        ·
          refine ⟨43697366185719855930474515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 466105239314345129925061493 43697366185719855930474515)
          ·
            refine ⟨65546049278579783895711773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43697366185719855930474515 65546049278579783895711773)
            ·
              refine ⟨24579768479467418960891915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65546049278579783895711773 24579768479467418960891915)
              ·
                refine ⟨36869652719201128441337873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24579768479467418960891915 36869652719201128441337873)
                ·
                  refine ⟨27652239539400846331003405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36869652719201128441337873 27652239539400846331003405)
                  ·
                    refine ⟨10369589827275317374126277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27652239539400846331003405 10369589827275317374126277)
                    ·
                      refine ⟨1944298092614122007648677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10369589827275317374126277 1944298092614122007648677)
                      ·
                        rfl

theorem cell23_3786507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_3786507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786507 prefixEnd_3786507 := by exact prefixLift 3786507
  have htrace : WordTrace (prefixWord ++ tailWord_3786507) baseStart_3786507 baseEnd_3786507 := by
    simpa [prefixWord, tailWord_3786507, baseEnd_3786507] using wordTrace_append hprefix tailTrace_3786507
  have hstable : (prefixWord ++ tailWord_3786507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786507).length < 2 ^ (prefixWord ++ tailWord_3786507).sum := by decide
  have hdescent : baseEnd_3786507 < baseStart_3786507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786517 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3786517 : Nat := 118140960795 + 3786517 * 2 ^ 59
def prefixEnd_3786517 : Nat := 4983230072969 + 3 ^ 40 * 3786517 * 2
def baseEnd_3786517 : Nat := 648101075806888989507877

theorem tailTrace_3786517 : CollatzResearch.WordTrace tailWord_3786517 prefixEnd_3786517 648101075806888989507877 := by
  unfold tailWord_3786517
  simp only [CollatzResearch.WordTrace]
  refine ⟨138105620823103069463437805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92070413882068712975625203 138105620823103069463437805)
  ·
    refine ⟨51789607808663651048789177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138105620823103069463437805 51789607808663651048789177)
    ·
      refine ⟨38842205856497738286591883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51789607808663651048789177 38842205856497738286591883)
      ·
        refine ⟨58263308784746607429887825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38842205856497738286591883 58263308784746607429887825)
        ·
          refine ⟨43697481588559955572415869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58263308784746607429887825 43697481588559955572415869)
          ·
            refine ⟨16386555595709983339655951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43697481588559955572415869 16386555595709983339655951)
            ·
              refine ⟨24579833393564975009483927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386555595709983339655951 24579833393564975009483927)
              ·
                refine ⟨36869750090347462514225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24579833393564975009483927 36869750090347462514225891)
                ·
                  refine ⟨55304625135521193771338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36869750090347462514225891 55304625135521193771338837)
                  ·
                    refine ⟨648101075806888989507877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55304625135521193771338837 648101075806888989507877)
                    ·
                      rfl

theorem cell23_3786517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3786517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786517 prefixEnd_3786517 := by exact prefixLift 3786517
  have htrace : WordTrace (prefixWord ++ tailWord_3786517) baseStart_3786517 baseEnd_3786517 := by
    simpa [prefixWord, tailWord_3786517, baseEnd_3786517] using wordTrace_append hprefix tailTrace_3786517
  have hstable : (prefixWord ++ tailWord_3786517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786517).length < 2 ^ (prefixWord ++ tailWord_3786517).sum := by decide
  have hdescent : baseEnd_3786517 < baseStart_3786517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786537 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_3786537 : Nat := 118140960795 + 3786537 * 2 ^ 59
def prefixEnd_3786537 : Nat := 4983230072969 + 3 ^ 40 * 3786537 * 2
def baseEnd_3786537 : Nat := 1944313497033756890273539

theorem tailTrace_3786537 : CollatzResearch.WordTrace tailWord_3786537 prefixEnd_3786537 1944313497033756890273539 := by
  unfold tailWord_3786537
  simp only [CollatzResearch.WordTrace]
  refine ⟨138106350283030612879165865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92070900188687075252777243 138106350283030612879165865)
  ·
    refine ⟨103579762712272959659374399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138106350283030612879165865 103579762712272959659374399)
    ·
      refine ⟨155369644068409439489061599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103579762712272959659374399 155369644068409439489061599)
      ·
        refine ⟨233054466102614159233592399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155369644068409439489061599 233054466102614159233592399)
        ·
          refine ⟨349581699153921238850388599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233054466102614159233592399 349581699153921238850388599)
          ·
            refine ⟨524372548730881858275582899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349581699153921238850388599 524372548730881858275582899)
            ·
              refine ⟨786558823096322787413374349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524372548730881858275582899 786558823096322787413374349)
              ·
                refine ⟨294959558661121045280015381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786558823096322787413374349 294959558661121045280015381)
                ·
                  refine ⟨13826229312240048997500721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294959558661121045280015381 13826229312240048997500721)
                  ·
                    refine ⟨10369671984180036748125541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13826229312240048997500721 10369671984180036748125541)
                    ·
                      refine ⟨1944313497033756890273539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10369671984180036748125541 1944313497033756890273539)
                      ·
                        rfl

theorem cell23_3786537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_3786537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786537 prefixEnd_3786537 := by exact prefixLift 3786537
  have htrace : WordTrace (prefixWord ++ tailWord_3786537) baseStart_3786537 baseEnd_3786537 := by
    simpa [prefixWord, tailWord_3786537, baseEnd_3786537] using wordTrace_append hprefix tailTrace_3786537
  have hstable : (prefixWord ++ tailWord_3786537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786537).length < 2 ^ (prefixWord ++ tailWord_3786537).sum := by decide
  have hdescent : baseEnd_3786537 < baseStart_3786537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786545 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_3786545 : Nat := 118140960795 + 3786545 * 2 ^ 59
def prefixEnd_3786545 : Nat := 4983230072969 + 3 ^ 40 * 3786545 * 2
def baseEnd_3786545 : Nat := 1944317604878992858973503

theorem tailTrace_3786545 : CollatzResearch.WordTrace tailWord_3786545 prefixEnd_3786545 1944317604878992858973503 := by
  unfold tailWord_3786545
  simp only [CollatzResearch.WordTrace]
  refine ⟨138106642067001630245457089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92071094711334420163638059 138106642067001630245457089)
  ·
    refine ⟨103579981550251222684092817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138106642067001630245457089 103579981550251222684092817)
    ·
      refine ⟨77684986162688417013069613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103579981550251222684092817 77684986162688417013069613)
      ·
        refine ⟨29131869811008156379901105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77684986162688417013069613 29131869811008156379901105)
        ·
          refine ⟨21848902358256117284925829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29131869811008156379901105 21848902358256117284925829)
          ·
            refine ⟨4096669192173021990923593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21848902358256117284925829 4096669192173021990923593)
            ·
              refine ⟨3072501894129766493192695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096669192173021990923593 3072501894129766493192695)
              ·
                refine ⟨4608752841194649739789043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072501894129766493192695 4608752841194649739789043)
                ·
                  refine ⟨6913129261791974609683565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608752841194649739789043 6913129261791974609683565)
                  ·
                    refine ⟨2592423473171990478631337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6913129261791974609683565 2592423473171990478631337)
                    ·
                      refine ⟨1944317604878992858973503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592423473171990478631337 1944317604878992858973503)
                      ·
                        rfl

theorem cell23_3786545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_3786545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786545 prefixEnd_3786545 := by exact prefixLift 3786545
  have htrace : WordTrace (prefixWord ++ tailWord_3786545) baseStart_3786545 baseEnd_3786545 := by
    simpa [prefixWord, tailWord_3786545, baseEnd_3786545] using wordTrace_append hprefix tailTrace_3786545
  have hstable : (prefixWord ++ tailWord_3786545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786545).length < 2 ^ (prefixWord ++ tailWord_3786545).sum := by decide
  have hdescent : baseEnd_3786545 < baseStart_3786545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786554 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3786554 : Nat := 118140960795 + 3786554 * 2 ^ 59
def prefixEnd_3786554 : Nat := 4983230072969 + 3 ^ 40 * 3786554 * 2
def baseEnd_3786554 : Nat := 1944322226204883323760961

theorem tailTrace_3786554 : CollatzResearch.WordTrace tailWord_3786554 prefixEnd_3786554 1944322226204883323760961 := by
  unfold tailWord_3786554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34526742580992256195633679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92071313549312683188356477 34526742580992256195633679)
  ·
    refine ⟨51790113871488384293450519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34526742580992256195633679 51790113871488384293450519)
    ·
      refine ⟨77685170807232576440175779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51790113871488384293450519 77685170807232576440175779)
      ·
        refine ⟨116527756210848864660263669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77685170807232576440175779 116527756210848864660263669)
        ·
          refine ⟨10924477144767081061899719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116527756210848864660263669 10924477144767081061899719)
          ·
            refine ⟨16386715717150621592849579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924477144767081061899719 16386715717150621592849579)
            ·
              refine ⟨24580073575725932389274369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386715717150621592849579 24580073575725932389274369)
              ·
                refine ⟨18435055181794449291955777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24580073575725932389274369 18435055181794449291955777)
                ·
                  refine ⟨13826291386345836968966833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18435055181794449291955777 13826291386345836968966833)
                  ·
                    refine ⟨10369718539759377726725125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13826291386345836968966833 10369718539759377726725125)
                    ·
                      refine ⟨1944322226204883323760961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10369718539759377726725125 1944322226204883323760961)
                      ·
                        rfl

theorem cell23_3786554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3786554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786554 prefixEnd_3786554 := by exact prefixLift 3786554
  have htrace : WordTrace (prefixWord ++ tailWord_3786554) baseStart_3786554 baseEnd_3786554 := by
    simpa [prefixWord, tailWord_3786554, baseEnd_3786554] using wordTrace_append hprefix tailTrace_3786554
  have hstable : (prefixWord ++ tailWord_3786554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786554).length < 2 ^ (prefixWord ++ tailWord_3786554).sum := by decide
  have hdescent : baseEnd_3786554 < baseStart_3786554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786708 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3786708 : Nat := 118140960795 + 3786708 * 2 ^ 59
def prefixEnd_3786708 : Nat := 4983230072969 + 3 ^ 40 * 3786708 * 2
def baseEnd_3786708 : Nat := 1944401302225675721235253

theorem tailTrace_3786708 : CollatzResearch.WordTrace tailWord_3786708 prefixEnd_3786708 1944401302225675721235253 := by
  unfold tailWord_3786708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69056293582705554541820389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92075058110274072722427185 69056293582705554541820389)
  ·
    refine ⟨12948055046757291476591323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69056293582705554541820389 12948055046757291476591323)
    ·
      refine ⟨19422082570135937214886985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12948055046757291476591323 19422082570135937214886985)
      ·
        refine ⟨14566561927601952911165239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19422082570135937214886985 14566561927601952911165239)
        ·
          refine ⟨21849842891402929366747859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566561927601952911165239 21849842891402929366747859)
          ·
            refine ⟨32774764337104394050121789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21849842891402929366747859 32774764337104394050121789)
            ·
              refine ⟨12290536626414147768795671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32774764337104394050121789 12290536626414147768795671)
              ·
                refine ⟨18435804939621221653193507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12290536626414147768795671 18435804939621221653193507)
                ·
                  refine ⟨27653707409431832479790261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18435804939621221653193507 27653707409431832479790261)
                  ·
                    refine ⟨2592535069634234294980337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27653707409431832479790261 2592535069634234294980337)
                    ·
                      refine ⟨1944401302225675721235253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592535069634234294980337 1944401302225675721235253)
                      ·
                        rfl

theorem cell23_3786708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3786708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786708 prefixEnd_3786708 := by exact prefixLift 3786708
  have htrace : WordTrace (prefixWord ++ tailWord_3786708) baseStart_3786708 baseEnd_3786708 := by
    simpa [prefixWord, tailWord_3786708, baseEnd_3786708] using wordTrace_append hprefix tailTrace_3786708
  have hstable : (prefixWord ++ tailWord_3786708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786708).length < 2 ^ (prefixWord ++ tailWord_3786708).sum := by decide
  have hdescent : baseEnd_3786708 < baseStart_3786708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786722 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_3786722 : Nat := 118140960795 + 3786722 * 2 ^ 59
def prefixEnd_3786722 : Nat := 4983230072969 + 3 ^ 40 * 3786722 * 2
def baseEnd_3786722 : Nat := 216045387883870962940021

theorem tailTrace_3786722 : CollatzResearch.WordTrace tailWord_3786722 prefixEnd_3786722 216045387883870962940021 := by
  unfold tailWord_3786722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34528274446840097368662605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92075398524906926316433613 34528274446840097368662605)
  ·
    refine ⟨12948102917565036513248477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34528274446840097368662605 12948102917565036513248477)
    ·
      refine ⟨4855538594086888692468179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12948102917565036513248477 4855538594086888692468179)
      ·
        refine ⟨7283307891130333038702269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855538594086888692468179 7283307891130333038702269)
        ·
          refine ⟨2731240459173874889513351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7283307891130333038702269 2731240459173874889513351)
          ·
            refine ⟨4096860688760812334270027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731240459173874889513351 4096860688760812334270027)
            ·
              refine ⟨6145291033141218501405041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096860688760812334270027 6145291033141218501405041)
              ·
                refine ⟨4608968274855913876053781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145291033141218501405041 4608968274855913876053781)
                ·
                  refine ⟨216045387883870962940021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4608968274855913876053781 216045387883870962940021)
                  ·
                    rfl

theorem cell23_3786722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_3786722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786722 prefixEnd_3786722 := by exact prefixLift 3786722
  have htrace : WordTrace (prefixWord ++ tailWord_3786722) baseStart_3786722 baseEnd_3786722 := by
    simpa [prefixWord, tailWord_3786722, baseEnd_3786722] using wordTrace_append hprefix tailTrace_3786722
  have hstable : (prefixWord ++ tailWord_3786722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786722).length < 2 ^ (prefixWord ++ tailWord_3786722).sum := by decide
  have hdescent : baseEnd_3786722 < baseStart_3786722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786771 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3]
def baseStart_3786771 : Nat := 118140960795 + 3786771 * 2 ^ 59
def prefixEnd_3786771 : Nat := 4983230072969 + 3 ^ 40 * 3786771 * 2
def baseEnd_3786771 : Nat := 1944433651506908974747463

theorem tailTrace_3786771 : CollatzResearch.WordTrace tailWord_3786771 prefixEnd_3786771 1944433651506908974747463 := by
  unfold tailWord_3786771
  simp only [CollatzResearch.WordTrace]
  refine ⟨138114884964182870843184167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92076589976121913895456111 138114884964182870843184167)
  ·
    refine ⟨207172327446274306264776251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138114884964182870843184167 207172327446274306264776251)
    ·
      refine ⟨310758491169411459397164377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207172327446274306264776251 310758491169411459397164377)
      ·
        refine ⟨233068868377058594547873283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310758491169411459397164377 233068868377058594547873283)
        ·
          refine ⟨349603302565587891821809925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233068868377058594547873283 349603302565587891821809925)
          ·
            refine ⟨65550619231047729716589361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349603302565587891821809925 65550619231047729716589361)
            ·
              refine ⟨49162964423285797287442021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65550619231047729716589361 49162964423285797287442021)
              ·
                refine ⟨9218055829366086991395379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49162964423285797287442021 9218055829366086991395379)
                ·
                  refine ⟨13827083744049130487093069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9218055829366086991395379 13827083744049130487093069)
                  ·
                    refine ⟨5185156404018423932659901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13827083744049130487093069 5185156404018423932659901)
                    ·
                      refine ⟨1944433651506908974747463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185156404018423932659901 1944433651506908974747463)
                      ·
                        rfl

theorem cell23_3786771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_3786771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786771 prefixEnd_3786771 := by exact prefixLift 3786771
  have htrace : WordTrace (prefixWord ++ tailWord_3786771) baseStart_3786771 baseEnd_3786771 := by
    simpa [prefixWord, tailWord_3786771, baseEnd_3786771] using wordTrace_append hprefix tailTrace_3786771
  have hstable : (prefixWord ++ tailWord_3786771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786771).length < 2 ^ (prefixWord ++ tailWord_3786771).sum := by decide
  have hdescent : baseEnd_3786771 < baseStart_3786771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786789 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_3786789 : Nat := 118140960795 + 3786789 * 2 ^ 59
def prefixEnd_3786789 : Nat := 4983230072969 + 3 ^ 40 * 3786789 * 2
def baseEnd_3786789 : Nat := 1944442894158689904322381

theorem tailTrace_3786789 : CollatzResearch.WordTrace tailWord_3786789 prefixEnd_3786789 1944442894158689904322381 := by
  unfold tailWord_3786789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138115541478117659917339421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92077027652078439944892947 138115541478117659917339421)
  ·
    refine ⟨51793328054294122469002283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138115541478117659917339421 51793328054294122469002283)
    ·
      refine ⟨77689992081441183703503425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51793328054294122469002283 77689992081441183703503425)
      ·
        refine ⟨58267494061080887777627569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77689992081441183703503425 58267494061080887777627569)
        ·
          refine ⟨43700620545810665833220677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58267494061080887777627569 43700620545810665833220677)
          ·
            refine ⟨8193866352339499843728877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43700620545810665833220677 8193866352339499843728877)
            ·
              refine ⟨3072699882127312441398329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8193866352339499843728877 3072699882127312441398329)
              ·
                refine ⟨2304524911595484331048747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072699882127312441398329 2304524911595484331048747)
                ·
                  refine ⟨3456787367393226496573121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304524911595484331048747 3456787367393226496573121)
                  ·
                    refine ⟨2592590525544919872429841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3456787367393226496573121 2592590525544919872429841)
                    ·
                      refine ⟨1944442894158689904322381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592590525544919872429841 1944442894158689904322381)
                      ·
                        rfl

theorem cell23_3786789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_3786789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786789 prefixEnd_3786789 := by exact prefixLift 3786789
  have htrace : WordTrace (prefixWord ++ tailWord_3786789) baseStart_3786789 baseEnd_3786789 := by
    simpa [prefixWord, tailWord_3786789, baseEnd_3786789] using wordTrace_append hprefix tailTrace_3786789
  have hstable : (prefixWord ++ tailWord_3786789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786789).length < 2 ^ (prefixWord ++ tailWord_3786789).sum := by decide
  have hdescent : baseEnd_3786789 < baseStart_3786789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786815 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 1, 3, 2]
def baseStart_3786815 : Nat := 118140960795 + 3786815 * 2 ^ 59
def prefixEnd_3786815 : Nat := 4983230072969 + 3 ^ 40 * 3786815 * 2
def baseEnd_3786815 : Nat := 1944456244655706802597261

theorem tailTrace_3786815 : CollatzResearch.WordTrace tailWord_3786815 prefixEnd_3786815 1944456244655706802597261 := by
  unfold tailWord_3786815
  simp only [CollatzResearch.WordTrace]
  refine ⟨138116489776023466357785899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92077659850682310905190599 138116489776023466357785899)
  ·
    refine ⟨207174734664035199536678849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138116489776023466357785899 207174734664035199536678849)
    ·
      refine ⟨155381050998026399652509137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207174734664035199536678849 155381050998026399652509137)
      ·
        refine ⟨116535788248519799739381853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155381050998026399652509137 116535788248519799739381853)
        ·
          refine ⟨43700920593194924902268195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116535788248519799739381853 43700920593194924902268195)
          ·
            refine ⟨65551380889792387353402293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43700920593194924902268195 65551380889792387353402293)
            ·
              refine ⟨6145441958418036314381465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65551380889792387353402293 6145441958418036314381465)
              ·
                refine ⟨4609081468813527235786099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145441958418036314381465 4609081468813527235786099)
                ·
                  refine ⟨6913622203220290853679149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609081468813527235786099 6913622203220290853679149)
                  ·
                    refine ⟨2592608326207609070129681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6913622203220290853679149 2592608326207609070129681)
                    ·
                      refine ⟨1944456244655706802597261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592608326207609070129681 1944456244655706802597261)
                      ·
                        rfl

theorem cell23_3786815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_3786815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786815 prefixEnd_3786815 := by exact prefixLift 3786815
  have htrace : WordTrace (prefixWord ++ tailWord_3786815) baseStart_3786815 baseEnd_3786815 := by
    simpa [prefixWord, tailWord_3786815, baseEnd_3786815] using wordTrace_append hprefix tailTrace_3786815
  have hstable : (prefixWord ++ tailWord_3786815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786815).length < 2 ^ (prefixWord ++ tailWord_3786815).sum := by decide
  have hdescent : baseEnd_3786815 < baseStart_3786815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786828 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3786828 : Nat := 118140960795 + 3786828 * 2 ^ 59
def prefixEnd_3786828 : Nat := 4983230072969 + 3 ^ 40 * 3786828 * 2
def baseEnd_3786828 : Nat := 1944462919904215251734701

theorem tailTrace_3786828 : CollatzResearch.WordTrace tailWord_3786828 prefixEnd_3786828 1944462919904215251734701 := by
  unfold tailWord_3786828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69058481962488184789004569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92077975949984246385339425 69058481962488184789004569)
  ·
    refine ⟨51793861471866138591753427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69058481962488184789004569 51793861471866138591753427)
    ·
      refine ⟨77690792207799207887630141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51793861471866138591753427 77690792207799207887630141)
      ·
        refine ⟨29134047077924702957861303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77690792207799207887630141 29134047077924702957861303)
        ·
          refine ⟨43701070616887054436791955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29134047077924702957861303 43701070616887054436791955)
          ·
            refine ⟨65551605925330581655187933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43701070616887054436791955 65551605925330581655187933)
            ·
              refine ⟨24581852221998968120695475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65551605925330581655187933 24581852221998968120695475)
              ·
                refine ⟨36872778332998452181043213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24581852221998968120695475 36872778332998452181043213)
                ·
                  refine ⟨13827291874874419567891205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36872778332998452181043213 13827291874874419567891205)
                  ·
                    refine ⟨2592617226538953668979601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13827291874874419567891205 2592617226538953668979601)
                    ·
                      refine ⟨1944462919904215251734701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592617226538953668979601 1944462919904215251734701)
                      ·
                        rfl

theorem cell23_3786828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3786828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786828 prefixEnd_3786828 := by exact prefixLift 3786828
  have htrace : WordTrace (prefixWord ++ tailWord_3786828) baseStart_3786828 baseEnd_3786828 := by
    simpa [prefixWord, tailWord_3786828, baseEnd_3786828] using wordTrace_append hprefix tailTrace_3786828
  have hstable : (prefixWord ++ tailWord_3786828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786828).length < 2 ^ (prefixWord ++ tailWord_3786828).sum := by decide
  have hdescent : baseEnd_3786828 < baseStart_3786828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786841 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_3786841 : Nat := 118140960795 + 3786841 * 2 ^ 59
def prefixEnd_3786841 : Nat := 4983230072969 + 3 ^ 40 * 3786841 * 2
def baseEnd_3786841 : Nat := 1944469595152723700872141

theorem tailTrace_3786841 : CollatzResearch.WordTrace tailWord_3786841 prefixEnd_3786841 1944469595152723700872141 := by
  unfold tailWord_3786841
  simp only [CollatzResearch.WordTrace]
  refine ⟨138117438073929272798232377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92078292049286181865488251 138117438073929272798232377)
  ·
    refine ⟨103588078555446954598674283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138117438073929272798232377 103588078555446954598674283)
    ·
      refine ⟨155382117833170431898011425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103588078555446954598674283 155382117833170431898011425)
      ·
        refine ⟨116536588374877823923508569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155382117833170431898011425 116536588374877823923508569)
        ·
          refine ⟨87402441281158367942631427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116536588374877823923508569 87402441281158367942631427)
          ·
            refine ⟨131103661921737551913947141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87402441281158367942631427 131103661921737551913947141)
            ·
              refine ⟨24581936610325790983865089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131103661921737551913947141 24581936610325790983865089)
              ·
                refine ⟨18436452457744343237898817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24581936610325790983865089 18436452457744343237898817)
                ·
                  refine ⟨13827339343308257428424113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18436452457744343237898817 13827339343308257428424113)
                  ·
                    refine ⟨10370504507481193071318085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13827339343308257428424113 10370504507481193071318085)
                    ·
                      refine ⟨1944469595152723700872141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10370504507481193071318085 1944469595152723700872141)
                      ·
                        rfl

theorem cell23_3786841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_3786841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786841 prefixEnd_3786841 := by exact prefixLift 3786841
  have htrace : WordTrace (prefixWord ++ tailWord_3786841) baseStart_3786841 baseEnd_3786841 := by
    simpa [prefixWord, tailWord_3786841, baseEnd_3786841] using wordTrace_append hprefix tailTrace_3786841
  have hstable : (prefixWord ++ tailWord_3786841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786841).length < 2 ^ (prefixWord ++ tailWord_3786841).sum := by decide
  have hdescent : baseEnd_3786841 < baseStart_3786841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786862 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3786862 : Nat := 118140960795 + 3786862 * 2 ^ 59
def prefixEnd_3786862 : Nat := 4983230072969 + 3 ^ 40 * 3786862 * 2
def baseEnd_3786862 : Nat := 1944480378246468118709545

theorem tailTrace_3786862 : CollatzResearch.WordTrace tailWord_3786862 prefixEnd_3786862 1944480378246468118709545 := by
  unfold tailWord_3786862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264775500856649173093355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92078802671235462256497893 17264775500856649173093355)
  ·
    refine ⟨25897163251284973759640033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264775500856649173093355 25897163251284973759640033)
    ·
      refine ⟨19422872438463730319730025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25897163251284973759640033 19422872438463730319730025)
      ·
        refine ⟨14567154328847797739797519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19422872438463730319730025 14567154328847797739797519)
        ·
          refine ⟨21850731493271696609696279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14567154328847797739797519 21850731493271696609696279)
          ·
            refine ⟨32776097239907544914544419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850731493271696609696279 32776097239907544914544419)
            ·
              refine ⟨49164145859861317371816629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32776097239907544914544419 49164145859861317371816629)
              ·
                refine ⟨4609138674361998503607809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49164145859861317371816629 4609138674361998503607809)
                ·
                  refine ⟨3456854005771498877705857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609138674361998503607809 3456854005771498877705857)
                  ·
                    refine ⟨2592640504328624158279393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3456854005771498877705857 2592640504328624158279393)
                    ·
                      refine ⟨1944480378246468118709545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592640504328624158279393 1944480378246468118709545)
                      ·
                        rfl

theorem cell23_3786862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3786862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786862 prefixEnd_3786862 := by exact prefixLift 3786862
  have htrace : WordTrace (prefixWord ++ tailWord_3786862) baseStart_3786862 baseEnd_3786862 := by
    simpa [prefixWord, tailWord_3786862, baseEnd_3786862] using wordTrace_append hprefix tailTrace_3786862
  have hstable : (prefixWord ++ tailWord_3786862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786862).length < 2 ^ (prefixWord ++ tailWord_3786862).sum := by decide
  have hdescent : baseEnd_3786862 < baseStart_3786862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786885 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 5]
def baseStart_3786885 : Nat := 118140960795 + 3786885 * 2 ^ 59
def prefixEnd_3786885 : Nat := 4983230072969 + 3 ^ 40 * 3786885 * 2
def baseEnd_3786885 : Nat := 216054687589057947635771

theorem tailTrace_3786885 : CollatzResearch.WordTrace tailWord_3786885 prefixEnd_3786885 216054687589057947635771 := by
  unfold tailWord_3786885
  simp only [CollatzResearch.WordTrace]
  refine ⟨138119042885769868312834109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92079361923846578875222739 138119042885769868312834109)
  ·
    refine ⟨51794641082163700617312791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138119042885769868312834109 51794641082163700617312791)
    ·
      refine ⟨77691961623245550925969187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51794641082163700617312791 77691961623245550925969187)
      ·
        refine ⟨116537942434868326388953781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77691961623245550925969187 116537942434868326388953781)
        ·
          refine ⟨10925432103268905598964417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116537942434868326388953781 10925432103268905598964417)
          ·
            refine ⟨8194074077451679199223313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925432103268905598964417 8194074077451679199223313)
            ·
              refine ⟨6145555558088759399417485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194074077451679199223313 6145555558088759399417485)
              ·
                refine ⟨2304583334283284774781557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6145555558088759399417485 2304583334283284774781557)
                ·
                  refine ⟨216054687589057947635771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304583334283284774781557 216054687589057947635771)
                  ·
                    rfl

theorem cell23_3786885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_3786885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786885 prefixEnd_3786885 := by exact prefixLift 3786885
  have htrace : WordTrace (prefixWord ++ tailWord_3786885) baseStart_3786885 baseEnd_3786885 := by
    simpa [prefixWord, tailWord_3786885, baseEnd_3786885] using wordTrace_append hprefix tailTrace_3786885
  have hstable : (prefixWord ++ tailWord_3786885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786885).length < 2 ^ (prefixWord ++ tailWord_3786885).sum := by decide
  have hdescent : baseEnd_3786885 < baseStart_3786885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786898 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3786898 : Nat := 118140960795 + 3786898 * 2 ^ 59
def prefixEnd_3786898 : Nat := 4983230072969 + 3 ^ 40 * 3786898 * 2
def baseEnd_3786898 : Nat := 648166287850009992619793

theorem tailTrace_3786898 : CollatzResearch.WordTrace tailWord_3786898 prefixEnd_3786898 648166287850009992619793 := by
  unfold tailWord_3786898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34529879258680692883264337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92079678023148514355371565 34529879258680692883264337)
  ·
    refine ⟨25897409444010519662448253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34529879258680692883264337 25897409444010519662448253)
    ·
      refine ⟨9711528541503944873418095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25897409444010519662448253 9711528541503944873418095)
      ·
        refine ⟨14567292812255917310127143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9711528541503944873418095 14567292812255917310127143)
        ·
          refine ⟨21850939218383875965190715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14567292812255917310127143 21850939218383875965190715)
          ·
            refine ⟨32776408827575813947786073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850939218383875965190715 32776408827575813947786073)
            ·
              refine ⟨24582306620681860460839555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32776408827575813947786073 24582306620681860460839555)
              ·
                refine ⟨36873459931022790691259333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24582306620681860460839555 36873459931022790691259333)
                ·
                  refine ⟨6913773737066773254611125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36873459931022790691259333 6913773737066773254611125)
                  ·
                    refine ⟨648166287850009992619793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6913773737066773254611125 648166287850009992619793)
                    ·
                      rfl

theorem cell23_3786898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3786898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786898 prefixEnd_3786898 := by exact prefixLift 3786898
  have htrace : WordTrace (prefixWord ++ tailWord_3786898) baseStart_3786898 baseEnd_3786898 := by
    simpa [prefixWord, tailWord_3786898, baseEnd_3786898] using wordTrace_append hprefix tailTrace_3786898
  have hstable : (prefixWord ++ tailWord_3786898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786898).length < 2 ^ (prefixWord ++ tailWord_3786898).sum := by decide
  have hdescent : baseEnd_3786898 < baseStart_3786898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786931 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_3786931 : Nat := 118140960795 + 3786931 * 2 ^ 59
def prefixEnd_3786931 : Nat := 4983230072969 + 3 ^ 40 * 3786931 * 2
def baseEnd_3786931 : Nat := 1944515808411628348746727

theorem tailTrace_3786931 : CollatzResearch.WordTrace tailWord_3786931 prefixEnd_3786931 1944515808411628348746727 := by
  unfold tailWord_3786931
  simp only [CollatzResearch.WordTrace]
  refine ⟨138120720643603218169008647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92080480429068812112672431 138120720643603218169008647)
  ·
    refine ⟨207181080965404827253512971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138120720643603218169008647 207181080965404827253512971)
    ·
      refine ⟨310771621448107240880269457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207181080965404827253512971 310771621448107240880269457)
      ·
        refine ⟨233078716086080430660202093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310771621448107240880269457 233078716086080430660202093)
        ·
          refine ⟨87404518532280161497575785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233078716086080430660202093 87404518532280161497575785)
          ·
            refine ⟨65553388899210121123181839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87404518532280161497575785 65553388899210121123181839)
            ·
              refine ⟨98330083348815181684772759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65553388899210121123181839 98330083348815181684772759)
              ·
                refine ⟨147495125023222772527159139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98330083348815181684772759 147495125023222772527159139)
                ·
                  refine ⟨221242687534834158790738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147495125023222772527159139 221242687534834158790738709)
                  ·
                    refine ⟨10370750978195351193315877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221242687534834158790738709 10370750978195351193315877)
                    ·
                      refine ⟨1944515808411628348746727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10370750978195351193315877 1944515808411628348746727)
                      ·
                        rfl

theorem cell23_3786931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_3786931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786931 prefixEnd_3786931 := by exact prefixLift 3786931
  have htrace : WordTrace (prefixWord ++ tailWord_3786931) baseStart_3786931 baseEnd_3786931 := by
    simpa [prefixWord, tailWord_3786931, baseEnd_3786931] using wordTrace_append hprefix tailTrace_3786931
  have hstable : (prefixWord ++ tailWord_3786931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786931).length < 2 ^ (prefixWord ++ tailWord_3786931).sum := by decide
  have hdescent : baseEnd_3786931 < baseStart_3786931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786938 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_3786938 : Nat := 118140960795 + 3786938 * 2 ^ 59
def prefixEnd_3786938 : Nat := 4983230072969 + 3 ^ 40 * 3786938 * 2
def baseEnd_3786938 : Nat := 1944519402776209821359195

theorem tailTrace_3786938 : CollatzResearch.WordTrace tailWord_3786938 prefixEnd_3786938 1944519402776209821359195 := by
  unfold tailWord_3786938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34530243988644464591128367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92080650636385238909675645 34530243988644464591128367)
  ·
    refine ⟨51795365982966696886692551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34530243988644464591128367 51795365982966696886692551)
    ·
      refine ⟨77693048974450045330038827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51795365982966696886692551 77693048974450045330038827)
      ·
        refine ⟨116539573461675067995058241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77693048974450045330038827 116539573461675067995058241)
        ·
          refine ⟨87404680096256300996293681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116539573461675067995058241 87404680096256300996293681)
          ·
            refine ⟨65553510072192225747220261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87404680096256300996293681 65553510072192225747220261)
            ·
              refine ⟨12291283138536042327603799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65553510072192225747220261 12291283138536042327603799)
              ·
                refine ⟨18436924707804063491405699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291283138536042327603799 18436924707804063491405699)
                ·
                  refine ⟨27655387061706095237108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18436924707804063491405699 27655387061706095237108549)
                  ·
                    refine ⟨5185385074069892856957853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27655387061706095237108549 5185385074069892856957853)
                    ·
                      refine ⟨1944519402776209821359195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185385074069892856957853 1944519402776209821359195)
                      ·
                        rfl

theorem cell23_3786938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_3786938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786938 prefixEnd_3786938 := by exact prefixLift 3786938
  have htrace : WordTrace (prefixWord ++ tailWord_3786938) baseStart_3786938 baseEnd_3786938 := by
    simpa [prefixWord, tailWord_3786938, baseEnd_3786938] using wordTrace_append hprefix tailTrace_3786938
  have hstable : (prefixWord ++ tailWord_3786938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786938).length < 2 ^ (prefixWord ++ tailWord_3786938).sum := by decide
  have hdescent : baseEnd_3786938 < baseStart_3786938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786958 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3786958 : Nat := 118140960795 + 3786958 * 2 ^ 59
def prefixEnd_3786958 : Nat := 4983230072969 + 3 ^ 40 * 3786958 * 2
def baseEnd_3786958 : Nat := 216058852487699971456567

theorem tailTrace_3786958 : CollatzResearch.WordTrace tailWord_3786958 prefixEnd_3786958 216058852487699971456567 := by
  unfold tailWord_3786958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265213176813175222530191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92081136943003601186827685 17265213176813175222530191)
  ·
    refine ⟨25897819765219762833795287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17265213176813175222530191 25897819765219762833795287)
    ·
      refine ⟨38846729647829644250692931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897819765219762833795287 38846729647829644250692931)
      ·
        refine ⟨58270094471744466376039397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38846729647829644250692931 58270094471744466376039397)
        ·
          refine ⟨10925642713452087445507387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58270094471744466376039397 10925642713452087445507387)
          ·
            refine ⟨16388464070178131168261081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10925642713452087445507387 16388464070178131168261081)
            ·
              refine ⟨12291348052633598376195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16388464070178131168261081 12291348052633598376195811)
              ·
                refine ⟨18437022078950397564293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291348052633598376195811 18437022078950397564293717)
                ·
                  refine ⟨216058852487699971456567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18437022078950397564293717 216058852487699971456567)
                  ·
                    rfl

theorem cell23_3786958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3786958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786958 prefixEnd_3786958 := by exact prefixLift 3786958
  have htrace : WordTrace (prefixWord ++ tailWord_3786958) baseStart_3786958 baseEnd_3786958 := by
    simpa [prefixWord, tailWord_3786958, baseEnd_3786958] using wordTrace_append hprefix tailTrace_3786958
  have hstable : (prefixWord ++ tailWord_3786958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786958).length < 2 ^ (prefixWord ++ tailWord_3786958).sum := by decide
  have hdescent : baseEnd_3786958 < baseStart_3786958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786961 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3786961 : Nat := 118140960795 + 3786961 * 2 ^ 59
def prefixEnd_3786961 : Nat := 4983230072969 + 3 ^ 40 * 3786961 * 2
def baseEnd_3786961 : Nat := 1944531212831263231371589

theorem tailTrace_3786961 : CollatzResearch.WordTrace tailWord_3786961 prefixEnd_3786961 1944531212831263231371589 := by
  unfold tailWord_3786961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138121814833494533292600737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92081209888996355528400491 138121814833494533292600737)
  ·
    refine ⟨103591361125120899969450553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138121814833494533292600737 103591361125120899969450553)
    ·
      refine ⟨77693520843840674977087915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103591361125120899969450553 77693520843840674977087915)
      ·
        refine ⟨116540281265761012465631873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77693520843840674977087915 116540281265761012465631873)
        ·
          refine ⟨87405210949320759349223905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116540281265761012465631873 87405210949320759349223905)
          ·
            refine ⟨65553908211990569511917929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87405210949320759349223905 65553908211990569511917929)
            ·
              refine ⟨49165431158992927133938447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65553908211990569511917929 49165431158992927133938447)
              ·
                refine ⟨73748146738489390700907671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49165431158992927133938447 73748146738489390700907671)
                ·
                  refine ⟨110622220107734086051361507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73748146738489390700907671 110622220107734086051361507)
                  ·
                    refine ⟨165933330161601129077042261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110622220107734086051361507 165933330161601129077042261)
                    ·
                      refine ⟨1944531212831263231371589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 165933330161601129077042261 1944531212831263231371589)
                      ·
                        rfl

theorem cell23_3786961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3786961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786961 prefixEnd_3786961 := by exact prefixLift 3786961
  have htrace : WordTrace (prefixWord ++ tailWord_3786961) baseStart_3786961 baseEnd_3786961 := by
    simpa [prefixWord, tailWord_3786961, baseEnd_3786961] using wordTrace_append hprefix tailTrace_3786961
  have hstable : (prefixWord ++ tailWord_3786961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786961).length < 2 ^ (prefixWord ++ tailWord_3786961).sum := by decide
  have hdescent : baseEnd_3786961 < baseStart_3786961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786962 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3786962 : Nat := 118140960795 + 3786962 * 2 ^ 59
def prefixEnd_3786962 : Nat := 4983230072969 + 3 ^ 40 * 3786962 * 2
def baseEnd_3786962 : Nat := 648177242103972575819695

theorem tailTrace_3786962 : CollatzResearch.WordTrace tailWord_3786962 prefixEnd_3786962 648177242103972575819695 := by
  unfold tailWord_3786962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34530462826622727615846785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92081234204327273642258093 34530462826622727615846785)
  ·
    refine ⟨25897847119967045711885089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34530462826622727615846785 25897847119967045711885089)
    ·
      refine ⟨19423385339975284283913817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25897847119967045711885089 19423385339975284283913817)
      ·
        refine ⟨14567539004981463212935363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19423385339975284283913817 14567539004981463212935363)
        ·
          refine ⟨21851308507472194819403045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14567539004981463212935363 21851308507472194819403045)
          ·
            refine ⟨4097120345151036528638071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21851308507472194819403045 4097120345151036528638071)
            ·
              refine ⟨6145680517726554792957107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097120345151036528638071 6145680517726554792957107)
              ·
                refine ⟨9218520776589832189435661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145680517726554792957107 9218520776589832189435661)
                ·
                  refine ⟨3456945291221187071038373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9218520776589832189435661 3456945291221187071038373)
                  ·
                    refine ⟨648177242103972575819695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456945291221187071038373 648177242103972575819695)
                    ·
                      rfl

theorem cell23_3786962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3786962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786962 prefixEnd_3786962 := by exact prefixLift 3786962
  have htrace : WordTrace (prefixWord ++ tailWord_3786962) baseStart_3786962 baseEnd_3786962 := by
    simpa [prefixWord, tailWord_3786962, baseEnd_3786962] using wordTrace_append hprefix tailTrace_3786962
  have hstable : (prefixWord ++ tailWord_3786962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786962).length < 2 ^ (prefixWord ++ tailWord_3786962).sum := by decide
  have hdescent : baseEnd_3786962 < baseStart_3786962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786988 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_3786988 : Nat := 118140960795 + 3786988 * 2 ^ 59
def prefixEnd_3786988 : Nat := 4983230072969 + 3 ^ 40 * 3786988 * 2
def baseEnd_3786988 : Nat := 648181692269644875244655

theorem tailTrace_3786988 : CollatzResearch.WordTrace tailWord_3786988 prefixEnd_3786988 648181692269644875244655 := by
  unfold tailWord_3786988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69061399802198358451916809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92081866402931144602555745 69061399802198358451916809)
  ·
    refine ⟨51796049851648768838937607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69061399802198358451916809 51796049851648768838937607)
    ·
      refine ⟨77694074777473153258406411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51796049851648768838937607 77694074777473153258406411)
      ·
        refine ⟨116541112166209729887609617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77694074777473153258406411 116541112166209729887609617)
        ·
          refine ⟨87405834124657297415707213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116541112166209729887609617 87405834124657297415707213)
          ·
            refine ⟨32777187796746486530890205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87405834124657297415707213 32777187796746486530890205)
            ·
              refine ⟨12291445423779932449083827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32777187796746486530890205 12291445423779932449083827)
              ·
                refine ⟨18437168135669898673625741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291445423779932449083827 18437168135669898673625741)
                ·
                  refine ⟨6913938050876212002609653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18437168135669898673625741 6913938050876212002609653)
                  ·
                    refine ⟨648181692269644875244655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6913938050876212002609653 648181692269644875244655)
                    ·
                      rfl

theorem cell23_3786988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_3786988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3786988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3786988 prefixEnd_3786988 := by exact prefixLift 3786988
  have htrace : WordTrace (prefixWord ++ tailWord_3786988) baseStart_3786988 baseEnd_3786988 := by
    simpa [prefixWord, tailWord_3786988, baseEnd_3786988] using wordTrace_append hprefix tailTrace_3786988
  have hstable : (prefixWord ++ tailWord_3786988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786988).length < 2 ^ (prefixWord ++ tailWord_3786988).sum := by decide
  have hdescent : baseEnd_3786988 < baseStart_3786988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787035 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 2, 4]
def baseStart_3787035 : Nat := 118140960795 + 3787035 * 2 ^ 59
def prefixEnd_3787035 : Nat := 4983230072969 + 3 ^ 40 * 3787035 * 2
def baseEnd_3787035 : Nat := 648189736799898647282083

theorem tailTrace_3787035 : CollatzResearch.WordTrace tailWord_3787035 prefixEnd_3787035 648189736799898647282083 := by
  unfold tailWord_3787035
  simp only [CollatzResearch.WordTrace]
  refine ⟨138124513835226443930794559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92083009223484295953863039 138124513835226443930794559)
  ·
    refine ⟨207186770752839665896191839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138124513835226443930794559 207186770752839665896191839)
    ·
      refine ⟨310780156129259498844287759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207186770752839665896191839 310780156129259498844287759)
      ·
        refine ⟨466170234193889248266431639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310780156129259498844287759 466170234193889248266431639)
        ·
          refine ⟨699255351290833872399647459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466170234193889248266431639 699255351290833872399647459)
          ·
            refine ⟨1048883026936250808599471189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699255351290833872399647459 1048883026936250808599471189)
            ·
              refine ⟨12291597971909189163275053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1048883026936250808599471189 12291597971909189163275053)
              ·
                refine ⟨4609349239465945936228145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12291597971909189163275053 4609349239465945936228145)
                ·
                  refine ⟨3457011929599459452171109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609349239465945936228145 3457011929599459452171109)
                  ·
                    refine ⟨648189736799898647282083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457011929599459452171109 648189736799898647282083)
                    ·
                      rfl

theorem cell23_3787035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 4].length) (baseStart_3787035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787035 prefixEnd_3787035 := by exact prefixLift 3787035
  have htrace : WordTrace (prefixWord ++ tailWord_3787035) baseStart_3787035 baseEnd_3787035 := by
    simpa [prefixWord, tailWord_3787035, baseEnd_3787035] using wordTrace_append hprefix tailTrace_3787035
  have hstable : (prefixWord ++ tailWord_3787035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787035).length < 2 ^ (prefixWord ++ tailWord_3787035).sum := by decide
  have hdescent : baseEnd_3787035 < baseStart_3787035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787053 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3787053 : Nat := 118140960795 + 3787053 * 2 ^ 59
def prefixEnd_3787053 : Nat := 4983230072969 + 3 ^ 40 * 3787053 * 2
def baseEnd_3787053 : Nat := 1944578453051476871421167

theorem tailTrace_3787053 : CollatzResearch.WordTrace tailWord_3787053 prefixEnd_3787053 1944578453051476871421167 := by
  unfold tailWord_3787053
  simp only [CollatzResearch.WordTrace]
  refine ⟨138125170349161233004949813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92083446899440822003299875 138125170349161233004949813)
  ·
    refine ⟨12949234720233865594214045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138125170349161233004949813 12949234720233865594214045)
    ·
      refine ⟨4855963020087699597830267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12949234720233865594214045 4855963020087699597830267)
      ·
        refine ⟨7283944530131549396745401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855963020087699597830267 7283944530131549396745401)
        ·
          refine ⟨5462958397598662047559051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7283944530131549396745401 5462958397598662047559051)
          ·
            refine ⟨8194437596397993071338577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462958397598662047559051 8194437596397993071338577)
            ·
              refine ⟨6145828197298494803503933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194437596397993071338577 6145828197298494803503933)
              ·
                refine ⟨2304685573986935551313975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6145828197298494803503933 2304685573986935551313975)
                ·
                  refine ⟨3457028360980403326970963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304685573986935551313975 3457028360980403326970963)
                  ·
                    refine ⟨5185542541470604990456445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457028360980403326970963 5185542541470604990456445)
                    ·
                      refine ⟨1944578453051476871421167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185542541470604990456445 1944578453051476871421167)
                      ·
                        rfl

theorem cell23_3787053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3787053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787053 prefixEnd_3787053 := by exact prefixLift 3787053
  have htrace : WordTrace (prefixWord ++ tailWord_3787053) baseStart_3787053 baseEnd_3787053 := by
    simpa [prefixWord, tailWord_3787053, baseEnd_3787053] using wordTrace_append hprefix tailTrace_3787053
  have hstable : (prefixWord ++ tailWord_3787053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787053).length < 2 ^ (prefixWord ++ tailWord_3787053).sum := by decide
  have hdescent : baseEnd_3787053 < baseStart_3787053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787092 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3787092 : Nat := 118140960795 + 3787092 * 2 ^ 59
def prefixEnd_3787092 : Nat := 4983230072969 + 3 ^ 40 * 3787092 * 2
def baseEnd_3787092 : Nat := 1944598478797002218833487

theorem tailTrace_3787092 : CollatzResearch.WordTrace tailWord_3787092 prefixEnd_3787092 1944598478797002218833487 := by
  unfold tailWord_3787092
  simp only [CollatzResearch.WordTrace]
  refine ⟨69063296398009971332809765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92084395197346628443746353 69063296398009971332809765)
  ·
    refine ⟨12949368074626869624901831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69063296398009971332809765 12949368074626869624901831)
    ·
      refine ⟨19424052111940304437352747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949368074626869624901831 19424052111940304437352747)
      ·
        refine ⟨29136078167910456656029121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424052111940304437352747 29136078167910456656029121)
        ·
          refine ⟨21852058625932842492021841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29136078167910456656029121 21852058625932842492021841)
          ·
            refine ⟨16389043969449631869016381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21852058625932842492021841 16389043969449631869016381)
            ·
              refine ⟨6145891488543611950881143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16389043969449631869016381 6145891488543611950881143)
              ·
                refine ⟨9218837232815417926321715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145891488543611950881143 9218837232815417926321715)
                ·
                  refine ⟨13828255849223126889482573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9218837232815417926321715 13828255849223126889482573)
                  ·
                    refine ⟨5185595943458672583555965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13828255849223126889482573 5185595943458672583555965)
                    ·
                      refine ⟨1944598478797002218833487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185595943458672583555965 1944598478797002218833487)
                      ·
                        rfl

theorem cell23_3787092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3787092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787092 prefixEnd_3787092 := by exact prefixLift 3787092
  have htrace : WordTrace (prefixWord ++ tailWord_3787092) baseStart_3787092 baseEnd_3787092 := by
    simpa [prefixWord, tailWord_3787092, baseEnd_3787092] using wordTrace_append hprefix tailTrace_3787092
  have hstable : (prefixWord ++ tailWord_3787092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787092).length < 2 ^ (prefixWord ++ tailWord_3787092).sum := by decide
  have hdescent : baseEnd_3787092 < baseStart_3787092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787166 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3787166 : Nat := 118140960795 + 3787166 * 2 ^ 59
def prefixEnd_3787166 : Nat := 4983230072969 + 3 ^ 40 * 3787166 * 2
def baseEnd_3787166 : Nat := 1944636476365434929308147

theorem tailTrace_3787166 : CollatzResearch.WordTrace tailWord_3787166 prefixEnd_3787166 1944636476365434929308147 := by
  unfold tailWord_3787166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266161474718981662976669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92086194531834568869208901 17266161474718981662976669)
  ·
    refine ⟨6474810553019618123616251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17266161474718981662976669 6474810553019618123616251)
    ·
      refine ⟨9712215829529427185424377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6474810553019618123616251 9712215829529427185424377)
      ·
        refine ⟨7284161872147070389068283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9712215829529427185424377 7284161872147070389068283)
        ·
          refine ⟨10926242808220605583602425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7284161872147070389068283 10926242808220605583602425)
          ·
            refine ⟨8194682106165454187701819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926242808220605583602425 8194682106165454187701819)
            ·
              refine ⟨12292023159248181281552729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194682106165454187701819 12292023159248181281552729)
              ·
                refine ⟨9219017369436135961164547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12292023159248181281552729 9219017369436135961164547)
                ·
                  refine ⟨13828526054154203941746821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219017369436135961164547 13828526054154203941746821)
                  ·
                    refine ⟨2592848635153913239077529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13828526054154203941746821 2592848635153913239077529)
                    ·
                      refine ⟨1944636476365434929308147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592848635153913239077529 1944636476365434929308147)
                      ·
                        rfl

theorem cell23_3787166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3787166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787166 prefixEnd_3787166 := by exact prefixLift 3787166
  have htrace : WordTrace (prefixWord ++ tailWord_3787166) baseStart_3787166 baseEnd_3787166 := by
    simpa [prefixWord, tailWord_3787166, baseEnd_3787166] using wordTrace_append hprefix tailTrace_3787166
  have hstable : (prefixWord ++ tailWord_3787166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787166).length < 2 ^ (prefixWord ++ tailWord_3787166).sum := by decide
  have hdescent : baseEnd_3787166 < baseStart_3787166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787189 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 5]
def baseStart_3787189 : Nat := 118140960795 + 3787189 * 2 ^ 59
def prefixEnd_3787189 : Nat := 4983230072969 + 3 ^ 40 * 3787189 * 2
def baseEnd_3787189 : Nat := 216072031824498704368949

theorem tailTrace_3787189 : CollatzResearch.WordTrace tailWord_3787189 prefixEnd_3787189 216072031824498704368949 := by
  unfold tailWord_3787189
  simp only [CollatzResearch.WordTrace]
  refine ⟨138130130676668528231900621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92086753784445685487933747 138130130676668528231900621)
  ·
    refine ⟨51798799003750698086962733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138130130676668528231900621 51798799003750698086962733)
    ·
      refine ⟨19424549626406511782611025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51798799003750698086962733 19424549626406511782611025)
      ·
        refine ⟨14568412219804883836958269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19424549626406511782611025 14568412219804883836958269)
        ·
          refine ⟨5463154582426831438859351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14568412219804883836958269 5463154582426831438859351)
          ·
            refine ⟨8194731873640247158289027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463154582426831438859351 8194731873640247158289027)
            ·
              refine ⟨12292097810460370737433541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194731873640247158289027 12292097810460370737433541)
              ·
                refine ⟨2304768339461319513268789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12292097810460370737433541 2304768339461319513268789)
                ·
                  refine ⟨216072031824498704368949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304768339461319513268789 216072031824498704368949)
                  ·
                    rfl

theorem cell23_3787189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_3787189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787189 prefixEnd_3787189 := by exact prefixLift 3787189
  have htrace : WordTrace (prefixWord ++ tailWord_3787189) baseStart_3787189 baseEnd_3787189 := by
    simpa [prefixWord, tailWord_3787189, baseEnd_3787189] using wordTrace_append hprefix tailTrace_3787189
  have hstable : (prefixWord ++ tailWord_3787189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787189).length < 2 ^ (prefixWord ++ tailWord_3787189).sum := by decide
  have hdescent : baseEnd_3787189 < baseStart_3787189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787249 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 1, 4]
def baseStart_3787249 : Nat := 118140960795 + 3787249 * 2 ^ 59
def prefixEnd_3787249 : Nat := 4983230072969 + 3 ^ 40 * 3787249 * 2
def baseEnd_3787249 : Nat := 648226365086586034856755

theorem tailTrace_3787249 : CollatzResearch.WordTrace tailWord_3787249 prefixEnd_3787249 648226365086586034856755 := by
  unfold tailWord_3787249
  simp only [CollatzResearch.WordTrace]
  refine ⟨138132319056451158479084801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92088212704300772319389867 138132319056451158479084801)
  ·
    refine ⟨103599239292338368859313601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138132319056451158479084801 103599239292338368859313601)
    ·
      refine ⟨77699429469253776644485201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103599239292338368859313601 77699429469253776644485201)
      ·
        refine ⟨58274572101940332483363901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77699429469253776644485201 58274572101940332483363901)
        ·
          refine ⟨21852964538227624681261463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58274572101940332483363901 21852964538227624681261463)
          ·
            refine ⟨32779446807341437021892195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852964538227624681261463 32779446807341437021892195)
            ·
              refine ⟨49169170211012155532838293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32779446807341437021892195 49169170211012155532838293)
              ·
                refine ⟨2304804853641194790601795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49169170211012155532838293 2304804853641194790601795)
                ·
                  refine ⟨3457207280461792185902693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304804853641194790601795 3457207280461792185902693)
                  ·
                    refine ⟨648226365086586034856755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457207280461792185902693 648226365086586034856755)
                    ·
                      rfl

theorem cell23_3787249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_3787249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787249 prefixEnd_3787249 := by exact prefixLift 3787249
  have htrace : WordTrace (prefixWord ++ tailWord_3787249) baseStart_3787249 baseEnd_3787249 := by
    simpa [prefixWord, tailWord_3787249, baseEnd_3787249] using wordTrace_append hprefix tailTrace_3787249
  have hstable : (prefixWord ++ tailWord_3787249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787249).length < 2 ^ (prefixWord ++ tailWord_3787249).sum := by decide
  have hdescent : baseEnd_3787249 < baseStart_3787249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787299 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 4, 3, 2]
def baseStart_3787299 : Nat := 118140960795 + 3787299 * 2 ^ 59
def prefixEnd_3787299 : Nat := 4983230072969 + 3 ^ 40 * 3787299 * 2
def baseEnd_3787299 : Nat := 1944704769292482908945035

theorem tailTrace_3787299 : CollatzResearch.WordTrace tailWord_3787299 prefixEnd_3787299 1944704769292482908945035 := by
  unfold tailWord_3787299
  simp only [CollatzResearch.WordTrace]
  refine ⟨138134142706270017018404951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92089428470846678012269967 138134142706270017018404951)
  ·
    refine ⟨207201214059405025527607427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138134142706270017018404951 207201214059405025527607427)
    ·
      refine ⟨310801821089107538291411141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207201214059405025527607427 310801821089107538291411141)
      ·
        refine ⟨58275341454207663429639589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310801821089107538291411141 58275341454207663429639589)
        ·
          refine ⟨10926626522663936893057423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58275341454207663429639589 10926626522663936893057423)
          ·
            refine ⟨16389939783995905339586135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10926626522663936893057423 16389939783995905339586135)
            ·
              refine ⟨24584909675993858009379203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16389939783995905339586135 24584909675993858009379203)
              ·
                refine ⟨36877364513990787014068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24584909675993858009379203 36877364513990787014068805)
                ·
                  refine ⟨6914505846373272565137901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36877364513990787014068805 6914505846373272565137901)
                  ·
                    refine ⟨2592939692389977211926713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6914505846373272565137901 2592939692389977211926713)
                    ·
                      refine ⟨1944704769292482908945035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592939692389977211926713 1944704769292482908945035)
                      ·
                        rfl

theorem cell23_3787299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_3787299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787299 prefixEnd_3787299 := by exact prefixLift 3787299
  have htrace : WordTrace (prefixWord ++ tailWord_3787299) baseStart_3787299 baseEnd_3787299 := by
    simpa [prefixWord, tailWord_3787299, baseEnd_3787299] using wordTrace_append hprefix tailTrace_3787299
  have hstable : (prefixWord ++ tailWord_3787299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787299).length < 2 ^ (prefixWord ++ tailWord_3787299).sum := by decide
  have hdescent : baseEnd_3787299 < baseStart_3787299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787300 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_3787300 : Nat := 118140960795 + 3787300 * 2 ^ 59
def prefixEnd_3787300 : Nat := 4983230072969 + 3 ^ 40 * 3787300 * 2
def baseEnd_3787300 : Nat := 648235094257712468344177

theorem tailTrace_3787300 : CollatzResearch.WordTrace tailWord_3787300 prefixEnd_3787300 648235094257712468344177 := by
  unfold tailWord_3787300
  simp only [CollatzResearch.WordTrace]
  refine ⟨69067089589633197094595677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92089452786177596126127569 69067089589633197094595677)
  ·
    refine ⟨25900158596112448910473379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69067089589633197094595677 25900158596112448910473379)
    ·
      refine ⟨38850237894168673365710069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25900158596112448910473379 38850237894168673365710069)
      ·
        refine ⟨3642209802578313128035319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38850237894168673365710069 3642209802578313128035319)
        ·
          refine ⟨5463314703867469692052979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642209802578313128035319 5463314703867469692052979)
          ·
            refine ⟨8194972055801204538079469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463314703867469692052979 8194972055801204538079469)
            ·
              refine ⟨3073114520925451701779801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8194972055801204538079469 3073114520925451701779801)
              ·
                refine ⟨2304835890694088776334851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073114520925451701779801 2304835890694088776334851)
                ·
                  refine ⟨3457253836041133164502277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304835890694088776334851 3457253836041133164502277)
                  ·
                    refine ⟨648235094257712468344177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457253836041133164502277 648235094257712468344177)
                    ·
                      rfl

theorem cell23_3787300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_3787300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787300 prefixEnd_3787300 := by exact prefixLift 3787300
  have htrace : WordTrace (prefixWord ++ tailWord_3787300) baseStart_3787300 baseEnd_3787300 := by
    simpa [prefixWord, tailWord_3787300, baseEnd_3787300] using wordTrace_append hprefix tailTrace_3787300
  have hstable : (prefixWord ++ tailWord_3787300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787300).length < 2 ^ (prefixWord ++ tailWord_3787300).sum := by decide
  have hdescent : baseEnd_3787300 < baseStart_3787300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787306 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3787306 : Nat := 118140960795 + 3787306 * 2 ^ 59
def prefixEnd_3787306 : Nat := 4983230072969 + 3 ^ 40 * 3787306 * 2
def baseEnd_3787306 : Nat := 1944708363657064381557503

theorem tailTrace_3787306 : CollatzResearch.WordTrace tailWord_3787306 prefixEnd_3787306 1944708363657064381557503 := by
  unfold tailWord_3787306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533599504311164303477443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92089598678163104809273181 34533599504311164303477443)
  ·
    refine ⟨51800399256466746455216165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34533599504311164303477443 51800399256466746455216165)
    ·
      refine ⟨9712574860587514960353031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51800399256466746455216165 9712574860587514960353031)
      ·
        refine ⟨14568862290881272440529547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9712574860587514960353031 14568862290881272440529547)
        ·
          refine ⟨21853293436321908660794321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568862290881272440529547 21853293436321908660794321)
          ·
            refine ⟨16389970077241431495595741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21853293436321908660794321 16389970077241431495595741)
            ·
              refine ⟨6146238778965536810848403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16389970077241431495595741 6146238778965536810848403)
              ·
                refine ⟨9219358168448305216272605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146238778965536810848403 9219358168448305216272605)
                ·
                  refine ⟨3457259313168114456102227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9219358168448305216272605 3457259313168114456102227)
                  ·
                    refine ⟨5185888969752171684153341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457259313168114456102227 5185888969752171684153341)
                    ·
                      refine ⟨1944708363657064381557503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185888969752171684153341 1944708363657064381557503)
                      ·
                        rfl

theorem cell23_3787306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3787306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787306 prefixEnd_3787306 := by exact prefixLift 3787306
  have htrace : WordTrace (prefixWord ++ tailWord_3787306) baseStart_3787306 baseEnd_3787306 := by
    simpa [prefixWord, tailWord_3787306, baseEnd_3787306] using wordTrace_append hprefix tailTrace_3787306
  have hstable : (prefixWord ++ tailWord_3787306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787306).length < 2 ^ (prefixWord ++ tailWord_3787306).sum := by decide
  have hdescent : baseEnd_3787306 < baseStart_3787306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787326 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3787326 : Nat := 118140960795 + 3787326 * 2 ^ 59
def prefixEnd_3787326 : Nat := 4983230072969 + 3 ^ 40 * 3787326 * 2
def baseEnd_3787326 : Nat := 648239544423384767769137

theorem tailTrace_3787326 : CollatzResearch.WordTrace tailWord_3787326 prefixEnd_3787326 648239544423384767769137 := by
  unfold tailWord_3787326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266890934646525078704729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92090084984781467086425221 17266890934646525078704729)
  ·
    refine ⟨12950168200984893809028547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17266890934646525078704729 12950168200984893809028547)
    ·
      refine ⟨19425252301477340713542821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12950168200984893809028547 19425252301477340713542821)
      ·
        refine ⟨3642234806527001383789279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19425252301477340713542821 3642234806527001383789279)
        ·
          refine ⟨5463352209790502075683919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642234806527001383789279 5463352209790502075683919)
          ·
            refine ⟨8195028314685753113525879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463352209790502075683919 8195028314685753113525879)
            ·
              refine ⟨12292542472028629670288819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195028314685753113525879 12292542472028629670288819)
              ·
                refine ⟨18438813708042944505433229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12292542472028629670288819 18438813708042944505433229)
                ·
                  refine ⟨6914555140516104189537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18438813708042944505433229 6914555140516104189537461)
                  ·
                    refine ⟨648239544423384767769137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6914555140516104189537461 648239544423384767769137)
                    ·
                      rfl

theorem cell23_3787326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3787326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787326 prefixEnd_3787326 := by exact prefixLift 3787326
  have htrace : WordTrace (prefixWord ++ tailWord_3787326) baseStart_3787326 baseEnd_3787326 := by
    simpa [prefixWord, tailWord_3787326, baseEnd_3787326] using wordTrace_append hprefix tailTrace_3787326
  have hstable : (prefixWord ++ tailWord_3787326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787326).length < 2 ^ (prefixWord ++ tailWord_3787326).sum := by decide
  have hdescent : baseEnd_3787326 < baseStart_3787326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787329 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3787329 : Nat := 118140960795 + 3787329 * 2 ^ 59
def prefixEnd_3787329 : Nat := 4983230072969 + 3 ^ 40 * 3787329 * 2
def baseEnd_3787329 : Nat := 1944720173712117791569897

theorem tailTrace_3787329 : CollatzResearch.WordTrace tailWord_3787329 prefixEnd_3787329 1944720173712117791569897 := by
  unfold tailWord_3787329
  simp only [CollatzResearch.WordTrace]
  refine ⟨138135236896161332141997041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92090157930774221427998027 138135236896161332141997041)
  ·
    refine ⟨103601427672120999106497781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138135236896161332141997041 103601427672120999106497781)
    ·
      refine ⟨9712633844261343666234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103601427672120999106497781 9712633844261343666234167)
      ·
        refine ⟨14568950766392015499351251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9712633844261343666234167 14568950766392015499351251)
        ·
          refine ⟨21853426149588023249026877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568950766392015499351251 21853426149588023249026877)
          ·
            refine ⟨8195034806095508718385079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21853426149588023249026877 8195034806095508718385079)
            ·
              refine ⟨12292552209143263077577619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195034806095508718385079 12292552209143263077577619)
              ·
                refine ⟨18438828313714894616366429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12292552209143263077577619 18438828313714894616366429)
                ·
                  refine ⟨6914560617643085481137411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18438828313714894616366429 6914560617643085481137411)
                  ·
                    refine ⟨10371840926464628221706117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914560617643085481137411 10371840926464628221706117)
                    ·
                      refine ⟨1944720173712117791569897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10371840926464628221706117 1944720173712117791569897)
                      ·
                        rfl

theorem cell23_3787329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3787329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787329 prefixEnd_3787329 := by exact prefixLift 3787329
  have htrace : WordTrace (prefixWord ++ tailWord_3787329) baseStart_3787329 baseEnd_3787329 := by
    simpa [prefixWord, tailWord_3787329, baseEnd_3787329] using wordTrace_append hprefix tailTrace_3787329
  have hstable : (prefixWord ++ tailWord_3787329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787329).length < 2 ^ (prefixWord ++ tailWord_3787329).sum := by decide
  have hdescent : baseEnd_3787329 < baseStart_3787329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787342 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3787342 : Nat := 118140960795 + 3787342 * 2 ^ 59
def prefixEnd_3787342 : Nat := 4983230072969 + 3 ^ 40 * 3787342 * 2
def baseEnd_3787342 : Nat := 1944726848960626240707337

theorem tailTrace_3787342 : CollatzResearch.WordTrace tailWord_3787342 prefixEnd_3787342 1944726848960626240707337 := by
  unfold tailWord_3787342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266963880639279420277535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92090474030076156908146853 17266963880639279420277535)
  ·
    refine ⟨25900445820958919130416303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17266963880639279420277535 25900445820958919130416303)
    ·
      refine ⟨38850668731438378695624455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25900445820958919130416303 38850668731438378695624455)
      ·
        refine ⟨58276003097157568043436683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38850668731438378695624455 58276003097157568043436683)
        ·
          refine ⟨87414004645736352065155025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58276003097157568043436683 87414004645736352065155025)
          ·
            refine ⟨65560503484302264048866269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87414004645736352065155025 65560503484302264048866269)
            ·
              refine ⟨24585188806613349018324851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65560503484302264048866269 24585188806613349018324851)
              ·
                refine ⟨36877783209920023527487277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24585188806613349018324851 36877783209920023527487277)
                ·
                  refine ⟨13829168703720008822807729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36877783209920023527487277 13829168703720008822807729)
                  ·
                    refine ⟨10371876527790006617105797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13829168703720008822807729 10371876527790006617105797)
                    ·
                      refine ⟨1944726848960626240707337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10371876527790006617105797 1944726848960626240707337)
                      ·
                        rfl

theorem cell23_3787342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3787342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787342 prefixEnd_3787342 := by exact prefixLift 3787342
  have htrace : WordTrace (prefixWord ++ tailWord_3787342) baseStart_3787342 baseEnd_3787342 := by
    simpa [prefixWord, tailWord_3787342, baseEnd_3787342] using wordTrace_append hprefix tailTrace_3787342
  have hstable : (prefixWord ++ tailWord_3787342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787342).length < 2 ^ (prefixWord ++ tailWord_3787342).sum := by decide
  have hdescent : baseEnd_3787342 < baseStart_3787342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787346 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_3787346 : Nat := 118140960795 + 3787346 * 2 ^ 59
def prefixEnd_3787346 : Nat := 4983230072969 + 3 ^ 40 * 3787346 * 2
def baseEnd_3787346 : Nat := 1944728902883244225057319

theorem tailTrace_3787346 : CollatzResearch.WordTrace tailWord_3787346 prefixEnd_3787346 1944728902883244225057319 := by
  unfold tailWord_3787346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533964234274936011341473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92090571291399829363577261 34533964234274936011341473)
  ·
    refine ⟨25900473175706202008506105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34533964234274936011341473 25900473175706202008506105)
    ·
      refine ⟨19425354881779651506379579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25900473175706202008506105 19425354881779651506379579)
      ·
        refine ⟨29138032322669477259569369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19425354881779651506379579 29138032322669477259569369)
        ·
          refine ⟨21853524242002107944677027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29138032322669477259569369 21853524242002107944677027)
          ·
            refine ⟨32780286363003161917015541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21853524242002107944677027 32780286363003161917015541)
            ·
              refine ⟨3073151846531546429720207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32780286363003161917015541 3073151846531546429720207)
              ·
                refine ⟨4609727769797319644580311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073151846531546429720207 4609727769797319644580311)
                ·
                  refine ⟨6914591654695979466870467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609727769797319644580311 6914591654695979466870467)
                  ·
                    refine ⟨10371887482043969200305701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914591654695979466870467 10371887482043969200305701)
                    ·
                      refine ⟨1944728902883244225057319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10371887482043969200305701 1944728902883244225057319)
                      ·
                        rfl

theorem cell23_3787346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_3787346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787346 prefixEnd_3787346 := by exact prefixLift 3787346
  have htrace : WordTrace (prefixWord ++ tailWord_3787346) baseStart_3787346 baseEnd_3787346 := by
    simpa [prefixWord, tailWord_3787346, baseEnd_3787346] using wordTrace_append hprefix tailTrace_3787346
  have hstable : (prefixWord ++ tailWord_3787346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787346).length < 2 ^ (prefixWord ++ tailWord_3787346).sum := by decide
  have hdescent : baseEnd_3787346 < baseStart_3787346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787349 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3787349 : Nat := 118140960795 + 3787349 * 2 ^ 59
def prefixEnd_3787349 : Nat := 4983230072969 + 3 ^ 40 * 3787349 * 2
def baseEnd_3787349 : Nat := 1944730443325207713319805

theorem tailTrace_3787349 : CollatzResearch.WordTrace tailWord_3787349 prefixEnd_3787349 1944730443325207713319805 := by
  unfold tailWord_3787349
  simp only [CollatzResearch.WordTrace]
  refine ⟨138135966356088875557725101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92090644237392583705150067 138135966356088875557725101)
  ·
    refine ⟨51800987383533328334146913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138135966356088875557725101 51800987383533328334146913)
    ·
      refine ⟨38850740537649996250610185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51800987383533328334146913 38850740537649996250610185)
      ·
        refine ⟨29138055403237497187957639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38850740537649996250610185 29138055403237497187957639)
        ·
          refine ⟨43707083104856245781936459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29138055403237497187957639 43707083104856245781936459)
          ·
            refine ⟨65560624657284368672904689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43707083104856245781936459 65560624657284368672904689)
            ·
              refine ⟨49170468492963276504678517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65560624657284368672904689 49170468492963276504678517)
              ·
                refine ⟨4609731421215307172313611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49170468492963276504678517 4609731421215307172313611)
                ·
                  refine ⟨6914597131822960758470417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609731421215307172313611 6914597131822960758470417)
                  ·
                    refine ⟨5185947848867220568852813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6914597131822960758470417 5185947848867220568852813)
                    ·
                      refine ⟨1944730443325207713319805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5185947848867220568852813 1944730443325207713319805)
                      ·
                        rfl

theorem cell23_3787349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3787349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787349 prefixEnd_3787349 := by exact prefixLift 3787349
  have htrace : WordTrace (prefixWord ++ tailWord_3787349) baseStart_3787349 baseEnd_3787349 := by
    simpa [prefixWord, tailWord_3787349, baseEnd_3787349] using wordTrace_append hprefix tailTrace_3787349
  have hstable : (prefixWord ++ tailWord_3787349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787349).length < 2 ^ (prefixWord ++ tailWord_3787349).sum := by decide
  have hdescent : baseEnd_3787349 < baseStart_3787349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787363 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3787363 : Nat := 118140960795 + 3787363 * 2 ^ 59
def prefixEnd_3787363 : Nat := 4983230072969 + 3 ^ 40 * 3787363 * 2
def baseEnd_3787363 : Nat := 1944737632054370658544741

theorem tailTrace_3787363 : CollatzResearch.WordTrace tailWord_3787363 prefixEnd_3787363 1944737632054370658544741 := by
  unfold tailWord_3787363
  simp only [CollatzResearch.WordTrace]
  refine ⟨138136476978038155948734743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92090984652025437299156495 138136476978038155948734743)
  ·
    refine ⟨207204715467057233923102115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138136476978038155948734743 207204715467057233923102115)
    ·
      refine ⟨310807073200585850884653173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207204715467057233923102115 310807073200585850884653173)
      ·
        refine ⟨29138163112554923520436235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310807073200585850884653173 29138163112554923520436235)
        ·
          refine ⟨43707244668832385280654353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29138163112554923520436235 43707244668832385280654353)
          ·
            refine ⟨32780433501624288960490765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43707244668832385280654353 32780433501624288960490765)
            ·
              refine ⟨12292662563109108360184037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32780433501624288960490765 12292662563109108360184037)
              ·
                refine ⟨2304874230582957817534507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12292662563109108360184037 2304874230582957817534507)
                ·
                  refine ⟨3457311345874436726301761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304874230582957817534507 3457311345874436726301761)
                  ·
                    refine ⟨2592983509405827544726321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457311345874436726301761 2592983509405827544726321)
                    ·
                      refine ⟨1944737632054370658544741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2592983509405827544726321 1944737632054370658544741)
                      ·
                        rfl

theorem cell23_3787363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3787363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787363 prefixEnd_3787363 := by exact prefixLift 3787363
  have htrace : WordTrace (prefixWord ++ tailWord_3787363) baseStart_3787363 baseEnd_3787363 := by
    simpa [prefixWord, tailWord_3787363, baseEnd_3787363] using wordTrace_append hprefix tailTrace_3787363
  have hstable : (prefixWord ++ tailWord_3787363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787363).length < 2 ^ (prefixWord ++ tailWord_3787363).sum := by decide
  have hdescent : baseEnd_3787363 < baseStart_3787363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787394 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3787394 : Nat := 118140960795 + 3787394 * 2 ^ 59
def prefixEnd_3787394 : Nat := 4983230072969 + 3 ^ 40 * 3787394 * 2
def baseEnd_3787394 : Nat := 648251183318220012419033

theorem tailTrace_3787394 : CollatzResearch.WordTrace tailWord_3787394 prefixEnd_3787394 648251183318220012419033 := by
  unfold tailWord_3787394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34534401910231462060778309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92091738427283898828742157 34534401910231462060778309)
  ·
    refine ⟨6475200358168399136395933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34534401910231462060778309 6475200358168399136395933)
    ·
      refine ⟨2428200134313149676148475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6475200358168399136395933 2428200134313149676148475)
      ·
        refine ⟨3642300201469724514222713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428200134313149676148475 3642300201469724514222713)
        ·
          refine ⟨2731725151102293385667035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3642300201469724514222713 2731725151102293385667035)
          ·
            refine ⟨4097587726653440078500553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731725151102293385667035 4097587726653440078500553)
            ·
              refine ⟨3073190794990080058875415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4097587726653440078500553 3073190794990080058875415)
              ·
                refine ⟨4609786192485120088313123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073190794990080058875415 4609786192485120088313123)
                ·
                  refine ⟨6914679288727680132469685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609786192485120088313123 6914679288727680132469685)
                  ·
                    refine ⟨648251183318220012419033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6914679288727680132469685 648251183318220012419033)
                    ·
                      rfl

theorem cell23_3787394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3787394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787394 prefixEnd_3787394 := by exact prefixLift 3787394
  have htrace : WordTrace (prefixWord ++ tailWord_3787394) baseStart_3787394 baseEnd_3787394 := by
    simpa [prefixWord, tailWord_3787394, baseEnd_3787394] using wordTrace_append hprefix tailTrace_3787394
  have hstable : (prefixWord ++ tailWord_3787394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787394).length < 2 ^ (prefixWord ++ tailWord_3787394).sum := by decide
  have hdescent : baseEnd_3787394 < baseStart_3787394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787506 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3787506 : Nat := 118140960795 + 3787506 * 2 ^ 59
def prefixEnd_3787506 : Nat := 4983230072969 + 3 ^ 40 * 3787506 * 2
def baseEnd_3787506 : Nat := 648270353262654533018861

theorem tailTrace_3787506 : CollatzResearch.WordTrace tailWord_3787506 prefixEnd_3787506 648270353262654533018861 := by
  unfold tailWord_3787506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34535423154130022842797593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92094461744346727580793581 34535423154130022842797593)
  ·
    refine ⟨25901567365597517132098195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34535423154130022842797593 25901567365597517132098195)
    ·
      refine ⟨38852351048396275698147293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25901567365597517132098195 38852351048396275698147293)
      ·
        refine ⟨14569631643148603386805235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38852351048396275698147293 14569631643148603386805235)
        ·
          refine ⟨21854447464722905080207853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14569631643148603386805235 21854447464722905080207853)
          ·
            refine ⟨8195417799271089405077945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21854447464722905080207853 8195417799271089405077945)
            ·
              refine ⟨6146563349453317053808459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195417799271089405077945 6146563349453317053808459)
              ·
                refine ⟨9219845024179975580712689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146563349453317053808459 9219845024179975580712689)
                ·
                  refine ⟨6914883768134981685534517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9219845024179975580712689 6914883768134981685534517)
                  ·
                    refine ⟨648270353262654533018861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6914883768134981685534517 648270353262654533018861)
                    ·
                      rfl

theorem cell23_3787506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3787506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787506 prefixEnd_3787506 := by exact prefixLift 3787506
  have htrace : WordTrace (prefixWord ++ tailWord_3787506) baseStart_3787506 baseEnd_3787506 := by
    simpa [prefixWord, tailWord_3787506, baseEnd_3787506] using wordTrace_append hprefix tailTrace_3787506
  have hstable : (prefixWord ++ tailWord_3787506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787506).length < 2 ^ (prefixWord ++ tailWord_3787506).sum := by decide
  have hdescent : baseEnd_3787506 < baseStart_3787506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787543 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3787543 : Nat := 118140960795 + 3787543 * 2 ^ 59
def prefixEnd_3787543 : Nat := 4983230072969 + 3 ^ 40 * 3787543 * 2
def baseEnd_3787543 : Nat := 1944830058572179954293913

theorem tailTrace_3787543 : CollatzResearch.WordTrace tailWord_3787543 prefixEnd_3787543 1944830058572179954293913 := by
  unfold tailWord_3787543
  simp only [CollatzResearch.WordTrace]
  refine ⟨138143042117386046690287283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92095361411590697793524855 138143042117386046690287283)
  ·
    refine ⟨207214563176079070035430925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138143042117386046690287283 207214563176079070035430925)
    ·
      refine ⟨77705461191029651263286597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207214563176079070035430925 77705461191029651263286597)
      ·
        refine ⟨14569773973318059611866237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77705461191029651263286597 14569773973318059611866237)
        ·
          refine ⟨5463665239994272354449839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14569773973318059611866237 5463665239994272354449839)
          ·
            refine ⟨8195497859991408531674759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463665239994272354449839 8195497859991408531674759)
            ·
              refine ⟨12293246789987112797512139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195497859991408531674759 12293246789987112797512139)
              ·
                refine ⟨18439870184980669196268209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293246789987112797512139 18439870184980669196268209)
                ·
                  refine ⟨13829902638735501897201157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18439870184980669196268209 13829902638735501897201157)
                  ·
                    refine ⟨2593106744762906605725217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13829902638735501897201157 2593106744762906605725217)
                    ·
                      refine ⟨1944830058572179954293913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593106744762906605725217 1944830058572179954293913)
                      ·
                        rfl

theorem cell23_3787543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3787543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787543 prefixEnd_3787543 := by exact prefixLift 3787543
  have htrace : WordTrace (prefixWord ++ tailWord_3787543) baseStart_3787543 baseEnd_3787543 := by
    simpa [prefixWord, tailWord_3787543, baseEnd_3787543] using wordTrace_append hprefix tailTrace_3787543
  have hstable : (prefixWord ++ tailWord_3787543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787543).length < 2 ^ (prefixWord ++ tailWord_3787543).sum := by decide
  have hdescent : baseEnd_3787543 < baseStart_3787543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787576 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_3787576 : Nat := 118140960795 + 3787576 * 2 ^ 59
def prefixEnd_3787576 : Nat := 4983230072969 + 3 ^ 40 * 3787576 * 2
def baseEnd_3787576 : Nat := 1944847003433778325181261

theorem tailTrace_3787576 : CollatzResearch.WordTrace tailWord_3787576 prefixEnd_3787576 1944847003433778325181261 := by
  unfold tailWord_3787576
  simp only [CollatzResearch.WordTrace]
  refine ⟨69072122863133246663119291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92096163817510995550825721 69072122863133246663119291)
  ·
    refine ⟨103608184294699869994678937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69072122863133246663119291 103608184294699869994678937)
    ·
      refine ⟨77706138221024902496009203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103608184294699869994678937 77706138221024902496009203)
      ·
        refine ⟨116559207331537353744013805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77706138221024902496009203 116559207331537353744013805)
        ·
          refine ⟨43709702749326507654005177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116559207331537353744013805 43709702749326507654005177)
          ·
            refine ⟨32782277061994880740503883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43709702749326507654005177 32782277061994880740503883)
            ·
              refine ⟨49173415592992321110755825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32782277061994880740503883 49173415592992321110755825)
              ·
                refine ⟨36880061694744240833066869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49173415592992321110755825 36880061694744240833066869)
                ·
                  refine ⟨3457505783882272578100019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36880061694744240833066869 3457505783882272578100019)
                  ·
                    refine ⟨5186258675823408867150029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457505783882272578100019 5186258675823408867150029)
                    ·
                      refine ⟨1944847003433778325181261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186258675823408867150029 1944847003433778325181261)
                      ·
                        rfl

theorem cell23_3787576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_3787576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787576 prefixEnd_3787576 := by exact prefixLift 3787576
  have htrace : WordTrace (prefixWord ++ tailWord_3787576) baseStart_3787576 baseEnd_3787576 := by
    simpa [prefixWord, tailWord_3787576, baseEnd_3787576] using wordTrace_append hprefix tailTrace_3787576
  have hstable : (prefixWord ++ tailWord_3787576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787576).length < 2 ^ (prefixWord ++ tailWord_3787576).sum := by decide
  have hdescent : baseEnd_3787576 < baseStart_3787576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787593 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_3787593 : Nat := 118140960795 + 3787593 * 2 ^ 59
def prefixEnd_3787593 : Nat := 4983230072969 + 3 ^ 40 * 3787593 * 2
def baseEnd_3787593 : Nat := 1944855732604904758668683

theorem tailTrace_3787593 : CollatzResearch.WordTrace tailWord_3787593 prefixEnd_3787593 1944855732604904758668683 := by
  unfold tailWord_3787593
  simp only [CollatzResearch.WordTrace]
  refine ⟨138144865767204905229607433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92096577178136603486404955 138144865767204905229607433)
  ·
    refine ⟨103608649325403678922205575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138144865767204905229607433 103608649325403678922205575)
    ·
      refine ⟨155412973988105518383308363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103608649325403678922205575 155412973988105518383308363)
      ·
        refine ⟨233119460982158277574962545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155412973988105518383308363 233119460982158277574962545)
        ·
          refine ⟨174839595736618708181221909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233119460982158277574962545 174839595736618708181221909)
          ·
            refine ⟨8195606050154001945994777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174839595736618708181221909 8195606050154001945994777)
            ·
              refine ⟨6146704537615501459496083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195606050154001945994777 6146704537615501459496083)
              ·
                refine ⟨9220056806423252189244125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146704537615501459496083 9220056806423252189244125)
                ·
                  refine ⟨3457521302408719570966547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9220056806423252189244125 3457521302408719570966547)
                  ·
                    refine ⟨5186281953613079356449821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457521302408719570966547 5186281953613079356449821)
                    ·
                      refine ⟨1944855732604904758668683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186281953613079356449821 1944855732604904758668683)
                      ·
                        rfl

theorem cell23_3787593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_3787593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787593 prefixEnd_3787593 := by exact prefixLift 3787593
  have htrace : WordTrace (prefixWord ++ tailWord_3787593) baseStart_3787593 baseEnd_3787593 := by
    simpa [prefixWord, tailWord_3787593, baseEnd_3787593] using wordTrace_append hprefix tailTrace_3787593
  have hstable : (prefixWord ++ tailWord_3787593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787593).length < 2 ^ (prefixWord ++ tailWord_3787593).sum := by decide
  have hdescent : baseEnd_3787593 < baseStart_3787593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787616 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2]
def baseStart_3787616 : Nat := 118140960795 + 3787616 * 2 ^ 59
def prefixEnd_3787616 : Nat := 4983230072969 + 3 ^ 40 * 3787616 * 2
def baseEnd_3787616 : Nat := 1944867542659958168681077

theorem tailTrace_3787616 : CollatzResearch.WordTrace tailWord_3787616 prefixEnd_3787616 1944867542659958168681077 := by
  unfold tailWord_3787616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69072852323060790078847351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92097136430747720105129801 69072852323060790078847351)
  ·
    refine ⟨103609278484591185118271027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69072852323060790078847351 103609278484591185118271027)
    ·
      refine ⟨155413917726886777677406541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103609278484591185118271027 155413917726886777677406541)
      ·
        refine ⟨58280219147582541629027453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155413917726886777677406541 58280219147582541629027453)
        ·
          refine ⟨21855082180343453110885295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58280219147582541629027453 21855082180343453110885295)
          ·
            refine ⟨32782623270515179666327943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21855082180343453110885295 32782623270515179666327943)
            ·
              refine ⟨49173934905772769499491915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32782623270515179666327943 49173934905772769499491915)
              ·
                refine ⟨73760902358659154249237873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49173934905772769499491915 73760902358659154249237873)
                ·
                  refine ⟨55320676768994365686928405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73760902358659154249237873 55320676768994365686928405)
                  ·
                    refine ⟨2593156723546610891574769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55320676768994365686928405 2593156723546610891574769)
                    ·
                      refine ⟨1944867542659958168681077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593156723546610891574769 1944867542659958168681077)
                      ·
                        rfl

theorem cell23_3787616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_3787616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787616 prefixEnd_3787616 := by exact prefixLift 3787616
  have htrace : WordTrace (prefixWord ++ tailWord_3787616) baseStart_3787616 baseEnd_3787616 := by
    simpa [prefixWord, tailWord_3787616, baseEnd_3787616] using wordTrace_append hprefix tailTrace_3787616
  have hstable : (prefixWord ++ tailWord_3787616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787616).length < 2 ^ (prefixWord ++ tailWord_3787616).sum := by decide
  have hdescent : baseEnd_3787616 < baseStart_3787616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787656 : List Nat := [2, 1, 3, 3, 2, 2, 2, 8]
def baseStart_3787656 : Nat := 118140960795 + 3787656 * 2 ^ 59
def prefixEnd_3787656 : Nat := 4983230072969 + 3 ^ 40 * 3787656 * 2
def baseEnd_3787656 : Nat := 72032891921708815265959

theorem tailTrace_3787656 : CollatzResearch.WordTrace tailWord_3787656 prefixEnd_3787656 72032891921708815265959 := by
  unfold tailWord_3787656
  simp only [CollatzResearch.WordTrace]
  refine ⟨69073581782988333494575411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92098109043984444659433881 69073581782988333494575411)
  ·
    refine ⟨103610372674482500241863117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69073581782988333494575411 103610372674482500241863117)
    ·
      refine ⟨38853889752930937590698669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103610372674482500241863117 38853889752930937590698669)
      ·
        refine ⟨14570208657349101596512001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38853889752930937590698669 14570208657349101596512001)
        ·
          refine ⟨10927656493011826197384001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14570208657349101596512001 10927656493011826197384001)
          ·
            refine ⟨8195742369758869648038001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10927656493011826197384001 8195742369758869648038001)
            ·
              refine ⟨6146806777319152236028501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195742369758869648038001 6146806777319152236028501)
              ·
                refine ⟨72032891921708815265959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6146806777319152236028501 72032891921708815265959)
                ·
                  rfl

theorem cell23_3787656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 8].length) (baseStart_3787656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787656 prefixEnd_3787656 := by exact prefixLift 3787656
  have htrace : WordTrace (prefixWord ++ tailWord_3787656) baseStart_3787656 baseEnd_3787656 := by
    simpa [prefixWord, tailWord_3787656, baseEnd_3787656] using wordTrace_append hprefix tailTrace_3787656
  have hstable : (prefixWord ++ tailWord_3787656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787656).length < 2 ^ (prefixWord ++ tailWord_3787656).sum := by decide
  have hdescent : baseEnd_3787656 < baseStart_3787656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787687 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3787687 : Nat := 118140960795 + 3787687 * 2 ^ 59
def prefixEnd_3787687 : Nat := 4983230072969 + 3 ^ 40 * 3787687 * 2
def baseEnd_3787687 : Nat := 1944903999786427390893251

theorem tailTrace_3787687 : CollatzResearch.WordTrace tailWord_3787687 prefixEnd_3787687 1944903999786427390893251 := by
  unfold tailWord_3787687
  simp only [CollatzResearch.WordTrace]
  refine ⟨138148294228864359283529315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92098862819242906189019543 138148294228864359283529315)
  ·
    refine ⟨207222441343296538925293973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138148294228864359283529315 207222441343296538925293973)
    ·
      refine ⟨9713551937967025262123155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207222441343296538925293973 9713551937967025262123155)
      ·
        refine ⟨14570327906950537893184733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9713551937967025262123155 14570327906950537893184733)
        ·
          refine ⟨5463872965106451709944275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14570327906950537893184733 5463872965106451709944275)
          ·
            refine ⟨8195809447659677564916413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463872965106451709944275 8195809447659677564916413)
            ·
              refine ⟨3073428542872379086843655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8195809447659677564916413 3073428542872379086843655)
              ·
                refine ⟨4610142814308568630265483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073428542872379086843655 4610142814308568630265483)
                ·
                  refine ⟨6915214221462852945398225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610142814308568630265483 6915214221462852945398225)
                  ·
                    refine ⟨5186410666097139709048669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6915214221462852945398225 5186410666097139709048669)
                    ·
                      refine ⟨1944903999786427390893251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186410666097139709048669 1944903999786427390893251)
                      ·
                        rfl

theorem cell23_3787687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3787687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787687 prefixEnd_3787687 := by exact prefixLift 3787687
  have htrace : WordTrace (prefixWord ++ tailWord_3787687) baseStart_3787687 baseEnd_3787687 := by
    simpa [prefixWord, tailWord_3787687, baseEnd_3787687] using wordTrace_append hprefix tailTrace_3787687
  have hstable : (prefixWord ++ tailWord_3787687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787687).length < 2 ^ (prefixWord ++ tailWord_3787687).sum := by decide
  have hdescent : baseEnd_3787687 < baseStart_3787687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787718 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3787718 : Nat := 118140960795 + 3787718 * 2 ^ 59
def prefixEnd_3787718 : Nat := 4983230072969 + 3 ^ 40 * 3787718 * 2
def baseEnd_3787718 : Nat := 1944919917686716769605609

theorem tailTrace_3787718 : CollatzResearch.WordTrace tailWord_3787718 prefixEnd_3787718 1944919917686716769605609 := by
  unfold tailWord_3787718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317169527867251611809619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92099616594501367718605205 4317169527867251611809619)
  ·
    refine ⟨6475754291800877417714429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317169527867251611809619 6475754291800877417714429)
    ·
      refine ⟨2428407859425329031642911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6475754291800877417714429 2428407859425329031642911)
      ·
        refine ⟨3642611789137993547464367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428407859425329031642911 3642611789137993547464367)
        ·
          refine ⟨5463917683706990321196551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642611789137993547464367 5463917683706990321196551)
          ·
            refine ⟨8195876525560485481794827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463917683706990321196551 8195876525560485481794827)
            ·
              refine ⟨12293814788340728222692241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195876525560485481794827 12293814788340728222692241)
              ·
                refine ⟨9220361091255546167019181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12293814788340728222692241 9220361091255546167019181)
                ·
                  refine ⟨3457635409220829812632193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9220361091255546167019181 3457635409220829812632193)
                  ·
                    refine ⟨2593226556915622359474145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457635409220829812632193 2593226556915622359474145)
                    ·
                      refine ⟨1944919917686716769605609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593226556915622359474145 1944919917686716769605609)
                      ·
                        rfl

theorem cell23_3787718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3787718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787718 prefixEnd_3787718 := by exact prefixLift 3787718
  have htrace : WordTrace (prefixWord ++ tailWord_3787718) baseStart_3787718 baseEnd_3787718 := by
    simpa [prefixWord, tailWord_3787718, baseEnd_3787718] using wordTrace_append hprefix tailTrace_3787718
  have hstable : (prefixWord ++ tailWord_3787718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787718).length < 2 ^ (prefixWord ++ tailWord_3787718).sum := by decide
  have hdescent : baseEnd_3787718 < baseStart_3787718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787723 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 4, 2]
def baseStart_3787723 : Nat := 118140960795 + 3787723 * 2 ^ 59
def prefixEnd_3787723 : Nat := 4983230072969 + 3 ^ 40 * 3787723 * 2
def baseEnd_3787723 : Nat := 1944922485089989250043085

theorem tailTrace_3787723 : CollatzResearch.WordTrace tailWord_3787723 prefixEnd_3787723 1944922485089989250043085 := by
  unfold tailWord_3787723
  simp only [CollatzResearch.WordTrace]
  refine ⟨138149607256733937431839823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92099738171155958287893215 138149607256733937431839823)
  ·
    refine ⟨207224410885100906147759735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138149607256733937431839823 207224410885100906147759735)
    ·
      refine ⟨310836616327651359221639603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207224410885100906147759735 310836616327651359221639603)
      ·
        refine ⟨466254924491477038832459405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310836616327651359221639603 466254924491477038832459405)
        ·
          refine ⟨174845596684303889562172277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466254924491477038832459405 174845596684303889562172277)
          ·
            refine ⟨16391774689153489646453651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174845596684303889562172277 16391774689153489646453651)
            ·
              refine ⟨24587662033730234469680477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16391774689153489646453651 24587662033730234469680477)
              ·
                refine ⟨9220373262648837926130179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24587662033730234469680477 9220373262648837926130179)
                ·
                  refine ⟨13830559893973256889195269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220373262648837926130179 13830559893973256889195269)
                  ·
                    refine ⟨2593229980119985666724113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13830559893973256889195269 2593229980119985666724113)
                    ·
                      refine ⟨1944922485089989250043085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593229980119985666724113 1944922485089989250043085)
                      ·
                        rfl

theorem cell23_3787723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4, 2].length) (baseStart_3787723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787723 prefixEnd_3787723 := by exact prefixLift 3787723
  have htrace : WordTrace (prefixWord ++ tailWord_3787723) baseStart_3787723 baseEnd_3787723 := by
    simpa [prefixWord, tailWord_3787723, baseEnd_3787723] using wordTrace_append hprefix tailTrace_3787723
  have hstable : (prefixWord ++ tailWord_3787723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787723).length < 2 ^ (prefixWord ++ tailWord_3787723).sum := by decide
  have hdescent : baseEnd_3787723 < baseStart_3787723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787774 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3787774 : Nat := 118140960795 + 3787774 * 2 ^ 59
def prefixEnd_3787774 : Nat := 4983230072969 + 3 ^ 40 * 3787774 * 2
def baseEnd_3787774 : Nat := 1944948672603368550505351

theorem tailTrace_3787774 : CollatzResearch.WordTrace tailWord_3787774 prefixEnd_3787774 1944948672603368550505351 := by
  unfold tailWord_3787774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268933422443646642743297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92100978253032782094630917 17268933422443646642743297)
  ·
    refine ⟨12951700066832734982057473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17268933422443646642743297 12951700066832734982057473)
    ·
      refine ⟨9713775050124551236543105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12951700066832734982057473 9713775050124551236543105)
      ·
        refine ⟨7285331287593413427407329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9713775050124551236543105 7285331287593413427407329)
        ·
          refine ⟨5463998465695060070555497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285331287593413427407329 5463998465695060070555497)
          ·
            refine ⟨4097998849271295052916623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5463998465695060070555497 4097998849271295052916623)
            ·
              refine ⟨6146998273906942579374935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097998849271295052916623 6146998273906942579374935)
              ·
                refine ⟨9220497410860413869062403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146998273906942579374935 9220497410860413869062403)
                ·
                  refine ⟨13830746116290620803593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220497410860413869062403 13830746116290620803593605)
                  ·
                    refine ⟨2593264896804491400673801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13830746116290620803593605 2593264896804491400673801)
                    ·
                      refine ⟨1944948672603368550505351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593264896804491400673801 1944948672603368550505351)
                      ·
                        rfl

theorem cell23_3787774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3787774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787774 prefixEnd_3787774 := by exact prefixLift 3787774
  have htrace : WordTrace (prefixWord ++ tailWord_3787774) baseStart_3787774 baseEnd_3787774 := by
    simpa [prefixWord, tailWord_3787774, baseEnd_3787774] using wordTrace_append hprefix tailTrace_3787774
  have hstable : (prefixWord ++ tailWord_3787774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787774).length < 2 ^ (prefixWord ++ tailWord_3787774).sum := by decide
  have hdescent : baseEnd_3787774 < baseStart_3787774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787813 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3787813 : Nat := 118140960795 + 3787813 * 2 ^ 59
def prefixEnd_3787813 : Nat := 4983230072969 + 3 ^ 40 * 3787813 * 2
def baseEnd_3787813 : Nat := 1944968698348893897917671

theorem tailTrace_3787813 : CollatzResearch.WordTrace tailWord_3787813 prefixEnd_3787813 1944968698348893897917671 := by
  unfold tailWord_3787813
  simp only [CollatzResearch.WordTrace]
  refine ⟨138152889826407882802616093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92101926550938588535077395 138152889826407882802616093)
  ·
    refine ⟨51807333684902956050981035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138152889826407882802616093 51807333684902956050981035)
    ·
      refine ⟨77711000527354434076471553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51807333684902956050981035 77711000527354434076471553)
      ·
        refine ⟨58283250395515825557353665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77711000527354434076471553 58283250395515825557353665)
        ·
          refine ⟨43712437796636869168015249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58283250395515825557353665 43712437796636869168015249)
          ·
            refine ⟨32784328347477651876011437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43712437796636869168015249 32784328347477651876011437)
            ·
              refine ⟨12294123130304119453504289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32784328347477651876011437 12294123130304119453504289)
              ·
                refine ⟨9220592347728089590128217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294123130304119453504289 9220592347728089590128217)
                ·
                  refine ⟨6915444260796067192596163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9220592347728089590128217 6915444260796067192596163)
                  ·
                    refine ⟨10373166391194100788894245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915444260796067192596163 10373166391194100788894245)
                    ·
                      refine ⟨1944968698348893897917671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10373166391194100788894245 1944968698348893897917671)
                      ·
                        rfl

theorem cell23_3787813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3787813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787813 prefixEnd_3787813 := by exact prefixLift 3787813
  have htrace : WordTrace (prefixWord ++ tailWord_3787813) baseStart_3787813 baseEnd_3787813 := by
    simpa [prefixWord, tailWord_3787813, baseEnd_3787813] using wordTrace_append hprefix tailTrace_3787813
  have hstable : (prefixWord ++ tailWord_3787813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787813).length < 2 ^ (prefixWord ++ tailWord_3787813).sum := by decide
  have hdescent : baseEnd_3787813 < baseStart_3787813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787874 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3787874 : Nat := 118140960795 + 3787874 * 2 ^ 59
def prefixEnd_3787874 : Nat := 4983230072969 + 3 ^ 40 * 3787874 * 2
def baseEnd_3787874 : Nat := 648333340222939386418297

theorem tailTrace_3787874 : CollatzResearch.WordTrace tailWord_3787874 prefixEnd_3787874 648333340222939386418297 := by
  unfold tailWord_3787874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34538778669796722555146669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92103409786124593480391117 34538778669796722555146669)
  ·
    refine ⟨12952042001173770958180001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34538778669796722555146669 12952042001173770958180001)
    ·
      refine ⟨9714031500880328218635001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12952042001173770958180001 9714031500880328218635001)
      ·
        refine ⟨7285523625660246163976251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9714031500880328218635001 7285523625660246163976251)
        ·
          refine ⟨10928285438490369245964377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285523625660246163976251 10928285438490369245964377)
          ·
            refine ⟨8196214078867776934473283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10928285438490369245964377 8196214078867776934473283)
            ·
              refine ⟨12294321118301665401709925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196214078867776934473283 12294321118301665401709925)
              ·
                refine ⟨2305185209681562262820611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12294321118301665401709925 2305185209681562262820611)
                ·
                  refine ⟨3457777814522343394230917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305185209681562262820611 3457777814522343394230917)
                  ·
                    refine ⟨648333340222939386418297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457777814522343394230917 648333340222939386418297)
                    ·
                      rfl

theorem cell23_3787874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3787874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787874 prefixEnd_3787874 := by exact prefixLift 3787874
  have htrace : WordTrace (prefixWord ++ tailWord_3787874) baseStart_3787874 baseEnd_3787874 := by
    simpa [prefixWord, tailWord_3787874, baseEnd_3787874] using wordTrace_append hprefix tailTrace_3787874
  have hstable : (prefixWord ++ tailWord_3787874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787874).length < 2 ^ (prefixWord ++ tailWord_3787874).sum := by decide
  have hdescent : baseEnd_3787874 < baseStart_3787874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787890 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_3787890 : Nat := 118140960795 + 3787890 * 2 ^ 59
def prefixEnd_3787890 : Nat := 4983230072969 + 3 ^ 40 * 3787890 * 2
def baseEnd_3787890 : Nat := 1945008236359290096654817

theorem tailTrace_3787890 : CollatzResearch.WordTrace tailWord_3787890 prefixEnd_3787890 1945008236359290096654817 := by
  unfold tailWord_3787890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34538924561782231238292281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92103798831419283302112749 34538924561782231238292281)
  ·
    refine ⟨25904193421336673428719211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34538924561782231238292281 25904193421336673428719211)
    ·
      refine ⟨38856290132005010143078817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904193421336673428719211 38856290132005010143078817)
      ·
        refine ⟨29142217599003757607309113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38856290132005010143078817 29142217599003757607309113)
        ·
          refine ⟨21856663199252818205481835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29142217599003757607309113 21856663199252818205481835)
          ·
            refine ⟨32784994798879227308222753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21856663199252818205481835 32784994798879227308222753)
            ·
              refine ⟨24588746099159420481167065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32784994798879227308222753 24588746099159420481167065)
              ·
                refine ⟨18441559574369565360875299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24588746099159420481167065 18441559574369565360875299)
                ·
                  refine ⟨27662339361554348041312949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18441559574369565360875299 27662339361554348041312949)
                  ·
                    refine ⟨2593344315145720128873089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27662339361554348041312949 2593344315145720128873089)
                    ·
                      refine ⟨1945008236359290096654817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593344315145720128873089 1945008236359290096654817)
                      ·
                        rfl

theorem cell23_3787890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_3787890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787890 prefixEnd_3787890 := by exact prefixLift 3787890
  have htrace : WordTrace (prefixWord ++ tailWord_3787890) baseStart_3787890 baseEnd_3787890 := by
    simpa [prefixWord, tailWord_3787890, baseEnd_3787890] using wordTrace_append hprefix tailTrace_3787890
  have hstable : (prefixWord ++ tailWord_3787890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787890).length < 2 ^ (prefixWord ++ tailWord_3787890).sum := by decide
  have hdescent : baseEnd_3787890 < baseStart_3787890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787897 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3787897 : Nat := 118140960795 + 3787897 * 2 ^ 59
def prefixEnd_3787897 : Nat := 4983230072969 + 3 ^ 40 * 3787897 * 2
def baseEnd_3787897 : Nat := 1945011830723871569267285

theorem tailTrace_3787897 : CollatzResearch.WordTrace tailWord_3787897 prefixEnd_3787897 1945011830723871569267285 := by
  unfold tailWord_3787897
  simp only [CollatzResearch.WordTrace]
  refine ⟨138155953558103565148673945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92103969038735710099115963 138155953558103565148673945)
  ·
    refine ⟨103616965168577673861505459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138155953558103565148673945 103616965168577673861505459)
    ·
      refine ⟨155425447752866510792258189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103616965168577673861505459 155425447752866510792258189)
      ·
        refine ⟨58284542907324941547096821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155425447752866510792258189 58284542907324941547096821)
        ·
          refine ⟨5464175897561713270040327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58284542907324941547096821 5464175897561713270040327)
          ·
            refine ⟨8196263846342569905060491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464175897561713270040327 8196263846342569905060491)
            ·
              refine ⟨12294395769513854857590737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196263846342569905060491 12294395769513854857590737)
              ·
                refine ⟨9220796827135391143193053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294395769513854857590737 9220796827135391143193053)
                ·
                  refine ⟨3457798810175771678697395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9220796827135391143193053 3457798810175771678697395)
                  ·
                    refine ⟨5186698215263657518046093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457798810175771678697395 5186698215263657518046093)
                    ·
                      refine ⟨1945011830723871569267285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186698215263657518046093 1945011830723871569267285)
                      ·
                        rfl

theorem cell23_3787897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3787897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787897 prefixEnd_3787897 := by exact prefixLift 3787897
  have htrace : WordTrace (prefixWord ++ tailWord_3787897) baseStart_3787897 baseEnd_3787897 := by
    simpa [prefixWord, tailWord_3787897, baseEnd_3787897] using wordTrace_append hprefix tailTrace_3787897
  have hstable : (prefixWord ++ tailWord_3787897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787897).length < 2 ^ (prefixWord ++ tailWord_3787897).sum := by decide
  have hdescent : baseEnd_3787897 < baseStart_3787897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787913 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_3787913 : Nat := 118140960795 + 3787913 * 2 ^ 59
def prefixEnd_3787913 : Nat := 4983230072969 + 3 ^ 40 * 3787913 * 2
def baseEnd_3787913 : Nat := 648340015471447835555737

theorem tailTrace_3787913 : CollatzResearch.WordTrace tailWord_3787913 prefixEnd_3787913 648340015471447835555737 := by
  unfold tailWord_3787913
  simp only [CollatzResearch.WordTrace]
  refine ⟨138156537126045599881256393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92104358084030399920837595 138156537126045599881256393)
  ·
    refine ⟨103617402844534199910942295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138156537126045599881256393 103617402844534199910942295)
    ·
      refine ⟨155426104266801299866413443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103617402844534199910942295 155426104266801299866413443)
      ·
        refine ⟨233139156400201949799620165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155426104266801299866413443 233139156400201949799620165)
        ·
          refine ⟨43713591825037865587428781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233139156400201949799620165 43713591825037865587428781)
          ·
            refine ⟨16392596934389199595285793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43713591825037865587428781 16392596934389199595285793)
            ·
              refine ⟨12294447700791899696464345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16392596934389199595285793 12294447700791899696464345)
              ·
                refine ⟨9220835775593924772348259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294447700791899696464345 9220835775593924772348259)
                ·
                  refine ⟨13831253663390887158522389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220835775593924772348259 13831253663390887158522389)
                  ·
                    refine ⟨648340015471447835555737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13831253663390887158522389 648340015471447835555737)
                    ·
                      rfl

theorem cell23_3787913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_3787913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787913 prefixEnd_3787913 := by exact prefixLift 3787913
  have htrace : WordTrace (prefixWord ++ tailWord_3787913) baseStart_3787913 baseEnd_3787913 := by
    simpa [prefixWord, tailWord_3787913, baseEnd_3787913] using wordTrace_append hprefix tailTrace_3787913
  have hstable : (prefixWord ++ tailWord_3787913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787913).length < 2 ^ (prefixWord ++ tailWord_3787913).sum := by decide
  have hdescent : baseEnd_3787913 < baseStart_3787913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787914 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_3787914 : Nat := 118140960795 + 3787914 * 2 ^ 59
def prefixEnd_3787914 : Nat := 4983230072969 + 3 ^ 40 * 3787914 * 2
def baseEnd_3787914 : Nat := 1945020559894998002754707

theorem tailTrace_3787914 : CollatzResearch.WordTrace tailWord_3787914 prefixEnd_3787914 1945020559894998002754707 := by
  unfold tailWord_3787914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539143399760494263010699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92104382399361318034695197 34539143399760494263010699)
  ·
    refine ⟨51808715099640741394516049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539143399760494263010699 51808715099640741394516049)
    ·
      refine ⟨38856536324730556045887037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51808715099640741394516049 38856536324730556045887037)
      ·
        refine ⟨14571201121773958517207639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38856536324730556045887037 14571201121773958517207639)
        ·
          refine ⟨21856801682660937775811459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14571201121773958517207639 21856801682660937775811459)
          ·
            refine ⟨32785202523991406663717189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21856801682660937775811459 32785202523991406663717189)
            ·
              refine ⟨6147225473248388749446973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32785202523991406663717189 6147225473248388749446973)
              ·
                refine ⟨2305209552468145781042615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6147225473248388749446973 2305209552468145781042615)
                ·
                  refine ⟨3457814328702218671563923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305209552468145781042615 3457814328702218671563923)
                  ·
                    refine ⟨5186721493053328007345885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457814328702218671563923 5186721493053328007345885)
                    ·
                      refine ⟨1945020559894998002754707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186721493053328007345885 1945020559894998002754707)
                      ·
                        rfl

theorem cell23_3787914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_3787914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787914 prefixEnd_3787914 := by exact prefixLift 3787914
  have htrace : WordTrace (prefixWord ++ tailWord_3787914) baseStart_3787914 baseEnd_3787914 := by
    simpa [prefixWord, tailWord_3787914, baseEnd_3787914] using wordTrace_append hprefix tailTrace_3787914
  have hstable : (prefixWord ++ tailWord_3787914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787914).length < 2 ^ (prefixWord ++ tailWord_3787914).sum := by decide
  have hdescent : baseEnd_3787914 < baseStart_3787914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787933 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3787933 : Nat := 118140960795 + 3787933 * 2 ^ 59
def prefixEnd_3787933 : Nat := 4983230072969 + 3 ^ 40 * 3787933 * 2
def baseEnd_3787933 : Nat := 1945030316027433428417119

theorem tailTrace_3787933 : CollatzResearch.WordTrace tailWord_3787933 prefixEnd_3787933 1945030316027433428417119 := by
  unfold tailWord_3787933
  simp only [CollatzResearch.WordTrace]
  refine ⟨138157266585973143296984453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92104844390648762197989635 138157266585973143296984453)
  ·
    refine ⟨25904487484869964368184585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138157266585973143296984453 25904487484869964368184585)
    ·
      refine ⟨19428365613652473276138439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25904487484869964368184585 19428365613652473276138439)
      ·
        refine ⟨29142548420478709914207659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428365613652473276138439 29142548420478709914207659)
        ·
          refine ⟨43713822630718064871311489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29142548420478709914207659 43713822630718064871311489)
          ·
            refine ⟨32785366973038548653483617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43713822630718064871311489 32785366973038548653483617)
            ·
              refine ⟨24589025229778911490112713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32785366973038548653483617 24589025229778911490112713)
              ·
                refine ⟨18441768922334183617584535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24589025229778911490112713 18441768922334183617584535)
                ·
                  refine ⟨27662653383501275426376803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18441768922334183617584535 27662653383501275426376803)
                  ·
                    refine ⟨41493980075251913139565205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27662653383501275426376803 41493980075251913139565205)
                    ·
                      refine ⟨1945030316027433428417119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41493980075251913139565205 1945030316027433428417119)
                      ·
                        rfl

theorem cell23_3787933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3787933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787933 prefixEnd_3787933 := by exact prefixLift 3787933
  have htrace : WordTrace (prefixWord ++ tailWord_3787933) baseStart_3787933 baseEnd_3787933 := by
    simpa [prefixWord, tailWord_3787933, baseEnd_3787933] using wordTrace_append hprefix tailTrace_3787933
  have hstable : (prefixWord ++ tailWord_3787933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787933).length < 2 ^ (prefixWord ++ tailWord_3787933).sum := by decide
  have hdescent : baseEnd_3787933 < baseStart_3787933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787940 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3787940 : Nat := 118140960795 + 3787940 * 2 ^ 59
def prefixEnd_3787940 : Nat := 4983230072969 + 3 ^ 40 * 3787940 * 2
def baseEnd_3787940 : Nat := 1945033910392014901029587

theorem tailTrace_3787940 : CollatzResearch.WordTrace tailWord_3787940 prefixEnd_3787940 1945033910392014901029587 := by
  unfold tailWord_3787940
  simp only [CollatzResearch.WordTrace]
  refine ⟨69078760948473891746244637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92105014597965188994992849 69078760948473891746244637)
  ·
    refine ⟨25904535355677709404841739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69078760948473891746244637 25904535355677709404841739)
    ·
      refine ⟨38856803033516564107262609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904535355677709404841739 38856803033516564107262609)
      ·
        refine ⟨29142602275137423080446957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38856803033516564107262609 29142602275137423080446957)
        ·
          refine ⟨10928475853176533655167609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29142602275137423080446957 10928475853176533655167609)
          ·
            refine ⟨8196356889882400241375707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10928475853176533655167609 8196356889882400241375707)
            ·
              refine ⟨12294535334823600362063561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196356889882400241375707 12294535334823600362063561)
              ·
                refine ⟨9220901501117700271547671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294535334823600362063561 9220901501117700271547671)
                ·
                  refine ⟨13831352251676550407321507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220901501117700271547671 13831352251676550407321507)
                  ·
                    refine ⟨20747028377514825610982261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13831352251676550407321507 20747028377514825610982261)
                    ·
                      refine ⟨1945033910392014901029587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20747028377514825610982261 1945033910392014901029587)
                      ·
                        rfl

theorem cell23_3787940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3787940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787940 prefixEnd_3787940 := by exact prefixLift 3787940
  have htrace : WordTrace (prefixWord ++ tailWord_3787940) baseStart_3787940 baseEnd_3787940 := by
    simpa [prefixWord, tailWord_3787940, baseEnd_3787940] using wordTrace_append hprefix tailTrace_3787940
  have hstable : (prefixWord ++ tailWord_3787940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787940).length < 2 ^ (prefixWord ++ tailWord_3787940).sum := by decide
  have hdescent : baseEnd_3787940 < baseStart_3787940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787988 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3787988 : Nat := 118140960795 + 3787988 * 2 ^ 59
def prefixEnd_3787988 : Nat := 4983230072969 + 3 ^ 40 * 3787988 * 2
def baseEnd_3787988 : Nat := 1945058557463430713229367

theorem tailTrace_3787988 : CollatzResearch.WordTrace tailWord_3787988 prefixEnd_3787988 1945058557463430713229367 := by
  unfold tailWord_3787988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69079636300386943845118309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92106181733849258460157745 69079636300386943845118309)
  ·
    refine ⟨12952431806322551970959683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69079636300386943845118309 12952431806322551970959683)
    ·
      refine ⟨19428647709483827956439525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12952431806322551970959683 19428647709483827956439525)
      ·
        refine ⟨3642871445528217741832411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19428647709483827956439525 3642871445528217741832411)
        ·
          refine ⟨5464307168292326612748617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642871445528217741832411 5464307168292326612748617)
          ·
            refine ⟨4098230376219244959561463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464307168292326612748617 4098230376219244959561463)
            ·
              refine ⟨6147345564328867439342195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098230376219244959561463 6147345564328867439342195)
              ·
                refine ⟨9221018346493301159013293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147345564328867439342195 9221018346493301159013293)
                ·
                  refine ⟨3457881879934987934629985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9221018346493301159013293 3457881879934987934629985)
                  ·
                    refine ⟨2593411409951240950972489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457881879934987934629985 2593411409951240950972489)
                    ·
                      refine ⟨1945058557463430713229367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593411409951240950972489 1945058557463430713229367)
                      ·
                        rfl

theorem cell23_3787988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3787988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787988 prefixEnd_3787988 := by exact prefixLift 3787988
  have htrace : WordTrace (prefixWord ++ tailWord_3787988) baseStart_3787988 baseEnd_3787988 := by
    simpa [prefixWord, tailWord_3787988, baseEnd_3787988] using wordTrace_append hprefix tailTrace_3787988
  have hstable : (prefixWord ++ tailWord_3787988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787988).length < 2 ^ (prefixWord ++ tailWord_3787988).sum := by decide
  have hdescent : baseEnd_3787988 < baseStart_3787988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787993 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_3787993 : Nat := 118140960795 + 3787993 * 2 ^ 59
def prefixEnd_3787993 : Nat := 4983230072969 + 3 ^ 40 * 3787993 * 2
def baseEnd_3787993 : Nat := 1945061124866703193666843

theorem tailTrace_3787993 : CollatzResearch.WordTrace tailWord_3787993 prefixEnd_3787993 1945061124866703193666843 := by
  unfold tailWord_3787993
  simp only [CollatzResearch.WordTrace]
  refine ⟨138159454965755773544168633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92106303310503849029445755 138159454965755773544168633)
  ·
    refine ⟨103619591224316830158126475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138159454965755773544168633 103619591224316830158126475)
    ·
      refine ⟨155429386836475245237189713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103619591224316830158126475 155429386836475245237189713)
      ·
        refine ⟨116572040127356433927892285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155429386836475245237189713 116572040127356433927892285)
        ·
          refine ⟨43714515047758662722959607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116572040127356433927892285 43714515047758662722959607)
          ·
            refine ⟨65571772571637994084439411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43714515047758662722959607 65571772571637994084439411)
            ·
              refine ⟨98357658857456991126659117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65571772571637994084439411 98357658857456991126659117)
              ·
                refine ⟨36884122071546371672497169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98357658857456991126659117 36884122071546371672497169)
                ·
                  refine ⟨27663091553659778754372877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36884122071546371672497169 27663091553659778754372877)
                  ·
                    refine ⟨10373659332622417032889829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27663091553659778754372877 10373659332622417032889829)
                    ·
                      refine ⟨1945061124866703193666843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10373659332622417032889829 1945061124866703193666843)
                      ·
                        rfl

theorem cell23_3787993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_3787993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3787993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3787993 prefixEnd_3787993 := by exact prefixLift 3787993
  have htrace : WordTrace (prefixWord ++ tailWord_3787993) baseStart_3787993 baseEnd_3787993 := by
    simpa [prefixWord, tailWord_3787993, baseEnd_3787993] using wordTrace_append hprefix tailTrace_3787993
  have hstable : (prefixWord ++ tailWord_3787993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787993).length < 2 ^ (prefixWord ++ tailWord_3787993).sum := by decide
  have hdescent : baseEnd_3787993 < baseStart_3787993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788004 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_3788004 : Nat := 118140960795 + 3788004 * 2 ^ 59
def prefixEnd_3788004 : Nat := 4983230072969 + 3 ^ 40 * 3788004 * 2
def baseEnd_3788004 : Nat := 1945066773153902650629293

theorem tailTrace_3788004 : CollatzResearch.WordTrace tailWord_3788004 prefixEnd_3788004 1945066773153902650629293 := by
  unfold tailWord_3788004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69079928084357961211409533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92106570779143948281879377 69079928084357961211409533)
  ·
    refine ⟨25904973031634235454278575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69079928084357961211409533 25904973031634235454278575)
    ·
      refine ⟨38857459547451353181417863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904973031634235454278575 38857459547451353181417863)
      ·
        refine ⟨58286189321177029772126795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38857459547451353181417863 58286189321177029772126795)
        ·
          refine ⟨87429283981765544658190193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58286189321177029772126795 87429283981765544658190193)
          ·
            refine ⟨65571962986324158493642645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87429283981765544658190193 65571962986324158493642645)
            ·
              refine ⟨3073685764983944929389499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65571962986324158493642645 3073685764983944929389499)
              ·
                refine ⟨4610528647475917394084249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073685764983944929389499 4610528647475917394084249)
                ·
                  refine ⟨3457896485606938045563187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610528647475917394084249 3457896485606938045563187)
                  ·
                    refine ⟨5186844728410407068344781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3457896485606938045563187 5186844728410407068344781)
                    ·
                      refine ⟨1945066773153902650629293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186844728410407068344781 1945066773153902650629293)
                      ·
                        rfl

theorem cell23_3788004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_3788004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788004 prefixEnd_3788004 := by exact prefixLift 3788004
  have htrace : WordTrace (prefixWord ++ tailWord_3788004) baseStart_3788004 baseEnd_3788004 := by
    simpa [prefixWord, tailWord_3788004, baseEnd_3788004] using wordTrace_append hprefix tailTrace_3788004
  have hstable : (prefixWord ++ tailWord_3788004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788004).length < 2 ^ (prefixWord ++ tailWord_3788004).sum := by decide
  have hdescent : baseEnd_3788004 < baseStart_3788004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788014 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_3788014 : Nat := 118140960795 + 3788014 * 2 ^ 59
def prefixEnd_3788014 : Nat := 4983230072969 + 3 ^ 40 * 3788014 * 2
def baseEnd_3788014 : Nat := 1945071907960447611504247

theorem tailTrace_3788014 : CollatzResearch.WordTrace tailWord_3788014 prefixEnd_3788014 1945071907960447611504247 := by
  unfold tailWord_3788014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270027612334961766335387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92106813932453129420455397 17270027612334961766335387)
  ·
    refine ⟨25905041418502442649503081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17270027612334961766335387 25905041418502442649503081)
    ·
      refine ⟨19428781063876831987127311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25905041418502442649503081 19428781063876831987127311)
      ·
        refine ⟨29143171595815247980690967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428781063876831987127311 29143171595815247980690967)
        ·
          refine ⟨43714757393722871971036451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143171595815247980690967 43714757393722871971036451)
          ·
            refine ⟨65572136090584307956554677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43714757393722871971036451 65572136090584307956554677)
            ·
              refine ⟨6147387758492278870927001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65572136090584307956554677 6147387758492278870927001)
              ·
                refine ⟨4610540818869209153195251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6147387758492278870927001 4610540818869209153195251)
                ·
                  refine ⟨6915811228303813729792877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610540818869209153195251 6915811228303813729792877)
                  ·
                    refine ⟨2593429210613930148672329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6915811228303813729792877 2593429210613930148672329)
                    ·
                      refine ⟨1945071907960447611504247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593429210613930148672329 1945071907960447611504247)
                      ·
                        rfl

theorem cell23_3788014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_3788014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788014 prefixEnd_3788014 := by exact prefixLift 3788014
  have htrace : WordTrace (prefixWord ++ tailWord_3788014) baseStart_3788014 baseEnd_3788014 := by
    simpa [prefixWord, tailWord_3788014, baseEnd_3788014] using wordTrace_append hprefix tailTrace_3788014
  have hstable : (prefixWord ++ tailWord_3788014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788014).length < 2 ^ (prefixWord ++ tailWord_3788014).sum := by decide
  have hdescent : baseEnd_3788014 < baseStart_3788014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788023 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3788023 : Nat := 118140960795 + 3788023 * 2 ^ 59
def prefixEnd_3788023 : Nat := 4983230072969 + 3 ^ 40 * 3788023 * 2
def baseEnd_3788023 : Nat := 1945076529286338076291705

theorem tailTrace_3788023 : CollatzResearch.WordTrace tailWord_3788023 prefixEnd_3788023 1945076529286338076291705 := by
  unfold tailWord_3788023
  simp only [CollatzResearch.WordTrace]
  refine ⟨138160549155647088667760723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92107032770431392445173815 138160549155647088667760723)
  ·
    refine ⟨207240823733470633001641085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138160549155647088667760723 207240823733470633001641085)
    ·
      refine ⟨77715308900051487375615407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207240823733470633001641085 77715308900051487375615407)
      ·
        refine ⟨116572963350077231063423111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77715308900051487375615407 116572963350077231063423111)
        ·
          refine ⟨174859445025115846595134667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116572963350077231063423111 174859445025115846595134667)
          ·
            refine ⟨262289167537673769892702001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174859445025115846595134667 262289167537673769892702001)
            ·
              refine ⟨196716875653255327419526501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262289167537673769892702001 196716875653255327419526501)
              ·
                refine ⟨36884414184985373891161219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196716875653255327419526501 36884414184985373891161219)
                ·
                  refine ⟨55326621277478060836741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36884414184985373891161219 55326621277478060836741829)
                  ·
                    refine ⟨10373741489527136406889093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55326621277478060836741829 10373741489527136406889093)
                    ·
                      refine ⟨1945076529286338076291705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10373741489527136406889093 1945076529286338076291705)
                      ·
                        rfl

theorem cell23_3788023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3788023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788023 prefixEnd_3788023 := by exact prefixLift 3788023
  have htrace : WordTrace (prefixWord ++ tailWord_3788023) baseStart_3788023 baseEnd_3788023 := by
    simpa [prefixWord, tailWord_3788023, baseEnd_3788023] using wordTrace_append hprefix tailTrace_3788023
  have hstable : (prefixWord ++ tailWord_3788023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788023).length < 2 ^ (prefixWord ++ tailWord_3788023).sum := by decide
  have hdescent : baseEnd_3788023 < baseStart_3788023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788044 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_3788044 : Nat := 118140960795 + 3788044 * 2 ^ 59
def prefixEnd_3788044 : Nat := 4983230072969 + 3 ^ 40 * 3788044 * 2
def baseEnd_3788044 : Nat := 1945087312380082494129109

theorem tailTrace_3788044 : CollatzResearch.WordTrace tailWord_3788044 prefixEnd_3788044 1945087312380082494129109 := by
  unfold tailWord_3788044
  simp only [CollatzResearch.WordTrace]
  refine ⟨69080657544285504627137593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92107543392380672836183457 69080657544285504627137593)
  ·
    refine ⟨51810493158214128470353195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69080657544285504627137593 51810493158214128470353195)
    ·
      refine ⟨77715739737321192705529793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51810493158214128470353195 77715739737321192705529793)
      ·
        refine ⟨58286804802990894529147345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77715739737321192705529793 58286804802990894529147345)
        ·
          refine ⟨43715103602243170896860509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58286804802990894529147345 43715103602243170896860509)
          ·
            refine ⟨16393163850841189086322691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43715103602243170896860509 16393163850841189086322691)
            ·
              refine ⟨24589745776261783629484037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16393163850841189086322691 24589745776261783629484037)
              ·
                refine ⟨4610577333049084430528257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24589745776261783629484037 4610577333049084430528257)
                ·
                  refine ⟨3457932999786813322896193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610577333049084430528257 3457932999786813322896193)
                  ·
                    refine ⟨2593449749840109992172145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457932999786813322896193 2593449749840109992172145)
                    ·
                      refine ⟨1945087312380082494129109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593449749840109992172145 1945087312380082494129109)
                      ·
                        rfl

theorem cell23_3788044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_3788044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788044 prefixEnd_3788044 := by exact prefixLift 3788044
  have htrace : WordTrace (prefixWord ++ tailWord_3788044) baseStart_3788044 baseEnd_3788044 := by
    simpa [prefixWord, tailWord_3788044, baseEnd_3788044] using wordTrace_append hprefix tailTrace_3788044
  have hstable : (prefixWord ++ tailWord_3788044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788044).length < 2 ^ (prefixWord ++ tailWord_3788044).sum := by decide
  have hdescent : baseEnd_3788044 < baseStart_3788044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788053 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3788053 : Nat := 118140960795 + 3788053 * 2 ^ 59
def prefixEnd_3788053 : Nat := 4983230072969 + 3 ^ 40 * 3788053 * 2
def baseEnd_3788053 : Nat := 1945091933705972958916567

theorem tailTrace_3788053 : CollatzResearch.WordTrace tailWord_3788053 prefixEnd_3788053 1945091933705972958916567 := by
  unfold tailWord_3788053
  simp only [CollatzResearch.WordTrace]
  refine ⟨138161643345538403791352813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92107762230358935860901875 138161643345538403791352813)
  ·
    refine ⟨51810616254576901421757305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138161643345538403791352813 51810616254576901421757305)
    ·
      refine ⟨38857962190932676066317979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51810616254576901421757305 38857962190932676066317979)
      ·
        refine ⟨58286943286399014099476969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38857962190932676066317979 58286943286399014099476969)
        ·
          refine ⟨43715207464799260574607727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58286943286399014099476969 43715207464799260574607727)
          ·
            refine ⟨65572811197198890861911591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43715207464799260574607727 65572811197198890861911591)
            ·
              refine ⟨98359216795798336292867387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65572811197198890861911591 98359216795798336292867387)
              ·
                refine ⟨147538825193697504439301081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98359216795798336292867387 147538825193697504439301081)
                ·
                  refine ⟨110654118895273128329475811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147538825193697504439301081 110654118895273128329475811)
                  ·
                    refine ⟨165981178342909692494213717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110654118895273128329475811 165981178342909692494213717)
                    ·
                      refine ⟨1945091933705972958916567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 165981178342909692494213717 1945091933705972958916567)
                      ·
                        rfl

theorem cell23_3788053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3788053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788053 prefixEnd_3788053 := by exact prefixLift 3788053
  have htrace : WordTrace (prefixWord ++ tailWord_3788053) baseStart_3788053 baseEnd_3788053 := by
    simpa [prefixWord, tailWord_3788053, baseEnd_3788053] using wordTrace_append hprefix tailTrace_3788053
  have hstable : (prefixWord ++ tailWord_3788053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788053).length < 2 ^ (prefixWord ++ tailWord_3788053).sum := by decide
  have hdescent : baseEnd_3788053 < baseStart_3788053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788060 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3788060 : Nat := 118140960795 + 3788060 * 2 ^ 59
def prefixEnd_3788060 : Nat := 4983230072969 + 3 ^ 40 * 3788060 * 2
def baseEnd_3788060 : Nat := 1945095528070554431529035

theorem tailTrace_3788060 : CollatzResearch.WordTrace tailWord_3788060 prefixEnd_3788060 1945095528070554431529035 := by
  unfold tailWord_3788060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69080949328256521993428817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92107932437675362657905089 69080949328256521993428817)
  ·
    refine ⟨51810711996192391495071613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69080949328256521993428817 51810711996192391495071613)
    ·
      refine ⟨19429016998572146810651855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51810711996192391495071613 19429016998572146810651855)
      ·
        refine ⟨29143525497858220215977783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429016998572146810651855 29143525497858220215977783)
        ·
          refine ⟨43715288246787330323966675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143525497858220215977783 43715288246787330323966675)
          ·
            refine ⟨65572932370180995485950013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43715288246787330323966675 65572932370180995485950013)
            ·
              refine ⟨24589849638817873307231255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65572932370180995485950013 24589849638817873307231255)
              ·
                refine ⟨36884774458226809960846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24589849638817873307231255 36884774458226809960846883)
                ·
                  refine ⟨55327161687340214941270325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36884774458226809960846883 55327161687340214941270325)
                  ·
                    refine ⟨5186921408188145150744093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55327161687340214941270325 5186921408188145150744093)
                    ·
                      refine ⟨1945095528070554431529035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5186921408188145150744093 1945095528070554431529035)
                      ·
                        rfl

theorem cell23_3788060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3788060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788060 prefixEnd_3788060 := by exact prefixLift 3788060
  have htrace : WordTrace (prefixWord ++ tailWord_3788060) baseStart_3788060 baseEnd_3788060 := by
    simpa [prefixWord, tailWord_3788060, baseEnd_3788060] using wordTrace_append hprefix tailTrace_3788060
  have hstable : (prefixWord ++ tailWord_3788060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788060).length < 2 ^ (prefixWord ++ tailWord_3788060).sum := by decide
  have hdescent : baseEnd_3788060 < baseStart_3788060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788061 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3788061 : Nat := 118140960795 + 3788061 * 2 ^ 59
def prefixEnd_3788061 : Nat := 4983230072969 + 3 ^ 40 * 3788061 * 2
def baseEnd_3788061 : Nat := 1945096041551208927616531

theorem tailTrace_3788061 : CollatzResearch.WordTrace tailWord_3788061 prefixEnd_3788061 1945096041551208927616531 := by
  unfold tailWord_3788061
  simp only [CollatzResearch.WordTrace]
  refine ⟨138161935129509421157644037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92107956753006280771762691 138161935129509421157644037)
  ·
    refine ⟨25905362836783016467058257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138161935129509421157644037 25905362836783016467058257)
    ·
      refine ⟨19429022127587262350293693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25905362836783016467058257 19429022127587262350293693)
      ·
        refine ⟨7285883297845223381360135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19429022127587262350293693 7285883297845223381360135)
        ·
          refine ⟨10928824946767835072040203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285883297845223381360135 10928824946767835072040203)
          ·
            refine ⟨16393237420151752608060305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10928824946767835072040203 16393237420151752608060305)
            ·
              refine ⟨12294928065113814456045229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16393237420151752608060305 12294928065113814456045229)
              ·
                refine ⟨4610598024417680421016961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12294928065113814456045229 4610598024417680421016961)
                ·
                  refine ⟨3457948518313260315762721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610598024417680421016961 3457948518313260315762721)
                  ·
                    refine ⟨2593461388734945236822041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457948518313260315762721 2593461388734945236822041)
                    ·
                      refine ⟨1945096041551208927616531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593461388734945236822041 1945096041551208927616531)
                      ·
                        rfl

theorem cell23_3788061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3788061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788061 prefixEnd_3788061 := by exact prefixLift 3788061
  have htrace : WordTrace (prefixWord ++ tailWord_3788061) baseStart_3788061 baseEnd_3788061 := by
    simpa [prefixWord, tailWord_3788061, baseEnd_3788061] using wordTrace_append hprefix tailTrace_3788061
  have hstable : (prefixWord ++ tailWord_3788061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788061).length < 2 ^ (prefixWord ++ tailWord_3788061).sum := by decide
  have hdescent : baseEnd_3788061 < baseStart_3788061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788084 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3788084 : Nat := 118140960795 + 3788084 * 2 ^ 59
def prefixEnd_3788084 : Nat := 4983230072969 + 3 ^ 40 * 3788084 * 2
def baseEnd_3788084 : Nat := 216123094622918037514325

theorem tailTrace_3788084 : CollatzResearch.WordTrace tailWord_3788084 prefixEnd_3788084 216123094622918037514325 := by
  unfold tailWord_3788084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69081387004213048042865653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92108516005617397390487537 69081387004213048042865653)
  ·
    refine ⟨6476380031644973254018655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69081387004213048042865653 6476380031644973254018655)
    ·
      refine ⟨9714570047467459881027983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6476380031644973254018655 9714570047467459881027983)
      ·
        refine ⟨14571855071201189821541975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9714570047467459881027983 14571855071201189821541975)
        ·
          refine ⟨21857782606801784732312963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14571855071201189821541975 21857782606801784732312963)
          ·
            refine ⟨32786673910202677098469445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857782606801784732312963 32786673910202677098469445)
            ·
              refine ⟨6147501358163001955963021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32786673910202677098469445 6147501358163001955963021)
              ·
                refine ⟨2305313009311125733486133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6147501358163001955963021 2305313009311125733486133)
                ·
                  refine ⟨216123094622918037514325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2305313009311125733486133 216123094622918037514325)
                  ·
                    rfl

theorem cell23_3788084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3788084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788084 prefixEnd_3788084 := by exact prefixLift 3788084
  have htrace : WordTrace (prefixWord ++ tailWord_3788084) baseStart_3788084 baseEnd_3788084 := by
    simpa [prefixWord, tailWord_3788084, baseEnd_3788084] using wordTrace_append hprefix tailTrace_3788084
  have hstable : (prefixWord ++ tailWord_3788084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788084).length < 2 ^ (prefixWord ++ tailWord_3788084).sum := by decide
  have hdescent : baseEnd_3788084 < baseStart_3788084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788120 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3788120 : Nat := 118140960795 + 3788120 * 2 ^ 59
def prefixEnd_3788120 : Nat := 4983230072969 + 3 ^ 40 * 3788120 * 2
def baseEnd_3788120 : Nat := 1945126336909824196778759

theorem tailTrace_3788120 : CollatzResearch.WordTrace tailWord_3788120 prefixEnd_3788120 1945126336909824196778759 := by
  unfold tailWord_3788120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082043518147837117020907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92109391357530449489361209 69082043518147837117020907)
  ·
    refine ⟨103623065277221755675531361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69082043518147837117020907 103623065277221755675531361)
    ·
      refine ⟨77717298957916316756648521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103623065277221755675531361 77717298957916316756648521)
      ·
        refine ⟨58287974218437237567486391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77717298957916316756648521 58287974218437237567486391)
        ·
          refine ⟨87431961327655856351229587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58287974218437237567486391 87431961327655856351229587)
          ·
            refine ⟨131147941991483784526844381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87431961327655856351229587 131147941991483784526844381)
            ·
              refine ⟨49180478246806419197566643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131147941991483784526844381 49180478246806419197566643)
              ·
                refine ⟨73770717370209628796349965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49180478246806419197566643 73770717370209628796349965)
                ·
                  refine ⟨27664019013828610798631237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73770717370209628796349965 27664019013828610798631237)
                  ·
                    refine ⟨5187003565092864524743357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27664019013828610798631237 5187003565092864524743357)
                    ·
                      refine ⟨1945126336909824196778759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187003565092864524743357 1945126336909824196778759)
                      ·
                        rfl

theorem cell23_3788120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3788120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788120 prefixEnd_3788120 := by exact prefixLift 3788120
  have htrace : WordTrace (prefixWord ++ tailWord_3788120) baseStart_3788120 baseEnd_3788120 := by
    simpa [prefixWord, tailWord_3788120, baseEnd_3788120] using wordTrace_append hprefix tailTrace_3788120
  have hstable : (prefixWord ++ tailWord_3788120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788120).length < 2 ^ (prefixWord ++ tailWord_3788120).sum := by decide
  have hdescent : baseEnd_3788120 < baseStart_3788120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788140 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 8]
def baseStart_3788140 : Nat := 118140960795 + 3788140 * 2 ^ 59
def prefixEnd_3788140 : Nat := 4983230072969 + 3 ^ 40 * 3788140 * 2
def baseEnd_3788140 : Nat := 216126289613657124280963

theorem tailTrace_3788140 : CollatzResearch.WordTrace tailWord_3788140 prefixEnd_3788140 216126289613657124280963 := by
  unfold tailWord_3788140
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082408248111608824884937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92109877664148811766513249 69082408248111608824884937)
  ·
    refine ⟨51811806186083706618663703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69082408248111608824884937 51811806186083706618663703)
    ·
      refine ⟨77717709279125559927995555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51811806186083706618663703 77717709279125559927995555)
      ·
        refine ⟨116576563918688339891993333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77717709279125559927995555 116576563918688339891993333)
        ·
          refine ⟨10929052867377031864874375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116576563918688339891993333 10929052867377031864874375)
          ·
            refine ⟨16393579301065547797311563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929052867377031864874375 16393579301065547797311563)
            ·
              refine ⟨24590368951598321695967345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16393579301065547797311563 24590368951598321695967345)
              ·
                refine ⟨18442776713698741271975509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24590368951598321695967345 18442776713698741271975509)
                ·
                  refine ⟨216126289613657124280963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18442776713698741271975509 216126289613657124280963)
                  ·
                    rfl

theorem cell23_3788140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_3788140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788140 prefixEnd_3788140 := by exact prefixLift 3788140
  have htrace : WordTrace (prefixWord ++ tailWord_3788140) baseStart_3788140 baseEnd_3788140 := by
    simpa [prefixWord, tailWord_3788140, baseEnd_3788140] using wordTrace_append hprefix tailTrace_3788140
  have hstable : (prefixWord ++ tailWord_3788140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788140).length < 2 ^ (prefixWord ++ tailWord_3788140).sum := by decide
  have hdescent : baseEnd_3788140 < baseStart_3788140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788161 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3788161 : Nat := 118140960795 + 3788161 * 2 ^ 59
def prefixEnd_3788161 : Nat := 4983230072969 + 3 ^ 40 * 3788161 * 2
def baseEnd_3788161 : Nat := 648382463205552845455357

theorem tailTrace_3788161 : CollatzResearch.WordTrace tailWord_3788161 prefixEnd_3788161 648382463205552845455357 := by
  unfold tailWord_3788161
  simp only [CollatzResearch.WordTrace]
  refine ⟨138165582429147138236284337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92110388286098092157522891 138165582429147138236284337)
  ·
    refine ⟨103624186821860353677213253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138165582429147138236284337 103624186821860353677213253)
    ·
      refine ⟨19429535029098816314477485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103624186821860353677213253 19429535029098816314477485)
      ·
        refine ⟨7286075635912056117929057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19429535029098816314477485 7286075635912056117929057)
        ·
          refine ⟨5464556726934042088446793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286075635912056117929057 5464556726934042088446793)
          ·
            refine ⟨4098417545200531566335095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464556726934042088446793 4098417545200531566335095)
            ·
              refine ⟨6147626317800797349502643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098417545200531566335095 6147626317800797349502643)
              ·
                refine ⟨9221439476701196024253965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147626317800797349502643 9221439476701196024253965)
                ·
                  refine ⟨3458039803762948509095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9221439476701196024253965 3458039803762948509095237)
                  ·
                    refine ⟨648382463205552845455357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458039803762948509095237 648382463205552845455357)
                    ·
                      rfl

theorem cell23_3788161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3788161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788161 prefixEnd_3788161 := by exact prefixLift 3788161
  have htrace : WordTrace (prefixWord ++ tailWord_3788161) baseStart_3788161 baseEnd_3788161 := by
    simpa [prefixWord, tailWord_3788161, baseEnd_3788161] using wordTrace_append hprefix tailTrace_3788161
  have hstable : (prefixWord ++ tailWord_3788161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788161).length < 2 ^ (prefixWord ++ tailWord_3788161).sum := by decide
  have hdescent : baseEnd_3788161 < baseStart_3788161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788174 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_3788174 : Nat := 118140960795 + 3788174 * 2 ^ 59
def prefixEnd_3788174 : Nat := 4983230072969 + 3 ^ 40 * 3788174 * 2
def baseEnd_3788174 : Nat := 216128229429462998389279

theorem tailTrace_3788174 : CollatzResearch.WordTrace tailWord_3788174 prefixEnd_3788174 216128229429462998389279 := by
  unfold tailWord_3788174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270757072262505182063447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92110704385400027637671717 17270757072262505182063447)
  ·
    refine ⟨25906135608393757773095171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17270757072262505182063447 25906135608393757773095171)
    ·
      refine ⟨38859203412590636659642757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25906135608393757773095171 38859203412590636659642757)
      ·
        refine ⟨7286100639860744373683017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38859203412590636659642757 7286100639860744373683017)
        ·
          refine ⟨5464575479895558280262263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286100639860744373683017 5464575479895558280262263)
          ·
            refine ⟨8196863219843337420393395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464575479895558280262263 8196863219843337420393395)
            ·
              refine ⟨12295294829765006130590093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196863219843337420393395 12295294829765006130590093)
              ·
                refine ⟨4610735561161877298971285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295294829765006130590093 4610735561161877298971285)
                ·
                  refine ⟨216128229429462998389279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4610735561161877298971285 216128229429462998389279)
                  ·
                    rfl

theorem cell23_3788174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_3788174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788174 prefixEnd_3788174 := by exact prefixLift 3788174
  have htrace : WordTrace (prefixWord ++ tailWord_3788174) baseStart_3788174 baseEnd_3788174 := by
    simpa [prefixWord, tailWord_3788174, baseEnd_3788174] using wordTrace_append hprefix tailTrace_3788174
  have hstable : (prefixWord ++ tailWord_3788174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788174).length < 2 ^ (prefixWord ++ tailWord_3788174).sum := by decide
  have hdescent : baseEnd_3788174 < baseStart_3788174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788207 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_3788207 : Nat := 118140960795 + 3788207 * 2 ^ 59
def prefixEnd_3788207 : Nat := 4983230072969 + 3 ^ 40 * 3788207 * 2
def baseEnd_3788207 : Nat := 1945171009726765356390859

theorem tailTrace_3788207 : CollatzResearch.WordTrace tailWord_3788207 prefixEnd_3788207 1945171009726765356390859 := by
  unfold tailWord_3788207
  simp only [CollatzResearch.WordTrace]
  refine ⟨138167260186980488092458875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92111506791320325394972583 138167260186980488092458875)
  ·
    refine ⟨207250890280470732138688313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138167260186980488092458875 207250890280470732138688313)
    ·
      refine ⟨155438167710353049104016235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207250890280470732138688313 155438167710353049104016235)
      ·
        refine ⟨233157251565529573656024353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155438167710353049104016235 233157251565529573656024353)
        ·
          refine ⟨174867938674147180242018265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233157251565529573656024353 174867938674147180242018265)
          ·
            refine ⟨131150954005610385181513699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174867938674147180242018265 131150954005610385181513699)
            ·
              refine ⟨196726431008415577772270549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131150954005610385181513699 196726431008415577772270549)
              ·
                refine ⟨4610775726759740104037591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196726431008415577772270549 4610775726759740104037591)
                ·
                  refine ⟨6916163590139610156056387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610775726759740104037591 6916163590139610156056387)
                  ·
                    refine ⟨10374245385209415234084581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916163590139610156056387 10374245385209415234084581)
                    ·
                      refine ⟨1945171009726765356390859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10374245385209415234084581 1945171009726765356390859)
                      ·
                        rfl

theorem cell23_3788207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_3788207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788207 prefixEnd_3788207 := by exact prefixLift 3788207
  have htrace : WordTrace (prefixWord ++ tailWord_3788207) baseStart_3788207 baseEnd_3788207 := by
    simpa [prefixWord, tailWord_3788207, baseEnd_3788207] using wordTrace_append hprefix tailTrace_3788207
  have hstable : (prefixWord ++ tailWord_3788207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788207).length < 2 ^ (prefixWord ++ tailWord_3788207).sum := by decide
  have hdescent : baseEnd_3788207 < baseStart_3788207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788227 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3]
def baseStart_3788227 : Nat := 118140960795 + 3788227 * 2 ^ 59
def prefixEnd_3788227 : Nat := 4983230072969 + 3 ^ 40 * 3788227 * 2
def baseEnd_3788227 : Nat := 1945181279339855278140767

theorem tailTrace_3788227 : CollatzResearch.WordTrace tailWord_3788227 prefixEnd_3788227 1945181279339855278140767 := by
  unfold tailWord_3788227
  simp only [CollatzResearch.WordTrace]
  refine ⟨138167989646908031508186935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92111993097938687672124623 138167989646908031508186935)
  ·
    refine ⟨207251984470362047262280403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138167989646908031508186935 207251984470362047262280403)
    ·
      refine ⟨310877976705543070893420605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207251984470362047262280403 310877976705543070893420605)
      ·
        refine ⟨116579241264578651585032727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310877976705543070893420605 116579241264578651585032727)
        ·
          refine ⟨174868861896867977377549091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116579241264578651585032727 174868861896867977377549091)
          ·
            refine ⟨262303292845301966066323637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174868861896867977377549091 262303292845301966066323637)
            ·
              refine ⟨24590933704247059318717841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262303292845301966066323637 24590933704247059318717841)
              ·
                refine ⟨18443200278185294489038381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24590933704247059318717841 18443200278185294489038381)
                ·
                  refine ⟨6916200104319485433389393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18443200278185294489038381 6916200104319485433389393)
                  ·
                    refine ⟨5187150078239614075042045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916200104319485433389393 5187150078239614075042045)
                    ·
                      refine ⟨1945181279339855278140767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187150078239614075042045 1945181279339855278140767)
                      ·
                        rfl

theorem cell23_3788227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_3788227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788227 prefixEnd_3788227 := by exact prefixLift 3788227
  have htrace : WordTrace (prefixWord ++ tailWord_3788227) baseStart_3788227 baseEnd_3788227 := by
    simpa [prefixWord, tailWord_3788227, baseEnd_3788227] using wordTrace_append hprefix tailTrace_3788227
  have hstable : (prefixWord ++ tailWord_3788227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788227).length < 2 ^ (prefixWord ++ tailWord_3788227).sum := by decide
  have hdescent : baseEnd_3788227 < baseStart_3788227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788234 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_3788234 : Nat := 118140960795 + 3788234 * 2 ^ 59
def prefixEnd_3788234 : Nat := 4983230072969 + 3 ^ 40 * 3788234 * 2
def baseEnd_3788234 : Nat := 648394957901478916917745

theorem tailTrace_3788234 : CollatzResearch.WordTrace tailWord_3788234 prefixEnd_3788234 648394957901478916917745 := by
  unfold tailWord_3788234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542061239470667925922939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92112163305255114469127837 34542061239470667925922939)
  ·
    refine ⟨51813091859206001888884409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34542061239470667925922939 51813091859206001888884409)
    ·
      refine ⟨38859818894404501416663307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51813091859206001888884409 38859818894404501416663307)
      ·
        refine ⟨58289728341606752124994961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38859818894404501416663307 58289728341606752124994961)
        ·
          refine ⟨43717296256205064093746221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58289728341606752124994961 43717296256205064093746221)
          ·
            refine ⟨16393986096076899035154833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43717296256205064093746221 16393986096076899035154833)
            ·
              refine ⟨12295489572057674276366125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16393986096076899035154833 12295489572057674276366125)
              ·
                refine ⟨4610808589521627853637297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295489572057674276366125 4610808589521627853637297)
                ·
                  refine ⟨3458106442141220890227973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610808589521627853637297 3458106442141220890227973)
                  ·
                    refine ⟨648394957901478916917745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458106442141220890227973 648394957901478916917745)
                    ·
                      rfl

theorem cell23_3788234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_3788234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788234 prefixEnd_3788234 := by exact prefixLift 3788234
  have htrace : WordTrace (prefixWord ++ tailWord_3788234) baseStart_3788234 baseEnd_3788234 := by
    simpa [prefixWord, tailWord_3788234, baseEnd_3788234] using wordTrace_append hprefix tailTrace_3788234
  have hstable : (prefixWord ++ tailWord_3788234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788234).length < 2 ^ (prefixWord ++ tailWord_3788234).sum := by decide
  have hdescent : baseEnd_3788234 < baseStart_3788234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788261 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3788261 : Nat := 118140960795 + 3788261 * 2 ^ 59
def prefixEnd_3788261 : Nat := 4983230072969 + 3 ^ 40 * 3788261 * 2
def baseEnd_3788261 : Nat := 1945198737682108145115611

theorem tailTrace_3788261 : CollatzResearch.WordTrace tailWord_3788261 prefixEnd_3788261 1945198737682108145115611 := by
  unfold tailWord_3788261
  simp only [CollatzResearch.WordTrace]
  refine ⟨138169229728784855314924637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92112819819189903543283091 138169229728784855314924637)
  ·
    refine ⟨51813461148294320743096739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138169229728784855314924637 51813461148294320743096739)
    ·
      refine ⟨77720191722441481114645109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51813461148294320743096739 77720191722441481114645109)
      ·
        refine ⟨7286267973978888854497979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77720191722441481114645109 7286267973978888854497979)
        ·
          refine ⟨10929401960968333281746969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286267973978888854497979 10929401960968333281746969)
          ·
            refine ⟨8197051470726249961310227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10929401960968333281746969 8197051470726249961310227)
            ·
              refine ⟨12295577206089374941965341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197051470726249961310227 12295577206089374941965341)
              ·
                refine ⟨4610841452283515603237003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295577206089374941965341 4610841452283515603237003)
                ·
                  refine ⟨6916262178425273404855505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610841452283515603237003 6916262178425273404855505)
                  ·
                    refine ⟨5187196633818955053641629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916262178425273404855505 5187196633818955053641629)
                    ·
                      refine ⟨1945198737682108145115611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187196633818955053641629 1945198737682108145115611)
                      ·
                        rfl

theorem cell23_3788261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3788261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788261 prefixEnd_3788261 := by exact prefixLift 3788261
  have htrace : WordTrace (prefixWord ++ tailWord_3788261) baseStart_3788261 baseEnd_3788261 := by
    simpa [prefixWord, tailWord_3788261, baseEnd_3788261] using wordTrace_append hprefix tailTrace_3788261
  have hstable : (prefixWord ++ tailWord_3788261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788261).length < 2 ^ (prefixWord ++ tailWord_3788261).sum := by decide
  have hdescent : baseEnd_3788261 < baseStart_3788261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788284 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_3788284 : Nat := 118140960795 + 3788284 * 2 ^ 59
def prefixEnd_3788284 : Nat := 4983230072969 + 3 ^ 40 * 3788284 * 2
def baseEnd_3788284 : Nat := 1945210547737161555128005

theorem tailTrace_3788284 : CollatzResearch.WordTrace tailWord_3788284 prefixEnd_3788284 1945210547737161555128005 := by
  unfold tailWord_3788284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085034303850765121505953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92113379071801020162007937 69085034303850765121505953)
  ·
    refine ⟨51813775727888073841129465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69085034303850765121505953 51813775727888073841129465)
    ·
      refine ⟨38860331795916055380847099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51813775727888073841129465 38860331795916055380847099)
      ·
        refine ⟨58290497693874083071270649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38860331795916055380847099 58290497693874083071270649)
        ·
          refine ⟨43717873270405562303452987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58290497693874083071270649 43717873270405562303452987)
          ·
            refine ⟨65576809905608343455179481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43717873270405562303452987 65576809905608343455179481)
            ·
              refine ⟨49182607429206257591384611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65576809905608343455179481 49182607429206257591384611)
              ·
                refine ⟨73773911143809386387076917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49182607429206257591384611 73773911143809386387076917)
                ·
                  refine ⟨6916304169732129973788461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73773911143809386387076917 6916304169732129973788461)
                  ·
                    refine ⟨2593614063649548740170673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6916304169732129973788461 2593614063649548740170673)
                    ·
                      refine ⟨1945210547737161555128005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593614063649548740170673 1945210547737161555128005)
                      ·
                        rfl

theorem cell23_3788284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_3788284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788284 prefixEnd_3788284 := by exact prefixLift 3788284
  have htrace : WordTrace (prefixWord ++ tailWord_3788284) baseStart_3788284 baseEnd_3788284 := by
    simpa [prefixWord, tailWord_3788284, baseEnd_3788284] using wordTrace_append hprefix tailTrace_3788284
  have hstable : (prefixWord ++ tailWord_3788284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788284).length < 2 ^ (prefixWord ++ tailWord_3788284).sum := by decide
  have hdescent : baseEnd_3788284 < baseStart_3788284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788314 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_3788314 : Nat := 118140960795 + 3788314 * 2 ^ 59
def prefixEnd_3788314 : Nat := 4983230072969 + 3 ^ 40 * 3788314 * 2
def baseEnd_3788314 : Nat := 1945225952156796437752867

theorem tailTrace_3788314 : CollatzResearch.WordTrace tailWord_3788314 prefixEnd_3788314 1945225952156796437752867 := by
  unfold tailWord_3788314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542790699398211341650999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92114108531728563577735997 34542790699398211341650999)
  ·
    refine ⟨51814186049097317012476499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34542790699398211341650999 51814186049097317012476499)
    ·
      refine ⟨77721279073645975518714749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51814186049097317012476499 77721279073645975518714749)
      ·
        refine ⟨29145479652617240819518031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77721279073645975518714749 29145479652617240819518031)
        ·
          refine ⟨43718219478925861229277047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29145479652617240819518031 43718219478925861229277047)
          ·
            refine ⟨65577329218388791843915571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43718219478925861229277047 65577329218388791843915571)
            ·
              refine ⟨98365993827583187765873357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65577329218388791843915571 98365993827583187765873357)
              ·
                refine ⟨36887247685343695412202509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98365993827583187765873357 36887247685343695412202509)
                ·
                  refine ⟨13832717882003885779575941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36887247685343695412202509 13832717882003885779575941)
                  ·
                    refine ⟨2593634602875728583670489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13832717882003885779575941 2593634602875728583670489)
                    ·
                      refine ⟨1945225952156796437752867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593634602875728583670489 1945225952156796437752867)
                      ·
                        rfl

theorem cell23_3788314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_3788314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788314 prefixEnd_3788314 := by exact prefixLift 3788314
  have htrace : WordTrace (prefixWord ++ tailWord_3788314) baseStart_3788314 baseEnd_3788314 := by
    simpa [prefixWord, tailWord_3788314, baseEnd_3788314] using wordTrace_append hprefix tailTrace_3788314
  have hstable : (prefixWord ++ tailWord_3788314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788314).length < 2 ^ (prefixWord ++ tailWord_3788314).sum := by decide
  have hdescent : baseEnd_3788314 < baseStart_3788314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788342 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_3788342 : Nat := 118140960795 + 3788342 * 2 ^ 59
def prefixEnd_3788342 : Nat := 4983230072969 + 3 ^ 40 * 3788342 * 2
def baseEnd_3788342 : Nat := 1945240329615122328202739

theorem tailTrace_3788342 : CollatzResearch.WordTrace tailWord_3788342 prefixEnd_3788342 1945240329615122328202739 := by
  unfold tailWord_3788342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635761502593212884288955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92114789360994270765748853 8635761502593212884288955)
  ·
    refine ⟨12953642253889819326433433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635761502593212884288955 12953642253889819326433433)
    ·
      refine ⟨9715231690417364494825075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12953642253889819326433433 9715231690417364494825075)
      ·
        refine ⟨14572847535626046742237613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715231690417364494825075 14572847535626046742237613)
        ·
          refine ⟨5464817825859767528339105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14572847535626046742237613 5464817825859767528339105)
          ·
            refine ⟨4098613369394825646254329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464817825859767528339105 4098613369394825646254329)
            ·
              refine ⟨3073960027046119234690747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098613369394825646254329 3073960027046119234690747)
              ·
                refine ⟨4610940040569178852036121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073960027046119234690747 4610940040569178852036121)
                ·
                  refine ⟨3458205030426884139027091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610940040569178852036121 3458205030426884139027091)
                  ·
                    refine ⟨5187307545640326208540637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3458205030426884139027091 5187307545640326208540637)
                    ·
                      refine ⟨1945240329615122328202739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187307545640326208540637 1945240329615122328202739)
                      ·
                        rfl

theorem cell23_3788342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_3788342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788342 prefixEnd_3788342 := by exact prefixLift 3788342
  have htrace : WordTrace (prefixWord ++ tailWord_3788342) baseStart_3788342 baseEnd_3788342 := by
    simpa [prefixWord, tailWord_3788342, baseEnd_3788342] using wordTrace_append hprefix tailTrace_3788342
  have hstable : (prefixWord ++ tailWord_3788342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788342).length < 2 ^ (prefixWord ++ tailWord_3788342).sum := by decide
  have hdescent : baseEnd_3788342 < baseStart_3788342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788388 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 5]
def baseStart_3788388 : Nat := 118140960795 + 3788388 * 2 ^ 59
def prefixEnd_3788388 : Nat := 4983230072969 + 3 ^ 40 * 3788388 * 2
def baseEnd_3788388 : Nat := 216140438858358794247503

theorem tailTrace_3788388 : CollatzResearch.WordTrace tailWord_3788388 prefixEnd_3788388 216140438858358794247503 := by
  unfold tailWord_3788388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69086930899662378002398909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92115907866216504003198545 69086930899662378002398909)
  ·
    refine ⟨25907599087373391750899591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69086930899662378002398909 25907599087373391750899591)
    ·
      refine ⟨38861398631060087626349387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25907599087373391750899591 38861398631060087626349387)
      ·
        refine ⟨58292097946590131439524081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38861398631060087626349387 58292097946590131439524081)
        ·
          refine ⟨43719073459942598579643061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58292097946590131439524081 43719073459942598579643061)
          ·
            refine ⟨4098663136869618616841537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43719073459942598579643061 4098663136869618616841537)
            ·
              refine ⟨3073997352652213962631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098663136869618616841537 3073997352652213962631153)
              ·
                refine ⟨2305498014489160471973365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073997352652213962631153 2305498014489160471973365)
                ·
                  refine ⟨216140438858358794247503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2305498014489160471973365 216140438858358794247503)
                  ·
                    rfl

theorem cell23_3788388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_3788388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788388 prefixEnd_3788388 := by exact prefixLift 3788388
  have htrace : WordTrace (prefixWord ++ tailWord_3788388) baseStart_3788388 baseEnd_3788388 := by
    simpa [prefixWord, tailWord_3788388, baseEnd_3788388] using wordTrace_append hprefix tailTrace_3788388
  have hstable : (prefixWord ++ tailWord_3788388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788388).length < 2 ^ (prefixWord ++ tailWord_3788388).sum := by decide
  have hdescent : baseEnd_3788388 < baseStart_3788388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788394 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3788394 : Nat := 118140960795 + 3788394 * 2 ^ 59
def prefixEnd_3788394 : Nat := 4983230072969 + 3 ^ 40 * 3788394 * 2
def baseEnd_3788394 : Nat := 1945267030609156124752499

theorem tailTrace_3788394 : CollatzResearch.WordTrace tailWord_3788394 prefixEnd_3788394 1945267030609156124752499 := by
  unfold tailWord_3788394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543520159325754757379059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92116053758202012686344157 34543520159325754757379059)
  ·
    refine ⟨51815280238988632136068589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34543520159325754757379059 51815280238988632136068589)
    ·
      refine ⟨19430730089620737051025721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51815280238988632136068589 19430730089620737051025721)
      ·
        refine ⟨14573047567215552788269291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19430730089620737051025721 14573047567215552788269291)
        ·
          refine ⟨21859571350823329182403937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14573047567215552788269291 21859571350823329182403937)
          ·
            refine ⟨16394678513117496886802953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21859571350823329182403937 16394678513117496886802953)
            ·
              refine ⟨12296008884838122665102215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16394678513117496886802953 12296008884838122665102215)
              ·
                refine ⟨18444013327257183997653323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296008884838122665102215 18444013327257183997653323)
                ·
                  refine ⟨27666019990885775996479985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18444013327257183997653323 27666019990885775996479985)
                  ·
                    refine ⟨20749514993164331997359989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27666019990885775996479985 20749514993164331997359989)
                    ·
                      refine ⟨1945267030609156124752499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20749514993164331997359989 1945267030609156124752499)
                      ·
                        rfl

theorem cell23_3788394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3788394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788394 prefixEnd_3788394 := by exact prefixLift 3788394
  have htrace : WordTrace (prefixWord ++ tailWord_3788394) baseStart_3788394 baseEnd_3788394 := by
    simpa [prefixWord, tailWord_3788394, baseEnd_3788394] using wordTrace_append hprefix tailTrace_3788394
  have hstable : (prefixWord ++ tailWord_3788394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788394).length < 2 ^ (prefixWord ++ tailWord_3788394).sum := by decide
  have hdescent : baseEnd_3788394 < baseStart_3788394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788427 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 8]
def baseStart_3788427 : Nat := 118140960795 + 3788427 * 2 ^ 59
def prefixEnd_3788427 : Nat := 4983230072969 + 3 ^ 40 * 3788427 * 2
def baseEnd_3788427 : Nat := 216142663941194943959983

theorem tailTrace_3788427 : CollatzResearch.WordTrace tailWord_3788427 prefixEnd_3788427 216142663941194943959983 := by
  unfold tailWord_3788427
  simp only [CollatzResearch.WordTrace]
  refine ⟨138175284246183465665467535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92116856164122310443645023 138175284246183465665467535)
  ·
    refine ⟨207262926369275198498201303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138175284246183465665467535 207262926369275198498201303)
    ·
      refine ⟨310894389553912797747301955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207262926369275198498201303 310894389553912797747301955)
      ·
        refine ⟨466341584330869196620952933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310894389553912797747301955 466341584330869196620952933)
        ·
          refine ⟨87439047062037974366428675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466341584330869196620952933 87439047062037974366428675)
          ·
            refine ⟨131158570593056961549643013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87439047062037974366428675 131158570593056961549643013)
            ·
              refine ⟨24592231986198180290558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131158570593056961549643013 24592231986198180290558065)
              ·
                refine ⟨18444173989648635217918549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24592231986198180290558065 18444173989648635217918549)
                ·
                  refine ⟨216142663941194943959983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18444173989648635217918549 216142663941194943959983)
                  ·
                    rfl

theorem cell23_3788427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_3788427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788427 prefixEnd_3788427 := by exact prefixLift 3788427
  have htrace : WordTrace (prefixWord ++ tailWord_3788427) baseStart_3788427 baseEnd_3788427 := by
    simpa [prefixWord, tailWord_3788427, baseEnd_3788427] using wordTrace_append hprefix tailTrace_3788427
  have hstable : (prefixWord ++ tailWord_3788427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788427).length < 2 ^ (prefixWord ++ tailWord_3788427).sum := by decide
  have hdescent : baseEnd_3788427 < baseStart_3788427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788448 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 1, 4]
def baseStart_3788448 : Nat := 118140960795 + 3788448 * 2 ^ 59
def prefixEnd_3788448 : Nat := 4983230072969 + 3 ^ 40 * 3788448 * 2
def baseEnd_3788448 : Nat := 648431586188166304492417

theorem tailTrace_3788448 : CollatzResearch.WordTrace tailWord_3788448 prefixEnd_3788448 648431586188166304492417 := by
  unfold tailWord_3788448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69088025089553693125990999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92117366786071590834654665 69088025089553693125990999)
  ·
    refine ⟨103632037634330539688986499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69088025089553693125990999 103632037634330539688986499)
    ·
      refine ⟨155448056451495809533479749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103632037634330539688986499 155448056451495809533479749)
      ·
        refine ⟨29146510584655464287527453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155448056451495809533479749 29146510584655464287527453)
        ·
          refine ⟨10929941469245799107822795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29146510584655464287527453 10929941469245799107822795)
          ·
            refine ⟨16394912203868698661734193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929941469245799107822795 16394912203868698661734193)
            ·
              refine ⟨12296184152901523996300645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16394912203868698661734193 12296184152901523996300645)
              ·
                refine ⟨2305534528669035749306371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12296184152901523996300645 2305534528669035749306371)
                ·
                  refine ⟨3458301793003553623959557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305534528669035749306371 3458301793003553623959557)
                  ·
                    refine ⟨648431586188166304492417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458301793003553623959557 648431586188166304492417)
                    ·
                      rfl

theorem cell23_3788448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_3788448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788448 prefixEnd_3788448 := by exact prefixLift 3788448
  have htrace : WordTrace (prefixWord ++ tailWord_3788448) baseStart_3788448 baseEnd_3788448 := by
    simpa [prefixWord, tailWord_3788448, baseEnd_3788448] using wordTrace_append hprefix tailTrace_3788448
  have hstable : (prefixWord ++ tailWord_3788448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788448).length < 2 ^ (prefixWord ++ tailWord_3788448).sum := by decide
  have hdescent : baseEnd_3788448 < baseStart_3788448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788498 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3788498 : Nat := 118140960795 + 3788498 * 2 ^ 59
def prefixEnd_3788498 : Nat := 4983230072969 + 3 ^ 40 * 3788498 * 2
def baseEnd_3788498 : Nat := 1945320432597223717852021

theorem tailTrace_3788498 : CollatzResearch.WordTrace tailWord_3788498 prefixEnd_3788498 1945320432597223717852021 := by
  unfold tailWord_3788498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544468457231561197825537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92118582552617496527534765 34544468457231561197825537)
  ·
    refine ⟨25908351342923670898369153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34544468457231561197825537 25908351342923670898369153)
    ·
      refine ⟨19431263507192753173776865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25908351342923670898369153 19431263507192753173776865)
      ·
        refine ⟨14573447630394564880332649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19431263507192753173776865 14573447630394564880332649)
        ·
          refine ⟨10930085722795923660249487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14573447630394564880332649 10930085722795923660249487)
          ·
            refine ⟨16395128584193885490374231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930085722795923660249487 16395128584193885490374231)
            ·
              refine ⟨24592692876290828235561347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395128584193885490374231 24592692876290828235561347)
              ·
                refine ⟨36889039314436242353342021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24592692876290828235561347 36889039314436242353342021)
                ·
                  refine ⟨6916694871456795441251629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36889039314436242353342021 6916694871456795441251629)
                  ·
                    refine ⟨2593760576796298290469361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6916694871456795441251629 2593760576796298290469361)
                    ·
                      refine ⟨1945320432597223717852021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593760576796298290469361 1945320432597223717852021)
                      ·
                        rfl

theorem cell23_3788498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3788498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788498 prefixEnd_3788498 := by exact prefixLift 3788498
  have htrace : WordTrace (prefixWord ++ tailWord_3788498) baseStart_3788498 baseEnd_3788498 := by
    simpa [prefixWord, tailWord_3788498, baseEnd_3788498] using wordTrace_append hprefix tailTrace_3788498
  have hstable : (prefixWord ++ tailWord_3788498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788498).length < 2 ^ (prefixWord ++ tailWord_3788498).sum := by decide
  have hdescent : baseEnd_3788498 < baseStart_3788498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788524 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_3788524 : Nat := 118140960795 + 3788524 * 2 ^ 59
def prefixEnd_3788524 : Nat := 4983230072969 + 3 ^ 40 * 3788524 * 2
def baseEnd_3788524 : Nat := 1945333783094240616126901

theorem tailTrace_3788524 : CollatzResearch.WordTrace tailWord_3788524 prefixEnd_3788524 1945333783094240616126901 := by
  unfold tailWord_3788524
  simp only [CollatzResearch.WordTrace]
  refine ⟨69089411063416025615874313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92119214751221367487832417 69089411063416025615874313)
  ·
    refine ⟨51817058297562019211905735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69089411063416025615874313 51817058297562019211905735)
    ·
      refine ⟨77725587446343028817858603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51817058297562019211905735 77725587446343028817858603)
      ·
        refine ⟨116588381169514543226787905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77725587446343028817858603 116588381169514543226787905)
        ·
          refine ⟨87441285877135907420090929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116588381169514543226787905 87441285877135907420090929)
          ·
            refine ⟨65580964407851930565068197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87441285877135907420090929 65580964407851930565068197)
            ·
              refine ⟨12296430826472236980950287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65580964407851930565068197 12296430826472236980950287)
              ·
                refine ⟨18444646239708355471425431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296430826472236980950287 18444646239708355471425431)
                ·
                  refine ⟨27666969359562533207138147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18444646239708355471425431 27666969359562533207138147)
                  ·
                    refine ⟨41500454039343799810707221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27666969359562533207138147 41500454039343799810707221)
                    ·
                      refine ⟨1945333783094240616126901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41500454039343799810707221 1945333783094240616126901)
                      ·
                        rfl

theorem cell23_3788524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_3788524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788524 prefixEnd_3788524 := by exact prefixLift 3788524
  have htrace : WordTrace (prefixWord ++ tailWord_3788524) baseStart_3788524 baseEnd_3788524 := by
    simpa [prefixWord, tailWord_3788524, baseEnd_3788524] using wordTrace_append hprefix tailTrace_3788524
  have hstable : (prefixWord ++ tailWord_3788524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788524).length < 2 ^ (prefixWord ++ tailWord_3788524).sum := by decide
  have hdescent : baseEnd_3788524 < baseStart_3788524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788532 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3788532 : Nat := 118140960795 + 3788532 * 2 ^ 59
def prefixEnd_3788532 : Nat := 4983230072969 + 3 ^ 40 * 3788532 * 2
def baseEnd_3788532 : Nat := 1945337890939476584826865

theorem tailTrace_3788532 : CollatzResearch.WordTrace tailWord_3788532 prefixEnd_3788532 1945337890939476584826865 := by
  unfold tailWord_3788532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69089556955401534299019925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92119409273868712398693233 69089556955401534299019925)
  ·
    refine ⟨3238572982284446920266559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69089556955401534299019925 3238572982284446920266559)
    ·
      refine ⟨4857859473426670380399839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238572982284446920266559 4857859473426670380399839)
      ·
        refine ⟨7286789210140005570599759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857859473426670380399839 7286789210140005570599759)
        ·
          refine ⟨10930183815210008355899639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286789210140005570599759 10930183815210008355899639)
          ·
            refine ⟨16395275722815012533849459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930183815210008355899639 16395275722815012533849459)
            ·
              refine ⟨24592913584222518800774189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395275722815012533849459 24592913584222518800774189)
              ·
                refine ⟨9222342594083444550290321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24592913584222518800774189 9222342594083444550290321)
                ·
                  refine ⟨6916756945562583412717741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222342594083444550290321 6916756945562583412717741)
                  ·
                    refine ⟨2593783854585968779769153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6916756945562583412717741 2593783854585968779769153)
                    ·
                      refine ⟨1945337890939476584826865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593783854585968779769153 1945337890939476584826865)
                      ·
                        rfl

theorem cell23_3788532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3788532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788532 prefixEnd_3788532 := by exact prefixLift 3788532
  have htrace : WordTrace (prefixWord ++ tailWord_3788532) baseStart_3788532 baseEnd_3788532 := by
    simpa [prefixWord, tailWord_3788532, baseEnd_3788532] using wordTrace_append hprefix tailTrace_3788532
  have hstable : (prefixWord ++ tailWord_3788532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788532).length < 2 ^ (prefixWord ++ tailWord_3788532).sum := by decide
  have hdescent : baseEnd_3788532 < baseStart_3788532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788548 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3788548 : Nat := 118140960795 + 3788548 * 2 ^ 59
def prefixEnd_3788548 : Nat := 4983230072969 + 3 ^ 40 * 3788548 * 2
def baseEnd_3788548 : Nat := 1945346106629948522226791

theorem tailTrace_3788548 : CollatzResearch.WordTrace tailWord_3788548 prefixEnd_3788548 1945346106629948522226791 := by
  unfold tailWord_3788548
  simp only [CollatzResearch.WordTrace]
  refine ⟨69089848739372551665311149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92119798319163402220414865 69089848739372551665311149)
  ·
    refine ⟨25908693277264706874491681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69089848739372551665311149 25908693277264706874491681)
    ·
      refine ⟨19431519957948530155868761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25908693277264706874491681 19431519957948530155868761)
      ·
        refine ⟨14573639968461397616901571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19431519957948530155868761 14573639968461397616901571)
        ·
          refine ⟨21860459952692096425352357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14573639968461397616901571 21860459952692096425352357)
          ·
            refine ⟨4098836241129768079753567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21860459952692096425352357 4098836241129768079753567)
            ·
              refine ⟨6148254361694652119630351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098836241129768079753567 6148254361694652119630351)
              ·
                refine ⟨9222381542541978179445527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148254361694652119630351 9222381542541978179445527)
                ·
                  refine ⟨13833572313812967269168291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9222381542541978179445527 13833572313812967269168291)
                  ·
                    refine ⟨20750358470719450903752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13833572313812967269168291 20750358470719450903752437)
                    ·
                      refine ⟨1945346106629948522226791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20750358470719450903752437 1945346106629948522226791)
                      ·
                        rfl

theorem cell23_3788548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3788548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788548 prefixEnd_3788548 := by exact prefixLift 3788548
  have htrace : WordTrace (prefixWord ++ tailWord_3788548) baseStart_3788548 baseEnd_3788548 := by
    simpa [prefixWord, tailWord_3788548, baseEnd_3788548] using wordTrace_append hprefix tailTrace_3788548
  have hstable : (prefixWord ++ tailWord_3788548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788548).length < 2 ^ (prefixWord ++ tailWord_3788548).sum := by decide
  have hdescent : baseEnd_3788548 < baseStart_3788548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788550 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3788550 : Nat := 118140960795 + 3788550 * 2 ^ 59
def prefixEnd_3788550 : Nat := 4983230072969 + 3 ^ 40 * 3788550 * 2
def baseEnd_3788550 : Nat := 648449044530419171467261

theorem tailTrace_3788550 : CollatzResearch.WordTrace tailWord_3788550 prefixEnd_3788550 648449044530419171467261 := by
  unfold tailWord_3788550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318117825773058052256097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92119846949825238448130069 4318117825773058052256097)
  ·
    refine ⟨3238588369329793539192073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4318117825773058052256097 3238588369329793539192073)
    ·
      refine ⟨2428941276997345154394055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238588369329793539192073 2428941276997345154394055)
      ·
        refine ⟨3643411915496017731591083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428941276997345154394055 3643411915496017731591083)
        ·
          refine ⟨5465117873244026597386625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643411915496017731591083 5465117873244026597386625)
          ·
            refine ⟨4098838404933019948039969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465117873244026597386625 4098838404933019948039969)
            ·
              refine ⟨3074128803699764961029977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098838404933019948039969 3074128803699764961029977)
              ·
                refine ⟨2305596602774823720772483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074128803699764961029977 2305596602774823720772483)
                ·
                  refine ⟨3458394904162235581158725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305596602774823720772483 3458394904162235581158725)
                  ·
                    refine ⟨648449044530419171467261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458394904162235581158725 648449044530419171467261)
                    ·
                      rfl

theorem cell23_3788550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3788550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788550 prefixEnd_3788550 := by exact prefixLift 3788550
  have htrace : WordTrace (prefixWord ++ tailWord_3788550) baseStart_3788550 baseEnd_3788550 := by
    simpa [prefixWord, tailWord_3788550, baseEnd_3788550] using wordTrace_append hprefix tailTrace_3788550
  have hstable : (prefixWord ++ tailWord_3788550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788550).length < 2 ^ (prefixWord ++ tailWord_3788550).sum := by decide
  have hdescent : baseEnd_3788550 < baseStart_3788550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788551 : List Nat := [1, 1, 4, 4, 3, 10]
def baseStart_3788551 : Nat := 118140960795 + 3788551 * 2 ^ 59
def prefixEnd_3788551 : Nat := 4983230072969 + 3 ^ 40 * 3788551 * 2
def baseEnd_3788551 : Nat := 8005545872723917738639

theorem tailTrace_3788551 : CollatzResearch.WordTrace tailWord_3788551 prefixEnd_3788551 8005545872723917738639 := by
  unfold tailWord_3788551
  simp only [CollatzResearch.WordTrace]
  refine ⟨138179806897734234842981507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92119871265156156561987671 138179806897734234842981507)
  ·
    refine ⟨207269710346601352264472261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138179806897734234842981507 207269710346601352264472261)
    ·
      refine ⟨38863070689987753549588549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207269710346601352264472261 38863070689987753549588549)
      ·
        refine ⟨7286825754372703790547853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38863070689987753549588549 7286825754372703790547853)
        ·
          refine ⟨2732559657889763921455445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286825754372703790547853 2732559657889763921455445)
          ·
            refine ⟨8005545872723917738639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2732559657889763921455445 8005545872723917738639)
            ·
              rfl

theorem cell23_3788551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 10].length) (baseStart_3788551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788551 prefixEnd_3788551 := by exact prefixLift 3788551
  have htrace : WordTrace (prefixWord ++ tailWord_3788551) baseStart_3788551 baseEnd_3788551 := by
    simpa [prefixWord, tailWord_3788551, baseEnd_3788551] using wordTrace_append hprefix tailTrace_3788551
  have hstable : (prefixWord ++ tailWord_3788551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788551).length < 2 ^ (prefixWord ++ tailWord_3788551).sum := by decide
  have hdescent : baseEnd_3788551 < baseStart_3788551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788578 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3788578 : Nat := 118140960795 + 3788578 * 2 ^ 59
def prefixEnd_3788578 : Nat := 4983230072969 + 3 ^ 40 * 3788578 * 2
def baseEnd_3788578 : Nat := 1945361511049583404851653

theorem tailTrace_3788578 : CollatzResearch.WordTrace tailWord_3788578 prefixEnd_3788578 1945361511049583404851653 := by
  unfold tailWord_3788578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34545197917159104613553597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92120527779090945636142925 34545197917159104613553597)
  ·
    refine ⟨12954449218934664230082599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34545197917159104613553597 12954449218934664230082599)
    ·
      refine ⟨19431673828401996345123899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954449218934664230082599 19431673828401996345123899)
      ·
        refine ⟨29147510742602994517685849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19431673828401996345123899 29147510742602994517685849)
        ·
          refine ⟨21860633056952245888264387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29147510742602994517685849 21860633056952245888264387)
          ·
            refine ⟨32790949585428368832396581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21860633056952245888264387 32790949585428368832396581)
            ·
              refine ⟨6148303047267819156074359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32790949585428368832396581 6148303047267819156074359)
              ·
                refine ⟨9222454570901728734111539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148303047267819156074359 9222454570901728734111539)
                ·
                  refine ⟨13833681856352593101167309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9222454570901728734111539 13833681856352593101167309)
                  ·
                    refine ⟨5187630696132222412937741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13833681856352593101167309 5187630696132222412937741)
                    ·
                      refine ⟨1945361511049583404851653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187630696132222412937741 1945361511049583404851653)
                      ·
                        rfl

theorem cell23_3788578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3788578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788578 prefixEnd_3788578 := by exact prefixLift 3788578
  have htrace : WordTrace (prefixWord ++ tailWord_3788578) baseStart_3788578 baseEnd_3788578 := by
    simpa [prefixWord, tailWord_3788578, baseEnd_3788578] using wordTrace_append hprefix tailTrace_3788578
  have hstable : (prefixWord ++ tailWord_3788578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788578).length < 2 ^ (prefixWord ++ tailWord_3788578).sum := by decide
  have hdescent : baseEnd_3788578 < baseStart_3788578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788588 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_3788588 : Nat := 118140960795 + 3788588 * 2 ^ 59
def prefixEnd_3788588 : Nat := 4983230072969 + 3 ^ 40 * 3788588 * 2
def baseEnd_3788588 : Nat := 1945366645856128365726607

theorem tailTrace_3788588 : CollatzResearch.WordTrace tailWord_3788588 prefixEnd_3788588 1945366645856128365726607 := by
  unfold tailWord_3788588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69090578199300095081039209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92120770932400126774718945 69090578199300095081039209)
  ·
    refine ⟨51817933649475071310779407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69090578199300095081039209 51817933649475071310779407)
    ·
      refine ⟨77726900474212606966169111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51817933649475071310779407 77726900474212606966169111)
      ·
        refine ⟨116590350711318910449253667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77726900474212606966169111 116590350711318910449253667)
        ·
          refine ⟨174885526066978365673880501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116590350711318910449253667 174885526066978365673880501)
          ·
            refine ⟨16395518068779221781926297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174885526066978365673880501 16395518068779221781926297)
            ·
              refine ⟨12296638551584416336444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16395518068779221781926297 12296638551584416336444723)
              ·
                refine ⟨18444957827376624504667085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296638551584416336444723 18444957827376624504667085)
                ·
                  refine ⟨6916859185266234189250157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18444957827376624504667085 6916859185266234189250157)
                  ·
                    refine ⟨2593822194474837820968809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6916859185266234189250157 2593822194474837820968809)
                    ·
                      refine ⟨1945366645856128365726607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2593822194474837820968809 1945366645856128365726607)
                      ·
                        rfl

theorem cell23_3788588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_3788588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788588 prefixEnd_3788588 := by exact prefixLift 3788588
  have htrace : WordTrace (prefixWord ++ tailWord_3788588) baseStart_3788588 baseEnd_3788588 := by
    simpa [prefixWord, tailWord_3788588, baseEnd_3788588] using wordTrace_append hprefix tailTrace_3788588
  have hstable : (prefixWord ++ tailWord_3788588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788588).length < 2 ^ (prefixWord ++ tailWord_3788588).sum := by decide
  have hdescent : baseEnd_3788588 < baseStart_3788588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788675 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 5]
def baseStart_3788675 : Nat := 118140960795 + 3788675 * 2 ^ 59
def prefixEnd_3788675 : Nat := 4983230072969 + 3 ^ 40 * 3788675 * 2
def baseEnd_3788675 : Nat := 216156813185896613926523

theorem tailTrace_3788675 : CollatzResearch.WordTrace tailWord_3788675 prefixEnd_3788675 216156813185896613926523 := by
  unfold tailWord_3788675
  simp only [CollatzResearch.WordTrace]
  refine ⟨138184329549285004020495479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92122886366190002680330319 138184329549285004020495479)
  ·
    refine ⟨207276494323927506030743219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138184329549285004020495479 207276494323927506030743219)
    ·
      refine ⟨310914741485891259046114829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207276494323927506030743219 310914741485891259046114829)
      ·
        refine ⟨116593028057209222142293061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310914741485891259046114829 116593028057209222142293061)
        ·
          refine ⟨21861192760726729151679949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116593028057209222142293061 21861192760726729151679949)
          ·
            refine ⟨8197947285272523431879981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21861192760726729151679949 8197947285272523431879981)
            ·
              refine ⟨3074230231977196286954993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8197947285272523431879981 3074230231977196286954993)
              ·
                refine ⟨2305672673982897215216245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074230231977196286954993 2305672673982897215216245)
                ·
                  refine ⟨216156813185896613926523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2305672673982897215216245 216156813185896613926523)
                  ·
                    rfl

theorem cell23_3788675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 5].length) (baseStart_3788675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788675 prefixEnd_3788675 := by exact prefixLift 3788675
  have htrace : WordTrace (prefixWord ++ tailWord_3788675) baseStart_3788675 baseEnd_3788675 := by
    simpa [prefixWord, tailWord_3788675, baseEnd_3788675] using wordTrace_append hprefix tailTrace_3788675
  have hstable : (prefixWord ++ tailWord_3788675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788675).length < 2 ^ (prefixWord ++ tailWord_3788675).sum := by decide
  have hdescent : baseEnd_3788675 < baseStart_3788675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788681 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_3788681 : Nat := 118140960795 + 3788681 * 2 ^ 59
def prefixEnd_3788681 : Nat := 4983230072969 + 3 ^ 40 * 3788681 * 2
def baseEnd_3788681 : Nat := 1945414399556996501863679

theorem tailTrace_3788681 : CollatzResearch.WordTrace tailWord_3788681 prefixEnd_3788681 1945414399556996501863679 := by
  unfold tailWord_3788681
  simp only [CollatzResearch.WordTrace]
  refine ⟨138184548387263267045213897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92123032258175511363475931 138184548387263267045213897)
  ·
    refine ⟨103638411290447450283910423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138184548387263267045213897 103638411290447450283910423)
    ·
      refine ⟨155457616935671175425865635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103638411290447450283910423 155457616935671175425865635)
      ·
        refine ⟨233186425403506763138798453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155457616935671175425865635 233186425403506763138798453)
        ·
          refine ⟨21861227381578759044262355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233186425403506763138798453 21861227381578759044262355)
          ·
            refine ⟨32791841072368138566393533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861227381578759044262355 32791841072368138566393533)
            ·
              refine ⟨12296940402138051962397575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32791841072368138566393533 12296940402138051962397575)
              ·
                refine ⟨18445410603207077943596363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296940402138051962397575 18445410603207077943596363)
                ·
                  refine ⟨27668115904810616915394545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18445410603207077943596363 27668115904810616915394545)
                  ·
                    refine ⟨20751086928607962686545909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27668115904810616915394545 20751086928607962686545909)
                    ·
                      refine ⟨1945414399556996501863679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20751086928607962686545909 1945414399556996501863679)
                      ·
                        rfl

theorem cell23_3788681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_3788681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788681 prefixEnd_3788681 := by exact prefixLift 3788681
  have htrace : WordTrace (prefixWord ++ tailWord_3788681) baseStart_3788681 baseEnd_3788681 := by
    simpa [prefixWord, tailWord_3788681, baseEnd_3788681] using wordTrace_append hprefix tailTrace_3788681
  have hstable : (prefixWord ++ tailWord_3788681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788681).length < 2 ^ (prefixWord ++ tailWord_3788681).sum := by decide
  have hdescent : baseEnd_3788681 < baseStart_3788681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788705 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3788705 : Nat := 118140960795 + 3788705 * 2 ^ 59
def prefixEnd_3788705 : Nat := 4983230072969 + 3 ^ 40 * 3788705 * 2
def baseEnd_3788705 : Nat := 648475574364234802654523

theorem tailTrace_3788705 : CollatzResearch.WordTrace tailWord_3788705 prefixEnd_3788705 648475574364234802654523 := by
  unfold tailWord_3788705
  simp only [CollatzResearch.WordTrace]
  refine ⟨138185423739176319144087569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92123615826117546096058379 138185423739176319144087569)
  ·
    refine ⟨103639067804382239358065677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138185423739176319144087569 103639067804382239358065677)
    ·
      refine ⟨38864650426643339759274629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103639067804382239358065677 38864650426643339759274629)
      ·
        refine ⟨7287121954995626204863993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38864650426643339759274629 7287121954995626204863993)
        ·
          refine ⟨5465341466246719653647995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287121954995626204863993 5465341466246719653647995)
          ·
            refine ⟨8198012199370079480471993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465341466246719653647995 8198012199370079480471993)
            ·
              refine ⟨6148509149527559610353995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198012199370079480471993 6148509149527559610353995)
              ·
                refine ⟨9222763724291339415530993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148509149527559610353995 9222763724291339415530993)
                ·
                  refine ⟨6917072793218504561648245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222763724291339415530993 6917072793218504561648245)
                  ·
                    refine ⟨648475574364234802654523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6917072793218504561648245 648475574364234802654523)
                    ·
                      rfl

theorem cell23_3788705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3788705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788705 prefixEnd_3788705 := by exact prefixLift 3788705
  have htrace : WordTrace (prefixWord ++ tailWord_3788705) baseStart_3788705 baseEnd_3788705 := by
    simpa [prefixWord, tailWord_3788705, baseEnd_3788705] using wordTrace_append hprefix tailTrace_3788705
  have hstable : (prefixWord ++ tailWord_3788705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788705).length < 2 ^ (prefixWord ++ tailWord_3788705).sum := by decide
  have hdescent : baseEnd_3788705 < baseStart_3788705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788708 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3788708 : Nat := 118140960795 + 3788708 * 2 ^ 59
def prefixEnd_3788708 : Nat := 4983230072969 + 3 ^ 40 * 3788708 * 2
def baseEnd_3788708 : Nat := 1945428263534667896226055

theorem tailTrace_3788708 : CollatzResearch.WordTrace tailWord_3788708 prefixEnd_3788708 1945428263534667896226055 := by
  unfold tailWord_3788708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69092766579082725328223389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92123688772110300437631185 69092766579082725328223389)
  ·
    refine ⟨25909787467156021998083771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69092766579082725328223389 25909787467156021998083771)
    ·
      refine ⟨38864681200734032997125657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25909787467156021998083771 38864681200734032997125657)
      ·
        refine ⟨29148510900550524747844243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38864681200734032997125657 29148510900550524747844243)
        ·
          refine ⟨43722766350825787121766365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29148510900550524747844243 43722766350825787121766365)
          ·
            refine ⟨16396037381559670170662387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43722766350825787121766365 16396037381559670170662387)
            ·
              refine ⟨24594056072339505255993581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16396037381559670170662387 24594056072339505255993581)
              ·
                refine ⟨9222771027127314470997593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24594056072339505255993581 9222771027127314470997593)
                ·
                  refine ⟨6917078270345485853248195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222771027127314470997593 6917078270345485853248195)
                  ·
                    refine ⟨10375617405518228779872293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917078270345485853248195 10375617405518228779872293)
                    ·
                      refine ⟨1945428263534667896226055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10375617405518228779872293 1945428263534667896226055)
                      ·
                        rfl

theorem cell23_3788708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3788708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788708 prefixEnd_3788708 := by exact prefixLift 3788708
  have htrace : WordTrace (prefixWord ++ tailWord_3788708) baseStart_3788708 baseEnd_3788708 := by
    simpa [prefixWord, tailWord_3788708, baseEnd_3788708] using wordTrace_append hprefix tailTrace_3788708
  have hstable : (prefixWord ++ tailWord_3788708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788708).length < 2 ^ (prefixWord ++ tailWord_3788708).sum := by decide
  have hdescent : baseEnd_3788708 < baseStart_3788708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788728 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_3788728 : Nat := 118140960795 + 3788728 * 2 ^ 59
def prefixEnd_3788728 : Nat := 4983230072969 + 3 ^ 40 * 3788728 * 2
def baseEnd_3788728 : Nat := 1945438533147757817975963

theorem tailTrace_3788728 : CollatzResearch.WordTrace tailWord_3788728 prefixEnd_3788728 1945438533147757817975963 := by
  unfold tailWord_3788728
  simp only [CollatzResearch.WordTrace]
  refine ⟨69093131309046497036087419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92124175078728662714783225 69093131309046497036087419)
  ·
    refine ⟨103639696963569745554131129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69093131309046497036087419 103639696963569745554131129)
    ·
      refine ⟨77729772722677309165598347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103639696963569745554131129 77729772722677309165598347)
      ·
        refine ⟨116594659084015963748397521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77729772722677309165598347 116594659084015963748397521)
        ·
          refine ⟨87445994313011972811298141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116594659084015963748397521 87445994313011972811298141)
          ·
            refine ⟨32792247867379489804236803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87445994313011972811298141 32792247867379489804236803)
            ·
              refine ⟨49188371801069234706355205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32792247867379489804236803 49188371801069234706355205)
              ·
                refine ⟨9222819712700481507441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49188371801069234706355205 9222819712700481507441601)
                ·
                  refine ⟨6917114784525361130581201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222819712700481507441601 6917114784525361130581201)
                  ·
                    refine ⟨5187836088394020847935901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6917114784525361130581201 5187836088394020847935901)
                    ·
                      refine ⟨1945438533147757817975963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187836088394020847935901 1945438533147757817975963)
                      ·
                        rfl

theorem cell23_3788728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_3788728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788728 prefixEnd_3788728 := by exact prefixLift 3788728
  have htrace : WordTrace (prefixWord ++ tailWord_3788728) baseStart_3788728 baseEnd_3788728 := by
    simpa [prefixWord, tailWord_3788728, baseEnd_3788728] using wordTrace_append hprefix tailTrace_3788728
  have hstable : (prefixWord ++ tailWord_3788728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788728).length < 2 ^ (prefixWord ++ tailWord_3788728).sum := by decide
  have hdescent : baseEnd_3788728 < baseStart_3788728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788731 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 6]
def baseStart_3788731 : Nat := 118140960795 + 3788731 * 2 ^ 59
def prefixEnd_3788731 : Nat := 4983230072969 + 3 ^ 40 * 3788731 * 2
def baseEnd_3788731 : Nat := 216160008176635700693161

theorem tailTrace_3788731 : CollatzResearch.WordTrace tailWord_3788731 prefixEnd_3788731 216160008176635700693161 := by
  unfold tailWord_3788731
  simp only [CollatzResearch.WordTrace]
  refine ⟨138186372037082125584534047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92124248024721417056356031 138186372037082125584534047)
  ·
    refine ⟨207279558055623188376801071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138186372037082125584534047 207279558055623188376801071)
    ·
      refine ⟨310919337083434782565201607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207279558055623188376801071 310919337083434782565201607)
      ·
        refine ⟨466379005625152173847802411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310919337083434782565201607 466379005625152173847802411)
        ·
          refine ⟨699568508437728260771703617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466379005625152173847802411 699568508437728260771703617)
          ·
            refine ⟨524676381328296195578777713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699568508437728260771703617 524676381328296195578777713)
            ·
              refine ⟨393507285996222146684083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524676381328296195578777713 393507285996222146684083285)
              ·
                refine ⟨4611413507768228281454101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 393507285996222146684083285 4611413507768228281454101)
                ·
                  refine ⟨216160008176635700693161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4611413507768228281454101 216160008176635700693161)
                  ·
                    rfl

theorem cell23_3788731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 6].length) (baseStart_3788731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788731 prefixEnd_3788731 := by exact prefixLift 3788731
  have htrace : WordTrace (prefixWord ++ tailWord_3788731) baseStart_3788731 baseEnd_3788731 := by
    simpa [prefixWord, tailWord_3788731, baseEnd_3788731] using wordTrace_append hprefix tailTrace_3788731
  have hstable : (prefixWord ++ tailWord_3788731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788731).length < 2 ^ (prefixWord ++ tailWord_3788731).sum := by decide
  have hdescent : baseEnd_3788731 < baseStart_3788731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788735 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 1, 4]
def baseStart_3788735 : Nat := 118140960795 + 3788735 * 2 ^ 59
def prefixEnd_3788735 : Nat := 4983230072969 + 3 ^ 40 * 3788735 * 2
def baseEnd_3788735 : Nat := 648480709170779763529477

theorem tailTrace_3788735 : CollatzResearch.WordTrace tailWord_3788735 prefixEnd_3788735 648480709170779763529477 := by
  unfold tailWord_3788735
  simp only [CollatzResearch.WordTrace]
  refine ⟨138186517929067634267679659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92124345286045089511786439 138186517929067634267679659)
  ·
    refine ⟨207279776893601451401519489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138186517929067634267679659 207279776893601451401519489)
    ·
      refine ⟨155459832670201088551139617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207279776893601451401519489 155459832670201088551139617)
      ·
        refine ⟨116594874502650816413354713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155459832670201088551139617 116594874502650816413354713)
        ·
          refine ⟨87446155876988112310016035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116594874502650816413354713 87446155876988112310016035)
          ·
            refine ⟨131169233815482168465024053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87446155876988112310016035 131169233815482168465024053)
            ·
              refine ⟨12297115670201453293596005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131169233815482168465024053 12297115670201453293596005)
              ·
                refine ⟨2305709188162772492549251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12297115670201453293596005 2305709188162772492549251)
                ·
                  refine ⟨3458563782244158738823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305709188162772492549251 3458563782244158738823877)
                  ·
                    refine ⟨648480709170779763529477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458563782244158738823877 648480709170779763529477)
                    ·
                      rfl

theorem cell23_3788735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_3788735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788735 prefixEnd_3788735 := by exact prefixLift 3788735
  have htrace : WordTrace (prefixWord ++ tailWord_3788735) baseStart_3788735 baseEnd_3788735 := by
    simpa [prefixWord, tailWord_3788735, baseEnd_3788735] using wordTrace_append hprefix tailTrace_3788735
  have hstable : (prefixWord ++ tailWord_3788735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788735).length < 2 ^ (prefixWord ++ tailWord_3788735).sum := by decide
  have hdescent : baseEnd_3788735 < baseStart_3788735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788748 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 6]
def baseStart_3788748 : Nat := 118140960795 + 3788748 * 2 ^ 59
def prefixEnd_3788748 : Nat := 4983230072969 + 3 ^ 40 * 3788748 * 2
def baseEnd_3788748 : Nat := 216160978084538637747319

theorem tailTrace_3788748 : CollatzResearch.WordTrace tailWord_3788748 prefixEnd_3788748 216160978084538637747319 := by
  unfold tailWord_3788748
  simp only [CollatzResearch.WordTrace]
  refine ⟨69093496039010268743951449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92124661385347024991935265 69093496039010268743951449)
  ·
    refine ⟨51820122029257701557963587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69093496039010268743951449 51820122029257701557963587)
    ·
      refine ⟨77730183043886552336945381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51820122029257701557963587 77730183043886552336945381)
      ·
        refine ⟨14574409320728728563177259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77730183043886552336945381 14574409320728728563177259)
        ·
          refine ⟨21861613981093092844765889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574409320728728563177259 21861613981093092844765889)
          ·
            refine ⟨16396210485819819633574417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21861613981093092844765889 16396210485819819633574417)
            ·
              refine ⟨12297157864364864725180813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16396210485819819633574417 12297157864364864725180813)
              ·
                refine ⟨4611434199136824271942805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12297157864364864725180813 4611434199136824271942805)
                ·
                  refine ⟨216160978084538637747319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4611434199136824271942805 216160978084538637747319)
                  ·
                    rfl

theorem cell23_3788748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_3788748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788748 prefixEnd_3788748 := by exact prefixLift 3788748
  have htrace : WordTrace (prefixWord ++ tailWord_3788748) baseStart_3788748 baseEnd_3788748 := by
    simpa [prefixWord, tailWord_3788748, baseEnd_3788748] using wordTrace_append hprefix tailTrace_3788748
  have hstable : (prefixWord ++ tailWord_3788748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788748).length < 2 ^ (prefixWord ++ tailWord_3788748).sum := by decide
  have hdescent : baseEnd_3788748 < baseStart_3788748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788762 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_3788762 : Nat := 118140960795 + 3788762 * 2 ^ 59
def prefixEnd_3788762 : Nat := 4983230072969 + 3 ^ 40 * 3788762 * 2
def baseEnd_3788762 : Nat := 1945455991490010684950807

theorem tailTrace_3788762 : CollatzResearch.WordTrace tailWord_3788762 prefixEnd_3788762 1945455991490010684950807 := by
  unfold tailWord_3788762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546875674992454469728135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92125001799979878585941693 34546875674992454469728135)
  ·
    refine ⟨51820313512488681704592203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34546875674992454469728135 51820313512488681704592203)
    ·
      refine ⟨77730470268733022556888305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51820313512488681704592203 77730470268733022556888305)
      ·
        refine ⟨58297852701549766917666229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77730470268733022556888305 58297852701549766917666229)
        ·
          refine ⟨5465423690770290648531209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58297852701549766917666229 5465423690770290648531209)
          ·
            refine ⟨4099067768077717986398407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465423690770290648531209 4099067768077717986398407)
            ·
              refine ⟨6148601652116576979597611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099067768077717986398407 6148601652116576979597611)
              ·
                refine ⟨9222902478174865469396417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148601652116576979597611 9222902478174865469396417)
                ·
                  refine ⟨6917176858631149102047313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222902478174865469396417 6917176858631149102047313)
                  ·
                    refine ⟨5187882643973361826535485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6917176858631149102047313 5187882643973361826535485)
                    ·
                      refine ⟨1945455991490010684950807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187882643973361826535485 1945455991490010684950807)
                      ·
                        rfl

theorem cell23_3788762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_3788762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788762 prefixEnd_3788762 := by exact prefixLift 3788762
  have htrace : WordTrace (prefixWord ++ tailWord_3788762) baseStart_3788762 baseEnd_3788762 := by
    simpa [prefixWord, tailWord_3788762, baseEnd_3788762] using wordTrace_append hprefix tailTrace_3788762
  have hstable : (prefixWord ++ tailWord_3788762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788762).length < 2 ^ (prefixWord ++ tailWord_3788762).sum := by decide
  have hdescent : baseEnd_3788762 < baseStart_3788762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788792 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_3788792 : Nat := 118140960795 + 3788792 * 2 ^ 59
def prefixEnd_3788792 : Nat := 4983230072969 + 3 ^ 40 * 3788792 * 2
def baseEnd_3788792 : Nat := 1945471395909645567575669

theorem tailTrace_3788792 : CollatzResearch.WordTrace tailWord_3788792 prefixEnd_3788792 1945471395909645567575669 := by
  unfold tailWord_3788792
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094298444930566501252315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92125731259907422001669753 69094298444930566501252315)
  ·
    refine ⟨103641447667395849751878473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69094298444930566501252315 103641447667395849751878473)
    ·
      refine ⟨77731085750546887313908855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103641447667395849751878473 77731085750546887313908855)
      ·
        refine ⟨116596628625820330970863283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77731085750546887313908855 116596628625820330970863283)
        ·
          refine ⟨174894942938730496456294925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116596628625820330970863283 174894942938730496456294925)
          ·
            refine ⟨65585603602023936171110597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174894942938730496456294925 65585603602023936171110597)
            ·
              refine ⟨12297300675379488032083237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65585603602023936171110597 12297300675379488032083237)
              ·
                refine ⟨2305743876633654006015607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12297300675379488032083237 2305743876633654006015607)
                ·
                  refine ⟨3458615814950481009023411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305743876633654006015607 3458615814950481009023411)
                  ·
                    refine ⟨5187923722425721513535117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3458615814950481009023411 5187923722425721513535117)
                    ·
                      refine ⟨1945471395909645567575669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187923722425721513535117 1945471395909645567575669)
                      ·
                        rfl

theorem cell23_3788792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_3788792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788792 prefixEnd_3788792 := by exact prefixLift 3788792
  have htrace : WordTrace (prefixWord ++ tailWord_3788792) baseStart_3788792 baseEnd_3788792 := by
    simpa [prefixWord, tailWord_3788792, baseEnd_3788792] using wordTrace_append hprefix tailTrace_3788792
  have hstable : (prefixWord ++ tailWord_3788792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788792).length < 2 ^ (prefixWord ++ tailWord_3788792).sum := by decide
  have hdescent : baseEnd_3788792 < baseStart_3788792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788835 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 3]
def baseStart_3788835 : Nat := 118140960795 + 3788835 * 2 ^ 59
def prefixEnd_3788835 : Nat := 4983230072969 + 3 ^ 40 * 3788835 * 2
def baseEnd_3788835 : Nat := 1945493475577788899337971

theorem tailTrace_3788835 : CollatzResearch.WordTrace tailWord_3788835 prefixEnd_3788835 1945493475577788899337971 := by
  unfold tailWord_3788835
  simp only [CollatzResearch.WordTrace]
  refine ⟨138190165228705351346319959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92126776819136900897546639 138190165228705351346319959)
  ·
    refine ⟨207285247843058027019479939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138190165228705351346319959 207285247843058027019479939)
    ·
      refine ⟨310927871764587040529219909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207285247843058027019479939 310927871764587040529219909)
      ·
        refine ⟨58298975955860070099228733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310927871764587040529219909 58298975955860070099228733)
        ·
          refine ⟨21862115983447526287210775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58298975955860070099228733 21862115983447526287210775)
          ·
            refine ⟨32793173975171289430816163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21862115983447526287210775 32793173975171289430816163)
            ·
              refine ⟨49189760962756934146224245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32793173975171289430816163 49189760962756934146224245)
              ·
                refine ⟨4611540090258462576208523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49189760962756934146224245 4611540090258462576208523)
                ·
                  refine ⟨6917310135387693864312785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611540090258462576208523 6917310135387693864312785)
                  ·
                    refine ⟨5187982601540770398234589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6917310135387693864312785 5187982601540770398234589)
                    ·
                      refine ⟨1945493475577788899337971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5187982601540770398234589 1945493475577788899337971)
                      ·
                        rfl

theorem cell23_3788835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_3788835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788835 prefixEnd_3788835 := by exact prefixLift 3788835
  have htrace : WordTrace (prefixWord ++ tailWord_3788835) baseStart_3788835 baseEnd_3788835 := by
    simpa [prefixWord, tailWord_3788835, baseEnd_3788835] using wordTrace_append hprefix tailTrace_3788835
  have hstable : (prefixWord ++ tailWord_3788835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788835).length < 2 ^ (prefixWord ++ tailWord_3788835).sum := by decide
  have hdescent : baseEnd_3788835 < baseStart_3788835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788849 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_3788849 : Nat := 118140960795 + 3788849 * 2 ^ 59
def prefixEnd_3788849 : Nat := 4983230072969 + 3 ^ 40 * 3788849 * 2
def baseEnd_3788849 : Nat := 1945500664306951844562907

theorem tailTrace_3788849 : CollatzResearch.WordTrace tailWord_3788849 prefixEnd_3788849 1945500664306951844562907 := by
  unfold tailWord_3788849
  simp only [CollatzResearch.WordTrace]
  refine ⟨138190675850654631737329601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92127117233769754491553067 138190675850654631737329601)
  ·
    refine ⟨103643006887990973802997201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138190675850654631737329601 103643006887990973802997201)
    ·
      refine ⟨77732255165993230352247901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103643006887990973802997201 77732255165993230352247901)
      ·
        refine ⟨29149595687247461382092963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77732255165993230352247901 29149595687247461382092963)
        ·
          refine ⟨43724393530871192073139445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29149595687247461382092963 43724393530871192073139445)
          ·
            refine ⟨4099161893519174256856823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43724393530871192073139445 4099161893519174256856823)
            ·
              refine ⟨6148742840278761385285235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099161893519174256856823 6148742840278761385285235)
              ·
                refine ⟨9223114260418142077927853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148742840278761385285235 9223114260418142077927853)
                ·
                  refine ⟨3458667847656803279222945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9223114260418142077927853 3458667847656803279222945)
                  ·
                    refine ⟨2594000885742602459417209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458667847656803279222945 2594000885742602459417209)
                    ·
                      refine ⟨1945500664306951844562907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594000885742602459417209 1945500664306951844562907)
                      ·
                        rfl

theorem cell23_3788849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_3788849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788849 prefixEnd_3788849 := by exact prefixLift 3788849
  have htrace : WordTrace (prefixWord ++ tailWord_3788849) baseStart_3788849 baseEnd_3788849 := by
    simpa [prefixWord, tailWord_3788849, baseEnd_3788849] using wordTrace_append hprefix tailTrace_3788849
  have hstable : (prefixWord ++ tailWord_3788849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788849).length < 2 ^ (prefixWord ++ tailWord_3788849).sum := by decide
  have hdescent : baseEnd_3788849 < baseStart_3788849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788875 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 3, 3, 2]
def baseStart_3788875 : Nat := 118140960795 + 3788875 * 2 ^ 59
def prefixEnd_3788875 : Nat := 4983230072969 + 3 ^ 40 * 3788875 * 2
def baseEnd_3788875 : Nat := 1945514014803968742837787

theorem tailTrace_3788875 : CollatzResearch.WordTrace tailWord_3788875 prefixEnd_3788875 1945514014803968742837787 := by
  unfold tailWord_3788875
  simp only [CollatzResearch.WordTrace]
  refine ⟨138191624148560438177776079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92127749432373625451850719 138191624148560438177776079)
  ·
    refine ⟨207287436222840657266664119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138191624148560438177776079 207287436222840657266664119)
    ·
      refine ⟨310931154334260985899996179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207287436222840657266664119 310931154334260985899996179)
      ·
        refine ⟨466396731501391478849994269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310931154334260985899996179 466396731501391478849994269)
        ·
          refine ⟨174898774313021804568747851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466396731501391478849994269 174898774313021804568747851)
          ·
            refine ⟨262348161469532706853121777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174898774313021804568747851 262348161469532706853121777)
            ·
              refine ⟨196761121102149530139841333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262348161469532706853121777 196761121102149530139841333)
              ·
                refine ⟨18446355103326518450610125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196761121102149530139841333 18446355103326518450610125)
                ·
                  refine ⟨6917383163747444418978797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18446355103326518450610125 6917383163747444418978797)
                  ·
                    refine ⟨2594018686405291657117049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6917383163747444418978797 2594018686405291657117049)
                    ·
                      refine ⟨1945514014803968742837787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594018686405291657117049 1945514014803968742837787)
                      ·
                        rfl

theorem cell23_3788875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3, 2].length) (baseStart_3788875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788875 prefixEnd_3788875 := by exact prefixLift 3788875
  have htrace : WordTrace (prefixWord ++ tailWord_3788875) baseStart_3788875 baseEnd_3788875 := by
    simpa [prefixWord, tailWord_3788875, baseEnd_3788875] using wordTrace_append hprefix tailTrace_3788875
  have hstable : (prefixWord ++ tailWord_3788875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788875).length < 2 ^ (prefixWord ++ tailWord_3788875).sum := by decide
  have hdescent : baseEnd_3788875 < baseStart_3788875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788882 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3788882 : Nat := 118140960795 + 3788882 * 2 ^ 59
def prefixEnd_3788882 : Nat := 4983230072969 + 3 ^ 40 * 3788882 * 2
def baseEnd_3788882 : Nat := 1945517609168550215450255

theorem tailTrace_3788882 : CollatzResearch.WordTrace tailWord_3788882 prefixEnd_3788882 1945517609168550215450255 := by
  unfold tailWord_3788882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34547969864883769593320225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92127919639690052248853933 34547969864883769593320225)
  ·
    refine ⟨25910977398662827194990169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34547969864883769593320225 25910977398662827194990169)
    ·
      refine ⟨19433233048997120396242627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25910977398662827194990169 19433233048997120396242627)
      ·
        refine ⟨29149849573495680594363941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19433233048997120396242627 29149849573495680594363941)
        ·
          refine ⟨5465596795030440111443239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29149849573495680594363941 5465596795030440111443239)
          ·
            refine ⟨8198395192545660167164859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465596795030440111443239 8198395192545660167164859)
            ·
              refine ⟨12297592788818490250747289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198395192545660167164859 12297592788818490250747289)
              ·
                refine ⟨9223194591613867688060467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12297592788818490250747289 9223194591613867688060467)
                ·
                  refine ⟨13834791887420801532090701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223194591613867688060467 13834791887420801532090701)
                  ·
                    refine ⟨5188046957782800574534013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13834791887420801532090701 5188046957782800574534013)
                    ·
                      refine ⟨1945517609168550215450255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188046957782800574534013 1945517609168550215450255)
                      ·
                        rfl

theorem cell23_3788882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3788882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788882 prefixEnd_3788882 := by exact prefixLift 3788882
  have htrace : WordTrace (prefixWord ++ tailWord_3788882) baseStart_3788882 baseEnd_3788882 := by
    simpa [prefixWord, tailWord_3788882, baseEnd_3788882] using wordTrace_append hprefix tailTrace_3788882
  have hstable : (prefixWord ++ tailWord_3788882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788882).length < 2 ^ (prefixWord ++ tailWord_3788882).sum := by decide
  have hdescent : baseEnd_3788882 < baseStart_3788882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788905 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 4, 2]
def baseStart_3788905 : Nat := 118140960795 + 3788905 * 2 ^ 59
def prefixEnd_3788905 : Nat := 4983230072969 + 3 ^ 40 * 3788905 * 2
def baseEnd_3788905 : Nat := 1945529419223603625462649

theorem tailTrace_3788905 : CollatzResearch.WordTrace tailWord_3788905 prefixEnd_3788905 1945529419223603625462649 := by
  unfold tailWord_3788905
  simp only [CollatzResearch.WordTrace]
  refine ⟨138192718338451753301368169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92128478892301168867578779 138192718338451753301368169)
  ·
    refine ⟨103644538753838814976026127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138192718338451753301368169 103644538753838814976026127)
    ·
      refine ⟨155466808130758222464039191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103644538753838814976026127 155466808130758222464039191)
      ·
        refine ⟨233200212196137333696058787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155466808130758222464039191 233200212196137333696058787)
        ·
          refine ⟨349800318294206000544088181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233200212196137333696058787 349800318294206000544088181)
          ·
            refine ⟨32793779840081812551008267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349800318294206000544088181 32793779840081812551008267)
            ·
              refine ⟨49190669760122718826512401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32793779840081812551008267 49190669760122718826512401)
              ·
                refine ⟨36893002320092039119884301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49190669760122718826512401 36893002320092039119884301)
                ·
                  refine ⟨13834875870034514669956613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36893002320092039119884301 13834875870034514669956613)
                  ·
                    refine ⟨2594039225631471500616865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13834875870034514669956613 2594039225631471500616865)
                    ·
                      refine ⟨1945529419223603625462649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594039225631471500616865 1945529419223603625462649)
                      ·
                        rfl

theorem cell23_3788905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4, 2].length) (baseStart_3788905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788905 prefixEnd_3788905 := by exact prefixLift 3788905
  have htrace : WordTrace (prefixWord ++ tailWord_3788905) baseStart_3788905 baseEnd_3788905 := by
    simpa [prefixWord, tailWord_3788905, baseEnd_3788905] using wordTrace_append hprefix tailTrace_3788905
  have hstable : (prefixWord ++ tailWord_3788905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788905).length < 2 ^ (prefixWord ++ tailWord_3788905).sum := by decide
  have hdescent : baseEnd_3788905 < baseStart_3788905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788950 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3788950 : Nat := 118140960795 + 3788950 * 2 ^ 59
def prefixEnd_3788950 : Nat := 4983230072969 + 3 ^ 40 * 3788950 * 2
def baseEnd_3788950 : Nat := 1945552525853055949399943

theorem tailTrace_3788950 : CollatzResearch.WordTrace tailWord_3788950 prefixEnd_3788950 1945552525853055949399943 := by
  unfold tailWord_3788950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637147476455545374172269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92129573082192483991170869 8637147476455545374172269)
  ·
    refine ⟨3238930303670829515314601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8637147476455545374172269 3238930303670829515314601)
    ·
      refine ⟨2429197727753122136485951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238930303670829515314601 2429197727753122136485951)
      ·
        refine ⟨3643796591629683204728927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429197727753122136485951 3643796591629683204728927)
        ·
          refine ⟨5465694887444524807093391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643796591629683204728927 5465694887444524807093391)
          ·
            refine ⟨8198542331166787210640087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465694887444524807093391 8198542331166787210640087)
            ·
              refine ⟨12297813496750180815960131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198542331166787210640087 12297813496750180815960131)
              ·
                refine ⟨18446720245125271223940197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297813496750180815960131 18446720245125271223940197)
                ·
                  refine ⟨3458760045960988354488787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18446720245125271223940197 3458760045960988354488787)
                  ·
                    refine ⟨5188140068941482531733181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3458760045960988354488787 5188140068941482531733181)
                    ·
                      refine ⟨1945552525853055949399943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188140068941482531733181 1945552525853055949399943)
                      ·
                        rfl

theorem cell23_3788950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3788950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788950 prefixEnd_3788950 := by exact prefixLift 3788950
  have htrace : WordTrace (prefixWord ++ tailWord_3788950) baseStart_3788950 baseEnd_3788950 := by
    simpa [prefixWord, tailWord_3788950, baseEnd_3788950] using wordTrace_append hprefix tailTrace_3788950
  have hstable : (prefixWord ++ tailWord_3788950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788950).length < 2 ^ (prefixWord ++ tailWord_3788950).sum := by decide
  have hdescent : baseEnd_3788950 < baseStart_3788950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788962 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3788962 : Nat := 118140960795 + 3788962 * 2 ^ 59
def prefixEnd_3788962 : Nat := 4983230072969 + 3 ^ 40 * 3788962 * 2
def baseEnd_3788962 : Nat := 216173187513434433605543

theorem tailTrace_3788962 : CollatzResearch.WordTrace tailWord_3788962 prefixEnd_3788962 216173187513434433605543 := by
  unfold tailWord_3788962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548699324811313009048285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92129864866163501357462093 34548699324811313009048285)
  ·
    refine ⟨12955762246804242378393107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34548699324811313009048285 12955762246804242378393107)
    ·
      refine ⟨19433643370206363567589661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12955762246804242378393107 19433643370206363567589661)
      ·
        refine ⟨7287616263827386337846123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19433643370206363567589661 7287616263827386337846123)
        ·
          refine ⟨10931424395741079506769185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287616263827386337846123 10931424395741079506769185)
          ·
            refine ⟨8198568296805809630076889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931424395741079506769185 8198568296805809630076889)
            ·
              refine ⟨6148926222604357222557667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198568296805809630076889 6148926222604357222557667)
              ·
                refine ⟨9223389333906535833836501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148926222604357222557667 9223389333906535833836501)
                ·
                  refine ⟨216173187513434433605543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9223389333906535833836501 216173187513434433605543)
                  ·
                    rfl

theorem cell23_3788962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3788962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788962 prefixEnd_3788962 := by exact prefixLift 3788962
  have htrace : WordTrace (prefixWord ++ tailWord_3788962) baseStart_3788962 baseEnd_3788962 := by
    simpa [prefixWord, tailWord_3788962, baseEnd_3788962] using wordTrace_append hprefix tailTrace_3788962
  have hstable : (prefixWord ++ tailWord_3788962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788962).length < 2 ^ (prefixWord ++ tailWord_3788962).sum := by decide
  have hdescent : baseEnd_3788962 < baseStart_3788962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788973 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_3788973 : Nat := 118140960795 + 3788973 * 2 ^ 59
def prefixEnd_3788973 : Nat := 4983230072969 + 3 ^ 40 * 3788973 * 2
def baseEnd_3788973 : Nat := 1945564335908109359412337

theorem tailTrace_3788973 : CollatzResearch.WordTrace tailWord_3788973 prefixEnd_3788973 1945564335908109359412337 := by
  unfold tailWord_3788973
  simp only [CollatzResearch.WordTrace]
  refine ⟨138195198502205400914843573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92130132334803600609895715 138195198502205400914843573)
  ·
    refine ⟨12955799859581756335766585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138195198502205400914843573 12955799859581756335766585)
    ·
      refine ⟨9716849894686317251824939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12955799859581756335766585 9716849894686317251824939)
      ·
        refine ⟨14575274842029475877737409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716849894686317251824939 14575274842029475877737409)
        ·
          refine ⟨10931456131522106908303057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14575274842029475877737409 10931456131522106908303057)
          ·
            refine ⟨8198592098641580181227293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931456131522106908303057 8198592098641580181227293)
            ·
              refine ⟨3074472036990592567960235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8198592098641580181227293 3074472036990592567960235)
              ·
                refine ⟨4611708055485888851940353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074472036990592567960235 4611708055485888851940353)
                ·
                  refine ⟨3458781041614416638955265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611708055485888851940353 3458781041614416638955265)
                  ·
                    refine ⟨2594085781210812479216449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458781041614416638955265 2594085781210812479216449)
                    ·
                      refine ⟨1945564335908109359412337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594085781210812479216449 1945564335908109359412337)
                      ·
                        rfl

theorem cell23_3788973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_3788973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3788973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3788973 prefixEnd_3788973 := by exact prefixLift 3788973
  have htrace : WordTrace (prefixWord ++ tailWord_3788973) baseStart_3788973 baseEnd_3788973 := by
    simpa [prefixWord, tailWord_3788973, baseEnd_3788973] using wordTrace_append hprefix tailTrace_3788973
  have hstable : (prefixWord ++ tailWord_3788973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788973).length < 2 ^ (prefixWord ++ tailWord_3788973).sum := by decide
  have hdescent : baseEnd_3788973 < baseStart_3788973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789035 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 6]
def baseStart_3789035 : Nat := 118140960795 + 3789035 * 2 ^ 59
def prefixEnd_3789035 : Nat := 4983230072969 + 3 ^ 40 * 3789035 * 2
def baseEnd_3789035 : Nat := 216177352412076457426339

theorem tailTrace_3789035 : CollatzResearch.WordTrace tailWord_3789035 prefixEnd_3789035 216177352412076457426339 := by
  unfold tailWord_3789035
  simp only [CollatzResearch.WordTrace]
  refine ⟨138197459827980785503600559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92131639885320523669067039 138197459827980785503600559)
  ·
    refine ⟨207296189741971178255400839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138197459827980785503600559 207296189741971178255400839)
    ·
      refine ⟨310944284612956767383101259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207296189741971178255400839 310944284612956767383101259)
      ·
        refine ⟨466416426919435151074651889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310944284612956767383101259 466416426919435151074651889)
        ·
          refine ⟨349812320189576363305988917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466416426919435151074651889 349812320189576363305988917)
          ·
            refine ⟨32794905017772784059936461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349812320189576363305988917 32794905017772784059936461)
            ·
              refine ⟨12298089381664794022476173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32794905017772784059936461 12298089381664794022476173)
              ·
                refine ⟨4611783518124297758428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12298089381664794022476173 4611783518124297758428565)
                ·
                  refine ⟨216177352412076457426339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4611783518124297758428565 216177352412076457426339)
                  ·
                    rfl

theorem cell23_3789035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 6].length) (baseStart_3789035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789035 prefixEnd_3789035 := by exact prefixLift 3789035
  have htrace : WordTrace (prefixWord ++ tailWord_3789035) baseStart_3789035 baseEnd_3789035 := by
    simpa [prefixWord, tailWord_3789035, baseEnd_3789035] using wordTrace_append hprefix tailTrace_3789035
  have hstable : (prefixWord ++ tailWord_3789035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789035).length < 2 ^ (prefixWord ++ tailWord_3789035).sum := by decide
  have hdescent : baseEnd_3789035 < baseStart_3789035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789096 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3789096 : Nat := 118140960795 + 3789096 * 2 ^ 59
def prefixEnd_3789096 : Nat := 4983230072969 + 3 ^ 40 * 3789096 * 2
def baseEnd_3789096 : Nat := 1945627494028612378174271

theorem tailTrace_3789096 : CollatzResearch.WordTrace tailWord_3789096 prefixEnd_3789096 1945627494028612378174271 := by
  unfold tailWord_3789096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69099842340379896460785571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92133123120506528614380761 69099842340379896460785571)
  ·
    refine ⟨103649763510569844691178357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69099842340379896460785571 103649763510569844691178357)
    ·
      refine ⟨9717165329115922939797971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103649763510569844691178357 9717165329115922939797971)
      ·
        refine ⟨14575747993673884409696957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717165329115922939797971 14575747993673884409696957)
        ·
          refine ⟨5465905497627706653636359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14575747993673884409696957 5465905497627706653636359)
          ·
            refine ⟨8198858246441559980454539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465905497627706653636359 8198858246441559980454539)
            ·
              refine ⟨12298287369662339970681809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198858246441559980454539 12298287369662339970681809)
              ·
                refine ⟨9223715527246754978011357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298287369662339970681809 9223715527246754978011357)
                ·
                  refine ⟨3458893322717533116754259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9223715527246754978011357 3458893322717533116754259)
                  ·
                    refine ⟨5188339984076299675131389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3458893322717533116754259 5188339984076299675131389)
                    ·
                      refine ⟨1945627494028612378174271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188339984076299675131389 1945627494028612378174271)
                      ·
                        rfl

theorem cell23_3789096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3789096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789096 prefixEnd_3789096 := by exact prefixLift 3789096
  have htrace : WordTrace (prefixWord ++ tailWord_3789096) baseStart_3789096 baseEnd_3789096 := by
    simpa [prefixWord, tailWord_3789096, baseEnd_3789096] using wordTrace_append hprefix tailTrace_3789096
  have hstable : (prefixWord ++ tailWord_3789096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789096).length < 2 ^ (prefixWord ++ tailWord_3789096).sum := by decide
  have hdescent : baseEnd_3789096 < baseStart_3789096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789113 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3789113 : Nat := 118140960795 + 3789113 * 2 ^ 59
def prefixEnd_3789113 : Nat := 4983230072969 + 3 ^ 40 * 3789113 * 2
def baseEnd_3789113 : Nat := 1945636223199738811661693

theorem tailTrace_3789113 : CollatzResearch.WordTrace tailWord_3789113 prefixEnd_3789113 1945636223199738811661693 := by
  unfold tailWord_3789113
  simp only [CollatzResearch.WordTrace]
  refine ⟨138200304721698204824939993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92133536481132136549959995 138200304721698204824939993)
  ·
    refine ⟨103650228541273653618704995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138200304721698204824939993 103650228541273653618704995)
    ·
      refine ⟨155475342811910480428057493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103650228541273653618704995 155475342811910480428057493)
      ·
        refine ⟨7287906694308303770065195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155475342811910480428057493 7287906694308303770065195)
        ·
          refine ⟨10931860041462455655097793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287906694308303770065195 10931860041462455655097793)
          ·
            refine ⟨8198895031096841741323345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931860041462455655097793 8198895031096841741323345)
            ·
              refine ⟨6149171273322631305992509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198895031096841741323345 6149171273322631305992509)
              ·
                refine ⟨2305939227495986739747191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6149171273322631305992509 2305939227495986739747191)
                ·
                  refine ⟨3458908841243980109620787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305939227495986739747191 3458908841243980109620787)
                  ·
                    refine ⟨5188363261865970164431181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3458908841243980109620787 5188363261865970164431181)
                    ·
                      refine ⟨1945636223199738811661693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188363261865970164431181 1945636223199738811661693)
                      ·
                        rfl

theorem cell23_3789113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3789113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789113 prefixEnd_3789113 := by exact prefixLift 3789113
  have htrace : WordTrace (prefixWord ++ tailWord_3789113) baseStart_3789113 baseEnd_3789113 := by
    simpa [prefixWord, tailWord_3789113, baseEnd_3789113] using wordTrace_append hprefix tailTrace_3789113
  have hstable : (prefixWord ++ tailWord_3789113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789113).length < 2 ^ (prefixWord ++ tailWord_3789113).sum := by decide
  have hdescent : baseEnd_3789113 < baseStart_3789113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789119 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 5, 2, 2]
def baseStart_3789119 : Nat := 118140960795 + 3789119 * 2 ^ 59
def prefixEnd_3789119 : Nat := 4983230072969 + 3 ^ 40 * 3789119 * 2
def baseEnd_3789119 : Nat := 1945639304083665788186665

theorem tailTrace_3789119 : CollatzResearch.WordTrace tailWord_3789119 prefixEnd_3789119 1945639304083665788186665 := by
  unfold tailWord_3789119
  simp only [CollatzResearch.WordTrace]
  refine ⟨138200523559676467849658411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92133682373117645233105607 138200523559676467849658411)
  ·
    refine ⟨207300785339514701774487617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138200523559676467849658411 207300785339514701774487617)
    ·
      refine ⟨155475589004636026330865713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207300785339514701774487617 155475589004636026330865713)
      ·
        refine ⟨116606691753477019748149285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155475589004636026330865713 116606691753477019748149285)
        ·
          refine ⟨21863754703776941202777991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116606691753477019748149285 21863754703776941202777991)
          ·
            refine ⟨32795632055665411804166987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21863754703776941202777991 32795632055665411804166987)
            ·
              refine ⟨49193448083498117706250481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32795632055665411804166987 49193448083498117706250481)
              ·
                refine ⟨36895086062623588279687861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49193448083498117706250481 36895086062623588279687861)
                ·
                  refine ⟨3458914318370961401220737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36895086062623588279687861 3458914318370961401220737)
                  ·
                    refine ⟨2594185738778221050915553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458914318370961401220737 2594185738778221050915553)
                    ·
                      refine ⟨1945639304083665788186665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594185738778221050915553 1945639304083665788186665)
                      ·
                        rfl

theorem cell23_3789119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_3789119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789119 prefixEnd_3789119 := by exact prefixLift 3789119
  have htrace : WordTrace (prefixWord ++ tailWord_3789119) baseStart_3789119 baseEnd_3789119 := by
    simpa [prefixWord, tailWord_3789119, baseEnd_3789119] using wordTrace_append hprefix tailTrace_3789119
  have hstable : (prefixWord ++ tailWord_3789119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789119).length < 2 ^ (prefixWord ++ tailWord_3789119).sum := by decide
  have hdescent : baseEnd_3789119 < baseStart_3789119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789136 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2]
def baseStart_3789136 : Nat := 118140960795 + 3789136 * 2 ^ 59
def prefixEnd_3789136 : Nat := 4983230072969 + 3 ^ 40 * 3789136 * 2
def baseEnd_3789136 : Nat := 1945648033254792221674087

theorem tailTrace_3789136 : CollatzResearch.WordTrace tailWord_3789136 prefixEnd_3789136 1945648033254792221674087 := by
  unfold tailWord_3789136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69100571800307439876513631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92134095733743253168684841 69100571800307439876513631)
  ·
    refine ⟨103650857700461159814770447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69100571800307439876513631 103650857700461159814770447)
    ·
      refine ⟨155476286550691739722155671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103650857700461159814770447 155476286550691739722155671)
      ·
        refine ⟨233214429826037609583233507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155476286550691739722155671 233214429826037609583233507)
        ·
          refine ⟨349821644739056414374850261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233214429826037609583233507 349821644739056414374850261)
          ·
            refine ⟨8198944798571634711910553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 349821644739056414374850261 8198944798571634711910553)
            ·
              refine ⟨6149208598928726033932915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198944798571634711910553 6149208598928726033932915)
              ·
                refine ⟨9223812898393089050899373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149208598928726033932915 9223812898393089050899373)
                ·
                  refine ⟨3458929836897408394087265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9223812898393089050899373 3458929836897408394087265)
                  ·
                    refine ⟨2594197377673056295565449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458929836897408394087265 2594197377673056295565449)
                    ·
                      refine ⟨1945648033254792221674087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594197377673056295565449 1945648033254792221674087)
                      ·
                        rfl

theorem cell23_3789136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2].length) (baseStart_3789136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789136 prefixEnd_3789136 := by exact prefixLift 3789136
  have htrace : WordTrace (prefixWord ++ tailWord_3789136) baseStart_3789136 baseEnd_3789136 := by
    simpa [prefixWord, tailWord_3789136, baseEnd_3789136] using wordTrace_append hprefix tailTrace_3789136
  have hstable : (prefixWord ++ tailWord_3789136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789136).length < 2 ^ (prefixWord ++ tailWord_3789136).sum := by decide
  have hdescent : baseEnd_3789136 < baseStart_3789136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789159 : List Nat := [1, 1, 5, 1, 3, 3, 2, 7]
def baseStart_3789159 : Nat := 118140960795 + 3789159 * 2 ^ 59
def prefixEnd_3789159 : Nat := 4983230072969 + 3 ^ 40 * 3789159 * 2
def baseEnd_3789159 : Nat := 72061475678142430803203

theorem tailTrace_3789159 : CollatzResearch.WordTrace tailWord_3789159 prefixEnd_3789159 72061475678142430803203 := by
  unfold tailWord_3789159
  simp only [CollatzResearch.WordTrace]
  refine ⟨138201982479531554681114531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92134654986354369787409687 138201982479531554681114531)
  ·
    refine ⟨207302973719297332021671797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138201982479531554681114531 207302973719297332021671797)
    ·
      refine ⟨19434653786184124877031731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207302973719297332021671797 19434653786184124877031731)
      ·
        refine ⟨29151980679276187315547597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19434653786184124877031731 29151980679276187315547597)
        ·
          refine ⟨10931992754728570243330349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29151980679276187315547597 10931992754728570243330349)
          ·
            refine ⟨4099497283023213841248881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10931992754728570243330349 4099497283023213841248881)
            ·
              refine ⟨3074622962267410380936661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099497283023213841248881 3074622962267410380936661)
              ·
                refine ⟨72061475678142430803203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3074622962267410380936661 72061475678142430803203)
                ·
                  rfl

theorem cell23_3789159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 7].length) (baseStart_3789159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789159 prefixEnd_3789159 := by exact prefixLift 3789159
  have htrace : WordTrace (prefixWord ++ tailWord_3789159) baseStart_3789159 baseEnd_3789159 := by
    simpa [prefixWord, tailWord_3789159, baseEnd_3789159] using wordTrace_append hprefix tailTrace_3789159
  have hstable : (prefixWord ++ tailWord_3789159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789159).length < 2 ^ (prefixWord ++ tailWord_3789159).sum := by decide
  have hdescent : baseEnd_3789159 < baseStart_3789159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789170 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_3789170 : Nat := 118140960795 + 3789170 * 2 ^ 59
def prefixEnd_3789170 : Nat := 4983230072969 + 3 ^ 40 * 3789170 * 2
def baseEnd_3789170 : Nat := 1945665491597045088648931

theorem tailTrace_3789170 : CollatzResearch.WordTrace tailWord_3789170 prefixEnd_3789170 1945665491597045088648931 := by
  unfold tailWord_3789170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34550595920622925889941241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92134922454994469039843309 34550595920622925889941241)
  ·
    refine ⟨25912946940467194417455931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34550595920622925889941241 25912946940467194417455931)
    ·
      refine ⟨38869420410700791626183897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25912946940467194417455931 38869420410700791626183897)
      ·
        refine ⟨29152065308025593719637923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38869420410700791626183897 29152065308025593719637923)
        ·
          refine ⟨43728097962038390579456885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29152065308025593719637923 43728097962038390579456885)
          ·
            refine ⟨4099509183941099116824083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43728097962038390579456885 4099509183941099116824083)
            ·
              refine ⟨6149263775911648675236125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099509183941099116824083 6149263775911648675236125)
              ·
                refine ⟨2305973915966868253213547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6149263775911648675236125 2305973915966868253213547)
                ·
                  refine ⟨3458960873950302379820321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305973915966868253213547 3458960873950302379820321)
                  ·
                    refine ⟨2594220655462726784865241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458960873950302379820321 2594220655462726784865241)
                    ·
                      refine ⟨1945665491597045088648931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594220655462726784865241 1945665491597045088648931)
                      ·
                        rfl

theorem cell23_3789170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_3789170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789170 prefixEnd_3789170 := by exact prefixLift 3789170
  have htrace : WordTrace (prefixWord ++ tailWord_3789170) baseStart_3789170 baseEnd_3789170 := by
    simpa [prefixWord, tailWord_3789170, baseEnd_3789170] using wordTrace_append hprefix tailTrace_3789170
  have hstable : (prefixWord ++ tailWord_3789170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789170).length < 2 ^ (prefixWord ++ tailWord_3789170).sum := by decide
  have hdescent : baseEnd_3789170 < baseStart_3789170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789192 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3789192 : Nat := 118140960795 + 3789192 * 2 ^ 59
def prefixEnd_3789192 : Nat := 4983230072969 + 3 ^ 40 * 3789192 * 2
def baseEnd_3789192 : Nat := 1945676788171444002573829

theorem tailTrace_3789192 : CollatzResearch.WordTrace tailWord_3789192 prefixEnd_3789192 1945676788171444002573829 := by
  unfold tailWord_3789192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69101593044206000658532915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92135457392274667544710553 69101593044206000658532915)
  ·
    refine ⟨103652389566309000987799373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69101593044206000658532915 103652389566309000987799373)
    ·
      refine ⟨38869646087365875370424765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103652389566309000987799373 38869646087365875370424765)
      ·
        refine ⟨14576117282762203263909287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38869646087365875370424765 14576117282762203263909287)
        ·
          refine ⟨21864175924143304895863931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576117282762203263909287 21864175924143304895863931)
          ·
            refine ⟨32796263886214957343795897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21864175924143304895863931 32796263886214957343795897)
            ·
              refine ⟨24597197914661218007846923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32796263886214957343795897 24597197914661218007846923)
              ·
                refine ⟨36895796871991827011770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24597197914661218007846923 36895796871991827011770385)
                ·
                  refine ⟨27671847653993870258827789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36895796871991827011770385 27671847653993870258827789)
                  ·
                    refine ⟨10376942870247701347060421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27671847653993870258827789 10376942870247701347060421)
                    ·
                      refine ⟨1945676788171444002573829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10376942870247701347060421 1945676788171444002573829)
                      ·
                        rfl

theorem cell23_3789192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3789192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789192 prefixEnd_3789192 := by exact prefixLift 3789192
  have htrace : WordTrace (prefixWord ++ tailWord_3789192) baseStart_3789192 baseEnd_3789192 := by
    simpa [prefixWord, tailWord_3789192, baseEnd_3789192] using wordTrace_append hprefix tailTrace_3789192
  have hstable : (prefixWord ++ tailWord_3789192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789192).length < 2 ^ (prefixWord ++ tailWord_3789192).sum := by decide
  have hdescent : baseEnd_3789192 < baseStart_3789192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789209 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 4, 2]
def baseStart_3789209 : Nat := 118140960795 + 3789209 * 2 ^ 59
def prefixEnd_3789209 : Nat := 4983230072969 + 3 ^ 40 * 3789209 * 2
def baseEnd_3789209 : Nat := 1945685517342570436061251

theorem tailTrace_3789209 : CollatzResearch.WordTrace tailWord_3789209 prefixEnd_3789209 1945685517342570436061251 := by
  unfold tailWord_3789209
  simp only [CollatzResearch.WordTrace]
  refine ⟨138203806129350413220434681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92135870752900275480289787 138203806129350413220434681)
  ·
    refine ⟨103652854597012809915326011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138203806129350413220434681 103652854597012809915326011)
    ·
      refine ⟨155479281895519214872989017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103652854597012809915326011 155479281895519214872989017)
      ·
        refine ⟨116609461421639411154741763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155479281895519214872989017 116609461421639411154741763)
        ·
          refine ⟨174914192132459116732112645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116609461421639411154741763 174914192132459116732112645)
          ·
            refine ⟨32796411024836084387271121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174914192132459116732112645 32796411024836084387271121)
            ·
              refine ⟨24597308268627063290453341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32796411024836084387271121 24597308268627063290453341)
              ·
                refine ⟨9223990600735148733920003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24597308268627063290453341 9223990600735148733920003)
                ·
                  refine ⟨13835985901102723100880005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223990600735148733920003 13835985901102723100880005)
                  ·
                    refine ⟨2594247356456760581415001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13835985901102723100880005 2594247356456760581415001)
                    ·
                      refine ⟨1945685517342570436061251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594247356456760581415001 1945685517342570436061251)
                      ·
                        rfl

theorem cell23_3789209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_3789209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789209 prefixEnd_3789209 := by exact prefixLift 3789209
  have htrace : WordTrace (prefixWord ++ tailWord_3789209) baseStart_3789209 baseEnd_3789209 := by
    simpa [prefixWord, tailWord_3789209, baseEnd_3789209] using wordTrace_append hprefix tailTrace_3789209
  have hstable : (prefixWord ++ tailWord_3789209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789209).length < 2 ^ (prefixWord ++ tailWord_3789209).sum := by decide
  have hdescent : baseEnd_3789209 < baseStart_3789209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789242 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_3789242 : Nat := 118140960795 + 3789242 * 2 ^ 59
def prefixEnd_3789242 : Nat := 4983230072969 + 3 ^ 40 * 3789242 * 2
def baseEnd_3789242 : Nat := 1945702462204168806948599

theorem tailTrace_3789242 : CollatzResearch.WordTrace tailWord_3789242 prefixEnd_3789242 1945702462204168806948599 := by
  unfold tailWord_3789242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551252434557714964096495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92136673158820573237590653 34551252434557714964096495)
  ·
    refine ⟨51826878651836572446144743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34551252434557714964096495 51826878651836572446144743)
    ·
      refine ⟨77740317977754858669217115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51826878651836572446144743 77740317977754858669217115)
      ·
        refine ⟨116610476966632288003825673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77740317977754858669217115 116610476966632288003825673)
        ·
          refine ⟨87457857724974216002869255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116610476966632288003825673 87457857724974216002869255)
          ·
            refine ⟨131186786587461324004303883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87457857724974216002869255 131186786587461324004303883)
            ·
              refine ⟨196780179881191986006455825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131186786587461324004303883 196780179881191986006455825)
              ·
                refine ⟨147585134910893989504841869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196780179881191986006455825 147585134910893989504841869)
                ·
                  refine ⟨55344425591585246064315701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147585134910893989504841869 55344425591585246064315701)
                  ·
                    refine ⟨5188539899211116818529597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55344425591585246064315701 5188539899211116818529597)
                    ·
                      refine ⟨1945702462204168806948599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188539899211116818529597 1945702462204168806948599)
                      ·
                        rfl

theorem cell23_3789242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_3789242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789242 prefixEnd_3789242 := by exact prefixLift 3789242
  have htrace : WordTrace (prefixWord ++ tailWord_3789242) baseStart_3789242 baseEnd_3789242 := by
    simpa [prefixWord, tailWord_3789242, baseEnd_3789242] using wordTrace_append hprefix tailTrace_3789242
  have hstable : (prefixWord ++ tailWord_3789242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789242).length < 2 ^ (prefixWord ++ tailWord_3789242).sum := by decide
  have hdescent : baseEnd_3789242 < baseStart_3789242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789262 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3789262 : Nat := 118140960795 + 3789262 * 2 ^ 59
def prefixEnd_3789262 : Nat := 4983230072969 + 3 ^ 40 * 3789262 * 2
def baseEnd_3789262 : Nat := 648570910605752909566169

theorem tailTrace_3789262 : CollatzResearch.WordTrace tailWord_3789262 prefixEnd_3789262 648570910605752909566169 := by
  unfold tailWord_3789262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275717399769800409014255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92137159465438935514742693 17275717399769800409014255)
  ·
    refine ⟨25913576099654700613521383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275717399769800409014255 25913576099654700613521383)
    ·
      refine ⟨38870364149482050920282075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913576099654700613521383 38870364149482050920282075)
      ·
        refine ⟨58305546224223076380423113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38870364149482050920282075 58305546224223076380423113)
        ·
          refine ⟨43729159668167307285317335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58305546224223076380423113 43729159668167307285317335)
          ·
            refine ⟨65593739502250960927976003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43729159668167307285317335 65593739502250960927976003)
            ·
              refine ⟨98390609253376441391964005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65593739502250960927976003 98390609253376441391964005)
              ·
                refine ⟨18448239235008082760993251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98390609253376441391964005 18448239235008082760993251)
                ·
                  refine ⟨27672358852512124141489877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18448239235008082760993251 27672358852512124141489877)
                  ·
                    refine ⟨648570910605752909566169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27672358852512124141489877 648570910605752909566169)
                    ·
                      rfl

theorem cell23_3789262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3789262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789262 prefixEnd_3789262 := by exact prefixLift 3789262
  have htrace : WordTrace (prefixWord ++ tailWord_3789262) baseStart_3789262 baseEnd_3789262 := by
    simpa [prefixWord, tailWord_3789262, baseEnd_3789262] using wordTrace_append hprefix tailTrace_3789262
  have hstable : (prefixWord ++ tailWord_3789262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789262).length < 2 ^ (prefixWord ++ tailWord_3789262).sum := by decide
  have hdescent : baseEnd_3789262 < baseStart_3789262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789266 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_3789266 : Nat := 118140960795 + 3789266 * 2 ^ 59
def prefixEnd_3789266 : Nat := 4983230072969 + 3 ^ 40 * 3789266 * 2
def baseEnd_3789266 : Nat := 216190531748875190338721

theorem tailTrace_3789266 : CollatzResearch.WordTrace tailWord_3789266 prefixEnd_3789266 216190531748875190338721 := by
  unfold tailWord_3789266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551471272535977988814913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92137256726762607970173101 34551471272535977988814913)
  ·
    refine ⟨25913603454401983491611185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34551471272535977988814913 25913603454401983491611185)
    ·
      refine ⟨19435202590801487618708389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25913603454401983491611185 19435202590801487618708389)
      ·
        refine ⟨3644100485775278928507823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19435202590801487618708389 3644100485775278928507823)
        ·
          refine ⟨5466150728662918392761735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644100485775278928507823 5466150728662918392761735)
          ·
            refine ⟨8199226092994377589142603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466150728662918392761735 8199226092994377589142603)
            ·
              refine ⟨12298839139491566383713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8199226092994377589142603 12298839139491566383713905)
              ·
                refine ⟨9224129354618674787785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298839139491566383713905 9224129354618674787785429)
                ·
                  refine ⟨216190531748875190338721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9224129354618674787785429 216190531748875190338721)
                  ·
                    rfl

theorem cell23_3789266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_3789266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789266 prefixEnd_3789266 := by exact prefixLift 3789266
  have htrace : WordTrace (prefixWord ++ tailWord_3789266) baseStart_3789266 baseEnd_3789266 := by
    simpa [prefixWord, tailWord_3789266, baseEnd_3789266] using wordTrace_append hprefix tailTrace_3789266
  have hstable : (prefixWord ++ tailWord_3789266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789266).length < 2 ^ (prefixWord ++ tailWord_3789266).sum := by decide
  have hdescent : baseEnd_3789266 < baseStart_3789266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789279 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 2, 5]
def baseStart_3789279 : Nat := 118140960795 + 3789279 * 2 ^ 59
def prefixEnd_3789279 : Nat := 4983230072969 + 3 ^ 40 * 3789279 * 2
def baseEnd_3789279 : Nat := 648573820329461720728643

theorem tailTrace_3789279 : CollatzResearch.WordTrace tailWord_3789279 prefixEnd_3789279 648573820329461720728643 := by
  unfold tailWord_3789279
  simp only [CollatzResearch.WordTrace]
  refine ⟨138206359239096815175482891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92137572826064543450321927 138206359239096815175482891)
  ·
    refine ⟨207309538858645222763224337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138206359239096815175482891 207309538858645222763224337)
    ·
      refine ⟨155482154143983917072418253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207309538858645222763224337 155482154143983917072418253)
      ·
        refine ⟨58305807803993968902156845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155482154143983917072418253 58305807803993968902156845)
        ·
          refine ⟨21864677926497738338308817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58305807803993968902156845 21864677926497738338308817)
          ·
            refine ⟨16398508444873303753731613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21864677926497738338308817 16398508444873303753731613)
            ·
              refine ⟨6149440666827488907649355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16398508444873303753731613 6149440666827488907649355)
              ·
                refine ⟨9224161000241233361474033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149440666827488907649355 9224161000241233361474033)
                ·
                  refine ⟨6918120750180925021105525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224161000241233361474033 6918120750180925021105525)
                  ·
                    refine ⟨648573820329461720728643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918120750180925021105525 648573820329461720728643)
                    ·
                      rfl

theorem cell23_3789279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_3789279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789279 prefixEnd_3789279 := by exact prefixLift 3789279
  have htrace : WordTrace (prefixWord ++ tailWord_3789279) baseStart_3789279 baseEnd_3789279 := by
    simpa [prefixWord, tailWord_3789279, baseEnd_3789279] using wordTrace_append hprefix tailTrace_3789279
  have hstable : (prefixWord ++ tailWord_3789279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789279).length < 2 ^ (prefixWord ++ tailWord_3789279).sum := by decide
  have hdescent : baseEnd_3789279 < baseStart_3789279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789299 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 4, 2]
def baseStart_3789299 : Nat := 118140960795 + 3789299 * 2 ^ 59
def prefixEnd_3789299 : Nat := 4983230072969 + 3 ^ 40 * 3789299 * 2
def baseEnd_3789299 : Nat := 1945731730601475083935837

theorem tailTrace_3789299 : CollatzResearch.WordTrace tailWord_3789299 prefixEnd_3789299 1945731730601475083935837 := by
  unfold tailWord_3789299
  simp only [CollatzResearch.WordTrace]
  refine ⟨138207088699024358591210951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92138059132682905727473967 138207088699024358591210951)
  ·
    refine ⟨207310633048536537886816427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138207088699024358591210951 207310633048536537886816427)
    ·
      refine ⟨310965949572804806830224641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207310633048536537886816427 310965949572804806830224641)
      ·
        refine ⟨233224462179603605122668481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310965949572804806830224641 233224462179603605122668481)
        ·
          refine ⟨174918346634702703842001361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233224462179603605122668481 174918346634702703842001361)
          ·
            refine ⟨131188759976027027881501021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174918346634702703842001361 131188759976027027881501021)
            ·
              refine ⟨49195784991010135455562883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131188759976027027881501021 49195784991010135455562883)
              ·
                refine ⟨73793677486515203183344325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49195784991010135455562883 73793677486515203183344325)
                ·
                  refine ⟨13836314528721600596877061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73793677486515203183344325 13836314528721600596877061)
                  ·
                    refine ⟨2594308974135300111914449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13836314528721600596877061 2594308974135300111914449)
                    ·
                      refine ⟨1945731730601475083935837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594308974135300111914449 1945731730601475083935837)
                      ·
                        rfl

theorem cell23_3789299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4, 2].length) (baseStart_3789299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789299 prefixEnd_3789299 := by exact prefixLift 3789299
  have htrace : WordTrace (prefixWord ++ tailWord_3789299) baseStart_3789299 baseEnd_3789299 := by
    simpa [prefixWord, tailWord_3789299, baseEnd_3789299] using wordTrace_append hprefix tailTrace_3789299
  have hstable : (prefixWord ++ tailWord_3789299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789299).length < 2 ^ (prefixWord ++ tailWord_3789299).sum := by decide
  have hdescent : baseEnd_3789299 < baseStart_3789299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789326 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3789326 : Nat := 118140960795 + 3789326 * 2 ^ 59
def prefixEnd_3789326 : Nat := 4983230072969 + 3 ^ 40 * 3789326 * 2
def baseEnd_3789326 : Nat := 648581864859715492766071

theorem tailTrace_3789326 : CollatzResearch.WordTrace tailWord_3789326 prefixEnd_3789326 648581864859715492766071 := by
  unfold tailWord_3789326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276009183740817775305479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92138715646617694801629221 17276009183740817775305479)
  ·
    refine ⟨25914013775611226662958219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17276009183740817775305479 25914013775611226662958219)
    ·
      refine ⟨38871020663416839994437329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25914013775611226662958219 38871020663416839994437329)
      ·
        refine ⟨29153265497562629995827997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38871020663416839994437329 29153265497562629995827997)
        ·
          refine ⟨10932474561585986248435499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29153265497562629995827997 10932474561585986248435499)
          ·
            refine ⟨16398711842378979372653249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10932474561585986248435499 16398711842378979372653249)
            ·
              refine ⟨12299033881784234529489937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16398711842378979372653249 12299033881784234529489937)
              ·
                refine ⟨9224275411338175897117453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12299033881784234529489937 9224275411338175897117453)
                ·
                  refine ⟨3459103279251815961419045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9224275411338175897117453 3459103279251815961419045)
                  ·
                    refine ⟨648581864859715492766071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459103279251815961419045 648581864859715492766071)
                    ·
                      rfl

theorem cell23_3789326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3789326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789326 prefixEnd_3789326 := by exact prefixLift 3789326
  have htrace : WordTrace (prefixWord ++ tailWord_3789326) baseStart_3789326 baseEnd_3789326 := by
    simpa [prefixWord, tailWord_3789326, baseEnd_3789326] using wordTrace_append hprefix tailTrace_3789326
  have hstable : (prefixWord ++ tailWord_3789326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789326).length < 2 ^ (prefixWord ++ tailWord_3789326).sum := by decide
  have hdescent : baseEnd_3789326 < baseStart_3789326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 9, 2]
def baseStart_3789359 : Nat := 118140960795 + 3789359 * 2 ^ 59
def prefixEnd_3789359 : Nat := 4983230072969 + 3 ^ 40 * 3789359 * 2
def baseEnd_3789359 : Nat := 1945762539440744849185561

theorem tailTrace_3789359 : CollatzResearch.WordTrace tailWord_3789359 prefixEnd_3789359 1945762539440744849185561 := by
  unfold tailWord_3789359
  simp only [CollatzResearch.WordTrace]
  refine ⟨138209277078806988838395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92139518052537992558930087 138209277078806988838395131)
  ·
    refine ⟨207313915618210483257592697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138209277078806988838395131 207313915618210483257592697)
    ·
      refine ⟨155485436713657862443194523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207313915618210483257592697 155485436713657862443194523)
      ·
        refine ⟨233228155070486793664791785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155485436713657862443194523 233228155070486793664791785)
        ·
          refine ⟨174921116302865095248593839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233228155070486793664791785 174921116302865095248593839)
          ·
            refine ⟨262381674454297642872890759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174921116302865095248593839 262381674454297642872890759)
            ·
              refine ⟨393572511681446464309336139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262381674454297642872890759 393572511681446464309336139)
              ·
                refine ⟨590358767522169696464004209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393572511681446464309336139 590358767522169696464004209)
                ·
                  refine ⟨442769075641627272348003157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590358767522169696464004209 442769075641627272348003157)
                  ·
                    refine ⟨2594350052587659798914081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 442769075641627272348003157 2594350052587659798914081)
                    ·
                      refine ⟨1945762539440744849185561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594350052587659798914081 1945762539440744849185561)
                      ·
                        rfl

theorem cell23_3789359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9, 2].length) (baseStart_3789359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789359 prefixEnd_3789359 := by exact prefixLift 3789359
  have htrace : WordTrace (prefixWord ++ tailWord_3789359) baseStart_3789359 baseEnd_3789359 := by
    simpa [prefixWord, tailWord_3789359, baseEnd_3789359] using wordTrace_append hprefix tailTrace_3789359
  have hstable : (prefixWord ++ tailWord_3789359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789359).length < 2 ^ (prefixWord ++ tailWord_3789359).sum := by decide
  have hdescent : baseEnd_3789359 < baseStart_3789359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789369 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_3789369 : Nat := 118140960795 + 3789369 * 2 ^ 59
def prefixEnd_3789369 : Nat := 4983230072969 + 3 ^ 40 * 3789369 * 2
def baseEnd_3789369 : Nat := 648589224749096603353505

theorem tailTrace_3789369 : CollatzResearch.WordTrace tailWord_3789369 prefixEnd_3789369 648589224749096603353505 := by
  unfold tailWord_3789369
  simp only [CollatzResearch.WordTrace]
  refine ⟨138209641808770760546259161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92139761205847173697506107 138209641808770760546259161)
  ·
    refine ⟨103657231356578070409694371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138209641808770760546259161 103657231356578070409694371)
    ·
      refine ⟨155485847034867105614541557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103657231356578070409694371 155485847034867105614541557)
      ·
        refine ⟨14576798159518791151363271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155485847034867105614541557 14576798159518791151363271)
        ·
          refine ⟨21865197239278186727044907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576798159518791151363271 21865197239278186727044907)
          ·
            refine ⟨32797795858917280090567361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21865197239278186727044907 32797795858917280090567361)
            ·
              refine ⟨24598346894187960067925521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32797795858917280090567361 24598346894187960067925521)
              ·
                refine ⟨18448760170640970050944141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24598346894187960067925521 18448760170640970050944141)
                ·
                  refine ⟨6918285063990363769104053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18448760170640970050944141 6918285063990363769104053)
                  ·
                    refine ⟨648589224749096603353505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918285063990363769104053 648589224749096603353505)
                    ·
                      rfl

theorem cell23_3789369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_3789369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789369 prefixEnd_3789369 := by exact prefixLift 3789369
  have htrace : WordTrace (prefixWord ++ tailWord_3789369) baseStart_3789369 baseEnd_3789369 := by
    simpa [prefixWord, tailWord_3789369, baseEnd_3789369] using wordTrace_append hprefix tailTrace_3789369
  have hstable : (prefixWord ++ tailWord_3789369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789369).length < 2 ^ (prefixWord ++ tailWord_3789369).sum := by decide
  have hdescent : baseEnd_3789369 < baseStart_3789369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789373 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 6]
def baseStart_3789373 : Nat := 118140960795 + 3789373 * 2 ^ 59
def prefixEnd_3789373 : Nat := 4983230072969 + 3 ^ 40 * 3789373 * 2
def baseEnd_3789373 : Nat := 216196636463323088267833

theorem tailTrace_3789373 : CollatzResearch.WordTrace tailWord_3789373 prefixEnd_3789373 216196636463323088267833 := by
  unfold tailWord_3789373
  simp only [CollatzResearch.WordTrace]
  refine ⟨138209787700756269229404773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92139858467170846152936515 138209787700756269229404773)
  ·
    refine ⟨25914335193891800480513395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138209787700756269229404773 25914335193891800480513395)
    ·
      refine ⟨38871502790837700720770093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25914335193891800480513395 38871502790837700720770093)
      ·
        refine ⟨14576813546564137770288785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38871502790837700720770093 14576813546564137770288785)
        ·
          refine ⟨10932610159923103327716589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14576813546564137770288785 10932610159923103327716589)
          ·
            refine ⟨4099728809971163747893721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10932610159923103327716589 4099728809971163747893721)
            ·
              refine ⟨3074796607478372810920291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099728809971163747893721 3074796607478372810920291)
              ·
                refine ⟨4612194911217559216380437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074796607478372810920291 4612194911217559216380437)
                ·
                  refine ⟨216196636463323088267833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4612194911217559216380437 216196636463323088267833)
                  ·
                    rfl

theorem cell23_3789373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_3789373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789373 prefixEnd_3789373 := by exact prefixLift 3789373
  have htrace : WordTrace (prefixWord ++ tailWord_3789373) baseStart_3789373 baseEnd_3789373 := by
    simpa [prefixWord, tailWord_3789373, baseEnd_3789373] using wordTrace_append hprefix tailTrace_3789373
  have hstable : (prefixWord ++ tailWord_3789373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789373).length < 2 ^ (prefixWord ++ tailWord_3789373).sum := by decide
  have hdescent : baseEnd_3789373 < baseStart_3789373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789386 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_3789386 : Nat := 118140960795 + 3789386 * 2 ^ 59
def prefixEnd_3789386 : Nat := 4983230072969 + 3 ^ 40 * 3789386 * 2
def baseEnd_3789386 : Nat := 648592134472805414515979

theorem tailTrace_3789386 : CollatzResearch.WordTrace tailWord_3789386 prefixEnd_3789386 648592134472805414515979 := by
  unfold tailWord_3789386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34552565462427293112407003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92140174566472781633085341 34552565462427293112407003)
  ·
    refine ⟨51828848193640939668610505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34552565462427293112407003 51828848193640939668610505)
    ·
      refine ⟨38871636145230704751457879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51828848193640939668610505 38871636145230704751457879)
      ·
        refine ⟨58307454217846057127186819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38871636145230704751457879 58307454217846057127186819)
        ·
          refine ⟨87461181326769085690780229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58307454217846057127186819 87461181326769085690780229)
          ·
            refine ⟨16398971498769203567021293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87461181326769085690780229 16398971498769203567021293)
            ·
              refine ⟨6149614312038451337632985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16398971498769203567021293 6149614312038451337632985)
              ·
                refine ⟨4612210734028838503224739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149614312038451337632985 4612210734028838503224739)
                ·
                  refine ⟨6918316101043257754837109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612210734028838503224739 6918316101043257754837109)
                  ·
                    refine ⟨648592134472805414515979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918316101043257754837109 648592134472805414515979)
                    ·
                      rfl

theorem cell23_3789386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_3789386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789386 prefixEnd_3789386 := by exact prefixLift 3789386
  have htrace : WordTrace (prefixWord ++ tailWord_3789386) baseStart_3789386 baseEnd_3789386 := by
    simpa [prefixWord, tailWord_3789386, baseEnd_3789386] using wordTrace_append hprefix tailTrace_3789386
  have hstable : (prefixWord ++ tailWord_3789386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789386).length < 2 ^ (prefixWord ++ tailWord_3789386).sum := by decide
  have hdescent : baseEnd_3789386 < baseStart_3789386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789393 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_3789393 : Nat := 118140960795 + 3789393 * 2 ^ 59
def prefixEnd_3789393 : Nat := 4983230072969 + 3 ^ 40 * 3789393 * 2
def baseEnd_3789393 : Nat := 1945779997782997716160405

theorem tailTrace_3789393 : CollatzResearch.WordTrace tailWord_3789393 prefixEnd_3789393 1945779997782997716160405 := by
  unfold tailWord_3789393
  simp only [CollatzResearch.WordTrace]
  refine ⟨138210517160683812645132833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92140344773789208430088555 138210517160683812645132833)
  ·
    refine ⟨103657887870512859483849625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138210517160683812645132833 103657887870512859483849625)
    ·
      refine ⟨77743415902884644612887219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103657887870512859483849625 77743415902884644612887219)
      ·
        refine ⟨116615123854326966919330829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77743415902884644612887219 116615123854326966919330829)
        ·
          refine ⟨43730671445372612594749061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116615123854326966919330829 43730671445372612594749061)
          ·
            refine ⟨8199500896007364861515449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43730671445372612594749061 8199500896007364861515449)
            ·
              refine ⟨6149625672005523646136587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8199500896007364861515449 6149625672005523646136587)
              ·
                refine ⟨9224438508008285469204881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149625672005523646136587 9224438508008285469204881)
                ·
                  refine ⟨6918328881006214101903661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224438508008285469204881 6918328881006214101903661)
                  ·
                    refine ⟨2594373330377330288213873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6918328881006214101903661 2594373330377330288213873)
                    ·
                      refine ⟨1945779997782997716160405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594373330377330288213873 1945779997782997716160405)
                      ·
                        rfl

theorem cell23_3789393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_3789393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789393 prefixEnd_3789393 := by exact prefixLift 3789393
  have htrace : WordTrace (prefixWord ++ tailWord_3789393) baseStart_3789393 baseEnd_3789393 := by
    simpa [prefixWord, tailWord_3789393, baseEnd_3789393] using wordTrace_append hprefix tailTrace_3789393
  have hstable : (prefixWord ++ tailWord_3789393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789393).length < 2 ^ (prefixWord ++ tailWord_3789393).sum := by decide
  have hdescent : baseEnd_3789393 < baseStart_3789393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789399 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 6]
def baseStart_3789399 : Nat := 118140960795 + 3789399 * 2 ^ 59
def prefixEnd_3789399 : Nat := 4983230072969 + 3 ^ 40 * 3789399 * 2
def baseEnd_3789399 : Nat := 648594359555641564228459

theorem tailTrace_3789399 : CollatzResearch.WordTrace tailWord_3789399 prefixEnd_3789399 648594359555641564228459 := by
  unfold tailWord_3789399
  simp only [CollatzResearch.WordTrace]
  refine ⟨138210735998662075669851251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92140490665774717113234167 138210735998662075669851251)
  ·
    refine ⟨207316103997993113504776877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138210735998662075669851251 207316103997993113504776877)
    ·
      refine ⟨77743538999247417564291329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207316103997993113504776877 77743538999247417564291329)
      ·
        refine ⟨58307654249435563173218497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77743538999247417564291329 58307654249435563173218497)
        ·
          refine ⟨43730740687076672379913873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58307654249435563173218497 43730740687076672379913873)
          ·
            refine ⟨32798055515307504284935405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43730740687076672379913873 32798055515307504284935405)
            ·
              refine ⟨12299270818240314106850777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32798055515307504284935405 12299270818240314106850777)
              ·
                refine ⟨9224453113680235580138083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12299270818240314106850777 9224453113680235580138083)
                ·
                  refine ⟨13836679670520353370207125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224453113680235580138083 13836679670520353370207125)
                  ·
                    refine ⟨648594359555641564228459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13836679670520353370207125 648594359555641564228459)
                    ·
                      rfl

theorem cell23_3789399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_3789399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789399 prefixEnd_3789399 := by exact prefixLift 3789399
  have htrace : WordTrace (prefixWord ++ tailWord_3789399) baseStart_3789399 baseEnd_3789399 := by
    simpa [prefixWord, tailWord_3789399, baseEnd_3789399] using wordTrace_append hprefix tailTrace_3789399
  have hstable : (prefixWord ++ tailWord_3789399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789399).length < 2 ^ (prefixWord ++ tailWord_3789399).sum := by decide
  have hdescent : baseEnd_3789399 < baseStart_3789399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789460 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3789460 : Nat := 118140960795 + 3789460 * 2 ^ 59
def prefixEnd_3789460 : Nat := 4983230072969 + 3 ^ 40 * 3789460 * 2
def baseEnd_3789460 : Nat := 1945814400986848954022597

theorem tailTrace_3789460 : CollatzResearch.WordTrace tailWord_3789460 prefixEnd_3789460 1945814400986848954022597 := by
  unfold tailWord_3789460
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106480425720541543910917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92141973900960722058547889 69106480425720541543910917)
  ·
    refine ⟨12957465079822601539483297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69106480425720541543910917 12957465079822601539483297)
    ·
      refine ⟨9718098809866951154612473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12957465079822601539483297 9718098809866951154612473)
      ·
        refine ⟨7288574107400213365959355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9718098809866951154612473 7288574107400213365959355)
        ·
          refine ⟨10932861161100320048939033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288574107400213365959355 10932861161100320048939033)
          ·
            refine ⟨8199645870825240036704275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10932861161100320048939033 8199645870825240036704275)
            ·
              refine ⟨12299468806237860055056413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8199645870825240036704275 12299468806237860055056413)
              ·
                refine ⟨4612300802339197520646155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12299468806237860055056413 4612300802339197520646155)
                ·
                  refine ⟨6918451203508796280969233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612300802339197520646155 6918451203508796280969233)
                  ·
                    refine ⟨5188838402631597210726925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918451203508796280969233 5188838402631597210726925)
                    ·
                      refine ⟨1945814400986848954022597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188838402631597210726925 1945814400986848954022597)
                      ·
                        rfl

theorem cell23_3789460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3789460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789460 prefixEnd_3789460 := by exact prefixLift 3789460
  have htrace : WordTrace (prefixWord ++ tailWord_3789460) baseStart_3789460 baseEnd_3789460 := by
    simpa [prefixWord, tailWord_3789460, baseEnd_3789460] using wordTrace_append hprefix tailTrace_3789460
  have hstable : (prefixWord ++ tailWord_3789460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789460).length < 2 ^ (prefixWord ++ tailWord_3789460).sum := by decide
  have hdescent : baseEnd_3789460 < baseStart_3789460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789500 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3789500 : Nat := 118140960795 + 3789500 * 2 ^ 59
def prefixEnd_3789500 : Nat := 4983230072969 + 3 ^ 40 * 3789500 * 2
def baseEnd_3789500 : Nat := 1945834940213028797522413

theorem tailTrace_3789500 : CollatzResearch.WordTrace tailWord_3789500 prefixEnd_3789500 1945834940213028797522413 := by
  unfold tailWord_3789500
  simp only [CollatzResearch.WordTrace]
  refine ⟨69107209885648084959638977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92142946514197446612851969 69107209885648084959638977)
  ·
    refine ⟨51830407414236063719729233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69107209885648084959638977 51830407414236063719729233)
    ·
      refine ⟨38872805560677047789796925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51830407414236063719729233 38872805560677047789796925)
      ·
        refine ⟨14577302085253892921173847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38872805560677047789796925 14577302085253892921173847)
        ·
          refine ⟨21865953127880839381760771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14577302085253892921173847 21865953127880839381760771)
          ·
            refine ⟨32798929691821259072641157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21865953127880839381760771 32798929691821259072641157)
            ·
              refine ⟨6149799317216486076120217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32798929691821259072641157 6149799317216486076120217)
              ·
                refine ⟨4612349487912364557090163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149799317216486076120217 4612349487912364557090163)
                ·
                  refine ⟨6918524231868546835635245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612349487912364557090163 6918524231868546835635245)
                  ·
                    refine ⟨2594446586950705063363217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6918524231868546835635245 2594446586950705063363217)
                    ·
                      refine ⟨1945834940213028797522413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594446586950705063363217 1945834940213028797522413)
                      ·
                        rfl

theorem cell23_3789500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3789500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789500 prefixEnd_3789500 := by exact prefixLift 3789500
  have htrace : WordTrace (prefixWord ++ tailWord_3789500) baseStart_3789500 baseEnd_3789500 := by
    simpa [prefixWord, tailWord_3789500, baseEnd_3789500] using wordTrace_append hprefix tailTrace_3789500
  have hstable : (prefixWord ++ tailWord_3789500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789500).length < 2 ^ (prefixWord ++ tailWord_3789500).sum := by decide
  have hdescent : baseEnd_3789500 < baseStart_3789500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789516 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3789516 : Nat := 118140960795 + 3789516 * 2 ^ 59
def prefixEnd_3789516 : Nat := 4983230072969 + 3 ^ 40 * 3789516 * 2
def baseEnd_3789516 : Nat := 1945843155903500734922339

theorem tailTrace_3789516 : CollatzResearch.WordTrace tailWord_3789516 prefixEnd_3789516 1945843155903500734922339 := by
  unfold tailWord_3789516
  simp only [CollatzResearch.WordTrace]
  refine ⟨69107501669619102325930201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92143335559492136434573601 69107501669619102325930201)
  ·
    refine ⟨51830626252214326744447651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69107501669619102325930201 51830626252214326744447651)
    ·
      refine ⟨77745939378321490116671477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51830626252214326744447651 77745939378321490116671477)
      ·
        refine ⟨7288681816717639698437951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77745939378321490116671477 7288681816717639698437951)
        ·
          refine ⟨10933022725076459547656927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288681816717639698437951 10933022725076459547656927)
          ·
            refine ⟨16399534087614689321485391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933022725076459547656927 16399534087614689321485391)
            ·
              refine ⟨24599301131422033982228087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399534087614689321485391 24599301131422033982228087)
              ·
                refine ⟨36898951697133050973342131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24599301131422033982228087 36898951697133050973342131)
                ·
                  refine ⟨55348427545699576460013197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36898951697133050973342131 55348427545699576460013197)
                  ·
                    refine ⟨20755660329637341172504949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55348427545699576460013197 20755660329637341172504949)
                    ·
                      refine ⟨1945843155903500734922339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20755660329637341172504949 1945843155903500734922339)
                      ·
                        rfl

theorem cell23_3789516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3789516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789516 prefixEnd_3789516 := by exact prefixLift 3789516
  have htrace : WordTrace (prefixWord ++ tailWord_3789516) baseStart_3789516 baseEnd_3789516 := by
    simpa [prefixWord, tailWord_3789516, baseEnd_3789516] using wordTrace_append hprefix tailTrace_3789516
  have hstable : (prefixWord ++ tailWord_3789516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789516).length < 2 ^ (prefixWord ++ tailWord_3789516).sum := by decide
  have hdescent : baseEnd_3789516 < baseStart_3789516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789529 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3789529 : Nat := 118140960795 + 3789529 * 2 ^ 59
def prefixEnd_3789529 : Nat := 4983230072969 + 3 ^ 40 * 3789529 * 2
def baseEnd_3789529 : Nat := 1945849831152009184059779

theorem tailTrace_3789529 : CollatzResearch.WordTrace tailWord_3789529 prefixEnd_3789529 1945849831152009184059779 := by
  unfold tailWord_3789529
  simp only [CollatzResearch.WordTrace]
  refine ⟨138215477488191107872083641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92143651658794071914722427 138215477488191107872083641)
  ·
    refine ⟨103661608116143330904062731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138215477488191107872083641 103661608116143330904062731)
    ·
      refine ⟨155492412174214996356094097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103661608116143330904062731 155492412174214996356094097)
      ·
        refine ⟨116619309130661247267070573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155492412174214996356094097 116619309130661247267070573)
        ·
          refine ⟨43732240923997967725151465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116619309130661247267070573 43732240923997967725151465)
          ·
            refine ⟨32799180692998475793863599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43732240923997967725151465 32799180692998475793863599)
            ·
              refine ⟨49198771039497713690795399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32799180692998475793863599 49198771039497713690795399)
              ·
                refine ⟨73798156559246570536193099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49198771039497713690795399 73798156559246570536193099)
                ·
                  refine ⟨110697234838869855804289649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73798156559246570536193099 110697234838869855804289649)
                  ·
                    refine ⟨83022926129152391853217237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110697234838869855804289649 83022926129152391853217237)
                    ·
                      refine ⟨1945849831152009184059779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83022926129152391853217237 1945849831152009184059779)
                      ·
                        rfl

theorem cell23_3789529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3789529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789529 prefixEnd_3789529 := by exact prefixLift 3789529
  have htrace : WordTrace (prefixWord ++ tailWord_3789529) baseStart_3789529 baseEnd_3789529 := by
    simpa [prefixWord, tailWord_3789529, baseEnd_3789529] using wordTrace_append hprefix tailTrace_3789529
  have hstable : (prefixWord ++ tailWord_3789529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789529).length < 2 ^ (prefixWord ++ tailWord_3789529).sum := by decide
  have hdescent : baseEnd_3789529 < baseStart_3789529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789530 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_3789530 : Nat := 118140960795 + 3789530 * 2 ^ 59
def prefixEnd_3789530 : Nat := 4983230072969 + 3 ^ 40 * 3789530 * 2
def baseEnd_3789530 : Nat := 1945850344632663680147275

theorem tailTrace_3789530 : CollatzResearch.WordTrace tailWord_3789530 prefixEnd_3789530 1945850344632663680147275 := by
  unfold tailWord_3789530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553878490296871260717511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92143675974124990028580029 34553878490296871260717511)
  ·
    refine ⟨51830817735445306891076267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34553878490296871260717511 51830817735445306891076267)
    ·
      refine ⟨77746226603167960336614401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51830817735445306891076267 77746226603167960336614401)
      ·
        refine ⟨58309669952375970252460801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77746226603167960336614401 58309669952375970252460801)
        ·
          refine ⟨43732252464281977689345601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58309669952375970252460801 43732252464281977689345601)
          ·
            refine ⟨32799189348211483267009201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43732252464281977689345601 32799189348211483267009201)
            ·
              refine ⟨24599392011158612450256901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32799189348211483267009201 24599392011158612450256901)
              ·
                refine ⟨4612386002092239834423169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24599392011158612450256901 4612386002092239834423169)
                ·
                  refine ⟨3459289501569179875817377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4612386002092239834423169 3459289501569179875817377)
                  ·
                    refine ⟨2594467126176884906863033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3459289501569179875817377 2594467126176884906863033)
                    ·
                      refine ⟨1945850344632663680147275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594467126176884906863033 1945850344632663680147275)
                      ·
                        rfl

theorem cell23_3789530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_3789530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789530 prefixEnd_3789530 := by exact prefixLift 3789530
  have htrace : WordTrace (prefixWord ++ tailWord_3789530) baseStart_3789530 baseEnd_3789530 := by
    simpa [prefixWord, tailWord_3789530, baseEnd_3789530] using wordTrace_append hprefix tailTrace_3789530
  have hstable : (prefixWord ++ tailWord_3789530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789530).length < 2 ^ (prefixWord ++ tailWord_3789530).sum := by decide
  have hdescent : baseEnd_3789530 < baseStart_3789530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789546 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_3789546 : Nat := 118140960795 + 3789546 * 2 ^ 59
def prefixEnd_3789546 : Nat := 4983230072969 + 3 ^ 40 * 3789546 * 2
def baseEnd_3789546 : Nat := 1945858560323135617547201

theorem tailTrace_3789546 : CollatzResearch.WordTrace tailWord_3789546 prefixEnd_3789546 1945858560323135617547201 := by
  unfold tailWord_3789546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554024382282379943863123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92144065019419679850301661 34554024382282379943863123)
  ·
    refine ⟨51831036573423569915794685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34554024382282379943863123 51831036573423569915794685)
    ·
      refine ⟨19436638715033838718423007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51831036573423569915794685 19436638715033838718423007)
      ·
        refine ⟨29154958072550758077634511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19436638715033838718423007 29154958072550758077634511)
        ·
          refine ⟨43732437108826137116451767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29154958072550758077634511 43732437108826137116451767)
          ·
            refine ⟨65598655663239205674677651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43732437108826137116451767 65598655663239205674677651)
            ·
              refine ⟨98397983494858808512016477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65598655663239205674677651 98397983494858808512016477)
              ·
                refine ⟨36899243810572053192006179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98397983494858808512016477 36899243810572053192006179)
                ·
                  refine ⟨55348865715858079788009269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36899243810572053192006179 55348865715858079788009269)
                  ·
                    refine ⟨5188956160861694980125869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55348865715858079788009269 5188956160861694980125869)
                    ·
                      refine ⟨1945858560323135617547201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5188956160861694980125869 1945858560323135617547201)
                      ·
                        rfl

theorem cell23_3789546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_3789546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789546 prefixEnd_3789546 := by exact prefixLift 3789546
  have htrace : WordTrace (prefixWord ++ tailWord_3789546) baseStart_3789546 baseEnd_3789546 := by
    simpa [prefixWord, tailWord_3789546, baseEnd_3789546] using wordTrace_append hprefix tailTrace_3789546
  have hstable : (prefixWord ++ tailWord_3789546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789546).length < 2 ^ (prefixWord ++ tailWord_3789546).sum := by decide
  have hdescent : baseEnd_3789546 < baseStart_3789546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789559 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3789559 : Nat := 118140960795 + 3789559 * 2 ^ 59
def prefixEnd_3789559 : Nat := 4983230072969 + 3 ^ 40 * 3789559 * 2
def baseEnd_3789559 : Nat := 1945865235571644066684641

theorem tailTrace_3789559 : CollatzResearch.WordTrace tailWord_3789559 prefixEnd_3789559 1945865235571644066684641 := by
  unfold tailWord_3789559
  simp only [CollatzResearch.WordTrace]
  refine ⟨138216571678082422995675731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92144381118721615330450487 138216571678082422995675731)
  ·
    refine ⟨207324857517123634493513597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138216571678082422995675731 207324857517123634493513597)
    ·
      refine ⟨77746821568921362935067599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207324857517123634493513597 77746821568921362935067599)
      ·
        refine ⟨116620232353382044402601399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77746821568921362935067599 116620232353382044402601399)
        ·
          refine ⟨174930348530073066603902099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116620232353382044402601399 174930348530073066603902099)
          ·
            refine ⟨262395522795109599905853149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174930348530073066603902099 262395522795109599905853149)
            ·
              refine ⟨98398321048166099964694931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262395522795109599905853149 98398321048166099964694931)
              ·
                refine ⟨147597481572249149947042397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98398321048166099964694931 147597481572249149947042397)
                ·
                  refine ⟨55349055589593431230140899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147597481572249149947042397 55349055589593431230140899)
                  ·
                    refine ⟨83023583384390146845211349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55349055589593431230140899 83023583384390146845211349)
                    ·
                      refine ⟨1945865235571644066684641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83023583384390146845211349 1945865235571644066684641)
                      ·
                        rfl

theorem cell23_3789559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3789559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789559 prefixEnd_3789559 := by exact prefixLift 3789559
  have htrace : WordTrace (prefixWord ++ tailWord_3789559) baseStart_3789559 baseEnd_3789559 := by
    simpa [prefixWord, tailWord_3789559, baseEnd_3789559] using wordTrace_append hprefix tailTrace_3789559
  have hstable : (prefixWord ++ tailWord_3789559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789559).length < 2 ^ (prefixWord ++ tailWord_3789559).sum := by decide
  have hdescent : baseEnd_3789559 < baseStart_3789559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789576 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3789576 : Nat := 118140960795 + 3789576 * 2 ^ 59
def prefixEnd_3789576 : Nat := 4983230072969 + 3 ^ 40 * 3789576 * 2
def baseEnd_3789576 : Nat := 1945873964742770500172063

theorem tailTrace_3789576 : CollatzResearch.WordTrace tailWord_3789576 prefixEnd_3789576 1945873964742770500172063 := by
  unfold tailWord_3789576
  simp only [CollatzResearch.WordTrace]
  refine ⟨69108595859510417449522291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92144794479347223266029721 69108595859510417449522291)
  ·
    refine ⟨103662893789265626174283437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69108595859510417449522291 103662893789265626174283437)
    ·
      refine ⟨38873585170974609815356289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103662893789265626174283437 38873585170974609815356289)
      ·
        refine ⟨29155188878230957361517217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38873585170974609815356289 29155188878230957361517217)
        ·
          refine ⟨21866391658673218021137913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29155188878230957361517217 21866391658673218021137913)
          ·
            refine ⟨16399793744004913515853435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21866391658673218021137913 16399793744004913515853435)
            ·
              refine ⟨24599690616007370273780153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399793744004913515853435 24599690616007370273780153)
              ·
                refine ⟨18449767962005527705335115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24599690616007370273780153 18449767962005527705335115)
                ·
                  refine ⟨27674651943008291558002673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18449767962005527705335115 27674651943008291558002673)
                  ·
                    refine ⟨20755988957256218668502005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27674651943008291558002673 20755988957256218668502005)
                    ·
                      refine ⟨1945873964742770500172063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20755988957256218668502005 1945873964742770500172063)
                      ·
                        rfl

theorem cell23_3789576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3789576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789576 prefixEnd_3789576 := by exact prefixLift 3789576
  have htrace : WordTrace (prefixWord ++ tailWord_3789576) baseStart_3789576 baseEnd_3789576 := by
    simpa [prefixWord, tailWord_3789576, baseEnd_3789576] using wordTrace_append hprefix tailTrace_3789576
  have hstable : (prefixWord ++ tailWord_3789576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789576).length < 2 ^ (prefixWord ++ tailWord_3789576).sum := by decide
  have hdescent : baseEnd_3789576 < baseStart_3789576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789620 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3789620 : Nat := 118140960795 + 3789620 * 2 ^ 59
def prefixEnd_3789620 : Nat := 4983230072969 + 3 ^ 40 * 3789620 * 2
def baseEnd_3789620 : Nat := 1945896557891568328021861

theorem tailTrace_3789620 : CollatzResearch.WordTrace tailWord_3789620 prefixEnd_3789620 1945896557891568328021861 := by
  unfold tailWord_3789620
  simp only [CollatzResearch.WordTrace]
  refine ⟨69109398265430715206823157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92145864353907620275764209 69109398265430715206823157)
  ·
    refine ⟨6479006087384129550639671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69109398265430715206823157 6479006087384129550639671)
    ·
      refine ⟨9718509131076194325959507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479006087384129550639671 9718509131076194325959507)
      ·
        refine ⟨14577763696614291488939261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718509131076194325959507 14577763696614291488939261)
        ·
          refine ⟨5466661386230359308352223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14577763696614291488939261 5466661386230359308352223)
          ·
            refine ⟨8199992079345538962528335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466661386230359308352223 8199992079345538962528335)
            ·
              refine ⟨12299988119018308443792503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8199992079345538962528335 12299988119018308443792503)
              ·
                refine ⟨18449982178527462665688755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12299988119018308443792503 18449982178527462665688755)
                ·
                  refine ⟨27674973267791193998533133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18449982178527462665688755 27674973267791193998533133)
                  ·
                    refine ⟨10378114975421697749449925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27674973267791193998533133 10378114975421697749449925)
                    ·
                      refine ⟨1945896557891568328021861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10378114975421697749449925 1945896557891568328021861)
                      ·
                        rfl

theorem cell23_3789620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3789620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789620 prefixEnd_3789620 := by exact prefixLift 3789620
  have htrace : WordTrace (prefixWord ++ tailWord_3789620) baseStart_3789620 baseEnd_3789620 := by
    simpa [prefixWord, tailWord_3789620, baseEnd_3789620] using wordTrace_append hprefix tailTrace_3789620
  have hstable : (prefixWord ++ tailWord_3789620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789620).length < 2 ^ (prefixWord ++ tailWord_3789620).sum := by decide
  have hdescent : baseEnd_3789620 < baseStart_3789620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789656 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_3789656 : Nat := 118140960795 + 3789656 * 2 ^ 59
def prefixEnd_3789656 : Nat := 4983230072969 + 3 ^ 40 * 3789656 * 2
def baseEnd_3789656 : Nat := 648638347731710062390565

theorem tailTrace_3789656 : CollatzResearch.WordTrace tailWord_3789656 prefixEnd_3789656 648638347731710062390565 := by
  unfold tailWord_3789656
  simp only [CollatzResearch.WordTrace]
  refine ⟨69110054779365504280978411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92146739705820672374637881 69110054779365504280978411)
  ·
    refine ⟨103665082169048256421467617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69110054779365504280978411 103665082169048256421467617)
    ·
      refine ⟨77748811626786192316100713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103665082169048256421467617 77748811626786192316100713)
      ·
        refine ⟨58311608720089644237075535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77748811626786192316100713 58311608720089644237075535)
        ·
          refine ⟨87467413080134466355613303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311608720089644237075535 87467413080134466355613303)
          ·
            refine ⟨131201119620201699533419955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87467413080134466355613303 131201119620201699533419955)
            ·
              refine ⟨196801679430302549300129933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131201119620201699533419955 196801679430302549300129933)
              ·
                refine ⟨73800629786363455987548725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196801679430302549300129933 73800629786363455987548725)
                ·
                  refine ⟨6918809042471573998832693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73800629786363455987548725 6918809042471573998832693)
                  ·
                    refine ⟨648638347731710062390565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918809042471573998832693 648638347731710062390565)
                    ·
                      rfl

theorem cell23_3789656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_3789656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789656 prefixEnd_3789656 := by exact prefixLift 3789656
  have htrace : WordTrace (prefixWord ++ tailWord_3789656) baseStart_3789656 baseEnd_3789656 := by
    simpa [prefixWord, tailWord_3789656, baseEnd_3789656] using wordTrace_append hprefix tailTrace_3789656
  have hstable : (prefixWord ++ tailWord_3789656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789656).length < 2 ^ (prefixWord ++ tailWord_3789656).sum := by decide
  have hdescent : baseEnd_3789656 < baseStart_3789656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789663 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 5, 2]
def baseStart_3789663 : Nat := 118140960795 + 3789663 * 2 ^ 59
def prefixEnd_3789663 : Nat := 4983230072969 + 3 ^ 40 * 3789663 * 2
def baseEnd_3789663 : Nat := 1945918637559711659784163

theorem tailTrace_3789663 : CollatzResearch.WordTrace tailWord_3789663 prefixEnd_3789663 1945918637559711659784163 := by
  unfold tailWord_3789663
  simp only [CollatzResearch.WordTrace]
  refine ⟨138220364869705648757461643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92146909913137099171641095 138220364869705648757461643)
  ·
    refine ⟨207330547304558473136192465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138220364869705648757461643 207330547304558473136192465)
    ·
      refine ⟨155497910478418854852144349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207330547304558473136192465 155497910478418854852144349)
      ·
        refine ⟨58311716429407070569554131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155497910478418854852144349 58311716429407070569554131)
        ·
          refine ⟨87467574644110605854331197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311716429407070569554131 87467574644110605854331197)
          ·
            refine ⟨32800340491541477195374199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87467574644110605854331197 32800340491541477195374199)
            ·
              refine ⟨49200510737312215793061299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32800340491541477195374199 49200510737312215793061299)
              ·
                refine ⟨73800766105968323689591949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49200510737312215793061299 73800766105968323689591949)
                ·
                  refine ⟨27675287289738121383596981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73800766105968323689591949 27675287289738121383596981)
                  ·
                    refine ⟨2594558183412948879712217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27675287289738121383596981 2594558183412948879712217)
                    ·
                      refine ⟨1945918637559711659784163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594558183412948879712217 1945918637559711659784163)
                      ·
                        rfl

theorem cell23_3789663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_3789663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789663 prefixEnd_3789663 := by exact prefixLift 3789663
  have htrace : WordTrace (prefixWord ++ tailWord_3789663) baseStart_3789663 baseEnd_3789663 := by
    simpa [prefixWord, tailWord_3789663, baseEnd_3789663] using wordTrace_append hprefix tailTrace_3789663
  have hstable : (prefixWord ++ tailWord_3789663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789663).length < 2 ^ (prefixWord ++ tailWord_3789663).sum := by decide
  have hdescent : baseEnd_3789663 < baseStart_3789663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789698 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3789698 : Nat := 118140960795 + 3789698 * 2 ^ 59
def prefixEnd_3789698 : Nat := 4983230072969 + 3 ^ 40 * 3789698 * 2
def baseEnd_3789698 : Nat := 648645536460873007615501

theorem tailTrace_3789698 : CollatzResearch.WordTrace tailWord_3789698 prefixEnd_3789698 648645536460873007615501 := by
  unfold tailWord_3789698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555410356144712433746437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92147760949719233156657165 34555410356144712433746437)
  ·
    refine ⟨6479139441777133581327457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34555410356144712433746437 6479139441777133581327457)
    ·
      refine ⟨4859354581332850185995593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479139441777133581327457 4859354581332850185995593)
      ·
        refine ⟨3644515935999637639496695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4859354581332850185995593 3644515935999637639496695)
        ·
          refine ⟨5466773903999456459245043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644515935999637639496695 5466773903999456459245043)
          ·
            refine ⟨8200160855999184688867565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466773903999456459245043 8200160855999184688867565)
            ·
              refine ⟨3075060320999694258325337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8200160855999184688867565 3075060320999694258325337)
              ·
                refine ⟨2306295240749770693744003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075060320999694258325337 2306295240749770693744003)
                ·
                  refine ⟨3459442861124656040616005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306295240749770693744003 3459442861124656040616005)
                  ·
                    refine ⟨648645536460873007615501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459442861124656040616005 648645536460873007615501)
                    ·
                      rfl

theorem cell23_3789698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3789698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789698 prefixEnd_3789698 := by exact prefixLift 3789698
  have htrace : WordTrace (prefixWord ++ tailWord_3789698) baseStart_3789698 baseEnd_3789698 := by
    simpa [prefixWord, tailWord_3789698, baseEnd_3789698] using wordTrace_append hprefix tailTrace_3789698
  have hstable : (prefixWord ++ tailWord_3789698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789698).length < 2 ^ (prefixWord ++ tailWord_3789698).sum := by decide
  have hdescent : baseEnd_3789698 < baseStart_3789698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789713 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_3789713 : Nat := 118140960795 + 3789713 * 2 ^ 59
def prefixEnd_3789713 : Nat := 4983230072969 + 3 ^ 40 * 3789713 * 2
def baseEnd_3789713 : Nat := 1945944311592436464158933

theorem tailTrace_3789713 : CollatzResearch.WordTrace tailWord_3789713 prefixEnd_3789713 1945944311592436464158933 := by
  unfold tailWord_3789713
  simp only [CollatzResearch.WordTrace]
  refine ⟨138222188519524507296781793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92148125679683004864521195 138222188519524507296781793)
  ·
    refine ⟨103666641389643380472586345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138222188519524507296781793 103666641389643380472586345)
    ·
      refine ⟨77749981042232535354439759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103666641389643380472586345 77749981042232535354439759)
      ·
        refine ⟨116624971563348803031659639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77749981042232535354439759 116624971563348803031659639)
        ·
          refine ⟨174937457345023204547489459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116624971563348803031659639 174937457345023204547489459)
          ·
            refine ⟨262406186017534806821234189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174937457345023204547489459 262406186017534806821234189)
            ·
              refine ⟨98402319756575552557962821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262406186017534806821234189 98402319756575552557962821)
              ·
                refine ⟨18450434954357916104618029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98402319756575552557962821 18450434954357916104618029)
                ·
                  refine ⟨6918913107884218539231761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18450434954357916104618029 6918913107884218539231761)
                  ·
                    refine ⟨5189184830913163904423821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918913107884218539231761 5189184830913163904423821)
                    ·
                      refine ⟨1945944311592436464158933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5189184830913163904423821 1945944311592436464158933)
                      ·
                        rfl

theorem cell23_3789713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_3789713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789713 prefixEnd_3789713 := by exact prefixLift 3789713
  have htrace : WordTrace (prefixWord ++ tailWord_3789713) baseStart_3789713 baseEnd_3789713 := by
    simpa [prefixWord, tailWord_3789713, baseEnd_3789713] using wordTrace_append hprefix tailTrace_3789713
  have hstable : (prefixWord ++ tailWord_3789713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789713).length < 2 ^ (prefixWord ++ tailWord_3789713).sum := by decide
  have hdescent : baseEnd_3789713 < baseStart_3789713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789724 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_3789724 : Nat := 118140960795 + 3789724 * 2 ^ 59
def prefixEnd_3789724 : Nat := 4983230072969 + 3 ^ 40 * 3789724 * 2
def baseEnd_3789724 : Nat := 648649986626545307040461

theorem tailTrace_3789724 : CollatzResearch.WordTrace tailWord_3789724 prefixEnd_3789724 648649986626545307040461 := by
  unfold tailWord_3789724
  simp only [CollatzResearch.WordTrace]
  refine ⟨69111294861242328087716113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92148393148323104116954817 69111294861242328087716113)
  ·
    refine ⟨51833471145931746065787085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69111294861242328087716113 51833471145931746065787085)
    ·
      refine ⟨19437551679724404774670157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51833471145931746065787085 19437551679724404774670157)
      ·
        refine ⟨7289081879896651790501309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19437551679724404774670157 7289081879896651790501309)
        ·
          refine ⟨2733405704961244421437991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7289081879896651790501309 2733405704961244421437991)
          ·
            refine ⟨4100108557441866632156987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733405704961244421437991 4100108557441866632156987)
            ·
              refine ⟨6150162836162799948235481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100108557441866632156987 6150162836162799948235481)
              ·
                refine ⟨4612622127122099961176611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150162836162799948235481 4612622127122099961176611)
                ·
                  refine ⟨6918933190683149941764917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612622127122099961176611 6918933190683149941764917)
                  ·
                    refine ⟨648649986626545307040461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918933190683149941764917 648649986626545307040461)
                    ·
                      rfl

theorem cell23_3789724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_3789724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789724 prefixEnd_3789724 := by exact prefixLift 3789724
  have htrace : WordTrace (prefixWord ++ tailWord_3789724) baseStart_3789724 baseEnd_3789724 := by
    simpa [prefixWord, tailWord_3789724, baseEnd_3789724] using wordTrace_append hprefix tailTrace_3789724
  have hstable : (prefixWord ++ tailWord_3789724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789724).length < 2 ^ (prefixWord ++ tailWord_3789724).sum := by decide
  have hdescent : baseEnd_3789724 < baseStart_3789724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789727 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3789727 : Nat := 118140960795 + 3789727 * 2 ^ 59
def prefixEnd_3789727 : Nat := 4983230072969 + 3 ^ 40 * 3789727 * 2
def baseEnd_3789727 : Nat := 1945951500321599409383869

theorem tailTrace_3789727 : CollatzResearch.WordTrace tailWord_3789727 prefixEnd_3789727 1945951500321599409383869 := by
  unfold tailWord_3789727
  simp only [CollatzResearch.WordTrace]
  refine ⟨138222699141473787687791435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92148466094315858458527623 138222699141473787687791435)
  ·
    refine ⟨207334048712210681531687153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138222699141473787687791435 207334048712210681531687153)
    ·
      refine ⟨155500536534158011148765365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207334048712210681531687153 155500536534158011148765365)
      ·
        refine ⟨14578175300077313545196753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155500536534158011148765365 14578175300077313545196753)
        ·
          refine ⟨10933631475057985158897565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14578175300077313545196753 10933631475057985158897565)
          ·
            refine ⟨4100111803146744434586587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10933631475057985158897565 4100111803146744434586587)
            ·
              refine ⟨6150167704720116651879881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100111803146744434586587 6150167704720116651879881)
              ·
                refine ⟨4612625778540087488909911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150167704720116651879881 4612625778540087488909911)
                ·
                  refine ⟨6918938667810131233364867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612625778540087488909911 6918938667810131233364867)
                  ·
                    refine ⟨10378408001715196850047301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918938667810131233364867 10378408001715196850047301)
                    ·
                      refine ⟨1945951500321599409383869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10378408001715196850047301 1945951500321599409383869)
                      ·
                        rfl

theorem cell23_3789727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3789727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789727 prefixEnd_3789727 := by exact prefixLift 3789727
  have htrace : WordTrace (prefixWord ++ tailWord_3789727) baseStart_3789727 baseEnd_3789727 := by
    simpa [prefixWord, tailWord_3789727, baseEnd_3789727] using wordTrace_append hprefix tailTrace_3789727
  have hstable : (prefixWord ++ tailWord_3789727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789727).length < 2 ^ (prefixWord ++ tailWord_3789727).sum := by decide
  have hdescent : baseEnd_3789727 < baseStart_3789727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789817 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 4, 2, 2]
def baseStart_3789817 : Nat := 118140960795 + 3789817 * 2 ^ 59
def prefixEnd_3789817 : Nat := 4983230072969 + 3 ^ 40 * 3789817 * 2
def baseEnd_3789817 : Nat := 1945997713580504057258455

theorem tailTrace_3789817 : CollatzResearch.WordTrace tailWord_3789817 prefixEnd_3789817 1945997713580504057258455 := by
  unfold tailWord_3789817
  simp only [CollatzResearch.WordTrace]
  refine ⟨138225981711147733058567705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92150654474098488705711803 138225981711147733058567705)
  ·
    refine ⟨103669486283360799793925779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138225981711147733058567705 103669486283360799793925779)
    ·
      refine ⟨155504229425041199690888669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103669486283360799793925779 155504229425041199690888669)
      ·
        refine ⟨58314086034390449884083251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155504229425041199690888669 58314086034390449884083251)
        ·
          refine ⟨87471129051585674826124877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58314086034390449884083251 87471129051585674826124877)
          ·
            refine ⟨32801673394344628059796829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87471129051585674826124877 32801673394344628059796829)
            ·
              refine ⟨12300627522879235522423811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32801673394344628059796829 12300627522879235522423811)
              ·
                refine ⟨18450941284318853283635717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300627522879235522423811 18450941284318853283635717)
                ·
                  refine ⟨3459551490809784990681697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18450941284318853283635717 3459551490809784990681697)
                  ·
                    refine ⟨2594663618107338743011273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3459551490809784990681697 2594663618107338743011273)
                    ·
                      refine ⟨1945997713580504057258455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594663618107338743011273 1945997713580504057258455)
                      ·
                        rfl

theorem cell23_3789817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_3789817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789817 prefixEnd_3789817 := by exact prefixLift 3789817
  have htrace : WordTrace (prefixWord ++ tailWord_3789817) baseStart_3789817 baseEnd_3789817 := by
    simpa [prefixWord, tailWord_3789817, baseEnd_3789817] using wordTrace_append hprefix tailTrace_3789817
  have hstable : (prefixWord ++ tailWord_3789817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789817).length < 2 ^ (prefixWord ++ tailWord_3789817).sum := by decide
  have hdescent : baseEnd_3789817 < baseStart_3789817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789834 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_3789834 : Nat := 118140960795 + 3789834 * 2 ^ 59
def prefixEnd_3789834 : Nat := 4983230072969 + 3 ^ 40 * 3789834 * 2
def baseEnd_3789834 : Nat := 1946006442751630490745877

theorem tailTrace_3789834 : CollatzResearch.WordTrace tailWord_3789834 prefixEnd_3789834 1946006442751630490745877 := by
  unfold tailWord_3789834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34556650438021536240484139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92151067834724096641291037 34556650438021536240484139)
  ·
    refine ⟨51834975657032304360726209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34556650438021536240484139 51834975657032304360726209)
    ·
      refine ⟨38876231742774228270544657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51834975657032304360726209 38876231742774228270544657)
      ·
        refine ⟨29157173807080671202908493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38876231742774228270544657 29157173807080671202908493)
        ·
          refine ⟨10933940177655251701090685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29157173807080671202908493 10933940177655251701090685)
          ·
            refine ⟨4100227566620719387909007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10933940177655251701090685 4100227566620719387909007)
            ·
              refine ⟨6150341349931079081863511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100227566620719387909007 6150341349931079081863511)
              ·
                refine ⟨9225512024896618622795267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150341349931079081863511 9225512024896618622795267)
                ·
                  refine ⟨13838268037344927934192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225512024896618622795267 13838268037344927934192901)
                  ·
                    refine ⟨2594675257002173987661169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13838268037344927934192901 2594675257002173987661169)
                    ·
                      refine ⟨1946006442751630490745877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594675257002173987661169 1946006442751630490745877)
                      ·
                        rfl

theorem cell23_3789834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_3789834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789834 prefixEnd_3789834 := by exact prefixLift 3789834
  have htrace : WordTrace (prefixWord ++ tailWord_3789834) baseStart_3789834 baseEnd_3789834 := by
    simpa [prefixWord, tailWord_3789834, baseEnd_3789834] using wordTrace_append hprefix tailTrace_3789834
  have hstable : (prefixWord ++ tailWord_3789834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789834).length < 2 ^ (prefixWord ++ tailWord_3789834).sum := by decide
  have hdescent : baseEnd_3789834 < baseStart_3789834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789857 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 5]
def baseStart_3789857 : Nat := 118140960795 + 3789857 * 2 ^ 59
def prefixEnd_3789857 : Nat := 4983230072969 + 3 ^ 40 * 3789857 * 2
def baseEnd_3789857 : Nat := 216224250311853766750919

theorem tailTrace_3789857 : CollatzResearch.WordTrace tailWord_3789857 prefixEnd_3789857 216224250311853766750919 := by
  unfold tailWord_3789857
  simp only [CollatzResearch.WordTrace]
  refine ⟨138227440631002819890023825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92151627087335213260015883 138227440631002819890023825)
  ·
    refine ⟨103670580473252114917517869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138227440631002819890023825 103670580473252114917517869)
    ·
      refine ⟨38876467677469543094069201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103670580473252114917517869 38876467677469543094069201)
      ·
        refine ⟨29157350758102157320551901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38876467677469543094069201 29157350758102157320551901)
        ·
          refine ⟨10934006534288308995206963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29157350758102157320551901 10934006534288308995206963)
          ·
            refine ⟨16401009801432463492810445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934006534288308995206963 16401009801432463492810445)
            ·
              refine ⟨6150378675537173809803917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16401009801432463492810445 6150378675537173809803917)
              ·
                refine ⟨2306392003326440178676469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6150378675537173809803917 2306392003326440178676469)
                ·
                  refine ⟨216224250311853766750919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306392003326440178676469 216224250311853766750919)
                  ·
                    rfl

theorem cell23_3789857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 5].length) (baseStart_3789857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789857 prefixEnd_3789857 := by exact prefixLift 3789857
  have htrace : WordTrace (prefixWord ++ tailWord_3789857) baseStart_3789857 baseEnd_3789857 := by
    simpa [prefixWord, tailWord_3789857, baseEnd_3789857] using wordTrace_append hprefix tailTrace_3789857
  have hstable : (prefixWord ++ tailWord_3789857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789857).length < 2 ^ (prefixWord ++ tailWord_3789857).sum := by decide
  have hdescent : baseEnd_3789857 < baseStart_3789857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789880 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_3789880 : Nat := 118140960795 + 3789880 * 2 ^ 59
def prefixEnd_3789880 : Nat := 4983230072969 + 3 ^ 40 * 3789880 * 2
def baseEnd_3789880 : Nat := 1946030062861737310770665

theorem tailTrace_3789880 : CollatzResearch.WordTrace tailWord_3789880 prefixEnd_3789880 1946030062861737310770665 := by
  unfold tailWord_3789880
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114139754959747409055547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92152186339946329878740729 69114139754959747409055547)
  ·
    refine ⟨103671209632439621113583321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69114139754959747409055547 103671209632439621113583321)
    ·
      refine ⟨77753407224329715835187491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103671209632439621113583321 77753407224329715835187491)
      ·
        refine ⟨116630110836494573752781237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77753407224329715835187491 116630110836494573752781237)
        ·
          refine ⟨10934072890921366289323241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116630110836494573752781237 10934072890921366289323241)
          ·
            refine ⟨8200554668191024716992431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10934072890921366289323241 8200554668191024716992431)
            ·
              refine ⟨12300832002286537075488647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200554668191024716992431 12300832002286537075488647)
              ·
                refine ⟨18451248003429805613232971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300832002286537075488647 18451248003429805613232971)
                ·
                  refine ⟨27676872005144708419849457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18451248003429805613232971 27676872005144708419849457)
                  ·
                    refine ⟨20757654003858531314887093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27676872005144708419849457 20757654003858531314887093)
                    ·
                      refine ⟨1946030062861737310770665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20757654003858531314887093 1946030062861737310770665)
                      ·
                        rfl

theorem cell23_3789880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_3789880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789880 prefixEnd_3789880 := by exact prefixLift 3789880
  have htrace : WordTrace (prefixWord ++ tailWord_3789880) baseStart_3789880 baseEnd_3789880 := by
    simpa [prefixWord, tailWord_3789880, baseEnd_3789880] using wordTrace_append hprefix tailTrace_3789880
  have hstable : (prefixWord ++ tailWord_3789880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789880).length < 2 ^ (prefixWord ++ tailWord_3789880).sum := by decide
  have hdescent : baseEnd_3789880 < baseStart_3789880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789900 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_3789900 : Nat := 118140960795 + 3789900 * 2 ^ 59
def prefixEnd_3789900 : Nat := 4983230072969 + 3 ^ 40 * 3789900 * 2
def baseEnd_3789900 : Nat := 648680110824942410840191

theorem tailTrace_3789900 : CollatzResearch.WordTrace tailWord_3789900 prefixEnd_3789900 648680110824942410840191 := by
  unfold tailWord_3789900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114504484923519116919577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92152672646564692155892769 69114504484923519116919577)
  ·
    refine ⟨51835878363692639337689683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69114504484923519116919577 51835878363692639337689683)
    ·
      refine ⟨77753817545538959006534525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51835878363692639337689683 77753817545538959006534525)
      ·
        refine ⟨29157681579577109627450447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77753817545538959006534525 29157681579577109627450447)
        ·
          refine ⟨43736522369365664441175671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29157681579577109627450447 43736522369365664441175671)
          ·
            refine ⟨65604783554048496661763507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43736522369365664441175671 65604783554048496661763507)
            ·
              refine ⟨98407175331072744992645261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65604783554048496661763507 98407175331072744992645261)
              ·
                refine ⟨36902690749152279372241973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98407175331072744992645261 36902690749152279372241973)
                ·
                  refine ⟨3459627257733026191147685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36902690749152279372241973 3459627257733026191147685)
                  ·
                    refine ⟨648680110824942410840191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459627257733026191147685 648680110824942410840191)
                    ·
                      rfl

theorem cell23_3789900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_3789900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789900 prefixEnd_3789900 := by exact prefixLift 3789900
  have htrace : WordTrace (prefixWord ++ tailWord_3789900) baseStart_3789900 baseEnd_3789900 := by
    simpa [prefixWord, tailWord_3789900, baseEnd_3789900] using wordTrace_append hprefix tailTrace_3789900
  have hstable : (prefixWord ++ tailWord_3789900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789900).length < 2 ^ (prefixWord ++ tailWord_3789900).sum := by decide
  have hdescent : baseEnd_3789900 < baseStart_3789900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789913 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 8]
def baseStart_3789913 : Nat := 118140960795 + 3789913 * 2 ^ 59
def prefixEnd_3789913 : Nat := 4983230072969 + 3 ^ 40 * 3789913 * 2
def baseEnd_3789913 : Nat := 216227445302592853517557

theorem tailTrace_3789913 : CollatzResearch.WordTrace tailWord_3789913 prefixEnd_3789913 216227445302592853517557 := by
  unfold tailWord_3789913
  simp only [CollatzResearch.WordTrace]
  refine ⟨138229483118799941454062393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92152988745866627636041595 138229483118799941454062393)
  ·
    refine ⟨103672112339099956090546795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138229483118799941454062393 103672112339099956090546795)
    ·
      refine ⟨155508168508649934135820193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103672112339099956090546795 155508168508649934135820193)
      ·
        refine ⟨116631126381487450601865145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155508168508649934135820193 116631126381487450601865145)
        ·
          refine ⟨87473344786115587951398859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116631126381487450601865145 87473344786115587951398859)
          ·
            refine ⟨131210017179173381927098289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87473344786115587951398859 131210017179173381927098289)
            ·
              refine ⟨98407512884380036445323717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131210017179173381927098289 98407512884380036445323717)
              ·
                refine ⟨18451408665821256833498197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98407512884380036445323717 18451408665821256833498197)
                ·
                  refine ⟨216227445302592853517557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18451408665821256833498197 216227445302592853517557)
                  ·
                    rfl

theorem cell23_3789913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_3789913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789913 prefixEnd_3789913 := by exact prefixLift 3789913
  have htrace : WordTrace (prefixWord ++ tailWord_3789913) baseStart_3789913 baseEnd_3789913 := by
    simpa [prefixWord, tailWord_3789913, baseEnd_3789913] using wordTrace_append hprefix tailTrace_3789913
  have hstable : (prefixWord ++ tailWord_3789913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789913).length < 2 ^ (prefixWord ++ tailWord_3789913).sum := by decide
  have hdescent : baseEnd_3789913 < baseStart_3789913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789927 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3789927 : Nat := 118140960795 + 3789927 * 2 ^ 59
def prefixEnd_3789927 : Nat := 4983230072969 + 3 ^ 40 * 3789927 * 2
def baseEnd_3789927 : Nat := 1946054196452498626882949

theorem tailTrace_3789927 : CollatzResearch.WordTrace tailWord_3789927 prefixEnd_3789927 1946054196452498626882949 := by
  unfold tailWord_3789927
  simp only [CollatzResearch.WordTrace]
  refine ⟨138229993740749221845072035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92153329160499481230048023 138229993740749221845072035)
  ·
    refine ⟨207344990611123832767608053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138229993740749221845072035 207344990611123832767608053)
    ·
      refine ⟨19438592869792859321963255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207344990611123832767608053 19438592869792859321963255)
      ·
        refine ⟨29157889304689288982944883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438592869792859321963255 29157889304689288982944883)
        ·
          refine ⟨43736833957033933474417325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29157889304689288982944883 43736833957033933474417325)
          ·
            refine ⟨16401312733887725052906497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43736833957033933474417325 16401312733887725052906497)
            ·
              refine ⟨12300984550415793789679873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401312733887725052906497 12300984550415793789679873)
              ·
                refine ⟨9225738412811845342259905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12300984550415793789679873 9225738412811845342259905)
                ·
                  refine ⟨6919303809608884006694929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9225738412811845342259905 6919303809608884006694929)
                  ·
                    refine ⟨5189477857206663005021197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6919303809608884006694929 5189477857206663005021197)
                    ·
                      refine ⟨1946054196452498626882949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5189477857206663005021197 1946054196452498626882949)
                      ·
                        rfl

theorem cell23_3789927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3789927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789927 prefixEnd_3789927 := by exact prefixLift 3789927
  have htrace : WordTrace (prefixWord ++ tailWord_3789927) baseStart_3789927 baseEnd_3789927 := by
    simpa [prefixWord, tailWord_3789927, baseEnd_3789927] using wordTrace_append hprefix tailTrace_3789927
  have hstable : (prefixWord ++ tailWord_3789927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789927).length < 2 ^ (prefixWord ++ tailWord_3789927).sum := by decide
  have hdescent : baseEnd_3789927 < baseStart_3789927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789941 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3789941 : Nat := 118140960795 + 3789941 * 2 ^ 59
def prefixEnd_3789941 : Nat := 4983230072969 + 3 ^ 40 * 3789941 * 2
def baseEnd_3789941 : Nat := 1946061385181661572107885

theorem tailTrace_3789941 : CollatzResearch.WordTrace tailWord_3789941 prefixEnd_3789941 1946061385181661572107885 := by
  unfold tailWord_3789941
  simp only [CollatzResearch.WordTrace]
  refine ⟨138230504362698502236081677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92153669575132334824054451 138230504362698502236081677)
  ·
    refine ⟨51836439136011938338530629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138230504362698502236081677 51836439136011938338530629)
    ·
      refine ⟨9719332338002238438474493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51836439136011938338530629 9719332338002238438474493)
      ·
        refine ⟨3644749626750839414427935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9719332338002238438474493 3644749626750839414427935)
        ·
          refine ⟨5467124440126259121641903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644749626750839414427935 5467124440126259121641903)
          ·
            refine ⟨8200686660189388682462855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467124440126259121641903 8200686660189388682462855)
            ·
              refine ⟨12301029990284083023694283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200686660189388682462855 12301029990284083023694283)
              ·
                refine ⟨18451544985426124535541425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12301029990284083023694283 18451544985426124535541425)
                ·
                  refine ⟨13838658739069593401656069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18451544985426124535541425 13838658739069593401656069)
                  ·
                    refine ⟨2594748513575548762810513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13838658739069593401656069 2594748513575548762810513)
                    ·
                      refine ⟨1946061385181661572107885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594748513575548762810513 1946061385181661572107885)
                      ·
                        rfl

theorem cell23_3789941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3789941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789941 prefixEnd_3789941 := by exact prefixLift 3789941
  have htrace : WordTrace (prefixWord ++ tailWord_3789941) baseStart_3789941 baseEnd_3789941 := by
    simpa [prefixWord, tailWord_3789941, baseEnd_3789941] using wordTrace_append hprefix tailTrace_3789941
  have hstable : (prefixWord ++ tailWord_3789941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789941).length < 2 ^ (prefixWord ++ tailWord_3789941).sum := by decide
  have hdescent : baseEnd_3789941 < baseStart_3789941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789991 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3789991 : Nat := 118140960795 + 3789991 * 2 ^ 59
def prefixEnd_3789991 : Nat := 4983230072969 + 3 ^ 40 * 3789991 * 2
def baseEnd_3789991 : Nat := 1946087059214386376482655

theorem tailTrace_3789991 : CollatzResearch.WordTrace tailWord_3789991 prefixEnd_3789991 1946087059214386376482655 := by
  unfold tailWord_3789991
  simp only [CollatzResearch.WordTrace]
  refine ⟨138232328012517360775401827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92154885341678240516934551 138232328012517360775401827)
  ·
    refine ⟨207348492018776041163102741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138232328012517360775401827 207348492018776041163102741)
    ·
      refine ⟨9719460563380126929520441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207348492018776041163102741 9719460563380126929520441)
      ·
        refine ⟨7289595422535095197140331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9719460563380126929520441 7289595422535095197140331)
        ·
          refine ⟨10934393133802642795710497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289595422535095197140331 10934393133802642795710497)
          ·
            refine ⟨8200794850351982096782873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10934393133802642795710497 8200794850351982096782873)
            ·
              refine ⟨6150596137763986572587155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8200794850351982096782873 6150596137763986572587155)
              ·
                refine ⟨9225894206645979858880733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150596137763986572587155 9225894206645979858880733)
                ·
                  refine ⟨3459710327492242447080275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9225894206645979858880733 3459710327492242447080275)
                  ·
                    refine ⟨5189565491238363670620413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3459710327492242447080275 5189565491238363670620413)
                    ·
                      refine ⟨1946087059214386376482655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5189565491238363670620413 1946087059214386376482655)
                      ·
                        rfl

theorem cell23_3789991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3789991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3789991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3789991 prefixEnd_3789991 := by exact prefixLift 3789991
  have htrace : WordTrace (prefixWord ++ tailWord_3789991) baseStart_3789991 baseEnd_3789991 := by
    simpa [prefixWord, tailWord_3789991, baseEnd_3789991] using wordTrace_append hprefix tailTrace_3789991
  have hstable : (prefixWord ++ tailWord_3789991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789991).length < 2 ^ (prefixWord ++ tailWord_3789991).sum := by decide
  have hdescent : baseEnd_3789991 < baseStart_3789991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_3790000 : Nat := 118140960795 + 3790000 * 2 ^ 59
def prefixEnd_3790000 : Nat := 4983230072969 + 3 ^ 40 * 3790000 * 2
def baseEnd_3790000 : Nat := 1946091680540276841270113

theorem tailTrace_3790000 : CollatzResearch.WordTrace tailWord_3790000 prefixEnd_3790000 1946091680540276841270113 := by
  unfold tailWord_3790000
  simp only [CollatzResearch.WordTrace]
  refine ⟨69116328134742377656239727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92155104179656503541652969 69116328134742377656239727)
  ·
    refine ⟨103674492202113566484359591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69116328134742377656239727 103674492202113566484359591)
    ·
      refine ⟨155511738303170349726539387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103674492202113566484359591 155511738303170349726539387)
      ·
        refine ⟨233267607454755524589809081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155511738303170349726539387 233267607454755524589809081)
        ·
          refine ⟨174950705591066643442356811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233267607454755524589809081 174950705591066643442356811)
          ·
            refine ⟨262426058386599965163535217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174950705591066643442356811 262426058386599965163535217)
            ·
              refine ⟨196819543789949973872651413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262426058386599965163535217 196819543789949973872651413)
              ·
                refine ⟨9225916115153905025280535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196819543789949973872651413 9225916115153905025280535)
                ·
                  refine ⟨13838874172730857537920803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225916115153905025280535 13838874172730857537920803)
                  ·
                    refine ⟨20758311259096286306881205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13838874172730857537920803 20758311259096286306881205)
                    ·
                      refine ⟨1946091680540276841270113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20758311259096286306881205 1946091680540276841270113)
                      ·
                        rfl

theorem cell23_3790000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_3790000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790000 prefixEnd_3790000 := by exact prefixLift 3790000
  have htrace : WordTrace (prefixWord ++ tailWord_3790000) baseStart_3790000 baseEnd_3790000 := by
    simpa [prefixWord, tailWord_3790000, baseEnd_3790000] using wordTrace_append hprefix tailTrace_3790000
  have hstable : (prefixWord ++ tailWord_3790000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790000).length < 2 ^ (prefixWord ++ tailWord_3790000).sum := by decide
  have hdescent : baseEnd_3790000 < baseStart_3790000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790014 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3790014 : Nat := 118140960795 + 3790014 * 2 ^ 59
def prefixEnd_3790014 : Nat := 4983230072969 + 3 ^ 40 * 3790014 * 2
def baseEnd_3790014 : Nat := 1946098869269439786495049

theorem tailTrace_3790014 : CollatzResearch.WordTrace tailWord_3790014 prefixEnd_3790014 1946098869269439786495049 := by
  unfold tailWord_3790014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279145861429254462936137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92155444594289357135659397 17279145861429254462936137)
  ·
    refine ⟨12959359396071940847202103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17279145861429254462936137 12959359396071940847202103)
    ·
      refine ⟨19439039094107911270803155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959359396071940847202103 19439039094107911270803155)
      ·
        refine ⟨29158558641161866906204733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19439039094107911270803155 29158558641161866906204733)
        ·
          refine ⟨10934459490435700089826775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29158558641161866906204733 10934459490435700089826775)
          ·
            refine ⟨16401689235653550134740163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934459490435700089826775 16401689235653550134740163)
            ·
              refine ⟨24602533853480325202110245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16401689235653550134740163 24602533853480325202110245)
              ·
                refine ⟨4612975097527560975395671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24602533853480325202110245 4612975097527560975395671)
                ·
                  refine ⟨6919462646291341463093507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612975097527560975395671 6919462646291341463093507)
                  ·
                    refine ⟨10379193969437012194640261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919462646291341463093507 10379193969437012194640261)
                    ·
                      refine ⟨1946098869269439786495049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10379193969437012194640261 1946098869269439786495049)
                      ·
                        rfl

theorem cell23_3790014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3790014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790014 prefixEnd_3790014 := by exact prefixLift 3790014
  have htrace : WordTrace (prefixWord ++ tailWord_3790014) baseStart_3790014 baseEnd_3790014 := by
    simpa [prefixWord, tailWord_3790014, baseEnd_3790014] using wordTrace_append hprefix tailTrace_3790014
  have hstable : (prefixWord ++ tailWord_3790014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790014).length < 2 ^ (prefixWord ++ tailWord_3790014).sum := by decide
  have hdescent : baseEnd_3790014 < baseStart_3790014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790031 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 1, 2, 2]
def baseStart_3790031 : Nat := 118140960795 + 3790031 * 2 ^ 59
def prefixEnd_3790031 : Nat := 4983230072969 + 3 ^ 40 * 3790031 * 2
def baseEnd_3790031 : Nat := 1946107598440566219982471

theorem tailTrace_3790031 : CollatzResearch.WordTrace tailWord_3790031 prefixEnd_3790031 1946107598440566219982471 := by
  unfold tailWord_3790031
  simp only [CollatzResearch.WordTrace]
  refine ⟨138233786932372447606857947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92155857954914965071238631 138233786932372447606857947)
  ·
    refine ⟨207350680398558671410286921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138233786932372447606857947 207350680398558671410286921)
    ·
      refine ⟨155513010298919003557715191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207350680398558671410286921 155513010298919003557715191)
      ·
        refine ⟨233269515448378505336572787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155513010298919003557715191 233269515448378505336572787)
        ·
          refine ⟨349904273172567758004859181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233269515448378505336572787 349904273172567758004859181)
          ·
            refine ⟨131214102439712909251822193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349904273172567758004859181 131214102439712909251822193)
            ·
              refine ⟨98410576829784681938866645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131214102439712909251822193 98410576829784681938866645)
              ·
                refine ⟨2306497894448078482942187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98410576829784681938866645 2306497894448078482942187)
                ·
                  refine ⟨3459746841672117724413281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306497894448078482942187 3459746841672117724413281)
                  ·
                    refine ⟨2594810131254088293309961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3459746841672117724413281 2594810131254088293309961)
                    ·
                      refine ⟨1946107598440566219982471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594810131254088293309961 1946107598440566219982471)
                      ·
                        rfl

theorem cell23_3790031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 2, 2].length) (baseStart_3790031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790031 prefixEnd_3790031 := by exact prefixLift 3790031
  have htrace : WordTrace (prefixWord ++ tailWord_3790031) baseStart_3790031 baseEnd_3790031 := by
    simpa [prefixWord, tailWord_3790031, baseEnd_3790031] using wordTrace_append hprefix tailTrace_3790031
  have hstable : (prefixWord ++ tailWord_3790031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790031).length < 2 ^ (prefixWord ++ tailWord_3790031).sum := by decide
  have hdescent : baseEnd_3790031 < baseStart_3790031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790034 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3790034 : Nat := 118140960795 + 3790034 * 2 ^ 59
def prefixEnd_3790034 : Nat := 4983230072969 + 3 ^ 40 * 3790034 * 2
def baseEnd_3790034 : Nat := 1946109138882529708244957

theorem tailTrace_3790034 : CollatzResearch.WordTrace tailWord_3790034 prefixEnd_3790034 1946109138882529708244957 := by
  unfold tailWord_3790034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558474087840394779804289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92155930900907719412811437 34558474087840394779804289)
  ·
    refine ⟨25918855565880296084853217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34558474087840394779804289 25918855565880296084853217)
    ·
      refine ⟨19439141674410222063639913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25918855565880296084853217 19439141674410222063639913)
      ·
        refine ⟨14579356255807666547729935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19439141674410222063639913 14579356255807666547729935)
        ·
          refine ⟨21869034383711499821594903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14579356255807666547729935 21869034383711499821594903)
          ·
            refine ⟨32803551575567249732392355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21869034383711499821594903 32803551575567249732392355)
            ·
              refine ⟨49205327363350874598588533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32803551575567249732392355 49205327363350874598588533)
              ·
                refine ⟨4612999440314144493617675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49205327363350874598588533 4612999440314144493617675)
                ·
                  refine ⟨6919499160471216740426513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612999440314144493617675 6919499160471216740426513)
                  ·
                    refine ⟨5189624370353412555319885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6919499160471216740426513 5189624370353412555319885)
                    ·
                      refine ⟨1946109138882529708244957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5189624370353412555319885 1946109138882529708244957)
                      ·
                        rfl

theorem cell23_3790034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3790034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790034 prefixEnd_3790034 := by exact prefixLift 3790034
  have htrace : WordTrace (prefixWord ++ tailWord_3790034) baseStart_3790034 baseEnd_3790034 := by
    simpa [prefixWord, tailWord_3790034, baseEnd_3790034] using wordTrace_append hprefix tailTrace_3790034
  have hstable : (prefixWord ++ tailWord_3790034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790034).length < 2 ^ (prefixWord ++ tailWord_3790034).sum := by decide
  have hdescent : baseEnd_3790034 < baseStart_3790034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790037 : List Nat := [1, 3, 2, 4, 1, 3, 9]
def baseStart_3790037 : Nat := 118140960795 + 3790037 * 2 ^ 59
def prefixEnd_3790037 : Nat := 4983230072969 + 3 ^ 40 * 3790037 * 2
def baseEnd_3790037 : Nat := 24026057769438187611203

theorem tailTrace_3790037 : CollatzResearch.WordTrace tailWord_3790037 prefixEnd_3790037 24026057769438187611203 := by
  unfold tailWord_3790037
  simp only [CollatzResearch.WordTrace]
  refine ⟨138234005770350710631576365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92156003846900473754384243 138234005770350710631576365)
  ·
    refine ⟨51837752163881516486841137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138234005770350710631576365 51837752163881516486841137)
    ·
      refine ⟨38878314122911137365130853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51837752163881516486841137 38878314122911137365130853)
      ·
        refine ⟨7289683898045838255962035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38878314122911137365130853 7289683898045838255962035)
        ·
          refine ⟨10934525847068757383943053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289683898045838255962035 10934525847068757383943053)
          ·
            refine ⟨4100447192650784018978645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10934525847068757383943053 4100447192650784018978645)
            ·
              refine ⟨24026057769438187611203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4100447192650784018978645 24026057769438187611203)
              ·
                rfl

theorem cell23_3790037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 9].length) (baseStart_3790037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790037 prefixEnd_3790037 := by exact prefixLift 3790037
  have htrace : WordTrace (prefixWord ++ tailWord_3790037) baseStart_3790037 baseEnd_3790037 := by
    simpa [prefixWord, tailWord_3790037, baseEnd_3790037] using wordTrace_append hprefix tailTrace_3790037
  have hstable : (prefixWord ++ tailWord_3790037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790037).length < 2 ^ (prefixWord ++ tailWord_3790037).sum := by decide
  have hdescent : baseEnd_3790037 < baseStart_3790037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790074 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_3790074 : Nat := 118140960795 + 3790074 * 2 ^ 59
def prefixEnd_3790074 : Nat := 4983230072969 + 3 ^ 40 * 3790074 * 2
def baseEnd_3790074 : Nat := 1946129678108709551744773

theorem tailTrace_3790074 : CollatzResearch.WordTrace tailWord_3790074 prefixEnd_3790074 1946129678108709551744773 := by
  unfold tailWord_3790074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558838817804166487668319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92156903514144443967115517 34558838817804166487668319)
  ·
    refine ⟨51838258226706249731502479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34558838817804166487668319 51838258226706249731502479)
    ·
      refine ⟨77757387340059374597253719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51838258226706249731502479 77757387340059374597253719)
      ·
        refine ⟨116636081010089061895880579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77757387340059374597253719 116636081010089061895880579)
        ·
          refine ⟨174954121515133592843820869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116636081010089061895880579 174954121515133592843820869)
          ·
            refine ⟨32803897784087548658216413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174954121515133592843820869 32803897784087548658216413)
            ·
              refine ⟨12301461669032830746831155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32803897784087548658216413 12301461669032830746831155)
              ·
                refine ⟨18452192503549246120246733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12301461669032830746831155 18452192503549246120246733)
                ·
                  refine ⟨6919572188830967295092525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18452192503549246120246733 6919572188830967295092525)
                  ·
                    refine ⟨2594839570811612735659697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6919572188830967295092525 2594839570811612735659697)
                    ·
                      refine ⟨1946129678108709551744773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2594839570811612735659697 1946129678108709551744773)
                      ·
                        rfl

theorem cell23_3790074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_3790074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790074 prefixEnd_3790074 := by exact prefixLift 3790074
  have htrace : WordTrace (prefixWord ++ tailWord_3790074) baseStart_3790074 baseEnd_3790074 := by
    simpa [prefixWord, tailWord_3790074, baseEnd_3790074] using wordTrace_append hprefix tailTrace_3790074
  have hstable : (prefixWord ++ tailWord_3790074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790074).length < 2 ^ (prefixWord ++ tailWord_3790074).sum := by decide
  have hdescent : baseEnd_3790074 < baseStart_3790074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790080 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_3790080 : Nat := 118140960795 + 3790080 * 2 ^ 59
def prefixEnd_3790080 : Nat := 4983230072969 + 3 ^ 40 * 3790080 * 2
def baseEnd_3790080 : Nat := 648710919664212176089915

theorem tailTrace_3790080 : CollatzResearch.WordTrace tailWord_3790080 prefixEnd_3790080 648710919664212176089915 := by
  unfold tailWord_3790080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69117787054597464487695847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92157049406129952650261129 69117787054597464487695847)
  ·
    refine ⟨103676680581896196731543771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69117787054597464487695847 103676680581896196731543771)
    ·
      refine ⟨155515020872844295097315657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103676680581896196731543771 155515020872844295097315657)
      ·
        refine ⟨116636265654633221322986743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155515020872844295097315657 116636265654633221322986743)
        ·
          refine ⟨174954398481949831984480115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116636265654633221322986743 174954398481949831984480115)
          ·
            refine ⟨262431597722924747976720173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174954398481949831984480115 262431597722924747976720173)
            ·
              refine ⟨98411849146096780491270065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262431597722924747976720173 98411849146096780491270065)
              ·
                refine ⟨73808886859572585368452549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98411849146096780491270065 73808886859572585368452549)
                ·
                  refine ⟨13839166286169859756584853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73808886859572585368452549 13839166286169859756584853)
                  ·
                    refine ⟨648710919664212176089915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13839166286169859756584853 648710919664212176089915)
                    ·
                      rfl

theorem cell23_3790080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_3790080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790080 prefixEnd_3790080 := by exact prefixLift 3790080
  have htrace : WordTrace (prefixWord ++ tailWord_3790080) baseStart_3790080 baseEnd_3790080 := by
    simpa [prefixWord, tailWord_3790080, baseEnd_3790080] using wordTrace_append hprefix tailTrace_3790080
  have hstable : (prefixWord ++ tailWord_3790080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790080).length < 2 ^ (prefixWord ++ tailWord_3790080).sum := by decide
  have hdescent : baseEnd_3790080 < baseStart_3790080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790114 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3790114 : Nat := 118140960795 + 3790114 * 2 ^ 59
def prefixEnd_3790114 : Nat := 4983230072969 + 3 ^ 40 * 3790114 * 2
def baseEnd_3790114 : Nat := 648716739111629798414863

theorem tailTrace_3790114 : CollatzResearch.WordTrace tailWord_3790114 prefixEnd_3790114 648716739111629798414863 := by
  unfold tailWord_3790114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34559203547767938195532349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92157876127381168521419597 34559203547767938195532349)
  ·
    refine ⟨12959701330412976823324631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34559203547767938195532349 12959701330412976823324631)
    ·
      refine ⟨19439551995619465234986947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959701330412976823324631 19439551995619465234986947)
      ·
        refine ⟨29159327993429197852480421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19439551995619465234986947 29159327993429197852480421)
        ·
          refine ⟨5467373998767974597340079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29159327993429197852480421 5467373998767974597340079)
          ·
            refine ⟨8201060998151961896010119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467373998767974597340079 8201060998151961896010119)
            ·
              refine ⟨12301591497227942844015179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201060998151961896010119 12301591497227942844015179)
              ·
                refine ⟨18452387245841914266022769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12301591497227942844015179 18452387245841914266022769)
                ·
                  refine ⟨13839290434381435699517077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18452387245841914266022769 13839290434381435699517077)
                  ·
                    refine ⟨648716739111629798414863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13839290434381435699517077 648716739111629798414863)
                    ·
                      rfl

theorem cell23_3790114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3790114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790114 prefixEnd_3790114 := by exact prefixLift 3790114
  have htrace : WordTrace (prefixWord ++ tailWord_3790114) baseStart_3790114 baseEnd_3790114 := by
    simpa [prefixWord, tailWord_3790114, baseEnd_3790114] using wordTrace_append hprefix tailTrace_3790114
  have hstable : (prefixWord ++ tailWord_3790114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790114).length < 2 ^ (prefixWord ++ tailWord_3790114).sum := by decide
  have hdescent : baseEnd_3790114 < baseStart_3790114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790117 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3790117 : Nat := 118140960795 + 3790117 * 2 ^ 59
def prefixEnd_3790117 : Nat := 4983230072969 + 3 ^ 40 * 3790117 * 2
def baseEnd_3790117 : Nat := 1946151757776852883507075

theorem tailTrace_3790117 : CollatzResearch.WordTrace tailWord_3790117 prefixEnd_3790117 1946151757776852883507075 := by
  unfold tailWord_3790117
  simp only [CollatzResearch.WordTrace]
  refine ⟨138236923610060884294488605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92157949073373922862992403 138236923610060884294488605)
  ·
    refine ⟨51838846353772831610433227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138236923610060884294488605 51838846353772831610433227)
    ·
      refine ⟨77758269530659247415649841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51838846353772831610433227 77758269530659247415649841)
      ·
        refine ⟨58318702147994435561737381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77758269530659247415649841 58318702147994435561737381)
        ·
          refine ⟨10934756652748956667825759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58318702147994435561737381 10934756652748956667825759)
          ·
            refine ⟨16402134979123435001738639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934756652748956667825759 16402134979123435001738639)
            ·
              refine ⟨24603202468685152502607959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16402134979123435001738639 24603202468685152502607959)
              ·
                refine ⟨36904803703027728753911939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24603202468685152502607959 36904803703027728753911939)
                ·
                  refine ⟨55357205554541593130867909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36904803703027728753911939 55357205554541593130867909)
                  ·
                    refine ⟨10379476041476548712037733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55357205554541593130867909 10379476041476548712037733)
                    ·
                      refine ⟨1946151757776852883507075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10379476041476548712037733 1946151757776852883507075)
                      ·
                        rfl

theorem cell23_3790117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3790117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790117 prefixEnd_3790117 := by exact prefixLift 3790117
  have htrace : WordTrace (prefixWord ++ tailWord_3790117) baseStart_3790117 baseEnd_3790117 := by
    simpa [prefixWord, tailWord_3790117, baseEnd_3790117] using wordTrace_append hprefix tailTrace_3790117
  have hstable : (prefixWord ++ tailWord_3790117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790117).length < 2 ^ (prefixWord ++ tailWord_3790117).sum := by decide
  have hdescent : baseEnd_3790117 < baseStart_3790117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790144 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 5]
def baseStart_3790144 : Nat := 118140960795 + 3790144 * 2 ^ 59
def prefixEnd_3790144 : Nat := 4983230072969 + 3 ^ 40 * 3790144 * 2
def baseEnd_3790144 : Nat := 216240624639391586429939

theorem tailTrace_3790144 : CollatzResearch.WordTrace tailWord_3790144 prefixEnd_3790144 216240624639391586429939 := by
  unfold tailWord_3790144
  simp only [CollatzResearch.WordTrace]
  refine ⟨69118954190481533952860743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92158605587308711937147657 69118954190481533952860743)
  ·
    refine ⟨103678431285722300929291115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69118954190481533952860743 103678431285722300929291115)
    ·
      refine ⟨155517646928583451393936673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103678431285722300929291115 155517646928583451393936673)
      ·
        refine ⟨116638235196437588545452505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155517646928583451393936673 116638235196437588545452505)
        ·
          refine ⟨87478676397328191409089379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116638235196437588545452505 87478676397328191409089379)
          ·
            refine ⟨131218014595992287113634069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87478676397328191409089379 131218014595992287113634069)
            ·
              refine ⟨6150844434187138458451597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131218014595992287113634069 6150844434187138458451597)
              ·
                refine ⟨2306566662820176921919349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6150844434187138458451597 2306566662820176921919349)
                ·
                  refine ⟨216240624639391586429939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306566662820176921919349 216240624639391586429939)
                  ·
                    rfl

theorem cell23_3790144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 5].length) (baseStart_3790144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790144 prefixEnd_3790144 := by exact prefixLift 3790144
  have htrace : WordTrace (prefixWord ++ tailWord_3790144) baseStart_3790144 baseEnd_3790144 := by
    simpa [prefixWord, tailWord_3790144, baseEnd_3790144] using wordTrace_append hprefix tailTrace_3790144
  have hstable : (prefixWord ++ tailWord_3790144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790144).length < 2 ^ (prefixWord ++ tailWord_3790144).sum := by decide
  have hdescent : baseEnd_3790144 < baseStart_3790144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790194 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3790194 : Nat := 118140960795 + 3790194 * 2 ^ 59
def prefixEnd_3790194 : Nat := 4983230072969 + 3 ^ 40 * 3790194 * 2
def baseEnd_3790194 : Nat := 1946191295787249082244221

theorem tailTrace_3790194 : CollatzResearch.WordTrace tailWord_3790194 prefixEnd_3790194 1946191295787249082244221 := by
  unfold tailWord_3790194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34559933007695481611260409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92159821353854617630027757 34559933007695481611260409)
  ·
    refine ⟨25919949755771611208445307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34559933007695481611260409 25919949755771611208445307)
    ·
      refine ⟨38879924633657416812667961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25919949755771611208445307 38879924633657416812667961)
      ·
        refine ⟨29159943475243062609500971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38879924633657416812667961 29159943475243062609500971)
        ·
          refine ⟨43739915212864593914251457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29159943475243062609500971 43739915212864593914251457)
          ·
            refine ⟨32804936409648445435688593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43739915212864593914251457 32804936409648445435688593)
            ·
              refine ⟨24603702307236334076766445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32804936409648445435688593 24603702307236334076766445)
              ·
                refine ⟨9226388365213625278787417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24603702307236334076766445 9226388365213625278787417)
                ·
                  refine ⟨6919791273910218959090563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226388365213625278787417 6919791273910218959090563)
                  ·
                    refine ⟨10379686910865328438635845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919791273910218959090563 10379686910865328438635845)
                    ·
                      refine ⟨1946191295787249082244221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10379686910865328438635845 1946191295787249082244221)
                      ·
                        rfl

theorem cell23_3790194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3790194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790194 prefixEnd_3790194 := by exact prefixLift 3790194
  have htrace : WordTrace (prefixWord ++ tailWord_3790194) baseStart_3790194 baseEnd_3790194 := by
    simpa [prefixWord, tailWord_3790194, baseEnd_3790194] using wordTrace_append hprefix tailTrace_3790194
  have hstable : (prefixWord ++ tailWord_3790194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790194).length < 2 ^ (prefixWord ++ tailWord_3790194).sum := by decide
  have hdescent : baseEnd_3790194 < baseStart_3790194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790234 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_3790234 : Nat := 118140960795 + 3790234 * 2 ^ 59
def prefixEnd_3790234 : Nat := 4983230072969 + 3 ^ 40 * 3790234 * 2
def baseEnd_3790234 : Nat := 216245759445936547304893

theorem tailTrace_3790234 : CollatzResearch.WordTrace tailWord_3790234 prefixEnd_3790234 216245759445936547304893 := by
  unfold tailWord_3790234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34560297737659253319124439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92160793967091342184331837 34560297737659253319124439)
  ·
    refine ⟨51840446606488879978686659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34560297737659253319124439 51840446606488879978686659)
    ·
      refine ⟨77760669909733319968029989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51840446606488879978686659 77760669909733319968029989)
      ·
        refine ⟨14580125608074997494005623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77760669909733319968029989 14580125608074997494005623)
        ·
          refine ⟨21870188412112496241008435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580125608074997494005623 21870188412112496241008435)
          ·
            refine ⟨32805282618168744361512653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21870188412112496241008435 32805282618168744361512653)
            ·
              refine ⟨12301980981813279135567245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32805282618168744361512653 12301980981813279135567245)
              ·
                refine ⟨4613242868179979675837717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12301980981813279135567245 4613242868179979675837717)
                ·
                  refine ⟨216245759445936547304893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4613242868179979675837717 216245759445936547304893)
                  ·
                    rfl

theorem cell23_3790234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_3790234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790234 prefixEnd_3790234 := by exact prefixLift 3790234
  have htrace : WordTrace (prefixWord ++ tailWord_3790234) baseStart_3790234 baseEnd_3790234 := by
    simpa [prefixWord, tailWord_3790234, baseEnd_3790234] using wordTrace_append hprefix tailTrace_3790234
  have hstable : (prefixWord ++ tailWord_3790234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790234).length < 2 ^ (prefixWord ++ tailWord_3790234).sum := by decide
  have hdescent : baseEnd_3790234 < baseStart_3790234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790264 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_3790264 : Nat := 118140960795 + 3790264 * 2 ^ 59
def prefixEnd_3790264 : Nat := 4983230072969 + 3 ^ 40 * 3790264 * 2
def baseEnd_3790264 : Nat := 648742413144354602789633

theorem tailTrace_3790264 : CollatzResearch.WordTrace tailWord_3790264 prefixEnd_3790264 648742413144354602789633 := by
  unfold tailWord_3790264
  simp only [CollatzResearch.WordTrace]
  refine ⟨69121142570264164200044923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92161523427018885600059897 69121142570264164200044923)
  ·
    refine ⟨103681713855396246300067385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69121142570264164200044923 103681713855396246300067385)
    ·
      refine ⟨77761285391547184725050539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103681713855396246300067385 77761285391547184725050539)
      ·
        refine ⟨116641928087320777087575809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77761285391547184725050539 116641928087320777087575809)
        ·
          refine ⟨87481446065490582815681857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116641928087320777087575809 87481446065490582815681857)
          ·
            refine ⟨65611084549117937111761393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87481446065490582815681857 65611084549117937111761393)
            ·
              refine ⟨49208313411838452833821045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65611084549117937111761393 49208313411838452833821045)
              ·
                refine ⟨4613279382359854953170723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49208313411838452833821045 4613279382359854953170723)
                ·
                  refine ⟨6919919073539782429756085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613279382359854953170723 6919919073539782429756085)
                  ·
                    refine ⟨648742413144354602789633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6919919073539782429756085 648742413144354602789633)
                    ·
                      rfl

theorem cell23_3790264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_3790264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790264 prefixEnd_3790264 := by exact prefixLift 3790264
  have htrace : WordTrace (prefixWord ++ tailWord_3790264) baseStart_3790264 baseEnd_3790264 := by
    simpa [prefixWord, tailWord_3790264, baseEnd_3790264] using wordTrace_append hprefix tailTrace_3790264
  have hstable : (prefixWord ++ tailWord_3790264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790264).length < 2 ^ (prefixWord ++ tailWord_3790264).sum := by decide
  have hdescent : baseEnd_3790264 < baseStart_3790264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790301 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3790301 : Nat := 118140960795 + 3790301 * 2 ^ 59
def prefixEnd_3790301 : Nat := 4983230072969 + 3 ^ 40 * 3790301 * 2
def baseEnd_3790301 : Nat := 1946246238217280163606229

theorem tailTrace_3790301 : CollatzResearch.WordTrace tailWord_3790301 prefixEnd_3790301 1946246238217280163606229 := by
  unfold tailWord_3790301
  simp only [CollatzResearch.WordTrace]
  refine ⟨138243634641394283719186757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92162423094262855812791171 138243634641394283719186757)
  ·
    refine ⟨25920681495261428197347517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138243634641394283719186757 25920681495261428197347517)
    ·
      refine ⟨9720255560723035574005319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25920681495261428197347517 9720255560723035574005319)
      ·
        refine ⟨14580383341084553361007979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9720255560723035574005319 14580383341084553361007979)
        ·
          refine ⟨21870575011626830041511969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580383341084553361007979 21870575011626830041511969)
          ·
            refine ⟨16402931258720122531133977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21870575011626830041511969 16402931258720122531133977)
            ·
              refine ⟨12302198444040091898350483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16402931258720122531133977 12302198444040091898350483)
              ·
                refine ⟨18453297666060137847525725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12302198444040091898350483 18453297666060137847525725)
                ·
                  refine ⟨6919986624772551692822147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18453297666060137847525725 6919986624772551692822147)
                  ·
                    refine ⟨10379979937158827539233221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919986624772551692822147 10379979937158827539233221)
                    ·
                      refine ⟨1946246238217280163606229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10379979937158827539233221 1946246238217280163606229)
                      ·
                        rfl

theorem cell23_3790301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3790301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790301 prefixEnd_3790301 := by exact prefixLift 3790301
  have htrace : WordTrace (prefixWord ++ tailWord_3790301) baseStart_3790301 baseEnd_3790301 := by
    simpa [prefixWord, tailWord_3790301, baseEnd_3790301] using wordTrace_append hprefix tailTrace_3790301
  have hstable : (prefixWord ++ tailWord_3790301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790301).length < 2 ^ (prefixWord ++ tailWord_3790301).sum := by decide
  have hdescent : baseEnd_3790301 < baseStart_3790301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790318 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_3790318 : Nat := 118140960795 + 3790318 * 2 ^ 59
def prefixEnd_3790318 : Nat := 4983230072969 + 3 ^ 40 * 3790318 * 2
def baseEnd_3790318 : Nat := 1946254967388406597093651

theorem tailTrace_3790318 : CollatzResearch.WordTrace tailWord_3790318 prefixEnd_3790318 1946254967388406597093651 := by
  unfold tailWord_3790318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280531835291586952819451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92162836454888463748370405 17280531835291586952819451)
  ·
    refine ⟨25920797752937380429229177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17280531835291586952819451 25920797752937380429229177)
    ·
      refine ⟨19440598314703035321921883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25920797752937380429229177 19440598314703035321921883)
      ·
        refine ⟨29160897472054552982882825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19440598314703035321921883 29160897472054552982882825)
        ·
          refine ⟨21870673104040914737162119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29160897472054552982882825 21870673104040914737162119)
          ·
            refine ⟨32806009656061372105743179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21870673104040914737162119 32806009656061372105743179)
            ·
              refine ⟨49209014484092058158614769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32806009656061372105743179 49209014484092058158614769)
              ·
                refine ⟨36906760863069043618961077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49209014484092058158614769 36906760863069043618961077)
                ·
                  refine ⟨3460008830912722839277601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36906760863069043618961077 3460008830912722839277601)
                  ·
                    refine ⟨2595006623184542129458201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460008830912722839277601 2595006623184542129458201)
                    ·
                      refine ⟨1946254967388406597093651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595006623184542129458201 1946254967388406597093651)
                      ·
                        rfl

theorem cell23_3790318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_3790318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790318 prefixEnd_3790318 := by exact prefixLift 3790318
  have htrace : WordTrace (prefixWord ++ tailWord_3790318) baseStart_3790318 baseEnd_3790318 := by
    simpa [prefixWord, tailWord_3790318, baseEnd_3790318] using wordTrace_append hprefix tailTrace_3790318
  have hstable : (prefixWord ++ tailWord_3790318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790318).length < 2 ^ (prefixWord ++ tailWord_3790318).sum := by decide
  have hdescent : baseEnd_3790318 < baseStart_3790318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790328 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_3790328 : Nat := 118140960795 + 3790328 * 2 ^ 59
def prefixEnd_3790328 : Nat := 4983230072969 + 3 ^ 40 * 3790328 * 2
def baseEnd_3790328 : Nat := 648753367398317185989535

theorem tailTrace_3790328 : CollatzResearch.WordTrace tailWord_3790328 prefixEnd_3790328 648753367398317185989535 := by
  unfold tailWord_3790328
  simp only [CollatzResearch.WordTrace]
  refine ⟨69122309706148233665209819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92163079608197644886946425 69122309706148233665209819)
  ·
    refine ⟨103683464559222350497814729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69122309706148233665209819 103683464559222350497814729)
    ·
      refine ⟨77762598419416762873361047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103683464559222350497814729 77762598419416762873361047)
      ·
        refine ⟨116643897629125144310041571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77762598419416762873361047 116643897629125144310041571)
        ·
          refine ⟨174965846443687716465062357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116643897629125144310041571 174965846443687716465062357)
          ·
            refine ⟨4100762026023930854649899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174965846443687716465062357 4100762026023930854649899)
            ·
              refine ⟨6151143039035896281974849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100762026023930854649899 6151143039035896281974849)
              ·
                refine ⟨4613357279276922211481137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151143039035896281974849 4613357279276922211481137)
                ·
                  refine ⟨3460017959457691658610853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613357279276922211481137 3460017959457691658610853)
                  ·
                    refine ⟨648753367398317185989535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460017959457691658610853 648753367398317185989535)
                    ·
                      rfl

theorem cell23_3790328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_3790328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790328 prefixEnd_3790328 := by exact prefixLift 3790328
  have htrace : WordTrace (prefixWord ++ tailWord_3790328) baseStart_3790328 baseEnd_3790328 := by
    simpa [prefixWord, tailWord_3790328, baseEnd_3790328] using wordTrace_append hprefix tailTrace_3790328
  have hstable : (prefixWord ++ tailWord_3790328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790328).length < 2 ^ (prefixWord ++ tailWord_3790328).sum := by decide
  have hdescent : baseEnd_3790328 < baseStart_3790328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790338 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3790338 : Nat := 118140960795 + 3790338 * 2 ^ 59
def prefixEnd_3790338 : Nat := 4983230072969 + 3 ^ 40 * 3790338 * 2
def baseEnd_3790338 : Nat := 1946265237001496518843559

theorem tailTrace_3790338 : CollatzResearch.WordTrace tailWord_3790338 prefixEnd_3790338 1946265237001496518843559 := by
  unfold tailWord_3790338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561246035565059759570917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92163322761506826025522445 34561246035565059759570917)
  ·
    refine ⟨6480233631668448704919547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34561246035565059759570917 6480233631668448704919547)
    ·
      refine ⟨9720350447502673057379321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480233631668448704919547 9720350447502673057379321)
      ·
        refine ⟨7290262835627004793034491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720350447502673057379321 7290262835627004793034491)
        ·
          refine ⟨10935394253440507189551737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290262835627004793034491 10935394253440507189551737)
          ·
            refine ⟨8201545690080380392163803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10935394253440507189551737 8201545690080380392163803)
            ·
              refine ⟨12302318535120570588245705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201545690080380392163803 12302318535120570588245705)
              ·
                refine ⟨9226738901340427941184279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12302318535120570588245705 9226738901340427941184279)
                ·
                  refine ⟨13840108352010641911776419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9226738901340427941184279 13840108352010641911776419)
                  ·
                    refine ⟨20760162528015962867664629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13840108352010641911776419 20760162528015962867664629)
                    ·
                      refine ⟨1946265237001496518843559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20760162528015962867664629 1946265237001496518843559)
                      ·
                        rfl

theorem cell23_3790338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3790338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790338 prefixEnd_3790338 := by exact prefixLift 3790338
  have htrace : WordTrace (prefixWord ++ tailWord_3790338) baseStart_3790338 baseEnd_3790338 := by
    simpa [prefixWord, tailWord_3790338, baseEnd_3790338] using wordTrace_append hprefix tailTrace_3790338
  have hstable : (prefixWord ++ tailWord_3790338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790338).length < 2 ^ (prefixWord ++ tailWord_3790338).sum := by decide
  have hdescent : baseEnd_3790338 < baseStart_3790338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790348 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3790348 : Nat := 118140960795 + 3790348 * 2 ^ 59
def prefixEnd_3790348 : Nat := 4983230072969 + 3 ^ 40 * 3790348 * 2
def baseEnd_3790348 : Nat := 1946270371808041479718513

theorem tailTrace_3790348 : CollatzResearch.WordTrace tailWord_3790348 prefixEnd_3790348 1946270371808041479718513 := by
  unfold tailWord_3790348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69122674436112005373073849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92163565914816007164098465 69122674436112005373073849)
  ·
    refine ⟨51842005827084004029805387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69122674436112005373073849 51842005827084004029805387)
    ·
      refine ⟨77763008740626006044708081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51842005827084004029805387 77763008740626006044708081)
      ·
        refine ⟨58322256555469504533531061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77763008740626006044708081 58322256555469504533531061)
        ·
          refine ⟨5467711552075266050018537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58322256555469504533531061 5467711552075266050018537)
          ·
            refine ⟨4100783664056449537513903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467711552075266050018537 4100783664056449537513903)
            ·
              refine ⟨6151175496084674306270855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100783664056449537513903 6151175496084674306270855)
              ·
                refine ⟨9226763244127011459406283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151175496084674306270855 9226763244127011459406283)
                ·
                  refine ⟨13840144866190517189109425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9226763244127011459406283 13840144866190517189109425)
                  ·
                    refine ⟨10380108649642887891832069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13840144866190517189109425 10380108649642887891832069)
                    ·
                      refine ⟨1946270371808041479718513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10380108649642887891832069 1946270371808041479718513)
                      ·
                        rfl

theorem cell23_3790348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3790348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790348 prefixEnd_3790348 := by exact prefixLift 3790348
  have htrace : WordTrace (prefixWord ++ tailWord_3790348) baseStart_3790348 baseEnd_3790348 := by
    simpa [prefixWord, tailWord_3790348, baseEnd_3790348] using wordTrace_append hprefix tailTrace_3790348
  have hstable : (prefixWord ++ tailWord_3790348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790348).length < 2 ^ (prefixWord ++ tailWord_3790348).sum := by decide
  have hdescent : baseEnd_3790348 < baseStart_3790348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790364 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3790364 : Nat := 118140960795 + 3790364 * 2 ^ 59
def prefixEnd_3790364 : Nat := 4983230072969 + 3 ^ 40 * 3790364 * 2
def baseEnd_3790364 : Nat := 1946278587498513417118439

theorem tailTrace_3790364 : CollatzResearch.WordTrace tailWord_3790364 prefixEnd_3790364 1946278587498513417118439 := by
  unfold tailWord_3790364
  simp only [CollatzResearch.WordTrace]
  refine ⟨69122966220083022739365073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92163954960110696985820097 69122966220083022739365073)
  ·
    refine ⟨51842224665062267054523805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69122966220083022739365073 51842224665062267054523805)
    ·
      refine ⟨19440834249398350145446427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51842224665062267054523805 19440834249398350145446427)
      ·
        refine ⟨29161251374097525218169641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19440834249398350145446427 29161251374097525218169641)
        ·
          refine ⟨21870938530573143913627231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29161251374097525218169641 21870938530573143913627231)
          ·
            refine ⟨32806407795859715870440847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21870938530573143913627231 32806407795859715870440847)
            ·
              refine ⟨49209611693789573805661271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32806407795859715870440847 49209611693789573805661271)
              ·
                refine ⟨73814417540684360708491907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49209611693789573805661271 73814417540684360708491907)
                ·
                  refine ⟨110721626311026541062737861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73814417540684360708491907 110721626311026541062737861)
                  ·
                    refine ⟨20760304933317476449263349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110721626311026541062737861 20760304933317476449263349)
                    ·
                      refine ⟨1946278587498513417118439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20760304933317476449263349 1946278587498513417118439)
                      ·
                        rfl

theorem cell23_3790364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3790364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790364 prefixEnd_3790364 := by exact prefixLift 3790364
  have htrace : WordTrace (prefixWord ++ tailWord_3790364) baseStart_3790364 baseEnd_3790364 := by
    simpa [prefixWord, tailWord_3790364, baseEnd_3790364] using wordTrace_append hprefix tailTrace_3790364
  have hstable : (prefixWord ++ tailWord_3790364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790364).length < 2 ^ (prefixWord ++ tailWord_3790364).sum := by decide
  have hdescent : baseEnd_3790364 < baseStart_3790364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790368 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3790368 : Nat := 118140960795 + 3790368 * 2 ^ 59
def prefixEnd_3790368 : Nat := 4983230072969 + 3 ^ 40 * 3790368 * 2
def baseEnd_3790368 : Nat := 1946280641421131401468421

theorem tailTrace_3790368 : CollatzResearch.WordTrace tailWord_3790368 prefixEnd_3790368 1946280641421131401468421 := by
  unfold tailWord_3790368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69123039166075777080937879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92164052221434369441250505 69123039166075777080937879)
  ·
    refine ⟨103684558749113665621406819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69123039166075777080937879 103684558749113665621406819)
    ·
      refine ⟨155526838123670498432110229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103684558749113665621406819 155526838123670498432110229)
      ·
        refine ⟨7290320537047054614005167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155526838123670498432110229 7290320537047054614005167)
        ·
          refine ⟨10935480805570581921007751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290320537047054614005167 10935480805570581921007751)
          ·
            refine ⟨16403221208355872881511627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935480805570581921007751 16403221208355872881511627)
            ·
              refine ⟨24604831812533809322267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16403221208355872881511627 24604831812533809322267441)
              ·
                refine ⟨18453623859400356991700581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24604831812533809322267441 18453623859400356991700581)
                ·
                  refine ⟨3460054473637566935943859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18453623859400356991700581 3460054473637566935943859)
                  ·
                    refine ⟨5190081710456350403915789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3460054473637566935943859 5190081710456350403915789)
                    ·
                      refine ⟨1946280641421131401468421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5190081710456350403915789 1946280641421131401468421)
                      ·
                        rfl

theorem cell23_3790368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3790368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790368 prefixEnd_3790368 := by exact prefixLift 3790368
  have htrace : WordTrace (prefixWord ++ tailWord_3790368) baseStart_3790368 baseEnd_3790368 := by
    simpa [prefixWord, tailWord_3790368, baseEnd_3790368] using wordTrace_append hprefix tailTrace_3790368
  have hstable : (prefixWord ++ tailWord_3790368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790368).length < 2 ^ (prefixWord ++ tailWord_3790368).sum := by decide
  have hdescent : baseEnd_3790368 < baseStart_3790368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790394 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3790394 : Nat := 118140960795 + 3790394 * 2 ^ 59
def prefixEnd_3790394 : Nat := 4983230072969 + 3 ^ 40 * 3790394 * 2
def baseEnd_3790394 : Nat := 1946293991918148299743301

theorem tailTrace_3790394 : CollatzResearch.WordTrace tailWord_3790394 prefixEnd_3790394 1946293991918148299743301 := by
  unfold tailWord_3790394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561756657514340150580559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92164684420038240401548157 34561756657514340150580559)
  ·
    refine ⟨51842634986271510225870839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34561756657514340150580559 51842634986271510225870839)
    ·
      refine ⟨77763952479407265338806259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51842634986271510225870839 77763952479407265338806259)
      ·
        refine ⟨116645928719110898008209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77763952479407265338806259 116645928719110898008209389)
        ·
          refine ⟨43742223269666586753078521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116645928719110898008209389 43742223269666586753078521)
          ·
            refine ⟨32806667452249940064808891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43742223269666586753078521 32806667452249940064808891)
            ·
              refine ⟨49210001178374910097213337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32806667452249940064808891 49210001178374910097213337)
              ·
                refine ⟨36907500883781182572910003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49210001178374910097213337 36907500883781182572910003)
                ·
                  refine ⟨55361251325671773859365005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36907500883781182572910003 55361251325671773859365005)
                  ·
                    refine ⟨20760469247126915197261877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55361251325671773859365005 20760469247126915197261877)
                    ·
                      refine ⟨1946293991918148299743301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20760469247126915197261877 1946293991918148299743301)
                      ·
                        rfl

theorem cell23_3790394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3790394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790394 prefixEnd_3790394 := by exact prefixLift 3790394
  have htrace : WordTrace (prefixWord ++ tailWord_3790394) baseStart_3790394 baseEnd_3790394 := by
    simpa [prefixWord, tailWord_3790394, baseEnd_3790394] using wordTrace_append hprefix tailTrace_3790394
  have hstable : (prefixWord ++ tailWord_3790394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790394).length < 2 ^ (prefixWord ++ tailWord_3790394).sum := by decide
  have hdescent : baseEnd_3790394 < baseStart_3790394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790414 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3790414 : Nat := 118140960795 + 3790414 * 2 ^ 59
def prefixEnd_3790414 : Nat := 4983230072969 + 3 ^ 40 * 3790414 * 2
def baseEnd_3790414 : Nat := 216256029059026469054801

theorem tailTrace_3790414 : CollatzResearch.WordTrace tailWord_3790414 prefixEnd_3790414 216256029059026469054801 := by
  unfold tailWord_3790414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280969511248113002256287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92165170726656602678700197 17280969511248113002256287)
  ·
    refine ⟨25921454266872169503384431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17280969511248113002256287 25921454266872169503384431)
    ·
      refine ⟨38882181400308254255076647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25921454266872169503384431 38882181400308254255076647)
      ·
        refine ⟨58323272100462381382614971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38882181400308254255076647 58323272100462381382614971)
        ·
          refine ⟨87484908150693572073922457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58323272100462381382614971 87484908150693572073922457)
          ·
            refine ⟨65613681113020179055441843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87484908150693572073922457 65613681113020179055441843)
            ·
              refine ⟨98420521669530268583162765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65613681113020179055441843 98420521669530268583162765)
              ·
                refine ⟨36907695626073850718686037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98420521669530268583162765 36907695626073850718686037)
                ·
                  refine ⟨216256029059026469054801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36907695626073850718686037 216256029059026469054801)
                  ·
                    rfl

theorem cell23_3790414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3790414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790414 prefixEnd_3790414 := by exact prefixLift 3790414
  have htrace : WordTrace (prefixWord ++ tailWord_3790414) baseStart_3790414 baseEnd_3790414 := by
    simpa [prefixWord, tailWord_3790414, baseEnd_3790414] using wordTrace_append hprefix tailTrace_3790414
  have hstable : (prefixWord ++ tailWord_3790414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790414).length < 2 ^ (prefixWord ++ tailWord_3790414).sum := by decide
  have hdescent : baseEnd_3790414 < baseStart_3790414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790442 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3790442 : Nat := 118140960795 + 3790442 * 2 ^ 59
def prefixEnd_3790442 : Nat := 4983230072969 + 3 ^ 40 * 3790442 * 2
def baseEnd_3790442 : Nat := 1946318638989564111943081

theorem tailTrace_3790442 : CollatzResearch.WordTrace tailWord_3790442 prefixEnd_3790442 1946318638989564111943081 := by
  unfold tailWord_3790442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562194333470866200017395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92165851555922309866713053 34562194333470866200017395)
  ·
    refine ⟨51843291500206299300026093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34562194333470866200017395 51843291500206299300026093)
    ·
      refine ⟨19441234312577362237509785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51843291500206299300026093 19441234312577362237509785)
      ·
        refine ⟨14580925734433021678132339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19441234312577362237509785 14580925734433021678132339)
        ·
          refine ⟨21871388601649532517198509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580925734433021678132339 21871388601649532517198509)
          ·
            refine ⟨8201770725618574693949441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21871388601649532517198509 8201770725618574693949441)
            ·
              refine ⟨6151328044213931020462081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8201770725618574693949441 6151328044213931020462081)
              ·
                refine ⟨4613496033160448265346561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151328044213931020462081 4613496033160448265346561)
                ·
                  refine ⟨3460122024870336199009921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613496033160448265346561 3460122024870336199009921)
                  ·
                    refine ⟨2595091518652752149257441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460122024870336199009921 2595091518652752149257441)
                    ·
                      refine ⟨1946318638989564111943081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2595091518652752149257441 1946318638989564111943081)
                      ·
                        rfl

theorem cell23_3790442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3790442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790442 prefixEnd_3790442 := by exact prefixLift 3790442
  have htrace : WordTrace (prefixWord ++ tailWord_3790442) baseStart_3790442 baseEnd_3790442 := by
    simpa [prefixWord, tailWord_3790442, baseEnd_3790442] using wordTrace_append hprefix tailTrace_3790442
  have hstable : (prefixWord ++ tailWord_3790442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790442).length < 2 ^ (prefixWord ++ tailWord_3790442).sum := by decide
  have hdescent : baseEnd_3790442 < baseStart_3790442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790444 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_3790444 : Nat := 118140960795 + 3790444 * 2 ^ 59
def prefixEnd_3790444 : Nat := 4983230072969 + 3 ^ 40 * 3790444 * 2
def baseEnd_3790444 : Nat := 648773221983624368039357

theorem tailTrace_3790444 : CollatzResearch.WordTrace tailWord_3790444 prefixEnd_3790444 648773221983624368039357 := by
  unfold tailWord_3790444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69124425139938109570821193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92165900186584146094428257 69124425139938109570821193)
  ·
    refine ⟨51843318854953582178115895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69124425139938109570821193 51843318854953582178115895)
    ·
      refine ⟨77764978282430373267173843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51843318854953582178115895 77764978282430373267173843)
      ·
        refine ⟨116647467423645559900760765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77764978282430373267173843 116647467423645559900760765)
        ·
          refine ⟨43742800283867084962785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116647467423645559900760765 43742800283867084962785287)
          ·
            refine ⟨65614200425800627444177931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43742800283867084962785287 65614200425800627444177931)
            ·
              refine ⟨98421300638700941166266897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65614200425800627444177931 98421300638700941166266897)
              ·
                refine ⟨73815975479025705874700173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98421300638700941166266897 73815975479025705874700173)
                ·
                  refine ⟨27680990804634639703012565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73815975479025705874700173 27680990804634639703012565)
                  ·
                    refine ⟨648773221983624368039357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27680990804634639703012565 648773221983624368039357)
                    ·
                      rfl

theorem cell23_3790444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_3790444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3790444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3790444 prefixEnd_3790444 := by exact prefixLift 3790444
  have htrace : WordTrace (prefixWord ++ tailWord_3790444) baseStart_3790444 baseEnd_3790444 := by
    simpa [prefixWord, tailWord_3790444, baseEnd_3790444] using wordTrace_append hprefix tailTrace_3790444
  have hstable : (prefixWord ++ tailWord_3790444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790444).length < 2 ^ (prefixWord ++ tailWord_3790444).sum := by decide
  have hdescent : baseEnd_3790444 < baseStart_3790444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
