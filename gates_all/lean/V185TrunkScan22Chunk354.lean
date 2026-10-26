import V185TrunkScan22Chunk353

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3158703 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 1, 4]
def baseStart_3158703 : Nat := 118140960795 + 3158703 * 2 ^ 59
def prefixEnd_3158703 : Nat := 4983230072969 + 3 ^ 40 * 3158703 * 2
def baseEnd_3158703 : Nat := 1081288589199240195790597

theorem tailTrace_3158703 : CollatzResearch.WordTrace tailWord_3158703 prefixEnd_3158703 1081288589199240195790597 := by
  unfold tailWord_3158703
  simp only [CollatzResearch.WordTrace]
  refine ⟨115207363075565969368624763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76804908717043979579083175 115207363075565969368624763)
  ·
    refine ⟨172811044613348954052937145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115207363075565969368624763 172811044613348954052937145)
    ·
      refine ⟨129608283460011715539702859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172811044613348954052937145 129608283460011715539702859)
      ·
        refine ⟨194412425190017573309554289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129608283460011715539702859 194412425190017573309554289)
        ·
          refine ⟨145809318892513179982165717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194412425190017573309554289 145809318892513179982165717)
          ·
            refine ⟨3417405911543277655832009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145809318892513179982165717 3417405911543277655832009)
            ·
              refine ⟨2563054433657458241874007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417405911543277655832009 2563054433657458241874007)
              ·
                refine ⟨3844581650486187362811011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563054433657458241874007 3844581650486187362811011)
                ·
                  refine ⟨5766872475729281044216517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844581650486187362811011 5766872475729281044216517)
                  ·
                    refine ⟨1081288589199240195790597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766872475729281044216517 1081288589199240195790597)
                    ·
                      rfl

theorem cell22_3158703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_3158703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158703 prefixEnd_3158703 := by exact prefixLift 3158703
  have htrace : WordTrace (prefixWord ++ tailWord_3158703) baseStart_3158703 baseEnd_3158703 := by
    simpa [prefixWord, tailWord_3158703, baseEnd_3158703] using wordTrace_append hprefix tailTrace_3158703
  have hstable : (prefixWord ++ tailWord_3158703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158703).length < 2 ^ (prefixWord ++ tailWord_3158703).sum := by decide
  have hdescent : baseEnd_3158703 < baseStart_3158703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158714 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_3158714 : Nat := 118140960795 + 3158714 * 2 ^ 59
def prefixEnd_3158714 : Nat := 4983230072969 + 3 ^ 40 * 3158714 * 2
def baseEnd_3158714 : Nat := 1081292354724039833765563

theorem tailTrace_3158714 : CollatzResearch.WordTrace tailWord_3158714 prefixEnd_3158714 1081292354724039833765563 := by
  unfold tailWord_3158714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801941069631529561818799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76805176185684078831516797 28801941069631529561818799)
  ·
    refine ⟨43202911604447294342728199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28801941069631529561818799 43202911604447294342728199)
    ·
      refine ⟨64804367406670941514092299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43202911604447294342728199 64804367406670941514092299)
      ·
        refine ⟨97206551110006412271138449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64804367406670941514092299 97206551110006412271138449)
        ·
          refine ⟨72904913332504809203353837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97206551110006412271138449 72904913332504809203353837)
          ·
            refine ⟨27339342499689303451257689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72904913332504809203353837 27339342499689303451257689)
            ·
              refine ⟨20504506874766977588443267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27339342499689303451257689 20504506874766977588443267)
              ·
                refine ⟨30756760312150466382664901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20504506874766977588443267 30756760312150466382664901)
                ·
                  refine ⟨5766892558528212446749669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30756760312150466382664901 5766892558528212446749669)
                  ·
                    refine ⟨1081292354724039833765563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766892558528212446749669 1081292354724039833765563)
                    ·
                      rfl

theorem cell22_3158714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_3158714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158714 prefixEnd_3158714 := by exact prefixLift 3158714
  have htrace : WordTrace (prefixWord ++ tailWord_3158714) baseStart_3158714 baseEnd_3158714 := by
    simpa [prefixWord, tailWord_3158714, baseEnd_3158714] using wordTrace_append hprefix tailTrace_3158714
  have hstable : (prefixWord ++ tailWord_3158714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158714).length < 2 ^ (prefixWord ++ tailWord_3158714).sum := by decide
  have hdescent : baseEnd_3158714 < baseStart_3158714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158716 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3158716 : Nat := 118140960795 + 3158716 * 2 ^ 59
def prefixEnd_3158716 : Nat := 4983230072969 + 3 ^ 40 * 3158716 * 2
def baseEnd_3158716 : Nat := 1081293039364912495215557

theorem tailTrace_3158716 : CollatzResearch.WordTrace tailWord_3158716 prefixEnd_3158716 1081293039364912495215557 := by
  unfold tailWord_3158716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57603918612259436294424001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76805224816345915059232001 57603918612259436294424001)
  ·
    refine ⟨43202938959194577220818001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57603918612259436294424001 43202938959194577220818001)
    ·
      refine ⟨32402204219395932915613501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43202938959194577220818001 32402204219395932915613501)
      ·
        refine ⟨12150826582273474843355063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32402204219395932915613501 12150826582273474843355063)
        ·
          refine ⟨18226239873410212265032595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150826582273474843355063 18226239873410212265032595)
          ·
            refine ⟨27339359810115318397548893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18226239873410212265032595 27339359810115318397548893)
            ·
              refine ⟨10252259928793244399080835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27339359810115318397548893 10252259928793244399080835)
              ·
                refine ⟨15378389893189866598621253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252259928793244399080835 15378389893189866598621253)
                ·
                  refine ⟨2883448104973099987241485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15378389893189866598621253 2883448104973099987241485)
                  ·
                    refine ⟨1081293039364912495215557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883448104973099987241485 1081293039364912495215557)
                    ·
                      rfl

theorem cell22_3158716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3158716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158716 prefixEnd_3158716 := by exact prefixLift 3158716
  have htrace : WordTrace (prefixWord ++ tailWord_3158716) baseStart_3158716 baseEnd_3158716 := by
    simpa [prefixWord, tailWord_3158716, baseEnd_3158716] using wordTrace_append hprefix tailTrace_3158716
  have hstable : (prefixWord ++ tailWord_3158716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158716).length < 2 ^ (prefixWord ++ tailWord_3158716).sum := by decide
  have hdescent : baseEnd_3158716 < baseStart_3158716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158778 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_3158778 : Nat := 118140960795 + 3158778 * 2 ^ 59
def prefixEnd_3158778 : Nat := 4983230072969 + 3 ^ 40 * 3158778 * 2
def baseEnd_3158778 : Nat := 1081314263231965000165367

theorem tailTrace_3158778 : CollatzResearch.WordTrace tailWord_3158778 prefixEnd_3158778 1081314263231965000165367 := by
  unfold tailWord_3158778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802524637573564294401247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76806732366862838118403325 28802524637573564294401247)
  ·
    refine ⟨43203786956360346441601871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28802524637573564294401247 43203786956360346441601871)
    ·
      refine ⟨64805680434540519662402807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43203786956360346441601871 64805680434540519662402807)
      ·
        refine ⟨97208520651810779493604211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64805680434540519662402807 97208520651810779493604211)
        ·
          refine ⟨145812780977716169240406317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97208520651810779493604211 145812780977716169240406317)
          ·
            refine ⟨54679792866643563465152369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145812780977716169240406317 54679792866643563465152369)
            ·
              refine ⟨41009844649982672598864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54679792866643563465152369 41009844649982672598864277)
              ·
                refine ⟨1922336467967937778071763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41009844649982672598864277 1922336467967937778071763)
                ·
                  refine ⟨2883504701951906667107645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922336467967937778071763 2883504701951906667107645)
                  ·
                    refine ⟨1081314263231965000165367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883504701951906667107645 1081314263231965000165367)
                    ·
                      rfl

theorem cell22_3158778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_3158778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158778 prefixEnd_3158778 := by exact prefixLift 3158778
  have htrace : WordTrace (prefixWord ++ tailWord_3158778) baseStart_3158778 baseEnd_3158778 := by
    simpa [prefixWord, tailWord_3158778, baseEnd_3158778] using wordTrace_append hprefix tailTrace_3158778
  have hstable : (prefixWord ++ tailWord_3158778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158778).length < 2 ^ (prefixWord ++ tailWord_3158778).sum := by decide
  have hdescent : baseEnd_3158778 < baseStart_3158778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3158789 : Nat := 118140960795 + 3158789 * 2 ^ 59
def prefixEnd_3158789 : Nat := 4983230072969 + 3 ^ 40 * 3158789 * 2
def baseEnd_3158789 : Nat := 1081318028756764638140333

theorem tailTrace_3158789 : CollatzResearch.WordTrace tailWord_3158789 prefixEnd_3158789 1081318028756764638140333 := by
  unfold tailWord_3158789
  simp only [CollatzResearch.WordTrace]
  refine ⟨115210499753254406056255421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76806999835502937370836947 115210499753254406056255421)
  ·
    refine ⟨43203937407470402271095783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115210499753254406056255421 43203937407470402271095783)
    ·
      refine ⟨64805906111205603406643675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43203937407470402271095783 64805906111205603406643675)
      ·
        refine ⟨97208859166808405109965513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64805906111205603406643675 97208859166808405109965513)
        ·
          refine ⟨72906644375106303832474135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97208859166808405109965513 72906644375106303832474135)
          ·
            refine ⟨109359966562659455748711203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72906644375106303832474135 109359966562659455748711203)
            ·
              refine ⟨164039949843989183623066805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109359966562659455748711203 164039949843989183623066805)
              ·
                refine ⟨15378745297873985964662513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164039949843989183623066805 15378745297873985964662513)
                ·
                  refine ⟨11534058973405489473496885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15378745297873985964662513 11534058973405489473496885)
                  ·
                    refine ⟨1081318028756764638140333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11534058973405489473496885 1081318028756764638140333)
                    ·
                      rfl

theorem cell22_3158789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3158789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158789 prefixEnd_3158789 := by exact prefixLift 3158789
  have htrace : WordTrace (prefixWord ++ tailWord_3158789) baseStart_3158789 baseEnd_3158789 := by
    simpa [prefixWord, tailWord_3158789, baseEnd_3158789] using wordTrace_append hprefix tailTrace_3158789
  have hstable : (prefixWord ++ tailWord_3158789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158789).length < 2 ^ (prefixWord ++ tailWord_3158789).sum := by decide
  have hdescent : baseEnd_3158789 < baseStart_3158789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158829 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3158829 : Nat := 118140960795 + 3158829 * 2 ^ 59
def prefixEnd_3158829 : Nat := 4983230072969 + 3 ^ 40 * 3158829 * 2
def baseEnd_3158829 : Nat := 1081331721574217867140211

theorem tailTrace_3158829 : CollatzResearch.WordTrace tailWord_3158829 prefixEnd_3158829 1081331721574217867140211 := by
  unfold tailWord_3158829
  simp only [CollatzResearch.WordTrace]
  refine ⟨115211958673109492887711541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76807972448739661925141027 115211958673109492887711541)
  ·
    refine ⟨10801121125604014958222957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115211958673109492887711541 10801121125604014958222957)
    ·
      refine ⟨4050420422101505609333609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10801121125604014958222957 4050420422101505609333609)
      ·
        refine ⟨3037815316576129207000207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050420422101505609333609 3037815316576129207000207)
        ·
          refine ⟨4556722974864193810500311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037815316576129207000207 4556722974864193810500311)
          ·
            refine ⟨6835084462296290715750467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556722974864193810500311 6835084462296290715750467)
            ·
              refine ⟨10252626693444436073625701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835084462296290715750467 10252626693444436073625701)
              ·
                refine ⟨1922367505020831763804819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10252626693444436073625701 1922367505020831763804819)
                ·
                  refine ⟨2883551257531247645707229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922367505020831763804819 2883551257531247645707229)
                  ·
                    refine ⟨1081331721574217867140211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883551257531247645707229 1081331721574217867140211)
                    ·
                      rfl

theorem cell22_3158829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3158829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158829 prefixEnd_3158829 := by exact prefixLift 3158829
  have htrace : WordTrace (prefixWord ++ tailWord_3158829) baseStart_3158829 baseEnd_3158829 := by
    simpa [prefixWord, tailWord_3158829, baseEnd_3158829] using wordTrace_append hprefix tailTrace_3158829
  have hstable : (prefixWord ++ tailWord_3158829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158829).length < 2 ^ (prefixWord ++ tailWord_3158829).sum := by decide
  have hdescent : baseEnd_3158829 < baseStart_3158829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158851 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_3158851 : Nat := 118140960795 + 3158851 * 2 ^ 59
def prefixEnd_3158851 : Nat := 4983230072969 + 3 ^ 40 * 3158851 * 2
def baseEnd_3158851 : Nat := 1081339252623817143090143

theorem tailTrace_3158851 : CollatzResearch.WordTrace tailWord_3158851 prefixEnd_3158851 1081339252623817143090143 := by
  unfold tailWord_3158851
  simp only [CollatzResearch.WordTrace]
  refine ⟨115212761079029790645012407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76808507386019860430008271 115212761079029790645012407)
  ·
    refine ⟨172819141618544685967518611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115212761079029790645012407 172819141618544685967518611)
    ·
      refine ⟨259228712427817028951277917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172819141618544685967518611 259228712427817028951277917)
      ·
        refine ⟨97210767160431385856729219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259228712427817028951277917 97210767160431385856729219)
        ·
          refine ⟨145816150740647078785093829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97210767160431385856729219 145816150740647078785093829)
          ·
            refine ⟨27340528263871327272205093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145816150740647078785093829 27340528263871327272205093)
            ·
              refine ⟨5126349049475873863538455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27340528263871327272205093 5126349049475873863538455)
              ·
                refine ⟨7689523574213810795307683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126349049475873863538455 7689523574213810795307683)
                ·
                  refine ⟨11534285361320716192961525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689523574213810795307683 11534285361320716192961525)
                  ·
                    refine ⟨1081339252623817143090143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11534285361320716192961525 1081339252623817143090143)
                    ·
                      rfl

theorem cell22_3158851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_3158851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158851 prefixEnd_3158851 := by exact prefixLift 3158851
  have htrace : WordTrace (prefixWord ++ tailWord_3158851) baseStart_3158851 baseEnd_3158851 := by
    simpa [prefixWord, tailWord_3158851, baseEnd_3158851] using wordTrace_append hprefix tailTrace_3158851
  have hstable : (prefixWord ++ tailWord_3158851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158851).length < 2 ^ (prefixWord ++ tailWord_3158851).sum := by decide
  have hdescent : baseEnd_3158851 < baseStart_3158851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158864 : List Nat := [2, 1, 1, 1, 1, 4, 2, 10]
def baseStart_3158864 : Nat := 118140960795 + 3158864 * 2 ^ 59
def prefixEnd_3158864 : Nat := 4983230072969 + 3 ^ 40 * 3158864 * 2
def baseEnd_3158864 : Nat := 120149300309943271390567

theorem tailTrace_3158864 : CollatzResearch.WordTrace tailWord_3158864 prefixEnd_3158864 120149300309943271390567 := by
  unfold tailWord_3158864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57606617613991346932617823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76808823485321795910157097 57606617613991346932617823)
  ·
    refine ⟨86409926420987020398926735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57606617613991346932617823 86409926420987020398926735)
    ·
      refine ⟨129614889631480530598390103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86409926420987020398926735 129614889631480530598390103)
      ·
        refine ⟨194422334447220795897585155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129614889631480530598390103 194422334447220795897585155)
        ·
          refine ⟨291633501670831193846377733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194422334447220795897585155 291633501670831193846377733)
          ·
            refine ⟨54681281563280848846195825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291633501670831193846377733 54681281563280848846195825)
            ·
              refine ⟨41010961172460636634646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54681281563280848846195825 41010961172460636634646869)
              ·
                refine ⟨120149300309943271390567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41010961172460636634646869 120149300309943271390567)
                ·
                  rfl

theorem cell22_3158864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_3158864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158864 prefixEnd_3158864 := by exact prefixLift 3158864
  have htrace : WordTrace (prefixWord ++ tailWord_3158864) baseStart_3158864 baseEnd_3158864 := by
    simpa [prefixWord, tailWord_3158864, baseEnd_3158864] using wordTrace_append hprefix tailTrace_3158864
  have hstable : (prefixWord ++ tailWord_3158864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158864).length < 2 ^ (prefixWord ++ tailWord_3158864).sum := by decide
  have hdescent : baseEnd_3158864 < baseStart_3158864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158866 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3158866 : Nat := 118140960795 + 3158866 * 2 ^ 59
def prefixEnd_3158866 : Nat := 4983230072969 + 3 ^ 40 * 3158866 * 2
def baseEnd_3158866 : Nat := 1081344387430362103965097

theorem tailTrace_3158866 : CollatzResearch.WordTrace tailWord_3158866 prefixEnd_3158866 1081344387430362103965097 := by
  unfold tailWord_3158866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28803327043493862051702113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76808872115983632137872301 28803327043493862051702113)
  ·
    refine ⟨21602495282620396538776585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28803327043493862051702113 21602495282620396538776585)
    ·
      refine ⟨16201871461965297404082439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21602495282620396538776585 16201871461965297404082439)
      ·
        refine ⟨24302807192947946106123659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16201871461965297404082439 24302807192947946106123659)
        ·
          refine ⟨36454210789421919159185489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24302807192947946106123659 36454210789421919159185489)
          ·
            refine ⟨27340658092066439369389117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36454210789421919159185489 27340658092066439369389117)
            ·
              refine ⟨10252746784524914763520919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27340658092066439369389117 10252746784524914763520919)
              ·
                refine ⟨15379120176787372145281379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252746784524914763520919 15379120176787372145281379)
                ·
                  refine ⟨23068680265181058217922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15379120176787372145281379 23068680265181058217922069)
                  ·
                    refine ⟨1081344387430362103965097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23068680265181058217922069 1081344387430362103965097)
                    ·
                      rfl

theorem cell22_3158866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3158866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158866 prefixEnd_3158866 := by exact prefixLift 3158866
  have htrace : WordTrace (prefixWord ++ tailWord_3158866) baseStart_3158866 baseEnd_3158866 := by
    simpa [prefixWord, tailWord_3158866, baseEnd_3158866] using wordTrace_append hprefix tailTrace_3158866
  have hstable : (prefixWord ++ tailWord_3158866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158866).length < 2 ^ (prefixWord ++ tailWord_3158866).sum := by decide
  have hdescent : baseEnd_3158866 < baseStart_3158866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158956 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_3158956 : Nat := 118140960795 + 3158956 * 2 ^ 59
def prefixEnd_3158956 : Nat := 4983230072969 + 3 ^ 40 * 3158956 * 2
def baseEnd_3158956 : Nat := 1081375196269631869214821

theorem tailTrace_3158956 : CollatzResearch.WordTrace tailWord_3158956 prefixEnd_3158956 1081375196269631869214821 := by
  unfold tailWord_3158956
  simp only [CollatzResearch.WordTrace]
  refine ⟨57608295371824696788792361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76811060495766262385056481 57608295371824696788792361)
  ·
    refine ⟨43206221528868522591594271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57608295371824696788792361 43206221528868522591594271)
    ·
      refine ⟨64809332293302783887391407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43206221528868522591594271 64809332293302783887391407)
      ·
        refine ⟨97213998439954175831087111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64809332293302783887391407 97213998439954175831087111)
        ·
          refine ⟨145820997659931263746630667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97213998439954175831087111 145820997659931263746630667)
          ·
            refine ⟨218731496489896895619946001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145820997659931263746630667 218731496489896895619946001)
            ·
              refine ⟨164048622367422671714959501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218731496489896895619946001 164048622367422671714959501)
              ·
                refine ⟨61518233387783501893109813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164048622367422671714959501 61518233387783501893109813)
                ·
                  refine ⟨5767334380104703302479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61518233387783501893109813 5767334380104703302479045)
                  ·
                    refine ⟨1081375196269631869214821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767334380104703302479045 1081375196269631869214821)
                    ·
                      rfl

theorem cell22_3158956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_3158956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158956 prefixEnd_3158956 := by exact prefixLift 3158956
  have htrace : WordTrace (prefixWord ++ tailWord_3158956) baseStart_3158956 baseEnd_3158956 := by
    simpa [prefixWord, tailWord_3158956, baseEnd_3158956] using wordTrace_append hprefix tailTrace_3158956
  have hstable : (prefixWord ++ tailWord_3158956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158956).length < 2 ^ (prefixWord ++ tailWord_3158956).sum := by decide
  have hdescent : baseEnd_3158956 < baseStart_3158956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159033 : List Nat := [1, 2, 1, 3, 1, 3, 5, 6]
def baseStart_3159033 : Nat := 118140960795 + 3159033 * 2 ^ 59
def prefixEnd_3159033 : Nat := 4983230072969 + 3 ^ 40 * 3159033 * 2
def baseEnd_3159033 : Nat := 120155728327025481671065

theorem tailTrace_3159033 : CollatzResearch.WordTrace tailWord_3159033 prefixEnd_3159033 120155728327025481671065 := by
  unfold tailWord_3159033
  simp only [CollatzResearch.WordTrace]
  refine ⟨115219399164370435728137753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76812932776246957152091835 115219399164370435728137753)
  ·
    refine ⟨86414549373277826796103315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115219399164370435728137753 86414549373277826796103315)
    ·
      refine ⟨129621824059916740194154973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86414549373277826796103315 129621824059916740194154973)
      ·
        refine ⟨48608184022468777572808115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129621824059916740194154973 48608184022468777572808115)
        ·
          refine ⟨72912276033703166359212173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48608184022468777572808115 72912276033703166359212173)
          ·
            refine ⟨27342103512638687384704565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72912276033703166359212173 27342103512638687384704565)
            ·
              refine ⟨2563322204309876942316053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27342103512638687384704565 2563322204309876942316053)
              ·
                refine ⟨120155728327025481671065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2563322204309876942316053 120155728327025481671065)
                ·
                  rfl

theorem cell22_3159033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 6].length) (baseStart_3159033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159033 prefixEnd_3159033 := by exact prefixLift 3159033
  have htrace : WordTrace (prefixWord ++ tailWord_3159033) baseStart_3159033 baseEnd_3159033 := by
    simpa [prefixWord, tailWord_3159033, baseEnd_3159033] using wordTrace_append hprefix tailTrace_3159033
  have hstable : (prefixWord ++ tailWord_3159033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159033).length < 2 ^ (prefixWord ++ tailWord_3159033).sum := by decide
  have hdescent : baseEnd_3159033 < baseStart_3159033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159172 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3159172 : Nat := 118140960795 + 3159172 * 2 ^ 59
def prefixEnd_3159172 : Nat := 4983230072969 + 3 ^ 40 * 3159172 * 2
def baseEnd_3159172 : Nat := 1081449137483879305814159

theorem tailTrace_3159172 : CollatzResearch.WordTrace tailWord_3159172 prefixEnd_3159172 1081449137483879305814159 := by
  unfold tailWord_3159172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57612234455433431233723885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76816312607244574978298513 57612234455433431233723885)
  ·
    refine ⟨21604587920787536712646457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57612234455433431233723885 21604587920787536712646457)
    ·
      refine ⟨16203440940590652534484843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21604587920787536712646457 16203440940590652534484843)
      ·
        refine ⟨24305161410885978801727265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16203440940590652534484843 24305161410885978801727265)
        ·
          refine ⟨18228871058164484101295449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24305161410885978801727265 18228871058164484101295449)
          ·
            refine ⟨13671653293623363075971587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18228871058164484101295449 13671653293623363075971587)
            ·
              refine ⟨20507479940435044613957381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671653293623363075971587 20507479940435044613957381)
              ·
                refine ⟨3845152488831570865117009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20507479940435044613957381 3845152488831570865117009)
                ·
                  refine ⟨2883864366623678148837757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845152488831570865117009 2883864366623678148837757)
                  ·
                    refine ⟨1081449137483879305814159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883864366623678148837757 1081449137483879305814159)
                    ·
                      rfl

theorem cell22_3159172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3159172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159172 prefixEnd_3159172 := by exact prefixLift 3159172
  have htrace : WordTrace (prefixWord ++ tailWord_3159172) baseStart_3159172 baseEnd_3159172 := by
    simpa [prefixWord, tailWord_3159172, baseEnd_3159172] using wordTrace_append hprefix tailTrace_3159172
  have hstable : (prefixWord ++ tailWord_3159172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159172).length < 2 ^ (prefixWord ++ tailWord_3159172).sum := by decide
  have hdescent : baseEnd_3159172 < baseStart_3159172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159243 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_3159243 : Nat := 118140960795 + 3159243 * 2 ^ 59
def prefixEnd_3159243 : Nat := 4983230072969 + 3 ^ 40 * 3159243 * 2
def baseEnd_3159243 : Nat := 1081473442234858787288941

theorem tailTrace_3159243 : CollatzResearch.WordTrace tailWord_3159243 prefixEnd_3159243 1081473442234858787288941 := by
  unfold tailWord_3159243
  simp only [CollatzResearch.WordTrace]
  refine ⟨115227058493609641593282383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76818038995739761062188255 115227058493609641593282383)
  ·
    refine ⟨172840587740414462389923575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115227058493609641593282383 172840587740414462389923575)
    ·
      refine ⟨259260881610621693584885363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172840587740414462389923575 259260881610621693584885363)
      ·
        refine ⟨388891322415932540377328045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259260881610621693584885363 388891322415932540377328045)
        ·
          refine ⟨145834245905974702641498017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388891322415932540377328045 145834245905974702641498017)
          ·
            refine ⟨109375684429481026981123513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145834245905974702641498017 109375684429481026981123513)
            ·
              refine ⟨82031763322110770235842635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109375684429481026981123513 82031763322110770235842635)
              ·
                refine ⟨123047644983166155353763953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82031763322110770235842635 123047644983166155353763953)
                ·
                  refine ⟨92285733737374616515322965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123047644983166155353763953 92285733737374616515322965)
                  ·
                    refine ⟨1081473442234858787288941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92285733737374616515322965 1081473442234858787288941)
                    ·
                      rfl

theorem cell22_3159243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_3159243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159243 prefixEnd_3159243 := by exact prefixLift 3159243
  have htrace : WordTrace (prefixWord ++ tailWord_3159243) baseStart_3159243 baseEnd_3159243 := by
    simpa [prefixWord, tailWord_3159243, baseEnd_3159243] using wordTrace_append hprefix tailTrace_3159243
  have hstable : (prefixWord ++ tailWord_3159243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159243).length < 2 ^ (prefixWord ++ tailWord_3159243).sum := by decide
  have hdescent : baseEnd_3159243 < baseStart_3159243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159298 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3159298 : Nat := 118140960795 + 3159298 * 2 ^ 59
def prefixEnd_3159298 : Nat := 4983230072969 + 3 ^ 40 * 3159298 * 2
def baseEnd_3159298 : Nat := 360497423286285659054591

theorem tailTrace_3159298 : CollatzResearch.WordTrace tailWord_3159298 prefixEnd_3159298 360497423286285659054591 := by
  unfold tailWord_3159298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28807266127102596496633637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76819376338940257324356365 28807266127102596496633637)
  ·
    refine ⟨5401362398831736843118807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28807266127102596496633637 5401362398831736843118807)
    ·
      refine ⟨8102043598247605264678211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401362398831736843118807 8102043598247605264678211)
      ·
        refine ⟨12153065397371407897017317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102043598247605264678211 12153065397371407897017317)
        ·
          refine ⟨2278699762007138980690747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12153065397371407897017317 2278699762007138980690747)
          ·
            refine ⟨3418049643010708471036121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278699762007138980690747 3418049643010708471036121)
            ·
              refine ⟨2563537232258031353277091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418049643010708471036121 2563537232258031353277091)
              ·
                refine ⟨3845305848387047029915637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563537232258031353277091 3845305848387047029915637)
                ·
                  refine ⟨360497423286285659054591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3845305848387047029915637 360497423286285659054591)
                  ·
                    rfl

theorem cell22_3159298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3159298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159298 prefixEnd_3159298 := by exact prefixLift 3159298
  have htrace : WordTrace (prefixWord ++ tailWord_3159298) baseStart_3159298 baseEnd_3159298 := by
    simpa [prefixWord, tailWord_3159298, baseEnd_3159298] using wordTrace_append hprefix tailTrace_3159298
  have hstable : (prefixWord ++ tailWord_3159298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159298).length < 2 ^ (prefixWord ++ tailWord_3159298).sum := by decide
  have hdescent : baseEnd_3159298 < baseStart_3159298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159305 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_3159305 : Nat := 118140960795 + 3159305 * 2 ^ 59
def prefixEnd_3159305 : Nat := 4983230072969 + 3 ^ 40 * 3159305 * 2
def baseEnd_3159305 : Nat := 1081494666101911292238751

theorem tailTrace_3159305 : CollatzResearch.WordTrace tailWord_3159305 prefixEnd_3159305 1081494666101911292238751 := by
  unfold tailWord_3159305
  simp only [CollatzResearch.WordTrace]
  refine ⟨115229319819385026182039369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76819546546256684121359579 115229319819385026182039369)
  ·
    refine ⟨86421989864538769636529527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115229319819385026182039369 86421989864538769636529527)
    ·
      refine ⟨129632984796808154454794291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86421989864538769636529527 129632984796808154454794291)
      ·
        refine ⟨194449477195212231682191437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129632984796808154454794291 194449477195212231682191437)
        ·
          refine ⟨72918553948204586880821789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194449477195212231682191437 72918553948204586880821789)
          ·
            refine ⟨27344457730576720080308171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72918553948204586880821789 27344457730576720080308171)
            ·
              refine ⟨41016686595865080120462257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27344457730576720080308171 41016686595865080120462257)
              ·
                refine ⟨30762514946898810090346693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41016686595865080120462257 30762514946898810090346693)
                ·
                  refine ⟨5767971552543526891940005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30762514946898810090346693 5767971552543526891940005)
                  ·
                    refine ⟨1081494666101911292238751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767971552543526891940005 1081494666101911292238751)
                    ·
                      rfl

theorem cell22_3159305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_3159305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159305 prefixEnd_3159305 := by exact prefixLift 3159305
  have htrace : WordTrace (prefixWord ++ tailWord_3159305) baseStart_3159305 baseEnd_3159305 := by
    simpa [prefixWord, tailWord_3159305, baseEnd_3159305] using wordTrace_append hprefix tailTrace_3159305
  have hstable : (prefixWord ++ tailWord_3159305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159305).length < 2 ^ (prefixWord ++ tailWord_3159305).sum := by decide
  have hdescent : baseEnd_3159305 < baseStart_3159305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159320 : List Nat := [2, 1, 2, 3, 1, 3, 2, 8]
def baseStart_3159320 : Nat := 118140960795 + 3159320 * 2 ^ 59
def prefixEnd_3159320 : Nat := 4983230072969 + 3 ^ 40 * 3159320 * 2
def baseEnd_3159320 : Nat := 120166644545384028123745

theorem tailTrace_3159320 : CollatzResearch.WordTrace tailWord_3159320 prefixEnd_3159320 120166644545384028123745 := by
  unfold tailWord_3159320
  simp only [CollatzResearch.WordTrace]
  refine ⟨57614933457165341871917707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76819911276220455829223609 57614933457165341871917707)
  ·
    refine ⟨86422400185748012807876561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57614933457165341871917707 86422400185748012807876561)
    ·
      refine ⟨64816800139311009605907421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86422400185748012807876561 64816800139311009605907421)
      ·
        refine ⟨24306300052241628602215283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64816800139311009605907421 24306300052241628602215283)
        ·
          refine ⟨36459450078362442903322925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24306300052241628602215283 36459450078362442903322925)
          ·
            refine ⟨13672293779385916088746097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36459450078362442903322925 13672293779385916088746097)
            ·
              refine ⟨10254220334539437066559573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672293779385916088746097 10254220334539437066559573)
              ·
                refine ⟨120166644545384028123745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10254220334539437066559573 120166644545384028123745)
                ·
                  rfl

theorem cell22_3159320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_3159320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159320 prefixEnd_3159320 := by exact prefixLift 3159320
  have htrace : WordTrace (prefixWord ++ tailWord_3159320) baseStart_3159320 baseEnd_3159320 := by
    simpa [prefixWord, tailWord_3159320, baseEnd_3159320] using wordTrace_append hprefix tailTrace_3159320
  have hstable : (prefixWord ++ tailWord_3159320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159320).length < 2 ^ (prefixWord ++ tailWord_3159320).sum := by decide
  have hdescent : baseEnd_3159320 < baseStart_3159320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159322 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_3159322 : Nat := 118140960795 + 3159322 * 2 ^ 59
def prefixEnd_3159322 : Nat := 4983230072969 + 3 ^ 40 * 3159322 * 2
def baseEnd_3159322 : Nat := 1081500485549328914563699

theorem tailTrace_3159322 : CollatzResearch.WordTrace tailWord_3159322 prefixEnd_3159322 1081500485549328914563699 := by
  unfold tailWord_3159322
  simp only [CollatzResearch.WordTrace]
  refine ⟨28807484965080859521352055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76819959906882292056938813 28807484965080859521352055)
  ·
    refine ⟨43211227447621289282028083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28807484965080859521352055 43211227447621289282028083)
    ·
      refine ⟨64816841171431933923042125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43211227447621289282028083 64816841171431933923042125)
      ·
        refine ⟨24306315439286975221140797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64816841171431933923042125 24306315439286975221140797)
        ·
          refine ⟨9114868289732615707927799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24306315439286975221140797 9114868289732615707927799)
          ·
            refine ⟨13672302434598923561891699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114868289732615707927799 13672302434598923561891699)
            ·
              refine ⟨20508453651898385342837549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672302434598923561891699 20508453651898385342837549)
              ·
                refine ⟨7690670119461894503564081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20508453651898385342837549 7690670119461894503564081)
                ·
                  refine ⟨5768002589596420877673061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690670119461894503564081 5768002589596420877673061)
                  ·
                    refine ⟨1081500485549328914563699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768002589596420877673061 1081500485549328914563699)
                    ·
                      rfl

theorem cell22_3159322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_3159322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159322 prefixEnd_3159322 := by exact prefixLift 3159322
  have htrace : WordTrace (prefixWord ++ tailWord_3159322) baseStart_3159322 baseEnd_3159322 := by
    simpa [prefixWord, tailWord_3159322, baseEnd_3159322] using wordTrace_append hprefix tailTrace_3159322
  have hstable : (prefixWord ++ tailWord_3159322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159322).length < 2 ^ (prefixWord ++ tailWord_3159322).sum := by decide
  have hdescent : baseEnd_3159322 < baseStart_3159322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159341 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3159341 : Nat := 118140960795 + 3159341 * 2 ^ 59
def prefixEnd_3159341 : Nat := 4983230072969 + 3 ^ 40 * 3159341 * 2
def baseEnd_3159341 : Nat := 1081506989637619198338641

theorem tailTrace_3159341 : CollatzResearch.WordTrace tailWord_3159341 prefixEnd_3159341 1081506989637619198338641 := by
  unfold tailWord_3159341
  simp only [CollatzResearch.WordTrace]
  refine ⟨115230632847254604330349877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76820421898169736220233251 115230632847254604330349877)
  ·
    refine ⟨10802871829430119155970301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115230632847254604330349877 10802871829430119155970301)
    ·
      refine ⟨4051076936036294683488863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10802871829430119155970301 4051076936036294683488863)
      ·
        refine ⟨6076615404054442025233295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051076936036294683488863 6076615404054442025233295)
        ·
          refine ⟨9114923106081663037849943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076615404054442025233295 9114923106081663037849943)
          ·
            refine ⟨13672384659122494556774915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114923106081663037849943 13672384659122494556774915)
            ·
              refine ⟨20508576988683741835162373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672384659122494556774915 20508576988683741835162373)
              ·
                refine ⟨3845358185378201594092945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20508576988683741835162373 3845358185378201594092945)
                ·
                  refine ⟨2884018639033651195569709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845358185378201594092945 2884018639033651195569709)
                  ·
                    refine ⟨1081506989637619198338641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884018639033651195569709 1081506989637619198338641)
                    ·
                      rfl

theorem cell22_3159341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3159341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159341 prefixEnd_3159341 := by exact prefixLift 3159341
  have htrace : WordTrace (prefixWord ++ tailWord_3159341) baseStart_3159341 baseEnd_3159341 := by
    simpa [prefixWord, tailWord_3159341, baseEnd_3159341] using wordTrace_append hprefix tailTrace_3159341
  have hstable : (prefixWord ++ tailWord_3159341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159341).length < 2 ^ (prefixWord ++ tailWord_3159341).sum := by decide
  have hdescent : baseEnd_3159341 < baseStart_3159341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159352 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_3159352 : Nat := 118140960795 + 3159352 * 2 ^ 59
def prefixEnd_3159352 : Nat := 4983230072969 + 3 ^ 40 * 3159352 * 2
def baseEnd_3159352 : Nat := 1081510755162418836313607

theorem tailTrace_3159352 : CollatzResearch.WordTrace tailWord_3159352 prefixEnd_3159352 1081510755162418836313607 := by
  unfold tailWord_3159352
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615517025107376604500155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76820689366809835472666873 57615517025107376604500155)
  ·
    refine ⟨86423275537661064906750233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57615517025107376604500155 86423275537661064906750233)
    ·
      refine ⟨64817456653245798680062675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86423275537661064906750233 64817456653245798680062675)
      ·
        refine ⟨97226184979868698020094013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64817456653245798680062675 97226184979868698020094013)
        ·
          refine ⟨36459819367450761757535255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97226184979868698020094013 36459819367450761757535255)
          ·
            refine ⟨54689729051176142636302883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36459819367450761757535255 54689729051176142636302883)
            ·
              refine ⟨82034593576764213954454325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54689729051176142636302883 82034593576764213954454325)
              ·
                refine ⟨7690743147821645058230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82034593576764213954454325 7690743147821645058230093)
                ·
                  refine ⟨2884028680433116896836285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7690743147821645058230093 2884028680433116896836285)
                  ·
                    refine ⟨1081510755162418836313607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884028680433116896836285 1081510755162418836313607)
                    ·
                      rfl

theorem cell22_3159352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_3159352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159352 prefixEnd_3159352 := by exact prefixLift 3159352
  have htrace : WordTrace (prefixWord ++ tailWord_3159352) baseStart_3159352 baseEnd_3159352 := by
    simpa [prefixWord, tailWord_3159352, baseEnd_3159352] using wordTrace_append hprefix tailTrace_3159352
  have hstable : (prefixWord ++ tailWord_3159352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159352).length < 2 ^ (prefixWord ++ tailWord_3159352).sum := by decide
  have hdescent : baseEnd_3159352 < baseStart_3159352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159373 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3159373 : Nat := 118140960795 + 3159373 * 2 ^ 59
def prefixEnd_3159373 : Nat := 4983230072969 + 3 ^ 40 * 3159373 * 2
def baseEnd_3159373 : Nat := 1081517943891581781538543

theorem tailTrace_3159373 : CollatzResearch.WordTrace tailWord_3159373 prefixEnd_3159373 1081517943891581781538543 := by
  unfold tailWord_3159373
  simp only [CollatzResearch.WordTrace]
  refine ⟨115231799983138673795514773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76821199988759115863676515 115231799983138673795514773)
  ·
    refine ⟨5401490624209625334164755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115231799983138673795514773 5401490624209625334164755)
    ·
      refine ⟨8102235936314438001247133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401490624209625334164755 8102235936314438001247133)
      ·
        refine ⟨3038338476117914250467675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8102235936314438001247133 3038338476117914250467675)
        ·
          refine ⟨4557507714176871375701513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038338476117914250467675 4557507714176871375701513)
          ·
            refine ⟨3418130785632653531776135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557507714176871375701513 3418130785632653531776135)
            ·
              refine ⟨5127196178448980297664203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418130785632653531776135 5127196178448980297664203)
              ·
                refine ⟨7690794267673470446496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127196178448980297664203 7690794267673470446496305)
                ·
                  refine ⟨5768095700755102834872229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690794267673470446496305 5768095700755102834872229)
                  ·
                    refine ⟨1081517943891581781538543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768095700755102834872229 1081517943891581781538543)
                    ·
                      rfl

theorem cell22_3159373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3159373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159373 prefixEnd_3159373 := by exact prefixLift 3159373
  have htrace : WordTrace (prefixWord ++ tailWord_3159373) baseStart_3159373 baseEnd_3159373 := by
    simpa [prefixWord, tailWord_3159373, baseEnd_3159373] using wordTrace_append hprefix tailTrace_3159373
  have hstable : (prefixWord ++ tailWord_3159373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159373).length < 2 ^ (prefixWord ++ tailWord_3159373).sum := by decide
  have hdescent : baseEnd_3159373 < baseStart_3159373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159427 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 6]
def baseStart_3159427 : Nat := 118140960795 + 3159427 * 2 ^ 59
def prefixEnd_3159427 : Nat := 4983230072969 + 3 ^ 40 * 3159427 * 2
def baseEnd_3159427 : Nat := 360512143065047880229459

theorem tailTrace_3159427 : CollatzResearch.WordTrace tailWord_3159427 prefixEnd_3159427 360512143065047880229459 := by
  unfold tailWord_3159427
  simp only [CollatzResearch.WordTrace]
  refine ⟨115233769524943041017980535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76822513016628694011987023 115233769524943041017980535)
  ·
    refine ⟨172850654287414561526970803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115233769524943041017980535 172850654287414561526970803)
    ·
      refine ⟨259275981431121842290456205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172850654287414561526970803 259275981431121842290456205)
      ·
        refine ⟨97228493036670690858921077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259275981431121842290456205 97228493036670690858921077)
        ·
          refine ⟨9115171222187877268023851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97228493036670690858921077 9115171222187877268023851)
          ·
            refine ⟨13672756833281815902035777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115171222187877268023851 13672756833281815902035777)
            ·
              refine ⟨10254567624961361926526833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672756833281815902035777 10254567624961361926526833)
              ·
                refine ⟨7690925718721021444895125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10254567624961361926526833 7690925718721021444895125)
                ·
                  refine ⟨360512143065047880229459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7690925718721021444895125 360512143065047880229459)
                  ·
                    rfl

theorem cell22_3159427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_3159427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159427 prefixEnd_3159427 := by exact prefixLift 3159427
  have htrace : WordTrace (prefixWord ++ tailWord_3159427) baseStart_3159427 baseEnd_3159427 := by
    simpa [prefixWord, tailWord_3159427, baseEnd_3159427] using wordTrace_append hprefix tailTrace_3159427
  have hstable : (prefixWord ++ tailWord_3159427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159427).length < 2 ^ (prefixWord ++ tailWord_3159427).sum := by decide
  have hdescent : baseEnd_3159427 < baseStart_3159427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159459 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 2, 3]
def baseStart_3159459 : Nat := 118140960795 + 3159459 * 2 ^ 59
def prefixEnd_3159459 : Nat := 4983230072969 + 3 ^ 40 * 3159459 * 2
def baseEnd_3159459 : Nat := 1081547383449106223888279

theorem tailTrace_3159459 : CollatzResearch.WordTrace tailWord_3159459 prefixEnd_3159459 1081547383449106223888279 := by
  unfold tailWord_3159459
  simp only [CollatzResearch.WordTrace]
  refine ⟨115234936660827110483145431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76823291107218073655430287 115234936660827110483145431)
  ·
    refine ⟨172852404991240665724718147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115234936660827110483145431 172852404991240665724718147)
    ·
      refine ⟨259278607486860998587077221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172852404991240665724718147 259278607486860998587077221)
      ·
        refine ⟨48614738903786437235076979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259278607486860998587077221 48614738903786437235076979)
        ·
          refine ⟨72922108355679655852615469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48614738903786437235076979 72922108355679655852615469)
          ·
            refine ⟨27345790633379870944730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72922108355679655852615469 27345790633379870944730801)
            ·
              refine ⟨20509342975034903208548101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27345790633379870944730801 20509342975034903208548101)
              ·
                refine ⟨3845501807819044351602769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20509342975034903208548101 3845501807819044351602769)
                ·
                  refine ⟨2884126355864283263702077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845501807819044351602769 2884126355864283263702077)
                  ·
                    refine ⟨1081547383449106223888279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884126355864283263702077 1081547383449106223888279)
                    ·
                      rfl

theorem cell22_3159459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].length) (baseStart_3159459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159459 prefixEnd_3159459 := by exact prefixLift 3159459
  have htrace : WordTrace (prefixWord ++ tailWord_3159459) baseStart_3159459 baseEnd_3159459 := by
    simpa [prefixWord, tailWord_3159459, baseEnd_3159459] using wordTrace_append hprefix tailTrace_3159459
  have hstable : (prefixWord ++ tailWord_3159459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159459).length < 2 ^ (prefixWord ++ tailWord_3159459).sum := by decide
  have hdescent : baseEnd_3159459 < baseStart_3159459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159534 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_3159534 : Nat := 118140960795 + 3159534 * 2 ^ 59
def prefixEnd_3159534 : Nat := 4983230072969 + 3 ^ 40 * 3159534 * 2
def baseEnd_3159534 : Nat := 360524352493943676087683

theorem tailTrace_3159534 : CollatzResearch.WordTrace tailWord_3159534 prefixEnd_3159534 360524352493943676087683 := by
  unfold tailWord_3159534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14404709016944424786515707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76825114757036932194750437 14404709016944424786515707)
  ·
    refine ⟨21607063525416637179773561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14404709016944424786515707 21607063525416637179773561)
    ·
      refine ⟨16205297644062477884830171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21607063525416637179773561 16205297644062477884830171)
      ·
        refine ⟨24307946466093716827245257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16205297644062477884830171 24307946466093716827245257)
        ·
          refine ⟨18230959849570287620433943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24307946466093716827245257 18230959849570287620433943)
          ·
            refine ⟨27346439774355431430650915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18230959849570287620433943 27346439774355431430650915)
            ·
              refine ⟨41019659661533147145976373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27346439774355431430650915 41019659661533147145976373)
              ·
                refine ⟨3845593093268732544935285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41019659661533147145976373 3845593093268732544935285)
                ·
                  refine ⟨360524352493943676087683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3845593093268732544935285 360524352493943676087683)
                  ·
                    rfl

theorem cell22_3159534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_3159534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159534 prefixEnd_3159534 := by exact prefixLift 3159534
  have htrace : WordTrace (prefixWord ++ tailWord_3159534) baseStart_3159534 baseEnd_3159534 := by
    simpa [prefixWord, tailWord_3159534, baseEnd_3159534] using wordTrace_append hprefix tailTrace_3159534
  have hstable : (prefixWord ++ tailWord_3159534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159534).length < 2 ^ (prefixWord ++ tailWord_3159534).sum := by decide
  have hdescent : baseEnd_3159534 < baseStart_3159534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159598 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3159598 : Nat := 118140960795 + 3159598 * 2 ^ 59
def prefixEnd_3159598 : Nat := 4983230072969 + 3 ^ 40 * 3159598 * 2
def baseEnd_3159598 : Nat := 1081594965989756194662853

theorem tailTrace_3159598 : CollatzResearch.WordTrace tailWord_3159598 prefixEnd_3159598 1081594965989756194662853 := by
  unfold tailWord_3159598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405000800915442152806931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76826670938215691481636965 14405000800915442152806931)
  ·
    refine ⟨21607501201373163229210397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14405000800915442152806931 21607501201373163229210397)
    ·
      refine ⟨8102812950514936210953899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21607501201373163229210397 8102812950514936210953899)
      ·
        refine ⟨12154219425772404316430849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102812950514936210953899 12154219425772404316430849)
        ·
          refine ⟨9115664569329303237323137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12154219425772404316430849 9115664569329303237323137)
          ·
            refine ⟨6836748426996977427992353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9115664569329303237323137 6836748426996977427992353)
            ·
              refine ⟨5127561320247733070994265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6836748426996977427992353 5127561320247733070994265)
              ·
                refine ⟨3845670990185799803245699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5127561320247733070994265 3845670990185799803245699)
                ·
                  refine ⟨5768506485278699704868549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845670990185799803245699 5768506485278699704868549)
                  ·
                    refine ⟨1081594965989756194662853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768506485278699704868549 1081594965989756194662853)
                    ·
                      rfl

theorem cell22_3159598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3159598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159598 prefixEnd_3159598 := by exact prefixLift 3159598
  have htrace : WordTrace (prefixWord ++ tailWord_3159598) baseStart_3159598 baseEnd_3159598 := by
    simpa [prefixWord, tailWord_3159598, baseEnd_3159598] using wordTrace_append hprefix tailTrace_3159598
  have hstable : (prefixWord ++ tailWord_3159598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159598).length < 2 ^ (prefixWord ++ tailWord_3159598).sum := by decide
  have hdescent : baseEnd_3159598 < baseStart_3159598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159609 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3159609 : Nat := 118140960795 + 3159609 * 2 ^ 59
def prefixEnd_3159609 : Nat := 4983230072969 + 3 ^ 40 * 3159609 * 2
def baseEnd_3159609 : Nat := 1081598731514555832637819

theorem tailTrace_3159609 : CollatzResearch.WordTrace tailWord_3159609 prefixEnd_3159609 1081598731514555832637819 := by
  unfold tailWord_3159609
  simp only [CollatzResearch.WordTrace]
  refine ⟨115240407610283686101105881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76826938406855790734070587 115240407610283686101105881)
  ·
    refine ⟨86430305707712764575829411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115240407610283686101105881 86430305707712764575829411)
    ·
      refine ⟨129645458561569146863744117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86430305707712764575829411 129645458561569146863744117)
      ·
        refine ⟨12154261740147107518476011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129645458561569146863744117 12154261740147107518476011)
        ·
          refine ⟨18231392610220661277714017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12154261740147107518476011 18231392610220661277714017)
          ·
            refine ⟨13673544457665495958285513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18231392610220661277714017 13673544457665495958285513)
            ·
              refine ⟨10255158343249121968714135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13673544457665495958285513 10255158343249121968714135)
              ·
                refine ⟨15382737514873682953071203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255158343249121968714135 15382737514873682953071203)
                ·
                  refine ⟨23074106272310524429606805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15382737514873682953071203 23074106272310524429606805)
                  ·
                    refine ⟨1081598731514555832637819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23074106272310524429606805 1081598731514555832637819)
                    ·
                      rfl

theorem cell22_3159609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3159609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159609 prefixEnd_3159609 := by exact prefixLift 3159609
  have htrace : WordTrace (prefixWord ++ tailWord_3159609) baseStart_3159609 baseEnd_3159609 := by
    simpa [prefixWord, tailWord_3159609, baseEnd_3159609] using wordTrace_append hprefix tailTrace_3159609
  have hstable : (prefixWord ++ tailWord_3159609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159609).length < 2 ^ (prefixWord ++ tailWord_3159609).sum := by decide
  have hdescent : baseEnd_3159609 < baseStart_3159609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159673 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_3159673 : Nat := 118140960795 + 3159673 * 2 ^ 59
def prefixEnd_3159673 : Nat := 4983230072969 + 3 ^ 40 * 3159673 * 2
def baseEnd_3159673 : Nat := 1081620640022480999037623

theorem tailTrace_3159673 : CollatzResearch.WordTrace tailWord_3159673 prefixEnd_3159673 1081620640022480999037623 := by
  unfold tailWord_3159673
  simp only [CollatzResearch.WordTrace]
  refine ⟨115242741882051825031435673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76828494588034550020957115 115242741882051825031435673)
  ·
    refine ⟨86432056411538868773576755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115242741882051825031435673 86432056411538868773576755)
    ·
      refine ⟨129648084617308303160365133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86432056411538868773576755 129648084617308303160365133)
      ·
        refine ⟨48618031731490613685136925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129648084617308303160365133 48618031731490613685136925)
        ·
          refine ⟨18231761899308980131926347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48618031731490613685136925 18231761899308980131926347)
          ·
            refine ⟨27347642848963470197889521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18231761899308980131926347 27347642848963470197889521)
            ·
              refine ⟨20510732136722602648417141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27347642848963470197889521 20510732136722602648417141)
              ·
                refine ⟨1922881137817743998289107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20510732136722602648417141 1922881137817743998289107)
                ·
                  refine ⟨2884321706726615997433661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922881137817743998289107 2884321706726615997433661)
                  ·
                    refine ⟨1081620640022480999037623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884321706726615997433661 1081620640022480999037623)
                    ·
                      rfl

theorem cell22_3159673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_3159673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159673 prefixEnd_3159673 := by exact prefixLift 3159673
  have htrace : WordTrace (prefixWord ++ tailWord_3159673) baseStart_3159673 baseEnd_3159673 := by
    simpa [prefixWord, tailWord_3159673, baseEnd_3159673] using wordTrace_append hprefix tailTrace_3159673
  have hstable : (prefixWord ++ tailWord_3159673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159673).length < 2 ^ (prefixWord ++ tailWord_3159673).sum := by decide
  have hdescent : baseEnd_3159673 < baseStart_3159673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159690 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_3159690 : Nat := 118140960795 + 3159690 * 2 ^ 59
def prefixEnd_3159690 : Nat := 4983230072969 + 3 ^ 40 * 3159690 * 2
def baseEnd_3159690 : Nat := 1081626459469898621362571

theorem tailTrace_3159690 : CollatzResearch.WordTrace tailWord_3159690 prefixEnd_3159690 1081626459469898621362571 := by
  unfold tailWord_3159690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28810840480747559233701131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76828907948660157956536349 28810840480747559233701131)
  ·
    refine ⟨43216260721121338850551697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28810840480747559233701131 43216260721121338850551697)
    ·
      refine ⟨32412195540841004137913773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43216260721121338850551697 32412195540841004137913773)
      ·
        refine ⟨12154573327815376551717665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32412195540841004137913773 12154573327815376551717665)
        ·
          refine ⟨9115929995861532413788249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12154573327815376551717665 9115929995861532413788249)
          ·
            refine ⟨6836947496896149310341187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9115929995861532413788249 6836947496896149310341187)
            ·
              refine ⟨10255421245344223965511781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836947496896149310341187 10255421245344223965511781)
              ·
                refine ⟨1922891483502041993533459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10255421245344223965511781 1922891483502041993533459)
                ·
                  refine ⟨2884337225253062990300189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922891483502041993533459 2884337225253062990300189)
                  ·
                    refine ⟨1081626459469898621362571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884337225253062990300189 1081626459469898621362571)
                    ·
                      rfl

theorem cell22_3159690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_3159690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159690 prefixEnd_3159690 := by exact prefixLift 3159690
  have htrace : WordTrace (prefixWord ++ tailWord_3159690) baseStart_3159690 baseEnd_3159690 := by
    simpa [prefixWord, tailWord_3159690, baseEnd_3159690] using wordTrace_append hprefix tailTrace_3159690
  have hstable : (prefixWord ++ tailWord_3159690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159690).length < 2 ^ (prefixWord ++ tailWord_3159690).sum := by decide
  have hdescent : baseEnd_3159690 < baseStart_3159690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159716 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3159716 : Nat := 118140960795 + 3159716 * 2 ^ 59
def prefixEnd_3159716 : Nat := 4983230072969 + 3 ^ 40 * 3159716 * 2
def baseEnd_3159716 : Nat := 1081635359801243220212491

theorem tailTrace_3159716 : CollatzResearch.WordTrace tailWord_3159716 prefixEnd_3159716 1081635359801243220212491 := by
  unfold tailWord_3159716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57622155110448021687625501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76829540147264028916834001 57622155110448021687625501)
  ·
    refine ⟨21608308166418008132859563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57622155110448021687625501 21608308166418008132859563)
    ·
      refine ⟨32412462249627012199289345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21608308166418008132859563 32412462249627012199289345)
      ·
        refine ⟨24309346687220259149467009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32412462249627012199289345 24309346687220259149467009)
        ·
          refine ⟨18232010015415194362100257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24309346687220259149467009 18232010015415194362100257)
          ·
            refine ⟨13674007511561395771575193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18232010015415194362100257 13674007511561395771575193)
            ·
              refine ⟨10255505633671046828681395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13674007511561395771575193 10255505633671046828681395)
              ·
                refine ⟨15383258450506570243022093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255505633671046828681395 15383258450506570243022093)
                ·
                  refine ⟨5768721918939963841133285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15383258450506570243022093 5768721918939963841133285)
                  ·
                    refine ⟨1081635359801243220212491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768721918939963841133285 1081635359801243220212491)
                    ·
                      rfl

theorem cell22_3159716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3159716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159716 prefixEnd_3159716 := by exact prefixLift 3159716
  have htrace : WordTrace (prefixWord ++ tailWord_3159716) baseStart_3159716 baseEnd_3159716 := by
    simpa [prefixWord, tailWord_3159716, baseEnd_3159716] using wordTrace_append hprefix tailTrace_3159716
  have hstable : (prefixWord ++ tailWord_3159716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159716).length < 2 ^ (prefixWord ++ tailWord_3159716).sum := by decide
  have hdescent : baseEnd_3159716 < baseStart_3159716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159748 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3159748 : Nat := 118140960795 + 3159748 * 2 ^ 59
def prefixEnd_3159748 : Nat := 4983230072969 + 3 ^ 40 * 3159748 * 2
def baseEnd_3159748 : Nat := 360548771351735267804131

theorem tailTrace_3159748 : CollatzResearch.WordTrace tailWord_3159748 prefixEnd_3159748 360548771351735267804131 := by
  unfold tailWord_3159748
  simp only [CollatzResearch.WordTrace]
  refine ⟨57622738678390056420207949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76830318237853408560277265 57622738678390056420207949)
  ·
    refine ⟨21608527004396271157577981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57622738678390056420207949 21608527004396271157577981)
    ·
      refine ⟨8103197626648601684091743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21608527004396271157577981 8103197626648601684091743)
      ·
        refine ⟨12154796439972902526137615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8103197626648601684091743 12154796439972902526137615)
        ·
          refine ⟨18232194659959353789206423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12154796439972902526137615 18232194659959353789206423)
          ·
            refine ⟨27348291989939030683809635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18232194659959353789206423 27348291989939030683809635)
            ·
              refine ⟨41022437984908546025714453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27348291989939030683809635 41022437984908546025714453)
              ·
                refine ⟨1922926780542588094955365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41022437984908546025714453 1922926780542588094955365)
                ·
                  refine ⟨360548771351735267804131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922926780542588094955365 360548771351735267804131)
                  ·
                    rfl

theorem cell22_3159748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3159748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159748 prefixEnd_3159748 := by exact prefixLift 3159748
  have htrace : WordTrace (prefixWord ++ tailWord_3159748) baseStart_3159748 baseEnd_3159748 := by
    simpa [prefixWord, tailWord_3159748, baseEnd_3159748] using wordTrace_append hprefix tailTrace_3159748
  have hstable : (prefixWord ++ tailWord_3159748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159748).length < 2 ^ (prefixWord ++ tailWord_3159748).sum := by decide
  have hdescent : baseEnd_3159748 < baseStart_3159748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159776 : List Nat := [2, 1, 1, 3, 1, 2, 6, 6]
def baseStart_3159776 : Nat := 118140960795 + 3159776 * 2 ^ 59
def prefixEnd_3159776 : Nat := 4983230072969 + 3 ^ 40 * 3159776 * 2
def baseEnd_3159776 : Nat := 120183988780824784856923

theorem tailTrace_3159776 : CollatzResearch.WordTrace tailWord_3159776 prefixEnd_3159776 120183988780824784856923 := by
  unfold tailWord_3159776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57623249300339336811217591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76830999067119115748290121 57623249300339336811217591)
  ·
    refine ⟨86434873950509005216826387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57623249300339336811217591 86434873950509005216826387)
    ·
      refine ⟨129652310925763507825239581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86434873950509005216826387 129652310925763507825239581)
      ·
        refine ⟨48619616597161315434464843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129652310925763507825239581 48619616597161315434464843)
        ·
          refine ⟨72929424895741973151697265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48619616597161315434464843 72929424895741973151697265)
          ·
            refine ⟨54697068671806479863772949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72929424895741973151697265 54697068671806479863772949)
            ·
              refine ⟨2563925093990928743614357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54697068671806479863772949 2563925093990928743614357)
              ·
                refine ⟨120183988780824784856923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2563925093990928743614357 120183988780824784856923)
                ·
                  rfl

theorem cell22_3159776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_3159776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159776 prefixEnd_3159776 := by exact prefixLift 3159776
  have htrace : WordTrace (prefixWord ++ tailWord_3159776) baseStart_3159776 baseEnd_3159776 := by
    simpa [prefixWord, tailWord_3159776, baseEnd_3159776] using wordTrace_append hprefix tailTrace_3159776
  have hstable : (prefixWord ++ tailWord_3159776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159776).length < 2 ^ (prefixWord ++ tailWord_3159776).sum := by decide
  have hdescent : baseEnd_3159776 < baseStart_3159776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159859 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 1, 3]
def baseStart_3159859 : Nat := 118140960795 + 3159859 * 2 ^ 59
def prefixEnd_3159859 : Nat := 4983230072969 + 3 ^ 40 * 3159859 * 2
def baseEnd_3159859 : Nat := 1081684311623638513887053

theorem tailTrace_3159859 : CollatzResearch.WordTrace tailWord_3159859 prefixEnd_3159859 1081684311623638513887053 := by
  unfold tailWord_3159859
  simp only [CollatzResearch.WordTrace]
  refine ⟨115249525859377978797706631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76833017239585319198471087 115249525859377978797706631)
  ·
    refine ⟨172874288789066968196559947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115249525859377978797706631 172874288789066968196559947)
    ·
      refine ⟨259311433183600452294839921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172874288789066968196559947 259311433183600452294839921)
      ·
        refine ⟨194483574887700339221129941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259311433183600452294839921 194483574887700339221129941)
        ·
          refine ⟨4558208786430476700495233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194483574887700339221129941 4558208786430476700495233)
          ·
            refine ⟨3418656589822857525371425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4558208786430476700495233 3418656589822857525371425)
            ·
              refine ⟨2563992442367143144028569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418656589822857525371425 2563992442367143144028569)
              ·
                refine ⟨1922994331775357358021427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563992442367143144028569 1922994331775357358021427)
                ·
                  refine ⟨2884491497663036037032141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922994331775357358021427 2884491497663036037032141)
                  ·
                    refine ⟨1081684311623638513887053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884491497663036037032141 1081684311623638513887053)
                    ·
                      rfl

theorem cell22_3159859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 3].length) (baseStart_3159859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159859 prefixEnd_3159859 := by exact prefixLift 3159859
  have htrace : WordTrace (prefixWord ++ tailWord_3159859) baseStart_3159859 baseEnd_3159859 := by
    simpa [prefixWord, tailWord_3159859, baseEnd_3159859] using wordTrace_append hprefix tailTrace_3159859
  have hstable : (prefixWord ++ tailWord_3159859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159859).length < 2 ^ (prefixWord ++ tailWord_3159859).sum := by decide
  have hdescent : baseEnd_3159859 < baseStart_3159859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159885 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3159885 : Nat := 118140960795 + 3159885 * 2 ^ 59
def prefixEnd_3159885 : Nat := 4983230072969 + 3 ^ 40 * 3159885 * 2
def baseEnd_3159885 : Nat := 1081693211954983112736973

theorem tailTrace_3159885 : CollatzResearch.WordTrace tailWord_3159885 prefixEnd_3159885 1081693211954983112736973 := by
  unfold tailWord_3159885
  simp only [CollatzResearch.WordTrace]
  refine ⟨115250474157283785238153109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76833649438189190158768739 115250474157283785238153109)
  ·
    refine ⟨5402365976122677433038427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115250474157283785238153109 5402365976122677433038427)
    ·
      refine ⟨8103548964184016149557641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5402365976122677433038427 8103548964184016149557641)
      ·
        refine ⟨6077661723138012112168231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8103548964184016149557641 6077661723138012112168231)
        ·
          refine ⟨9116492584707018168252347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077661723138012112168231 9116492584707018168252347)
          ·
            refine ⟨13674738877060527252378521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116492584707018168252347 13674738877060527252378521)
            ·
              refine ⟨10256054157795395439283891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13674738877060527252378521 10256054157795395439283891)
              ·
                refine ⟨15384081236693093158925837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256054157795395439283891 15384081236693093158925837)
                ·
                  refine ⟨5769030463759909934597189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15384081236693093158925837 5769030463759909934597189)
                  ·
                    refine ⟨1081693211954983112736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769030463759909934597189 1081693211954983112736973)
                    ·
                      rfl

theorem cell22_3159885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3159885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159885 prefixEnd_3159885 := by exact prefixLift 3159885
  have htrace : WordTrace (prefixWord ++ tailWord_3159885) baseStart_3159885 baseEnd_3159885 := by
    simpa [prefixWord, tailWord_3159885, baseEnd_3159885] using wordTrace_append hprefix tailTrace_3159885
  have hstable : (prefixWord ++ tailWord_3159885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159885).length < 2 ^ (prefixWord ++ tailWord_3159885).sum := by decide
  have hdescent : baseEnd_3159885 < baseStart_3159885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159898 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_3159898 : Nat := 118140960795 + 3159898 * 2 ^ 59
def prefixEnd_3159898 : Nat := 4983230072969 + 3 ^ 40 * 3159898 * 2
def baseEnd_3159898 : Nat := 1081697662120655412161933

theorem tailTrace_3159898 : CollatzResearch.WordTrace tailWord_3159898 prefixEnd_3159898 1081697662120655412161933 := by
  unfold tailWord_3159898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28812737076559172114594087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76833965537491125638917565 28812737076559172114594087)
  ·
    refine ⟨43219105614838758171891131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28812737076559172114594087 43219105614838758171891131)
    ·
      refine ⟨64828658422258137257836697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43219105614838758171891131 64828658422258137257836697)
      ·
        refine ⟨48621493816693602943377523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64828658422258137257836697 48621493816693602943377523)
        ·
          refine ⟨72932240725040404415066285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48621493816693602943377523 72932240725040404415066285)
          ·
            refine ⟨27349590271890151655649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72932240725040404415066285 27349590271890151655649857)
            ·
              refine ⟨20512192703917613741737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27349590271890151655649857 20512192703917613741737393)
              ·
                refine ⟨15384144527938210306303045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20512192703917613741737393 15384144527938210306303045)
                ·
                  refine ⟨2884527098988414432431821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15384144527938210306303045 2884527098988414432431821)
                  ·
                    refine ⟨1081697662120655412161933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884527098988414432431821 1081697662120655412161933)
                    ·
                      rfl

theorem cell22_3159898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_3159898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159898 prefixEnd_3159898 := by exact prefixLift 3159898
  have htrace : WordTrace (prefixWord ++ tailWord_3159898) baseStart_3159898 baseEnd_3159898 := by
    simpa [prefixWord, tailWord_3159898, baseEnd_3159898] using wordTrace_append hprefix tailTrace_3159898
  have hstable : (prefixWord ++ tailWord_3159898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159898).length < 2 ^ (prefixWord ++ tailWord_3159898).sum := by decide
  have hdescent : baseEnd_3159898 < baseStart_3159898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159911 : List Nat := [1, 1, 5, 1, 2, 1, 11]
def baseStart_3159911 : Nat := 118140960795 + 3159911 * 2 ^ 59
def prefixEnd_3159911 : Nat := 4983230072969 + 3 ^ 40 * 3159911 * 2
def baseEnd_3159911 : Nat := 40063041195789915243959

theorem tailTrace_3159911 : CollatzResearch.WordTrace tailWord_3159911 prefixEnd_3159911 40063041195789915243959 := by
  unfold tailWord_3159911
  simp only [CollatzResearch.WordTrace]
  refine ⟨115251422455189591678599587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76834281636793061119066391 115251422455189591678599587)
  ·
    refine ⟨172877133682784387517899381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115251422455189591678599587 172877133682784387517899381)
    ·
      refine ⟨16207231282761036329803067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172877133682784387517899381 16207231282761036329803067)
      ·
        refine ⟨24310846924141554494704601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16207231282761036329803067 24310846924141554494704601)
        ·
          refine ⟨18233135193106165871028451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24310846924141554494704601 18233135193106165871028451)
          ·
            refine ⟨27349702789659248806542677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18233135193106165871028451 27349702789659248806542677)
            ·
              refine ⟨40063041195789915243959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27349702789659248806542677 40063041195789915243959)
              ·
                rfl

theorem cell22_3159911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 11].length) (baseStart_3159911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3159911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3159911 prefixEnd_3159911 := by exact prefixLift 3159911
  have htrace : WordTrace (prefixWord ++ tailWord_3159911) baseStart_3159911 baseEnd_3159911 := by
    simpa [prefixWord, tailWord_3159911, baseEnd_3159911] using wordTrace_append hprefix tailTrace_3159911
  have hstable : (prefixWord ++ tailWord_3159911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159911).length < 2 ^ (prefixWord ++ tailWord_3159911).sum := by decide
  have hdescent : baseEnd_3159911 < baseStart_3159911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160028 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3160028 : Nat := 118140960795 + 3160028 * 2 ^ 59
def prefixEnd_3160028 : Nat := 4983230072969 + 3 ^ 40 * 3160028 * 2
def baseEnd_3160028 : Nat := 1081742163777378406411535

theorem tailTrace_3160028 : CollatzResearch.WordTrace tailWord_3160028 prefixEnd_3160028 1081742163777378406411535 := by
  unfold tailWord_3160028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57627844897882860330304369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76837126530510480440405825 57627844897882860330304369)
  ·
    refine ⟨43220883673412145247728277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57627844897882860330304369 43220883673412145247728277)
    ·
      refine ⟨2025978922191194308487263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43220883673412145247728277 2025978922191194308487263)
      ·
        refine ⟨3038968383286791462730895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025978922191194308487263 3038968383286791462730895)
        ·
          refine ⟨4558452574930187194096343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038968383286791462730895 4558452574930187194096343)
          ·
            refine ⟨6837678862395280791144515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558452574930187194096343 6837678862395280791144515)
            ·
              refine ⟨10256518293592921186716773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837678862395280791144515 10256518293592921186716773)
              ·
                refine ⟨1923097180048672722509395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10256518293592921186716773 1923097180048672722509395)
                ·
                  refine ⟨2884645770073009083764093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923097180048672722509395 2884645770073009083764093)
                  ·
                    refine ⟨1081742163777378406411535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884645770073009083764093 1081742163777378406411535)
                    ·
                      rfl

theorem cell22_3160028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3160028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160028 prefixEnd_3160028 := by exact prefixLift 3160028
  have htrace : WordTrace (prefixWord ++ tailWord_3160028) baseStart_3160028 baseEnd_3160028 := by
    simpa [prefixWord, tailWord_3160028, baseEnd_3160028] using wordTrace_append hprefix tailTrace_3160028
  have hstable : (prefixWord ++ tailWord_3160028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160028).length < 2 ^ (prefixWord ++ tailWord_3160028).sum := by decide
  have hdescent : baseEnd_3160028 < baseStart_3160028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160048 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_3160048 : Nat := 118140960795 + 3160048 * 2 ^ 59
def prefixEnd_3160048 : Nat := 4983230072969 + 3 ^ 40 * 3160048 * 2
def baseEnd_3160048 : Nat := 1081749010186105020911473

theorem tailTrace_3160048 : CollatzResearch.WordTrace tailWord_3160048 prefixEnd_3160048 1081749010186105020911473 := by
  unfold tailWord_3160048
  simp only [CollatzResearch.WordTrace]
  refine ⟨57628209627846632038168399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76837612837128842717557865 57628209627846632038168399)
  ·
    refine ⟨86442314441769948057252599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57628209627846632038168399 86442314441769948057252599)
    ·
      refine ⟨129663471662654922085878899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86442314441769948057252599 129663471662654922085878899)
      ·
        refine ⟨194495207493982383128818349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129663471662654922085878899 194495207493982383128818349)
        ·
          refine ⟨72935702810243393673306881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194495207493982383128818349 72935702810243393673306881)
          ·
            refine ⟨54701777107682545254980161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72935702810243393673306881 54701777107682545254980161)
            ·
              refine ⟨41026332830761908941235121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54701777107682545254980161 41026332830761908941235121)
              ·
                refine ⟨30769749623071431705926341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41026332830761908941235121 30769749623071431705926341)
                ·
                  refine ⟨5769328054325893444861189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30769749623071431705926341 5769328054325893444861189)
                  ·
                    refine ⟨1081749010186105020911473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769328054325893444861189 1081749010186105020911473)
                    ·
                      rfl

theorem cell22_3160048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_3160048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160048 prefixEnd_3160048 := by exact prefixLift 3160048
  have htrace : WordTrace (prefixWord ++ tailWord_3160048) baseStart_3160048 baseEnd_3160048 := by
    simpa [prefixWord, tailWord_3160048, baseEnd_3160048] using wordTrace_append hprefix tailTrace_3160048
  have hstable : (prefixWord ++ tailWord_3160048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160048).length < 2 ^ (prefixWord ++ tailWord_3160048).sum := by decide
  have hdescent : baseEnd_3160048 < baseStart_3160048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160146 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3160146 : Nat := 118140960795 + 3160146 * 2 ^ 59
def prefixEnd_3160146 : Nat := 4983230072969 + 3 ^ 40 * 3160146 * 2
def baseEnd_3160146 : Nat := 1081782557588865431961173

theorem tailTrace_3160146 : CollatzResearch.WordTrace tailWord_3160146 prefixEnd_3160146 1081782557588865431961173 := by
  unfold tailWord_3160146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28814998402334556703351073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76839995739558817875602861 28814998402334556703351073)
  ·
    refine ⟨21611248801750917527513305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28814998402334556703351073 21611248801750917527513305)
    ·
      refine ⟨16208436601313188145634979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21611248801750917527513305 16208436601313188145634979)
      ·
        refine ⟨24312654901969782218452469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16208436601313188145634979 24312654901969782218452469)
        ·
          refine ⟨2279311397059667082979919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24312654901969782218452469 2279311397059667082979919)
          ·
            refine ⟨3418967095589500624469879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279311397059667082979919 3418967095589500624469879)
            ·
              refine ⟨5128450643384250936704819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418967095589500624469879 5128450643384250936704819)
              ·
                refine ⟨7692675965076376405057229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5128450643384250936704819 7692675965076376405057229)
                ·
                  refine ⟨2884753486903641151896461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7692675965076376405057229 2884753486903641151896461)
                  ·
                    refine ⟨1081782557588865431961173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884753486903641151896461 1081782557588865431961173)
                    ·
                      rfl

theorem cell22_3160146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3160146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160146 prefixEnd_3160146 := by exact prefixLift 3160146
  have htrace : WordTrace (prefixWord ++ tailWord_3160146) baseStart_3160146 baseEnd_3160146 := by
    simpa [prefixWord, tailWord_3160146, baseEnd_3160146] using wordTrace_append hprefix tailTrace_3160146
  have hstable : (prefixWord ++ tailWord_3160146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160146).length < 2 ^ (prefixWord ++ tailWord_3160146).sum := by decide
  have hdescent : baseEnd_3160146 < baseStart_3160146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160172 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_3160172 : Nat := 118140960795 + 3160172 * 2 ^ 59
def prefixEnd_3160172 : Nat := 4983230072969 + 3 ^ 40 * 3160172 * 2
def baseEnd_3160172 : Nat := 1081791457920210030811093

theorem tailTrace_3160172 : CollatzResearch.WordTrace tailWord_3160172 prefixEnd_3160172 1081791457920210030811093 := by
  unfold tailWord_3160172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630470953622016626925385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76840627938162688835900513 57630470953622016626925385)
  ·
    refine ⟨43222853215216512470194039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57630470953622016626925385 43222853215216512470194039)
    ·
      refine ⟨64834279822824768705291059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43222853215216512470194039 64834279822824768705291059)
      ·
        refine ⟨97251419734237153057936589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64834279822824768705291059 97251419734237153057936589)
        ·
          refine ⟨36469282400338932396726221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97251419734237153057936589 36469282400338932396726221)
          ·
            refine ⟨13675980900127099648772333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36469282400338932396726221 13675980900127099648772333)
            ·
              refine ⟨5128492837547662368289625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13675980900127099648772333 5128492837547662368289625)
              ·
                refine ⟨3846369628160746776217219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128492837547662368289625 3846369628160746776217219)
                ·
                  refine ⟨5769554442241120164325829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846369628160746776217219 5769554442241120164325829)
                  ·
                    refine ⟨1081791457920210030811093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769554442241120164325829 1081791457920210030811093)
                    ·
                      rfl

theorem cell22_3160172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_3160172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160172 prefixEnd_3160172 := by exact prefixLift 3160172
  have htrace : WordTrace (prefixWord ++ tailWord_3160172) baseStart_3160172 baseEnd_3160172 := by
    simpa [prefixWord, tailWord_3160172, baseEnd_3160172] using wordTrace_append hprefix tailTrace_3160172
  have hstable : (prefixWord ++ tailWord_3160172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160172).length < 2 ^ (prefixWord ++ tailWord_3160172).sum := by decide
  have hdescent : baseEnd_3160172 < baseStart_3160172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160185 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3160185 : Nat := 118140960795 + 3160185 * 2 ^ 59
def prefixEnd_3160185 : Nat := 4983230072969 + 3 ^ 40 * 3160185 * 2
def baseEnd_3160185 : Nat := 1081795908085882330236053

theorem tailTrace_3160185 : CollatzResearch.WordTrace tailWord_3160185 prefixEnd_3160185 1081795908085882330236053 := by
  unfold tailWord_3160185
  simp only [CollatzResearch.WordTrace]
  refine ⟨115261416056196936474074009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76840944037464624316049339 115261416056196936474074009)
  ·
    refine ⟨86446062042147702355555507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115261416056196936474074009 86446062042147702355555507)
    ·
      refine ⟨129669093063221553533333261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86446062042147702355555507 129669093063221553533333261)
      ·
        refine ⟨48625909898708082574999973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129669093063221553533333261 48625909898708082574999973)
        ·
          refine ⟨9117358106007765482812495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48625909898708082574999973 9117358106007765482812495)
          ·
            refine ⟨13676037159011648224218743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117358106007765482812495 13676037159011648224218743)
            ·
              refine ⟨20514055738517472336328115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676037159011648224218743 20514055738517472336328115)
              ·
                refine ⟨30771083607776208504492173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20514055738517472336328115 30771083607776208504492173)
                ·
                  refine ⟨11539156352916078189184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30771083607776208504492173 11539156352916078189184565)
                  ·
                    refine ⟨1081795908085882330236053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11539156352916078189184565 1081795908085882330236053)
                    ·
                      rfl

theorem cell22_3160185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3160185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160185 prefixEnd_3160185 := by exact prefixLift 3160185
  have htrace : WordTrace (prefixWord ++ tailWord_3160185) baseStart_3160185 baseEnd_3160185 := by
    simpa [prefixWord, tailWord_3160185, baseEnd_3160185] using wordTrace_append hprefix tailTrace_3160185
  have hstable : (prefixWord ++ tailWord_3160185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160185).length < 2 ^ (prefixWord ++ tailWord_3160185).sum := by decide
  have hdescent : baseEnd_3160185 < baseStart_3160185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160189 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_3160189 : Nat := 118140960795 + 3160189 * 2 ^ 59
def prefixEnd_3160189 : Nat := 4983230072969 + 3 ^ 40 * 3160189 * 2
def baseEnd_3160189 : Nat := 1081797277367627653136041

theorem tailTrace_3160189 : CollatzResearch.WordTrace tailWord_3160189 prefixEnd_3160189 1081797277367627653136041 := by
  unfold tailWord_3160189
  simp only [CollatzResearch.WordTrace]
  refine ⟨115261561948182445157219621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76841041298788296771479747 115261561948182445157219621)
  ·
    refine ⟨21611542865284208466978679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115261561948182445157219621 21611542865284208466978679)
    ·
      refine ⟨32417314297926312700468019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21611542865284208466978679 32417314297926312700468019)
      ·
        refine ⟨48625971446889469050702029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32417314297926312700468019 48625971446889469050702029)
        ·
          refine ⟨18234739292583550894013261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48625971446889469050702029 18234739292583550894013261)
          ·
            refine ⟨6838027234718831585254973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18234739292583550894013261 6838027234718831585254973)
            ·
              refine ⟨2564260213019561844470615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6838027234718831585254973 2564260213019561844470615)
              ·
                refine ⟨3846390319529342766705923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564260213019561844470615 3846390319529342766705923)
                ·
                  refine ⟨5769585479294014150058885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846390319529342766705923 5769585479294014150058885)
                  ·
                    refine ⟨1081797277367627653136041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769585479294014150058885 1081797277367627653136041)
                    ·
                      rfl

theorem cell22_3160189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_3160189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160189 prefixEnd_3160189 := by exact prefixLift 3160189
  have htrace : WordTrace (prefixWord ++ tailWord_3160189) baseStart_3160189 baseEnd_3160189 := by
    simpa [prefixWord, tailWord_3160189, baseEnd_3160189] using wordTrace_append hprefix tailTrace_3160189
  have hstable : (prefixWord ++ tailWord_3160189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160189).length < 2 ^ (prefixWord ++ tailWord_3160189).sum := by decide
  have hdescent : baseEnd_3160189 < baseStart_3160189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160234 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3160234 : Nat := 118140960795 + 3160234 * 2 ^ 59
def prefixEnd_3160234 : Nat := 4983230072969 + 3 ^ 40 * 3160234 * 2
def baseEnd_3160234 : Nat := 1081812681787262535760903

theorem tailTrace_3160234 : CollatzResearch.WordTrace tailWord_3160234 prefixEnd_3160234 1081812681787262535760903 := by
  unfold tailWord_3160234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28815800808254854460651939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76842135488679611895071837 28815800808254854460651939)
  ·
    refine ⟨43223701212382281690977909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28815800808254854460651939 43223701212382281690977909)
    ·
      refine ⟨4052221988660838908529179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43223701212382281690977909 4052221988660838908529179)
      ·
        refine ⟨6078332982991258362793769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052221988660838908529179 6078332982991258362793769)
        ·
          refine ⟨4558749737243443772095327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6078332982991258362793769 4558749737243443772095327)
          ·
            refine ⟨6838124605865165658142991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558749737243443772095327 6838124605865165658142991)
            ·
              refine ⟨10257186908797748487214487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838124605865165658142991 10257186908797748487214487)
              ·
                refine ⟨15385780363196622730821731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10257186908797748487214487 15385780363196622730821731)
                ·
                  refine ⟨23078670544794934096232597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15385780363196622730821731 23078670544794934096232597)
                  ·
                    refine ⟨1081812681787262535760903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23078670544794934096232597 1081812681787262535760903)
                    ·
                      rfl

theorem cell22_3160234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3160234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160234 prefixEnd_3160234 := by exact prefixLift 3160234
  have htrace : WordTrace (prefixWord ++ tailWord_3160234) baseStart_3160234 baseEnd_3160234 := by
    simpa [prefixWord, tailWord_3160234, baseEnd_3160234] using wordTrace_append hprefix tailTrace_3160234
  have hstable : (prefixWord ++ tailWord_3160234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160234).length < 2 ^ (prefixWord ++ tailWord_3160234).sum := by decide
  have hdescent : baseEnd_3160234 < baseStart_3160234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160238 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3160238 : Nat := 118140960795 + 3160238 * 2 ^ 59
def prefixEnd_3160238 : Nat := 4983230072969 + 3 ^ 40 * 3160238 * 2
def baseEnd_3160238 : Nat := 360604683689669286220297

theorem tailTrace_3160238 : CollatzResearch.WordTrace tailWord_3160238 prefixEnd_3160238 360604683689669286220297 := by
  unfold tailWord_3160238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407918640625615815719171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76842232750003284350502245 14407918640625615815719171)
  ·
    refine ⟨21611877960938423723578757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14407918640625615815719171 21611877960938423723578757)
    ·
      refine ⟨4052227117675954448171017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21611877960938423723578757 4052227117675954448171017)
      ·
        refine ⟨3039170338256965836128263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4052227117675954448171017 3039170338256965836128263)
        ·
          refine ⟨4558755507385448754192395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039170338256965836128263 4558755507385448754192395)
          ·
            refine ⟨6838133261078173131288593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558755507385448754192395 6838133261078173131288593)
            ·
              refine ⟨5128599945808629848466445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838133261078173131288593 5128599945808629848466445)
              ·
                refine ⟨1923224979678236193174917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5128599945808629848466445 1923224979678236193174917)
                ·
                  refine ⟨360604683689669286220297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923224979678236193174917 360604683689669286220297)
                  ·
                    rfl

theorem cell22_3160238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3160238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160238 prefixEnd_3160238 := by exact prefixLift 3160238
  have htrace : WordTrace (prefixWord ++ tailWord_3160238) baseStart_3160238 baseEnd_3160238 := by
    simpa [prefixWord, tailWord_3160238, baseEnd_3160238] using wordTrace_append hprefix tailTrace_3160238
  have hstable : (prefixWord ++ tailWord_3160238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160238).length < 2 ^ (prefixWord ++ tailWord_3160238).sum := by decide
  have hdescent : baseEnd_3160238 < baseStart_3160238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160305 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 8]
def baseStart_3160305 : Nat := 118140960795 + 3160305 * 2 ^ 59
def prefixEnd_3160305 : Nat := 4983230072969 + 3 ^ 40 * 3160305 * 2
def baseEnd_3160305 : Nat := 360612328846080672411895

theorem tailTrace_3160305 : CollatzResearch.WordTrace tailWord_3160305 prefixEnd_3160305 360612328846080672411895 := by
  unfold tailWord_3160305
  simp only [CollatzResearch.WordTrace]
  refine ⟨115265792815762196968442369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76843861877174797978961579 115265792815762196968442369)
  ·
    refine ⟨86449344611821647726331777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115265792815762196968442369 86449344611821647726331777)
    ·
      refine ⟨64837008458866235794748833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86449344611821647726331777 64837008458866235794748833)
      ·
        refine ⟨48627756344149676846061625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64837008458866235794748833 48627756344149676846061625)
        ·
          refine ⟨36470817258112257634546219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48627756344149676846061625 36470817258112257634546219)
          ·
            refine ⟨54706225887168386451819329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36470817258112257634546219 54706225887168386451819329)
            ·
              refine ⟨41029669415376289838864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54706225887168386451819329 41029669415376289838864497)
              ·
                refine ⟨30772252061532217379148373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41029669415376289838864497 30772252061532217379148373)
                ·
                  refine ⟨360612328846080672411895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30772252061532217379148373 360612328846080672411895)
                  ·
                    rfl

theorem cell22_3160305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_3160305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160305 prefixEnd_3160305 := by exact prefixLift 3160305
  have htrace : WordTrace (prefixWord ++ tailWord_3160305) baseStart_3160305 baseEnd_3160305 := by
    simpa [prefixWord, tailWord_3160305, baseEnd_3160305] using wordTrace_append hprefix tailTrace_3160305
  have hstable : (prefixWord ++ tailWord_3160305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160305).length < 2 ^ (prefixWord ++ tailWord_3160305).sum := by decide
  have hdescent : baseEnd_3160305 < baseStart_3160305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160307 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 1, 4]
def baseStart_3160307 : Nat := 118140960795 + 3160307 * 2 ^ 59
def prefixEnd_3160307 : Nat := 4983230072969 + 3 ^ 40 * 3160307 * 2
def baseEnd_3160307 : Nat := 1081837671179114678685679

theorem tailTrace_3160307 : CollatzResearch.WordTrace tailWord_3160307 prefixEnd_3160307 1081837671179114678685679 := by
  unfold tailWord_3160307
  simp only [CollatzResearch.WordTrace]
  refine ⟨115265865761754951310015175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76843910507836634206676783 115265865761754951310015175)
  ·
    refine ⟨172898798642632426965022763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115265865761754951310015175 172898798642632426965022763)
    ·
      refine ⟨259348197963948640447534145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172898798642632426965022763 259348197963948640447534145)
      ·
        refine ⟨194511148472961480335650609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259348197963948640447534145 194511148472961480335650609)
        ·
          refine ⟨145883361354721110251737957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194511148472961480335650609 145883361354721110251737957)
          ·
            refine ⟨27353130254010208172200867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145883361354721110251737957 27353130254010208172200867)
            ·
              refine ⟨41029695381015312258301301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27353130254010208172200867 41029695381015312258301301)
              ·
                refine ⟨3846533941970185524215747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41029695381015312258301301 3846533941970185524215747)
                ·
                  refine ⟨5769800912955278286323621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846533941970185524215747 5769800912955278286323621)
                  ·
                    refine ⟨1081837671179114678685679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769800912955278286323621 1081837671179114678685679)
                    ·
                      rfl

theorem cell22_3160307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_3160307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160307 prefixEnd_3160307 := by exact prefixLift 3160307
  have htrace : WordTrace (prefixWord ++ tailWord_3160307) baseStart_3160307 baseEnd_3160307 := by
    simpa [prefixWord, tailWord_3160307, baseEnd_3160307] using wordTrace_append hprefix tailTrace_3160307
  have hstable : (prefixWord ++ tailWord_3160307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160307).length < 2 ^ (prefixWord ++ tailWord_3160307).sum := by decide
  have hdescent : baseEnd_3160307 < baseStart_3160307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160335 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3160335 : Nat := 118140960795 + 3160335 * 2 ^ 59
def prefixEnd_3160335 : Nat := 4983230072969 + 3 ^ 40 * 3160335 * 2
def baseEnd_3160335 : Nat := 1081847256151331938985593

theorem tailTrace_3160335 : CollatzResearch.WordTrace tailWord_3160335 prefixEnd_3160335 1081847256151331938985593 := by
  unfold tailWord_3160335
  simp only [CollatzResearch.WordTrace]
  refine ⟨115266887005653512092034459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76844591337102341394689639 115266887005653512092034459)
  ·
    refine ⟨172900330508480268138051689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115266887005653512092034459 172900330508480268138051689)
    ·
      refine ⟨129675247881360201103538767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172900330508480268138051689 129675247881360201103538767)
      ·
        refine ⟨194512871822040301655308151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129675247881360201103538767 194512871822040301655308151)
        ·
          refine ⟨291769307733060452482962227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194512871822040301655308151 291769307733060452482962227)
          ·
            refine ⟨437653961599590678724443341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291769307733060452482962227 437653961599590678724443341)
            ·
              refine ⟨164120235599846504521666253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437653961599590678724443341 164120235599846504521666253)
              ·
                refine ⟨61545088349942439195624845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164120235599846504521666253 61545088349942439195624845)
                ·
                  refine ⟨23079408131228414698359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61545088349942439195624845 23079408131228414698359317)
                  ·
                    refine ⟨1081847256151331938985593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23079408131228414698359317 1081847256151331938985593)
                    ·
                      rfl

theorem cell22_3160335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3160335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160335 prefixEnd_3160335 := by exact prefixLift 3160335
  have htrace : WordTrace (prefixWord ++ tailWord_3160335) baseStart_3160335 baseEnd_3160335 := by
    simpa [prefixWord, tailWord_3160335, baseEnd_3160335] using wordTrace_append hprefix tailTrace_3160335
  have hstable : (prefixWord ++ tailWord_3160335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160335).length < 2 ^ (prefixWord ++ tailWord_3160335).sum := by decide
  have hdescent : baseEnd_3160335 < baseStart_3160335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160354 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3160354 : Nat := 118140960795 + 3160354 * 2 ^ 59
def prefixEnd_3160354 : Nat := 4983230072969 + 3 ^ 40 * 3160354 * 2
def baseEnd_3160354 : Nat := 1081853760239622222760535

theorem tailTrace_3160354 : CollatzResearch.WordTrace tailWord_3160354 prefixEnd_3160354 1081853760239622222760535 := by
  unfold tailWord_3160354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816894998146169584244029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76845053328389785557984077 28816894998146169584244029)
  ·
    refine ⟨10806335624304813594091511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28816894998146169584244029 10806335624304813594091511)
    ·
      refine ⟨16209503436457220391137267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806335624304813594091511 16209503436457220391137267)
      ·
        refine ⟨24314255154685830586705901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16209503436457220391137267 24314255154685830586705901)
        ·
          refine ⟨9117845683007186470014713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24314255154685830586705901 9117845683007186470014713)
          ·
            refine ⟨6838384262255389852511035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9117845683007186470014713 6838384262255389852511035)
            ·
              refine ⟨10257576393383084778766553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838384262255389852511035 10257576393383084778766553)
              ·
                refine ⟨7693182295037313584074915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10257576393383084778766553 7693182295037313584074915)
                ·
                  refine ⟨11539773442555970376112373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693182295037313584074915 11539773442555970376112373)
                  ·
                    refine ⟨1081853760239622222760535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11539773442555970376112373 1081853760239622222760535)
                    ·
                      rfl

theorem cell22_3160354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3160354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160354 prefixEnd_3160354 := by exact prefixLift 3160354
  have htrace : WordTrace (prefixWord ++ tailWord_3160354) baseStart_3160354 baseEnd_3160354 := by
    simpa [prefixWord, tailWord_3160354, baseEnd_3160354] using wordTrace_append hprefix tailTrace_3160354
  have hstable : (prefixWord ++ tailWord_3160354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160354).length < 2 ^ (prefixWord ++ tailWord_3160354).sum := by decide
  have hdescent : baseEnd_3160354 < baseStart_3160354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160459 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 1, 4]
def baseStart_3160459 : Nat := 118140960795 + 3160459 * 2 ^ 59
def prefixEnd_3160459 : Nat := 4983230072969 + 3 ^ 40 * 3160459 * 2
def baseEnd_3160459 : Nat := 1081889703885436948885213

theorem tailTrace_3160459 : CollatzResearch.WordTrace tailWord_3160459 prefixEnd_3160459 1081889703885436948885213 := by
  unfold tailWord_3160459
  simp only [CollatzResearch.WordTrace]
  refine ⟨115271409657204281269548431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76847606438136187513032287 115271409657204281269548431)
  ·
    refine ⟨172907114485806421904322647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115271409657204281269548431 172907114485806421904322647)
    ·
      refine ⟨259360671728709632856483971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172907114485806421904322647 259360671728709632856483971)
      ·
        refine ⟨389041007593064449284725957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259360671728709632856483971 389041007593064449284725957)
        ·
          refine ⟨72945188923699584240886117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389041007593064449284725957 72945188923699584240886117)
          ·
            refine ⟨13677222923193672045166147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72945188923699584240886117 13677222923193672045166147)
            ·
              refine ⟨20515834384790508067749221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13677222923193672045166147 20515834384790508067749221)
              ·
                refine ⟨3846718947148220262702979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20515834384790508067749221 3846718947148220262702979)
                ·
                  refine ⟨5770078420722330394054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846718947148220262702979 5770078420722330394054469)
                  ·
                    refine ⟨1081889703885436948885213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770078420722330394054469 1081889703885436948885213)
                    ·
                      rfl

theorem cell22_3160459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_3160459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160459 prefixEnd_3160459 := by exact prefixLift 3160459
  have htrace : WordTrace (prefixWord ++ tailWord_3160459) baseStart_3160459 baseEnd_3160459 := by
    simpa [prefixWord, tailWord_3160459, baseEnd_3160459] using wordTrace_append hprefix tailTrace_3160459
  have hstable : (prefixWord ++ tailWord_3160459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160459).length < 2 ^ (prefixWord ++ tailWord_3160459).sum := by decide
  have hdescent : baseEnd_3160459 < baseStart_3160459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160551 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3160551 : Nat := 118140960795 + 3160551 * 2 ^ 59
def prefixEnd_3160551 : Nat := 4983230072969 + 3 ^ 40 * 3160551 * 2
def baseEnd_3160551 : Nat := 1081921197365579375584931

theorem tailTrace_3160551 : CollatzResearch.WordTrace tailWord_3160551 prefixEnd_3160551 1081921197365579375584931 := by
  unfold tailWord_3160551
  simp only [CollatzResearch.WordTrace]
  refine ⟨115274765172870980981897507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76849843448580653987931671 115274765172870980981897507)
  ·
    refine ⟨172912147759306471472846261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115274765172870980981897507 172912147759306471472846261)
    ·
      refine ⟨16210513852434981700579337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172912147759306471472846261 16210513852434981700579337)
      ·
        refine ⟨12157885389326236275434503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16210513852434981700579337 12157885389326236275434503)
        ·
          refine ⟨18236828083989354413151755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157885389326236275434503 18236828083989354413151755)
          ·
            refine ⟨27355242125984031619727633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236828083989354413151755 27355242125984031619727633)
            ·
              refine ⟨20516431594488023714795725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27355242125984031619727633 20516431594488023714795725)
              ·
                refine ⟨7693661847933008893048397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20516431594488023714795725 7693661847933008893048397)
                ·
                  refine ⟨2885123192974878334893149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7693661847933008893048397 2885123192974878334893149)
                  ·
                    refine ⟨1081921197365579375584931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885123192974878334893149 1081921197365579375584931)
                    ·
                      rfl

theorem cell22_3160551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3160551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160551 prefixEnd_3160551 := by exact prefixLift 3160551
  have htrace : WordTrace (prefixWord ++ tailWord_3160551) baseStart_3160551 baseEnd_3160551 := by
    simpa [prefixWord, tailWord_3160551, baseEnd_3160551] using wordTrace_append hprefix tailTrace_3160551
  have hstable : (prefixWord ++ tailWord_3160551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160551).length < 2 ^ (prefixWord ++ tailWord_3160551).sum := by decide
  have hdescent : baseEnd_3160551 < baseStart_3160551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160639 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3160639 : Nat := 118140960795 + 3160639 * 2 ^ 59
def prefixEnd_3160639 : Nat := 4983230072969 + 3 ^ 40 * 3160639 * 2
def baseEnd_3160639 : Nat := 1081951321563976479384661

theorem tailTrace_3160639 : CollatzResearch.WordTrace tailWord_3160639 prefixEnd_3160639 1081951321563976479384661 := by
  unfold tailWord_3160639
  simp only [CollatzResearch.WordTrace]
  refine ⟨115277974796552172011100971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76851983197701448007400647 115277974796552172011100971)
  ·
    refine ⟨172916962194828258016651457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115277974796552172011100971 172916962194828258016651457)
    ·
      refine ⟨129687721646121193512488593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172916962194828258016651457 129687721646121193512488593)
      ·
        refine ⟨97265791234590895134366445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129687721646121193512488593 97265791234590895134366445)
        ·
          refine ⟨36474671712971585675387417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97265791234590895134366445 36474671712971585675387417)
          ·
            refine ⟨27356003784728689256540563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36474671712971585675387417 27356003784728689256540563)
            ·
              refine ⟨41034005677093033884810845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356003784728689256540563 41034005677093033884810845)
              ·
                refine ⟨15387752128909887706804067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41034005677093033884810845 15387752128909887706804067)
                ·
                  refine ⟨23081628193364831560206101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15387752128909887706804067 23081628193364831560206101)
                  ·
                    refine ⟨1081951321563976479384661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23081628193364831560206101 1081951321563976479384661)
                    ·
                      rfl

theorem cell22_3160639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3160639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160639 prefixEnd_3160639 := by exact prefixLift 3160639
  have htrace : WordTrace (prefixWord ++ tailWord_3160639) baseStart_3160639 baseEnd_3160639 := by
    simpa [prefixWord, tailWord_3160639, baseEnd_3160639] using wordTrace_append hprefix tailTrace_3160639
  have hstable : (prefixWord ++ tailWord_3160639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160639).length < 2 ^ (prefixWord ++ tailWord_3160639).sum := by decide
  have hdescent : baseEnd_3160639 < baseStart_3160639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160654 : List Nat := [4, 1, 1, 1, 1, 2, 12]
def baseStart_3160654 : Nat := 118140960795 + 3160654 * 2 ^ 59
def prefixEnd_3160654 : Nat := 4983230072969 + 3 ^ 40 * 3160654 * 2
def baseEnd_3160654 : Nat := 40072461347056349639245

theorem tailTrace_3160654 : CollatzResearch.WordTrace tailWord_3160654 prefixEnd_3160654 40072461347056349639245 := by
  unfold tailWord_3160654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409815236437228696612127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76852347927665219715264677 14409815236437228696612127)
  ·
    refine ⟨21614722854655843044918191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14409815236437228696612127 21614722854655843044918191)
    ·
      refine ⟨32422084281983764567377287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21614722854655843044918191 32422084281983764567377287)
      ·
        refine ⟨48633126422975646851065931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32422084281983764567377287 48633126422975646851065931)
        ·
          refine ⟨72949689634463470276598897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48633126422975646851065931 72949689634463470276598897)
          ·
            refine ⟨54712267225847602707449173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72949689634463470276598897 54712267225847602707449173)
            ·
              refine ⟨40072461347056349639245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54712267225847602707449173 40072461347056349639245)
              ·
                rfl

theorem cell22_3160654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 12].length) (baseStart_3160654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160654 prefixEnd_3160654 := by exact prefixLift 3160654
  have htrace : WordTrace (prefixWord ++ tailWord_3160654) baseStart_3160654 baseEnd_3160654 := by
    simpa [prefixWord, tailWord_3160654, baseEnd_3160654] using wordTrace_append hprefix tailTrace_3160654
  have hstable : (prefixWord ++ tailWord_3160654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160654).length < 2 ^ (prefixWord ++ tailWord_3160654).sum := by decide
  have hdescent : baseEnd_3160654 < baseStart_3160654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160658 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3160658 : Nat := 118140960795 + 3160658 * 2 ^ 59
def prefixEnd_3160658 : Nat := 4983230072969 + 3 ^ 40 * 3160658 * 2
def baseEnd_3160658 : Nat := 1081957825652266763159603

theorem tailTrace_3160658 : CollatzResearch.WordTrace tailWord_3160658 prefixEnd_3160658 1081957825652266763159603 := by
  unfold tailWord_3160658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28819666945870834564010657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76852445188988892170695085 28819666945870834564010657)
  ·
    refine ⟨21614750209403125923007993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28819666945870834564010657 21614750209403125923007993)
    ·
      refine ⟨16211062657052344442255995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21614750209403125923007993 16211062657052344442255995)
      ·
        refine ⟨24316593985578516663383993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211062657052344442255995 24316593985578516663383993)
        ·
          refine ⟨18237445489183887497537995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24316593985578516663383993 18237445489183887497537995)
          ·
            refine ⟨27356168233775831246306993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237445489183887497537995 27356168233775831246306993)
            ·
              refine ⟨20517126175331873434730245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27356168233775831246306993 20517126175331873434730245)
              ·
                refine ⟨3846961157874726269011921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20517126175331873434730245 3846961157874726269011921)
                ·
                  refine ⟨2885220868406044701758941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3846961157874726269011921 2885220868406044701758941)
                  ·
                    refine ⟨1081957825652266763159603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885220868406044701758941 1081957825652266763159603)
                    ·
                      rfl

theorem cell22_3160658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3160658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160658 prefixEnd_3160658 := by exact prefixLift 3160658
  have htrace : WordTrace (prefixWord ++ tailWord_3160658) baseStart_3160658 baseEnd_3160658 := by
    simpa [prefixWord, tailWord_3160658, baseEnd_3160658] using wordTrace_append hprefix tailTrace_3160658
  have hstable : (prefixWord ++ tailWord_3160658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160658).length < 2 ^ (prefixWord ++ tailWord_3160658).sum := by decide
  have hdescent : baseEnd_3160658 < baseStart_3160658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160660 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3160660 : Nat := 118140960795 + 3160660 * 2 ^ 59
def prefixEnd_3160660 : Nat := 4983230072969 + 3 ^ 40 * 3160660 * 2
def baseEnd_3160660 : Nat := 360652836764379808203199

theorem tailTrace_3160660 : CollatzResearch.WordTrace tailWord_3160660 prefixEnd_3160660 360652836764379808203199 := by
  unfold tailWord_3160660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57639370364738046298807717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76852493819650728398410289 57639370364738046298807717)
  ·
    refine ⟨10807381943388383681026447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57639370364738046298807717 10807381943388383681026447)
    ·
      refine ⟨16211072915082575521539671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807381943388383681026447 16211072915082575521539671)
      ·
        refine ⟨24316609372623863282309507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211072915082575521539671 24316609372623863282309507)
        ·
          refine ⟨36474914058935794923464261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24316609372623863282309507 36474914058935794923464261)
          ·
            refine ⟨6839046386050461548149549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36474914058935794923464261 6839046386050461548149549)
            ·
              refine ⟨2564642394768923080556081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839046386050461548149549 2564642394768923080556081)
              ·
                refine ⟨1923481796076692310417061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564642394768923080556081 1923481796076692310417061)
                ·
                  refine ⟨360652836764379808203199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923481796076692310417061 360652836764379808203199)
                  ·
                    rfl

theorem cell22_3160660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3160660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160660 prefixEnd_3160660 := by exact prefixLift 3160660
  have htrace : WordTrace (prefixWord ++ tailWord_3160660) baseStart_3160660 baseEnd_3160660 := by
    simpa [prefixWord, tailWord_3160660, baseEnd_3160660] using wordTrace_append hprefix tailTrace_3160660
  have hstable : (prefixWord ++ tailWord_3160660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160660).length < 2 ^ (prefixWord ++ tailWord_3160660).sum := by decide
  have hdescent : baseEnd_3160660 < baseStart_3160660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160699 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 7]
def baseStart_3160699 : Nat := 118140960795 + 3160699 * 2 ^ 59
def prefixEnd_3160699 : Nat := 4983230072969 + 3 ^ 40 * 3160699 * 2
def baseEnd_3160699 : Nat := 360657286930052107628159

theorem tailTrace_3160699 : CollatzResearch.WordTrace tailWord_3160699 prefixEnd_3160699 360657286930052107628159 := by
  unfold tailWord_3160699
  simp only [CollatzResearch.WordTrace]
  refine ⟨115280163176334802258285151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76853442117556534838856767 115280163176334802258285151)
  ·
    refine ⟨172920244764502203387427727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115280163176334802258285151 172920244764502203387427727)
    ·
      refine ⟨259380367146753305081141591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172920244764502203387427727 259380367146753305081141591)
      ·
        refine ⟨389070550720129957621712387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259380367146753305081141591 389070550720129957621712387)
        ·
          refine ⟨583605826080194936432568581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389070550720129957621712387 583605826080194936432568581)
          ·
            refine ⟨109426092390036550581106609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583605826080194936432568581 109426092390036550581106609)
            ·
              refine ⟨82069569292527412935829957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109426092390036550581106609 82069569292527412935829957)
              ·
                refine ⟨15388044242348889925468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82069569292527412935829957 15388044242348889925468117)
                ·
                  refine ⟨360657286930052107628159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15388044242348889925468117 360657286930052107628159)
                  ·
                    rfl

theorem cell22_3160699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_3160699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160699 prefixEnd_3160699 := by exact prefixLift 3160699
  have htrace : WordTrace (prefixWord ++ tailWord_3160699) baseStart_3160699 baseEnd_3160699 := by
    simpa [prefixWord, tailWord_3160699, baseEnd_3160699] using wordTrace_append hprefix tailTrace_3160699
  have hstable : (prefixWord ++ tailWord_3160699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160699).length < 2 ^ (prefixWord ++ tailWord_3160699).sum := by decide
  have hdescent : baseEnd_3160699 < baseStart_3160699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160778 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_3160778 : Nat := 118140960795 + 3160778 * 2 ^ 59
def prefixEnd_3160778 : Nat := 4983230072969 + 3 ^ 40 * 3160778 * 2
def baseEnd_3160778 : Nat := 360666301368208816719745

theorem tailTrace_3160778 : CollatzResearch.WordTrace tailWord_3160778 prefixEnd_3160778 360666301368208816719745 := by
  unfold tailWord_3160778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820761135762149687602747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76855363028699065833607325 28820761135762149687602747)
  ·
    refine ⟨43231141703643224531404121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28820761135762149687602747 43231141703643224531404121)
    ·
      refine ⟨32423356277732418398553091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43231141703643224531404121 32423356277732418398553091)
      ·
        refine ⟨48635034416598627597829637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32423356277732418398553091 48635034416598627597829637)
        ·
          refine ⟨9119068953112242674593057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48635034416598627597829637 9119068953112242674593057)
          ·
            refine ⟨6839301714834182005944793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9119068953112242674593057 6839301714834182005944793)
            ·
              refine ⟨5129476286125636504458595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839301714834182005944793 5129476286125636504458595)
              ·
                refine ⟨7694214429188454756687893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129476286125636504458595 7694214429188454756687893)
                ·
                  refine ⟨360666301368208816719745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7694214429188454756687893 360666301368208816719745)
                  ·
                    rfl

theorem cell22_3160778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_3160778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160778 prefixEnd_3160778 := by exact prefixLift 3160778
  have htrace : WordTrace (prefixWord ++ tailWord_3160778) baseStart_3160778 baseEnd_3160778 := by
    simpa [prefixWord, tailWord_3160778, baseEnd_3160778] using wordTrace_append hprefix tailTrace_3160778
  have hstable : (prefixWord ++ tailWord_3160778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160778).length < 2 ^ (prefixWord ++ tailWord_3160778).sum := by decide
  have hdescent : baseEnd_3160778 < baseStart_3160778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160791 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3160791 : Nat := 118140960795 + 3160791 * 2 ^ 59
def prefixEnd_3160791 : Nat := 4983230072969 + 3 ^ 40 * 3160791 * 2
def baseEnd_3160791 : Nat := 1082003354270298749584195

theorem tailTrace_3160791 : CollatzResearch.WordTrace tailWord_3160791 prefixEnd_3160791 1082003354270298749584195 := by
  unfold tailWord_3160791
  simp only [CollatzResearch.WordTrace]
  refine ⟨115283518692001501970634227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76855679128001001313756151 115283518692001501970634227)
  ·
    refine ⟨172925278038002252955951341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115283518692001501970634227 172925278038002252955951341)
    ·
      refine ⟨64846979264250844858481753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172925278038002252955951341 64846979264250844858481753)
      ·
        refine ⟨48635234448188133643861315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64846979264250844858481753 48635234448188133643861315)
        ·
          refine ⟨72952851672282200465791973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48635234448188133643861315 72952851672282200465791973)
          ·
            refine ⟨13678659688552912587335995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72952851672282200465791973 13678659688552912587335995)
            ·
              refine ⟨20517989532829368881003993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13678659688552912587335995 20517989532829368881003993)
              ·
                refine ⟨15388492149622026660752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20517989532829368881003993 15388492149622026660752995)
                ·
                  refine ⟨23082738224433039991129493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15388492149622026660752995 23082738224433039991129493)
                  ·
                    refine ⟨1082003354270298749584195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23082738224433039991129493 1082003354270298749584195)
                    ·
                      rfl

theorem cell22_3160791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3160791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160791 prefixEnd_3160791 := by exact prefixLift 3160791
  have htrace : WordTrace (prefixWord ++ tailWord_3160791) baseStart_3160791 baseEnd_3160791 := by
    simpa [prefixWord, tailWord_3160791, baseEnd_3160791] using wordTrace_append hprefix tailTrace_3160791
  have hstable : (prefixWord ++ tailWord_3160791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160791).length < 2 ^ (prefixWord ++ tailWord_3160791).sum := by decide
  have hdescent : baseEnd_3160791 < baseStart_3160791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160872 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3160872 : Nat := 118140960795 + 3160872 * 2 ^ 59
def prefixEnd_3160872 : Nat := 4983230072969 + 3 ^ 40 * 3160872 * 2
def baseEnd_3160872 : Nat := 1082031082225641538308947

theorem tailTrace_3160872 : CollatzResearch.WordTrace tailWord_3160872 prefixEnd_3160872 1082031082225641538308947 := by
  unfold tailWord_3160872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57643236502354026402166435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76857648669805368536221913 57643236502354026402166435)
  ·
    refine ⟨86464854753531039603249653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57643236502354026402166435 86464854753531039603249653)
    ·
      refine ⟨8106080133143534962804655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86464854753531039603249653 8106080133143534962804655)
      ·
        refine ⟨12159120199715302444206983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8106080133143534962804655 12159120199715302444206983)
        ·
          refine ⟨18238680299572953666310475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12159120199715302444206983 18238680299572953666310475)
          ·
            refine ⟨27358020449359430499465713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18238680299572953666310475 27358020449359430499465713)
            ·
              refine ⟨20518515337019572874599285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27358020449359430499465713 20518515337019572874599285)
              ·
                refine ⟨1923610812845584956993683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20518515337019572874599285 1923610812845584956993683)
                ·
                  refine ⟨2885416219268377435490525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923610812845584956993683 2885416219268377435490525)
                  ·
                    refine ⟨1082031082225641538308947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885416219268377435490525 1082031082225641538308947)
                    ·
                      rfl

theorem cell22_3160872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3160872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160872 prefixEnd_3160872 := by exact prefixLift 3160872
  have htrace : WordTrace (prefixWord ++ tailWord_3160872) baseStart_3160872 baseEnd_3160872 := by
    simpa [prefixWord, tailWord_3160872, baseEnd_3160872] using wordTrace_append hprefix tailTrace_3160872
  have hstable : (prefixWord ++ tailWord_3160872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160872).length < 2 ^ (prefixWord ++ tailWord_3160872).sum := by decide
  have hdescent : baseEnd_3160872 < baseStart_3160872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160885 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 5]
def baseStart_3160885 : Nat := 118140960795 + 3160885 * 2 ^ 59
def prefixEnd_3160885 : Nat := 4983230072969 + 3 ^ 40 * 3160885 * 2
def baseEnd_3160885 : Nat := 360678510797104612577969

theorem tailTrace_3160885 : CollatzResearch.WordTrace tailWord_3160885 prefixEnd_3160885 360678510797104612577969 := by
  unfold tailWord_3160885
  simp only [CollatzResearch.WordTrace]
  refine ⟨115286947153660956024556109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76857964769107304016370739 115286947153660956024556109)
  ·
    refine ⟨43232605182622858509208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115286947153660956024556109 43232605182622858509208541)
    ·
      refine ⟨16212226943483571940953203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43232605182622858509208541 16212226943483571940953203)
      ·
        refine ⟨24318340415225357911429805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212226943483571940953203 24318340415225357911429805)
        ·
          refine ⟨9119377655709509216786177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24318340415225357911429805 9119377655709509216786177)
          ·
            refine ⟨6839533241782131912589633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9119377655709509216786177 6839533241782131912589633)
            ·
              refine ⟨5129649931336598934442225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839533241782131912589633 5129649931336598934442225)
              ·
                refine ⟨3847237448502449200831669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5129649931336598934442225 3847237448502449200831669)
                ·
                  refine ⟨360678510797104612577969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3847237448502449200831669 360678510797104612577969)
                  ·
                    rfl

theorem cell22_3160885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_3160885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160885 prefixEnd_3160885 := by exact prefixLift 3160885
  have htrace : WordTrace (prefixWord ++ tailWord_3160885) baseStart_3160885 baseEnd_3160885 := by
    simpa [prefixWord, tailWord_3160885, baseEnd_3160885] using wordTrace_append hprefix tailTrace_3160885
  have hstable : (prefixWord ++ tailWord_3160885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160885).length < 2 ^ (prefixWord ++ tailWord_3160885).sum := by decide
  have hdescent : baseEnd_3160885 < baseStart_3160885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160896 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_3160896 : Nat := 118140960795 + 3160896 * 2 ^ 59
def prefixEnd_3160896 : Nat := 4983230072969 + 3 ^ 40 * 3160896 * 2
def baseEnd_3160896 : Nat := 360679765972037825236291

theorem tailTrace_3160896 : CollatzResearch.WordTrace tailWord_3160896 prefixEnd_3160896 360679765972037825236291 := by
  unfold tailWord_3160896
  simp only [CollatzResearch.WordTrace]
  refine ⟨57643674178310552451603271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76858232237747403268804361 57643674178310552451603271)
  ·
    refine ⟨86465511267465828677404907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57643674178310552451603271 86465511267465828677404907)
    ·
      refine ⟨129698266901198743016107361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86465511267465828677404907 129698266901198743016107361)
      ·
        refine ⟨97273700175899057262080521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129698266901198743016107361 97273700175899057262080521)
        ·
          refine ⟨72955275131924292946560391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97273700175899057262080521 72955275131924292946560391)
          ·
            refine ⟨109432912697886439419840587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72955275131924292946560391 109432912697886439419840587)
            ·
              refine ⟨164149369046829659129760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109432912697886439419840587 164149369046829659129760881)
              ·
                refine ⟨123112026785122244347320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164149369046829659129760881 123112026785122244347320661)
                ·
                  refine ⟨360679765972037825236291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123112026785122244347320661 360679765972037825236291)
                  ·
                    rfl

theorem cell22_3160896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_3160896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160896 prefixEnd_3160896 := by exact prefixLift 3160896
  have htrace : WordTrace (prefixWord ++ tailWord_3160896) baseStart_3160896 baseEnd_3160896 := by
    simpa [prefixWord, tailWord_3160896, baseEnd_3160896] using wordTrace_append hprefix tailTrace_3160896
  have hstable : (prefixWord ++ tailWord_3160896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160896).length < 2 ^ (prefixWord ++ tailWord_3160896).sum := by decide
  have hdescent : baseEnd_3160896 < baseStart_3160896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160928 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_3160928 : Nat := 118140960795 + 3160928 * 2 ^ 59
def prefixEnd_3160928 : Nat := 4983230072969 + 3 ^ 40 * 3160928 * 2
def baseEnd_3160928 : Nat := 1082050252170076058908775

theorem tailTrace_3160928 : CollatzResearch.WordTrace tailWord_3160928 prefixEnd_3160928 1082050252170076058908775 := by
  unfold tailWord_3160928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644257746252587184185719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76859010328336782912247625 57644257746252587184185719)
  ·
    refine ⟨86466386619378880776278579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57644257746252587184185719 86466386619378880776278579)
    ·
      refine ⟨129699579929068321164417869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86466386619378880776278579 129699579929068321164417869)
      ·
        refine ⟨48637342473400620436656701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129699579929068321164417869 48637342473400620436656701)
        ·
          refine ⟨18239003427525232663746263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48637342473400620436656701 18239003427525232663746263)
          ·
            refine ⟨27358505141287848995619395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18239003427525232663746263 27358505141287848995619395)
            ·
              refine ⟨41037757711931773493429093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27358505141287848995619395 41037757711931773493429093)
              ·
                refine ⟨7694579570987207530017955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41037757711931773493429093 7694579570987207530017955)
                ·
                  refine ⟨11541869356480811295026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694579570987207530017955 11541869356480811295026933)
                  ·
                    refine ⟨1082050252170076058908775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11541869356480811295026933 1082050252170076058908775)
                    ·
                      rfl

theorem cell22_3160928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_3160928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160928 prefixEnd_3160928 := by exact prefixLift 3160928
  have htrace : WordTrace (prefixWord ++ tailWord_3160928) baseStart_3160928 baseEnd_3160928 := by
    simpa [prefixWord, tailWord_3160928, baseEnd_3160928] using wordTrace_append hprefix tailTrace_3160928
  have hstable : (prefixWord ++ tailWord_3160928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160928).length < 2 ^ (prefixWord ++ tailWord_3160928).sum := by decide
  have hdescent : baseEnd_3160928 < baseStart_3160928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160932 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_3160932 : Nat := 118140960795 + 3160932 * 2 ^ 59
def prefixEnd_3160932 : Nat := 4983230072969 + 3 ^ 40 * 3160932 * 2
def baseEnd_3160932 : Nat := 1082051621451821381808763

theorem tailTrace_3160932 : CollatzResearch.WordTrace tailWord_3160932 prefixEnd_3160932 1082051621451821381808763 := by
  unfold tailWord_3160932
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644330692245341525758525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76859107589660455367678033 57644330692245341525758525)
  ·
    refine ⟨21616624009592003072159447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57644330692245341525758525 21616624009592003072159447)
    ·
      refine ⟨32424936014388004608239171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21616624009592003072159447 32424936014388004608239171)
      ·
        refine ⟨48637404021582006912358757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32424936014388004608239171 48637404021582006912358757)
        ·
          refine ⟨9119513254046626296067267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48637404021582006912358757 9119513254046626296067267)
          ·
            refine ⟨13679269881069939444100901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119513254046626296067267 13679269881069939444100901)
            ·
              refine ⟨2564863102700613645768919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13679269881069939444100901 2564863102700613645768919)
              ·
                refine ⟨3847294654050920468653379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564863102700613645768919 3847294654050920468653379)
                ·
                  refine ⟨5770941981076380702980069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847294654050920468653379 5770941981076380702980069)
                  ·
                    refine ⟨1082051621451821381808763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770941981076380702980069 1082051621451821381808763)
                    ·
                      rfl

theorem cell22_3160932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_3160932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160932 prefixEnd_3160932 := by exact prefixLift 3160932
  have htrace : WordTrace (prefixWord ++ tailWord_3160932) baseStart_3160932 baseEnd_3160932 := by
    simpa [prefixWord, tailWord_3160932, baseEnd_3160932] using wordTrace_append hprefix tailTrace_3160932
  have hstable : (prefixWord ++ tailWord_3160932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160932).length < 2 ^ (prefixWord ++ tailWord_3160932).sum := by decide
  have hdescent : baseEnd_3160932 < baseStart_3160932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160943 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_3160943 : Nat := 118140960795 + 3160943 * 2 ^ 59
def prefixEnd_3160943 : Nat := 4983230072969 + 3 ^ 40 * 3160943 * 2
def baseEnd_3160943 : Nat := 1082055386976621019783729

theorem tailTrace_3160943 : CollatzResearch.WordTrace tailWord_3160943 prefixEnd_3160943 1082055386976621019783729 := by
  unfold tailWord_3160943
  simp only [CollatzResearch.WordTrace]
  refine ⟨115289062587450831930167483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76859375058300554620111655 115289062587450831930167483)
  ·
    refine ⟨172933593881176247895251225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115289062587450831930167483 172933593881176247895251225)
    ·
      refine ⟨129700195410882185921438419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172933593881176247895251225 129700195410882185921438419)
      ·
        refine ⟨194550293116323278882157629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129700195410882185921438419 194550293116323278882157629)
        ·
          refine ⟨72956359918621229580809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194550293116323278882157629 72956359918621229580809111)
          ·
            refine ⟨109434539877931844371213667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72956359918621229580809111 109434539877931844371213667)
            ·
              refine ⟨164151809816897766556820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109434539877931844371213667 164151809816897766556820501)
              ·
                refine ⟨7694616085167082807350961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164151809816897766556820501 7694616085167082807350961)
                ·
                  refine ⟨5770962063875312105513221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694616085167082807350961 5770962063875312105513221)
                  ·
                    refine ⟨1082055386976621019783729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770962063875312105513221 1082055386976621019783729)
                    ·
                      rfl

theorem cell22_3160943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_3160943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160943 prefixEnd_3160943 := by exact prefixLift 3160943
  have htrace : WordTrace (prefixWord ++ tailWord_3160943) baseStart_3160943 baseEnd_3160943 := by
    simpa [prefixWord, tailWord_3160943, baseEnd_3160943] using wordTrace_append hprefix tailTrace_3160943
  have hstable : (prefixWord ++ tailWord_3160943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160943).length < 2 ^ (prefixWord ++ tailWord_3160943).sum := by decide
  have hdescent : baseEnd_3160943 < baseStart_3160943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160945 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_3160945 : Nat := 118140960795 + 3160945 * 2 ^ 59
def prefixEnd_3160945 : Nat := 4983230072969 + 3 ^ 40 * 3160945 * 2
def baseEnd_3160945 : Nat := 1082056071617493681233723

theorem tailTrace_3160945 : CollatzResearch.WordTrace tailWord_3160945 prefixEnd_3160945 1082056071617493681233723 := by
  unfold tailWord_3160945
  simp only [CollatzResearch.WordTrace]
  refine ⟨115289135533443586271740289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76859423688962390847826859 115289135533443586271740289)
  ·
    refine ⟨86466851650082689703805217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115289135533443586271740289 86466851650082689703805217)
    ·
      refine ⟨64850138737562017277853913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86466851650082689703805217 64850138737562017277853913)
      ·
        refine ⟨48637604053171512958390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64850138737562017277853913 48637604053171512958390435)
        ·
          refine ⟨72956406079757269437585653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48637604053171512958390435 72956406079757269437585653)
          ·
            refine ⟨6839663069977244009773655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72956406079757269437585653 6839663069977244009773655)
            ·
              refine ⟨10259494604965866014660483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839663069977244009773655 10259494604965866014660483)
              ·
                refine ⟨15389241907448799021990725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259494604965866014660483 15389241907448799021990725)
                ·
                  refine ⟨2885482857646649816623261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15389241907448799021990725 2885482857646649816623261)
                  ·
                    refine ⟨1082056071617493681233723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885482857646649816623261 1082056071617493681233723)
                    ·
                      rfl

theorem cell22_3160945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_3160945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3160945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3160945 prefixEnd_3160945 := by exact prefixLift 3160945
  have htrace : WordTrace (prefixWord ++ tailWord_3160945) baseStart_3160945 baseEnd_3160945 := by
    simpa [prefixWord, tailWord_3160945, baseEnd_3160945] using wordTrace_append hprefix tailTrace_3160945
  have hstable : (prefixWord ++ tailWord_3160945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160945).length < 2 ^ (prefixWord ++ tailWord_3160945).sum := by decide
  have hdescent : baseEnd_3160945 < baseStart_3160945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161018 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3161018 : Nat := 118140960795 + 3161018 * 2 ^ 59
def prefixEnd_3161018 : Nat := 4983230072969 + 3 ^ 40 * 3161018 * 2
def baseEnd_3161018 : Nat := 1082081061009345824158499

theorem tailTrace_3161018 : CollatzResearch.WordTrace tailWord_3161018 prefixEnd_3161018 1082081061009345824158499 := by
  unfold tailWord_3161018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822949515544779934786927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76861198708119413159431805 28822949515544779934786927)
  ·
    refine ⟨43234424273317169902180391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28822949515544779934786927 43234424273317169902180391)
    ·
      refine ⟨64851636409975754853270587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43234424273317169902180391 64851636409975754853270587)
      ·
        refine ⟨97277454614963632279905881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64851636409975754853270587 97277454614963632279905881)
        ·
          refine ⟨72958090961222724209929411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97277454614963632279905881 72958090961222724209929411)
          ·
            refine ⟨109437136441834086314894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72958090961222724209929411 109437136441834086314894117)
            ·
              refine ⟨20519463082843891184042647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109437136441834086314894117 20519463082843891184042647)
              ·
                refine ⟨30779194624265836776063971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20519463082843891184042647 30779194624265836776063971)
                ·
                  refine ⟨46168791936398755164095957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30779194624265836776063971 46168791936398755164095957)
                  ·
                    refine ⟨1082081061009345824158499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46168791936398755164095957 1082081061009345824158499)
                    ·
                      rfl

theorem cell22_3161018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3161018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161018 prefixEnd_3161018 := by exact prefixLift 3161018
  have htrace : WordTrace (prefixWord ++ tailWord_3161018) baseStart_3161018 baseEnd_3161018 := by
    simpa [prefixWord, tailWord_3161018, baseEnd_3161018] using wordTrace_append hprefix tailTrace_3161018
  have hstable : (prefixWord ++ tailWord_3161018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161018).length < 2 ^ (prefixWord ++ tailWord_3161018).sum := by decide
  have hdescent : baseEnd_3161018 < baseStart_3161018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161058 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3161058 : Nat := 118140960795 + 3161058 * 2 ^ 59
def prefixEnd_3161058 : Nat := 4983230072969 + 3 ^ 40 * 3161058 * 2
def baseEnd_3161058 : Nat := 1082094753826799053158377

theorem tailTrace_3161058 : CollatzResearch.WordTrace tailWord_3161058 prefixEnd_3161058 1082094753826799053158377 := by
  unfold tailWord_3161058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28823314245508551642650957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76862171321356137713735885 28823314245508551642650957)
  ·
    refine ⟨10808742842065706865994109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28823314245508551642650957 10808742842065706865994109)
    ·
      refine ⟨4053278565774640074747791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10808742842065706865994109 4053278565774640074747791)
      ·
        refine ⟨6079917848661960112121687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053278565774640074747791 6079917848661960112121687)
        ·
          refine ⟨9119876772992940168182531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079917848661960112121687 9119876772992940168182531)
          ·
            refine ⟨13679815159489410252273797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119876772992940168182531 13679815159489410252273797)
            ·
              refine ⟨2564965342404264422301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13679815159489410252273797 2564965342404264422301337)
              ·
                refine ⟨1923724006803198316726003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564965342404264422301337 1923724006803198316726003)
                ·
                  refine ⟨2885586010204797475089005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923724006803198316726003 2885586010204797475089005)
                  ·
                    refine ⟨1082094753826799053158377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885586010204797475089005 1082094753826799053158377)
                    ·
                      rfl

theorem cell22_3161058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3161058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161058 prefixEnd_3161058 := by exact prefixLift 3161058
  have htrace : WordTrace (prefixWord ++ tailWord_3161058) baseStart_3161058 baseEnd_3161058 := by
    simpa [prefixWord, tailWord_3161058, baseEnd_3161058] using wordTrace_append hprefix tailTrace_3161058
  have hstable : (prefixWord ++ tailWord_3161058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161058).length < 2 ^ (prefixWord ++ tailWord_3161058).sum := by decide
  have hdescent : baseEnd_3161058 < baseStart_3161058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161080 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_3161080 : Nat := 118140960795 + 3161080 * 2 ^ 59
def prefixEnd_3161080 : Nat := 4983230072969 + 3 ^ 40 * 3161080 * 2
def baseEnd_3161080 : Nat := 1082102284876398329108309

theorem tailTrace_3161080 : CollatzResearch.WordTrace tailWord_3161080 prefixEnd_3161080 1082102284876398329108309 := by
  unfold tailWord_3161080
  simp only [CollatzResearch.WordTrace]
  refine ⟨57647029693977252163952347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76862706258636336218603129 57647029693977252163952347)
  ·
    refine ⟨86470544540965878245928521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57647029693977252163952347 86470544540965878245928521)
    ·
      refine ⟨64852908405724408684446391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86470544540965878245928521 64852908405724408684446391)
      ·
        refine ⟨97279362608586613026669587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64852908405724408684446391 97279362608586613026669587)
        ·
          refine ⟨145919043912879919540004381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97279362608586613026669587 145919043912879919540004381)
          ·
            refine ⟨54719641467329969827501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145919043912879919540004381 54719641467329969827501643)
            ·
              refine ⟨82079462200994954741252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54719641467329969827501643 82079462200994954741252465)
              ·
                refine ⟨61559596650746216055939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82079462200994954741252465 61559596650746216055939349)
                ·
                  refine ⟨2885606093003728877622157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61559596650746216055939349 2885606093003728877622157)
                  ·
                    refine ⟨1082102284876398329108309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885606093003728877622157 1082102284876398329108309)
                    ·
                      rfl

theorem cell22_3161080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_3161080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161080 prefixEnd_3161080 := by exact prefixLift 3161080
  have htrace : WordTrace (prefixWord ++ tailWord_3161080) baseStart_3161080 baseEnd_3161080 := by
    simpa [prefixWord, tailWord_3161080, baseEnd_3161080] using wordTrace_append hprefix tailTrace_3161080
  have hstable : (prefixWord ++ tailWord_3161080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161080).length < 2 ^ (prefixWord ++ tailWord_3161080).sum := by decide
  have hdescent : baseEnd_3161080 < baseStart_3161080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161095 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3161095 : Nat := 118140960795 + 3161095 * 2 ^ 59
def prefixEnd_3161095 : Nat := 4983230072969 + 3 ^ 40 * 3161095 * 2
def baseEnd_3161095 : Nat := 1082107419682943289983263

theorem tailTrace_3161095 : CollatzResearch.WordTrace tailWord_3161095 prefixEnd_3161095 1082107419682943289983263 := by
  unfold tailWord_3161095
  simp only [CollatzResearch.WordTrace]
  refine ⟨115294606482900161889700739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76863070988600107926467159 115294606482900161889700739)
  ·
    refine ⟨172941909724350242834551109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115294606482900161889700739 172941909724350242834551109)
    ·
      refine ⟨32426608073315670531478333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172941909724350242834551109 32426608073315670531478333)
      ·
        refine ⟨12159978027493376449304375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32426608073315670531478333 12159978027493376449304375)
        ·
          refine ⟨18239967041240064673956563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12159978027493376449304375 18239967041240064673956563)
          ·
            refine ⟨27359950561860097010934845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18239967041240064673956563 27359950561860097010934845)
            ·
              refine ⟨10259981460697536379100567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27359950561860097010934845 10259981460697536379100567)
              ·
                refine ⟨15389972191046304568650851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259981460697536379100567 15389972191046304568650851)
                ·
                  refine ⟨23084958286569456852976277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15389972191046304568650851 23084958286569456852976277)
                  ·
                    refine ⟨1082107419682943289983263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23084958286569456852976277 1082107419682943289983263)
                    ·
                      rfl

theorem cell22_3161095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3161095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161095 prefixEnd_3161095 := by exact prefixLift 3161095
  have htrace : WordTrace (prefixWord ++ tailWord_3161095) baseStart_3161095 baseEnd_3161095 := by
    simpa [prefixWord, tailWord_3161095, baseEnd_3161095] using wordTrace_append hprefix tailTrace_3161095
  have hstable : (prefixWord ++ tailWord_3161095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161095).length < 2 ^ (prefixWord ++ tailWord_3161095).sum := by decide
  have hdescent : baseEnd_3161095 < baseStart_3161095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161176 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_3161176 : Nat := 118140960795 + 3161176 * 2 ^ 59
def prefixEnd_3161176 : Nat := 4983230072969 + 3 ^ 40 * 3161176 * 2
def baseEnd_3161176 : Nat := 1082135147638286078708015

theorem tailTrace_3161176 : CollatzResearch.WordTrace tailWord_3161176 prefixEnd_3161176 1082135147638286078708015 := by
  unfold tailWord_3161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨57648780397803356361699691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76865040530404475148932921 57648780397803356361699691)
  ·
    refine ⟨86473170596705034542549537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57648780397803356361699691 86473170596705034542549537)
    ·
      refine ⟨64854877947528775906912153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86473170596705034542549537 64854877947528775906912153)
      ·
        refine ⟨48641158460646581930184115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64854877947528775906912153 48641158460646581930184115)
        ·
          refine ⟨72961737690969872895276173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48641158460646581930184115 72961737690969872895276173)
          ·
            refine ⟨27360651634113702335728565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72961737690969872895276173 27360651634113702335728565)
            ·
              refine ⟨2565061090698159593974553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27360651634113702335728565 2565061090698159593974553)
              ·
                refine ⟨1923795818023619695480915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565061090698159593974553 1923795818023619695480915)
                ·
                  refine ⟨2885693727035429543221373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923795818023619695480915 2885693727035429543221373)
                  ·
                    refine ⟨1082135147638286078708015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885693727035429543221373 1082135147638286078708015)
                    ·
                      rfl

theorem cell22_3161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_3161176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161176 prefixEnd_3161176 := by exact prefixLift 3161176
  have htrace : WordTrace (prefixWord ++ tailWord_3161176) baseStart_3161176 baseEnd_3161176 := by
    simpa [prefixWord, tailWord_3161176, baseEnd_3161176] using wordTrace_append hprefix tailTrace_3161176
  have hstable : (prefixWord ++ tailWord_3161176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161176).length < 2 ^ (prefixWord ++ tailWord_3161176).sum := by decide
  have hdescent : baseEnd_3161176 < baseStart_3161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161200 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_3161200 : Nat := 118140960795 + 3161200 * 2 ^ 59
def prefixEnd_3161200 : Nat := 4983230072969 + 3 ^ 40 * 3161200 * 2
def baseEnd_3161200 : Nat := 360714454442919338702647

theorem tailTrace_3161200 : CollatzResearch.WordTrace tailWord_3161200 prefixEnd_3161200 360714454442919338702647 := by
  unfold tailWord_3161200
  simp only [CollatzResearch.WordTrace]
  refine ⟨57649218073759882411136527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76865624098346509881515369 57649218073759882411136527)
  ·
    refine ⟨86473827110639823616704791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57649218073759882411136527 86473827110639823616704791)
    ·
      refine ⟨129710740665959735425057187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86473827110639823616704791 129710740665959735425057187)
      ·
        refine ⟨194566110998939603137585781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129710740665959735425057187 194566110998939603137585781)
        ·
          refine ⟨18240572906150587794148667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194566110998939603137585781 18240572906150587794148667)
          ·
            refine ⟨27360859359225881691223001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240572906150587794148667 27360859359225881691223001)
            ·
              refine ⟨20520644519419411268417251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27360859359225881691223001 20520644519419411268417251)
              ·
                refine ⟨30780966779129116902625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20520644519419411268417251 30780966779129116902625877)
                ·
                  refine ⟨360714454442919338702647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30780966779129116902625877 360714454442919338702647)
                  ·
                    rfl

theorem cell22_3161200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_3161200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161200 prefixEnd_3161200 := by exact prefixLift 3161200
  have htrace : WordTrace (prefixWord ++ tailWord_3161200) baseStart_3161200 baseEnd_3161200 := by
    simpa [prefixWord, tailWord_3161200, baseEnd_3161200] using wordTrace_append hprefix tailTrace_3161200
  have hstable : (prefixWord ++ tailWord_3161200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161200).length < 2 ^ (prefixWord ++ tailWord_3161200).sum := by decide
  have hdescent : baseEnd_3161200 < baseStart_3161200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161202 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_3161202 : Nat := 118140960795 + 3161202 * 2 ^ 59
def prefixEnd_3161202 : Nat := 4983230072969 + 3 ^ 40 * 3161202 * 2
def baseEnd_3161202 : Nat := 1082144047969630677557935

theorem tailTrace_3161202 : CollatzResearch.WordTrace tailWord_3161202 prefixEnd_3161202 1082144047969630677557935 := by
  unfold tailWord_3161202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28824627273378129790961465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76865672729008346109230573 28824627273378129790961465)
  ·
    refine ⟨21618470455033597343221099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28824627273378129790961465 21618470455033597343221099)
    ·
      refine ⟨32427705682550396014831649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21618470455033597343221099 32427705682550396014831649)
      ·
        refine ⟨24320779261912797011123737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32427705682550396014831649 24320779261912797011123737)
        ·
          refine ⟨18240584446434597758342803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24320779261912797011123737 18240584446434597758342803)
          ·
            refine ⟨27360876669651896637514205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240584446434597758342803 27360876669651896637514205)
            ·
              refine ⟨10260328751119461239067827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27360876669651896637514205 10260328751119461239067827)
              ·
                refine ⟨15390493126679191858601741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260328751119461239067827 15390493126679191858601741)
                ·
                  refine ⟨5771434922504696946975653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15390493126679191858601741 5771434922504696946975653)
                  ·
                    refine ⟨1082144047969630677557935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771434922504696946975653 1082144047969630677557935)
                    ·
                      rfl

theorem cell22_3161202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_3161202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161202 prefixEnd_3161202 := by exact prefixLift 3161202
  have htrace : WordTrace (prefixWord ++ tailWord_3161202) baseStart_3161202 baseEnd_3161202 := by
    simpa [prefixWord, tailWord_3161202, baseEnd_3161202] using wordTrace_append hprefix tailTrace_3161202
  have hstable : (prefixWord ++ tailWord_3161202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161202).length < 2 ^ (prefixWord ++ tailWord_3161202).sum := by decide
  have hdescent : baseEnd_3161202 < baseStart_3161202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161219 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 1, 4]
def baseStart_3161219 : Nat := 118140960795 + 3161219 * 2 ^ 59
def prefixEnd_3161219 : Nat := 4983230072969 + 3 ^ 40 * 3161219 * 2
def baseEnd_3161219 : Nat := 1082149867417048299882883

theorem tailTrace_3161219 : CollatzResearch.WordTrace tailWord_3161219 prefixEnd_3161219 1082149867417048299882883 := by
  unfold tailWord_3161219
  simp only [CollatzResearch.WordTrace]
  refine ⟨115299129134450931067214711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76866086089633954044809807 115299129134450931067214711)
  ·
    refine ⟨172948693701676396600822067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115299129134450931067214711 172948693701676396600822067)
    ·
      refine ⟨259423040552514594901233101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172948693701676396600822067 259423040552514594901233101)
      ·
        refine ⟨97283640207192973087962413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259423040552514594901233101 97283640207192973087962413)
        ·
          refine ⟨36481365077697364907985905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97283640207192973087962413 36481365077697364907985905)
          ·
            refine ⟨27361023808273023680989429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36481365077697364907985905 27361023808273023680989429)
            ·
              refine ⟨2565095982025595970092759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27361023808273023680989429 2565095982025595970092759)
              ·
                refine ⟨3847643973038393955139139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565095982025595970092759 3847643973038393955139139)
                ·
                  refine ⟨5771465959557590932708709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847643973038393955139139 5771465959557590932708709)
                  ·
                    refine ⟨1082149867417048299882883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771465959557590932708709 1082149867417048299882883)
                    ·
                      rfl

theorem cell22_3161219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 4].length) (baseStart_3161219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161219 prefixEnd_3161219 := by exact prefixLift 3161219
  have htrace : WordTrace (prefixWord ++ tailWord_3161219) baseStart_3161219 baseEnd_3161219 := by
    simpa [prefixWord, tailWord_3161219, baseEnd_3161219] using wordTrace_append hprefix tailTrace_3161219
  have hstable : (prefixWord ++ tailWord_3161219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161219).length < 2 ^ (prefixWord ++ tailWord_3161219).sum := by decide
  have hdescent : baseEnd_3161219 < baseStart_3161219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161249 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3161249 : Nat := 118140960795 + 3161249 * 2 ^ 59
def prefixEnd_3161249 : Nat := 4983230072969 + 3 ^ 40 * 3161249 * 2
def baseEnd_3161249 : Nat := 1082160137030138221632791

theorem tailTrace_3161249 : CollatzResearch.WordTrace tailWord_3161249 prefixEnd_3161249 1082160137030138221632791 := by
  unfold tailWord_3161249
  simp only [CollatzResearch.WordTrace]
  refine ⟨115300223324342246190806801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76866815549561497460537867 115300223324342246190806801)
  ·
    refine ⟨86475167493256684643105101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115300223324342246190806801 86475167493256684643105101)
    ·
      refine ⟨32428187809971256741164413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86475167493256684643105101 32428187809971256741164413)
      ·
        refine ⟨12160570428739221277936655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32428187809971256741164413 12160570428739221277936655)
        ·
          refine ⟨18240855643108831916904983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12160570428739221277936655 18240855643108831916904983)
          ·
            refine ⟨27361283464663247875357475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240855643108831916904983 27361283464663247875357475)
            ·
              refine ⟨41041925196994871813036213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27361283464663247875357475 41041925196994871813036213)
              ·
                refine ⟨3847680487218269232472145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41041925196994871813036213 3847680487218269232472145)
                ·
                  refine ⟨2885760365413701924354109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847680487218269232472145 2885760365413701924354109)
                  ·
                    refine ⟨1082160137030138221632791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885760365413701924354109 1082160137030138221632791)
                    ·
                      rfl

theorem cell22_3161249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3161249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161249 prefixEnd_3161249 := by exact prefixLift 3161249
  have htrace : WordTrace (prefixWord ++ tailWord_3161249) baseStart_3161249 baseEnd_3161249 := by
    simpa [prefixWord, tailWord_3161249, baseEnd_3161249] using wordTrace_append hprefix tailTrace_3161249
  have hstable : (prefixWord ++ tailWord_3161249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161249).length < 2 ^ (prefixWord ++ tailWord_3161249).sum := by decide
  have hdescent : baseEnd_3161249 < baseStart_3161249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_3161260 : Nat := 118140960795 + 3161260 * 2 ^ 59
def prefixEnd_3161260 : Nat := 4983230072969 + 3 ^ 40 * 3161260 * 2
def baseEnd_3161260 : Nat := 1082163902554937859607757

theorem tailTrace_3161260 : CollatzResearch.WordTrace tailWord_3161260 prefixEnd_3161260 1082163902554937859607757 := by
  unfold tailWord_3161260
  simp only [CollatzResearch.WordTrace]
  refine ⟨57650312263651197534728617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76867083018201596712971489 57650312263651197534728617)
  ·
    refine ⟨43237734197738398151046463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57650312263651197534728617 43237734197738398151046463)
    ·
      refine ⟨64856601296607597226569695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43237734197738398151046463 64856601296607597226569695)
      ·
        refine ⟨97284901944911395839854543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64856601296607597226569695 97284901944911395839854543)
        ·
          refine ⟨145927352917367093759781815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97284901944911395839854543 145927352917367093759781815)
          ·
            refine ⟨218891029376050640639672723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145927352917367093759781815 218891029376050640639672723)
            ·
              refine ⟨328336544064075960959509085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218891029376050640639672723 328336544064075960959509085)
              ·
                refine ⟨123126204024028485359815907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328336544064075960959509085 123126204024028485359815907)
                ·
                  refine ⟨184689306036042728039723861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123126204024028485359815907 184689306036042728039723861)
                  ·
                    refine ⟨1082163902554937859607757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 184689306036042728039723861 1082163902554937859607757)
                    ·
                      rfl

theorem cell22_3161260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_3161260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161260 prefixEnd_3161260 := by exact prefixLift 3161260
  have htrace : WordTrace (prefixWord ++ tailWord_3161260) baseStart_3161260 baseEnd_3161260 := by
    simpa [prefixWord, tailWord_3161260, baseEnd_3161260] using wordTrace_append hprefix tailTrace_3161260
  have hstable : (prefixWord ++ tailWord_3161260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161260).length < 2 ^ (prefixWord ++ tailWord_3161260).sum := by decide
  have hdescent : baseEnd_3161260 < baseStart_3161260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161275 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_3161275 : Nat := 118140960795 + 3161275 * 2 ^ 59
def prefixEnd_3161275 : Nat := 4983230072969 + 3 ^ 40 * 3161275 * 2
def baseEnd_3161275 : Nat := 1082169037361482820482711

theorem tailTrace_3161275 : CollatzResearch.WordTrace tailWord_3161275 prefixEnd_3161275 1082169037361482820482711 := by
  unfold tailWord_3161275
  simp only [CollatzResearch.WordTrace]
  refine ⟨115301171622248052631253279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76867447748165368420835519 115301171622248052631253279)
  ·
    refine ⟨172951757433372078946879919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115301171622248052631253279 172951757433372078946879919)
    ·
      refine ⟨259427636150058118420319879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172951757433372078946879919 259427636150058118420319879)
      ·
        refine ⟨389141454225087177630479819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259427636150058118420319879 389141454225087177630479819)
        ·
          refine ⟨583712181337630766445719729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389141454225087177630479819 583712181337630766445719729)
          ·
            refine ⟨437784136003223074834289797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583712181337630766445719729 437784136003223074834289797)
            ·
              refine ⟨82084525500604326531429337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437784136003223074834289797 82084525500604326531429337)
              ·
                refine ⟨61563394125453244898572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82084525500604326531429337 61563394125453244898572003)
                ·
                  refine ⟨92345091188179867347858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61563394125453244898572003 92345091188179867347858005)
                  ·
                    refine ⟨1082169037361482820482711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92345091188179867347858005 1082169037361482820482711)
                    ·
                      rfl

theorem cell22_3161275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_3161275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161275 prefixEnd_3161275 := by exact prefixLift 3161275
  have htrace : WordTrace (prefixWord ++ tailWord_3161275) baseStart_3161275 baseEnd_3161275 := by
    simpa [prefixWord, tailWord_3161275, baseEnd_3161275] using wordTrace_append hprefix tailTrace_3161275
  have hstable : (prefixWord ++ tailWord_3161275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161275).length < 2 ^ (prefixWord ++ tailWord_3161275).sum := by decide
  have hdescent : baseEnd_3161275 < baseStart_3161275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161300 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3161300 : Nat := 118140960795 + 3161300 * 2 ^ 59
def prefixEnd_3161300 : Nat := 4983230072969 + 3 ^ 40 * 3161300 * 2
def baseEnd_3161300 : Nat := 1082177595372391088607635

theorem tailTrace_3161300 : CollatzResearch.WordTrace tailWord_3161300 prefixEnd_3161300 1082177595372391088607635 := by
  unfold tailWord_3161300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57651041723578740950456677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76868055631438321267275569 57651041723578740950456677)
  ·
    refine ⟨10809570323171013928210627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57651041723578740950456677 10809570323171013928210627)
    ·
      refine ⟨16214355484756520892315941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809570323171013928210627 16214355484756520892315941)
      ·
        refine ⟨3040191653391847667309239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16214355484756520892315941 3040191653391847667309239)
        ·
          refine ⟨4560287480087771500963859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040191653391847667309239 4560287480087771500963859)
          ·
            refine ⟨6840431220131657251445789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560287480087771500963859 6840431220131657251445789)
            ·
              refine ⟨2565161707549371469292171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6840431220131657251445789 2565161707549371469292171)
              ·
                refine ⟨3847742561324057203938257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565161707549371469292171 3847742561324057203938257)
                ·
                  refine ⟨2885806920993042902953693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847742561324057203938257 2885806920993042902953693)
                  ·
                    refine ⟨1082177595372391088607635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885806920993042902953693 1082177595372391088607635)
                    ·
                      rfl

theorem cell22_3161300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3161300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161300 prefixEnd_3161300 := by exact prefixLift 3161300
  have htrace : WordTrace (prefixWord ++ tailWord_3161300) baseStart_3161300 baseEnd_3161300 := by
    simpa [prefixWord, tailWord_3161300, baseEnd_3161300] using wordTrace_append hprefix tailTrace_3161300
  have hstable : (prefixWord ++ tailWord_3161300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161300).length < 2 ^ (prefixWord ++ tailWord_3161300).sum := by decide
  have hdescent : baseEnd_3161300 < baseStart_3161300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161384 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3161384 : Nat := 118140960795 + 3161384 * 2 ^ 59
def prefixEnd_3161384 : Nat := 4983230072969 + 3 ^ 40 * 3161384 * 2
def baseEnd_3161384 : Nat := 1082206350289042869507377

theorem tailTrace_3161384 : CollatzResearch.WordTrace tailWord_3161384 prefixEnd_3161384 1082206350289042869507377 := by
  unfold tailWord_3161384
  simp only [CollatzResearch.WordTrace]
  refine ⟨57652573589426582123485603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76870098119235442831314137 57652573589426582123485603)
  ·
    refine ⟨86478860384139873185228405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57652573589426582123485603 86478860384139873185228405)
    ·
      refine ⟨8107393161013113111115163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86478860384139873185228405 8107393161013113111115163)
      ·
        refine ⟨12161089741519669666672745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107393161013113111115163 12161089741519669666672745)
        ·
          refine ⟨9120817306139752250004559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12161089741519669666672745 9120817306139752250004559)
          ·
            refine ⟨13681225959209628375006839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120817306139752250004559 13681225959209628375006839)
            ·
              refine ⟨20521838938814442562510259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13681225959209628375006839 20521838938814442562510259)
              ·
                refine ⟨30782758408221663843765389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20521838938814442562510259 30782758408221663843765389)
                ·
                  refine ⟨11543534403083123941412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30782758408221663843765389 11543534403083123941412021)
                  ·
                    refine ⟨1082206350289042869507377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11543534403083123941412021 1082206350289042869507377)
                    ·
                      rfl

theorem cell22_3161384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3161384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161384 prefixEnd_3161384 := by exact prefixLift 3161384
  have htrace : WordTrace (prefixWord ++ tailWord_3161384) baseStart_3161384 baseEnd_3161384 := by
    simpa [prefixWord, tailWord_3161384, baseEnd_3161384] using wordTrace_append hprefix tailTrace_3161384
  have hstable : (prefixWord ++ tailWord_3161384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161384).length < 2 ^ (prefixWord ++ tailWord_3161384).sum := by decide
  have hdescent : baseEnd_3161384 < baseStart_3161384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161397 : List Nat := [1, 3, 3, 1, 2, 12]
def baseStart_3161397 : Nat := 118140960795 + 3161397 * 2 ^ 59
def prefixEnd_3161397 : Nat := 4983230072969 + 3 ^ 40 * 3161397 * 2
def baseEnd_3161397 : Nat := 13360627166107594678177

theorem tailTrace_3161397 : CollatzResearch.WordTrace tailWord_3161397 prefixEnd_3161397 13360627166107594678177 := by
  unfold tailWord_3161397
  simp only [CollatzResearch.WordTrace]
  refine ⟨115305621327806067467194445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76870414218537378311462963 115305621327806067467194445)
  ·
    refine ⟨43239607997927275300197917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115305621327806067467194445 43239607997927275300197917)
    ·
      refine ⟨16214852999222728237574219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43239607997927275300197917 16214852999222728237574219)
      ·
        refine ⟨24322279498834092356361329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16214852999222728237574219 24322279498834092356361329)
        ·
          refine ⟨18241709624125569267270997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24322279498834092356361329 18241709624125569267270997)
          ·
            refine ⟨13360627166107594678177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18241709624125569267270997 13360627166107594678177)
            ·
              rfl

theorem cell22_3161397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 12].length) (baseStart_3161397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161397 prefixEnd_3161397 := by exact prefixLift 3161397
  have htrace : WordTrace (prefixWord ++ tailWord_3161397) baseStart_3161397 baseEnd_3161397 := by
    simpa [prefixWord, tailWord_3161397, baseEnd_3161397] using wordTrace_append hprefix tailTrace_3161397
  have hstable : (prefixWord ++ tailWord_3161397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161397).length < 2 ^ (prefixWord ++ tailWord_3161397).sum := by decide
  have hdescent : baseEnd_3161397 < baseStart_3161397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161427 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_3161427 : Nat := 118140960795 + 3161427 * 2 ^ 59
def prefixEnd_3161427 : Nat := 4983230072969 + 3 ^ 40 * 3161427 * 2
def baseEnd_3161427 : Nat := 1082221070067805090682245

theorem tailTrace_3161427 : CollatzResearch.WordTrace tailWord_3161427 prefixEnd_3161427 1082221070067805090682245 := by
  unfold tailWord_3161427
  simp only [CollatzResearch.WordTrace]
  refine ⟨115306715517697382590786535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76871143678464921727191023 115306715517697382590786535)
  ·
    refine ⟨172960073276546073886179803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115306715517697382590786535 172960073276546073886179803)
    ·
      refine ⟨259440109914819110829269705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172960073276546073886179803 259440109914819110829269705)
      ·
        refine ⟨194580082436114333121952279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259440109914819110829269705 194580082436114333121952279)
        ·
          refine ⟨291870123654171499682928419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194580082436114333121952279 291870123654171499682928419)
          ·
            refine ⟨437805185481257249524392629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291870123654171499682928419 437805185481257249524392629)
            ·
              refine ⟨41044236138867867142911809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437805185481257249524392629 41044236138867867142911809)
              ·
                refine ⟨30783177104150900357183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41044236138867867142911809 30783177104150900357183857)
                ·
                  refine ⟨23087382828113175267887893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30783177104150900357183857 23087382828113175267887893)
                  ·
                    refine ⟨1082221070067805090682245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23087382828113175267887893 1082221070067805090682245)
                    ·
                      rfl

theorem cell22_3161427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_3161427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161427 prefixEnd_3161427 := by exact prefixLift 3161427
  have htrace : WordTrace (prefixWord ++ tailWord_3161427) baseStart_3161427 baseEnd_3161427 := by
    simpa [prefixWord, tailWord_3161427, baseEnd_3161427] using wordTrace_append hprefix tailTrace_3161427
  have hstable : (prefixWord ++ tailWord_3161427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161427).length < 2 ^ (prefixWord ++ tailWord_3161427).sum := by decide
  have hdescent : baseEnd_3161427 < baseStart_3161427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161437 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 4]
def baseStart_3161437 : Nat := 118140960795 + 3161437 * 2 ^ 59
def prefixEnd_3161437 : Nat := 4983230072969 + 3 ^ 40 * 3161437 * 2
def baseEnd_3161437 : Nat := 360741497757389465977405

theorem tailTrace_3161437 : CollatzResearch.WordTrace tailWord_3161437 prefixEnd_3161437 360741497757389465977405 := by
  unfold tailWord_3161437
  simp only [CollatzResearch.WordTrace]
  refine ⟨115307080247661154298650565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76871386831774102865767043 115307080247661154298650565)
  ·
    refine ⟨21620077546436466430996981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115307080247661154298650565 21620077546436466430996981)
    ·
      refine ⟨2026882269978418727905967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21620077546436466430996981 2026882269978418727905967)
      ·
        refine ⟨3040323404967628091858951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026882269978418727905967 3040323404967628091858951)
        ·
          refine ⟨4560485107451442137788427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040323404967628091858951 4560485107451442137788427)
          ·
            refine ⟨6840727661177163206682641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560485107451442137788427 6840727661177163206682641)
            ·
              refine ⟨5130545745882872405011981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840727661177163206682641 5130545745882872405011981)
              ·
                refine ⟨1923954654706077151879493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5130545745882872405011981 1923954654706077151879493)
                ·
                  refine ⟨360741497757389465977405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923954654706077151879493 360741497757389465977405)
                  ·
                    rfl

theorem cell22_3161437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_3161437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161437 prefixEnd_3161437 := by exact prefixLift 3161437
  have htrace : WordTrace (prefixWord ++ tailWord_3161437) baseStart_3161437 baseEnd_3161437 := by
    simpa [prefixWord, tailWord_3161437, baseEnd_3161437] using wordTrace_append hprefix tailTrace_3161437
  have hstable : (prefixWord ++ tailWord_3161437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161437).length < 2 ^ (prefixWord ++ tailWord_3161437).sum := by decide
  have hdescent : baseEnd_3161437 < baseStart_3161437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161540 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3161540 : Nat := 118140960795 + 3161540 * 2 ^ 59
def prefixEnd_3161540 : Nat := 4983230072969 + 3 ^ 40 * 3161540 * 2
def baseEnd_3161540 : Nat := 1082259752277110462606899

theorem tailTrace_3161540 : CollatzResearch.WordTrace tailWord_3161540 prefixEnd_3161540 1082259752277110462606899 := by
  unfold tailWord_3161540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57655418483144001444825037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76873891310858668593100049 57655418483144001444825037)
  ·
    refine ⟨21620781931179000541809389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57655418483144001444825037 21620781931179000541809389)
    ·
      refine ⟨8107793224192125203178521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21620781931179000541809389 8107793224192125203178521)
      ·
        refine ⟨6080844918144093902383891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8107793224192125203178521 6080844918144093902383891)
        ·
          refine ⟨9121267377216140853575837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080844918144093902383891 9121267377216140853575837)
          ·
            refine ⟨3420475266456052820090939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9121267377216140853575837 3420475266456052820090939)
            ·
              refine ⟨5130712899684079230136409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420475266456052820090939 5130712899684079230136409)
              ·
                refine ⟨3848034674763059422602307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130712899684079230136409 3848034674763059422602307)
                ·
                  refine ⟨5772052012144589133903461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848034674763059422602307 5772052012144589133903461)
                  ·
                    refine ⟨1082259752277110462606899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772052012144589133903461 1082259752277110462606899)
                    ·
                      rfl

theorem cell22_3161540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3161540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161540 prefixEnd_3161540 := by exact prefixLift 3161540
  have htrace : WordTrace (prefixWord ++ tailWord_3161540) baseStart_3161540 baseEnd_3161540 := by
    simpa [prefixWord, tailWord_3161540, baseEnd_3161540] using wordTrace_append hprefix tailTrace_3161540
  have hstable : (prefixWord ++ tailWord_3161540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161540).length < 2 ^ (prefixWord ++ tailWord_3161540).sum := by decide
  have hdescent : baseEnd_3161540 < baseStart_3161540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161609 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3161609 : Nat := 118140960795 + 3161609 * 2 ^ 59
def prefixEnd_3161609 : Nat := 4983230072969 + 3 ^ 40 * 3161609 * 2
def baseEnd_3161609 : Nat := 1082283372387217282631687

theorem tailTrace_3161609 : CollatzResearch.WordTrace tailWord_3161609 prefixEnd_3161609 1082283372387217282631687 := by
  unfold tailWord_3161609
  simp only [CollatzResearch.WordTrace]
  refine ⟨115313353603038027673911881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76875569068692018449274587 115313353603038027673911881)
  ·
    refine ⟨86485015202278520755433911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115313353603038027673911881 86485015202278520755433911)
    ·
      refine ⟨129727522803417781133150867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86485015202278520755433911 129727522803417781133150867)
      ·
        refine ⟨194591284205126671699726301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129727522803417781133150867 194591284205126671699726301)
        ·
          refine ⟨72971731576922501887397363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194591284205126671699726301 72971731576922501887397363)
          ·
            refine ⟨109457597365383752831096045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72971731576922501887397363 109457597365383752831096045)
            ·
              refine ⟨41046599012018907311661017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109457597365383752831096045 41046599012018907311661017)
              ·
                refine ⟨30784949259014180483745763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41046599012018907311661017 30784949259014180483745763)
                ·
                  refine ⟨46177423888521270725618645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30784949259014180483745763 46177423888521270725618645)
                  ·
                    refine ⟨1082283372387217282631687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46177423888521270725618645 1082283372387217282631687)
                    ·
                      rfl

theorem cell22_3161609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3161609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161609 prefixEnd_3161609 := by exact prefixLift 3161609
  have htrace : WordTrace (prefixWord ++ tailWord_3161609) baseStart_3161609 baseEnd_3161609 := by
    simpa [prefixWord, tailWord_3161609, baseEnd_3161609] using wordTrace_append hprefix tailTrace_3161609
  have hstable : (prefixWord ++ tailWord_3161609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161609).length < 2 ^ (prefixWord ++ tailWord_3161609).sum := by decide
  have hdescent : baseEnd_3161609 < baseStart_3161609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161656 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_3161656 : Nat := 118140960795 + 3161656 * 2 ^ 59
def prefixEnd_3161656 : Nat := 4983230072969 + 3 ^ 40 * 3161656 * 2
def baseEnd_3161656 : Nat := 360766487149241608902181

theorem tailTrace_3161656 : CollatzResearch.WordTrace tailWord_3161656 prefixEnd_3161656 360766487149241608902181 := by
  unfold tailWord_3161656
  simp only [CollatzResearch.WordTrace]
  refine ⟨57657533916933877350436411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76876711889245169800581881 57657533916933877350436411)
  ·
    refine ⟨86486300875400816025654617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57657533916933877350436411 86486300875400816025654617)
    ·
      refine ⟨64864725656550612019240963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86486300875400816025654617 64864725656550612019240963)
      ·
        refine ⟨97297088484825918028861445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64864725656550612019240963 97297088484825918028861445)
        ·
          refine ⟨18243204090904859630411521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97297088484825918028861445 18243204090904859630411521)
          ·
            refine ⟨13682403068178644722808641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18243204090904859630411521 13682403068178644722808641)
            ·
              refine ⟨10261802301133983542106481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13682403068178644722808641 10261802301133983542106481)
              ·
                refine ⟨7696351725850487656579861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10261802301133983542106481 7696351725850487656579861)
                ·
                  refine ⟨360766487149241608902181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7696351725850487656579861 360766487149241608902181)
                  ·
                    rfl

theorem cell22_3161656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_3161656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161656 prefixEnd_3161656 := by exact prefixLift 3161656
  have htrace : WordTrace (prefixWord ++ tailWord_3161656) baseStart_3161656 baseEnd_3161656 := by
    simpa [prefixWord, tailWord_3161656, baseEnd_3161656] using wordTrace_append hprefix tailTrace_3161656
  have hstable : (prefixWord ++ tailWord_3161656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161656).length < 2 ^ (prefixWord ++ tailWord_3161656).sum := by decide
  have hdescent : baseEnd_3161656 < baseStart_3161656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161658 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_3161658 : Nat := 118140960795 + 3161658 * 2 ^ 59
def prefixEnd_3161658 : Nat := 4983230072969 + 3 ^ 40 * 3161658 * 2
def baseEnd_3161658 : Nat := 1082300146088597488156537

theorem tailTrace_3161658 : CollatzResearch.WordTrace tailWord_3161658 prefixEnd_3161658 1082300146088597488156537 := by
  unfold tailWord_3161658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828785194965127260611407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76876760519907006028297085 28828785194965127260611407)
  ·
    refine ⟨43243177792447690890917111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28828785194965127260611407 43243177792447690890917111)
    ·
      refine ⟨64864766688671536336375667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43243177792447690890917111 64864766688671536336375667)
      ·
        refine ⟨97297150033007304504563501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64864766688671536336375667 97297150033007304504563501)
        ·
          refine ⟨36486431262377739189211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97297150033007304504563501 36486431262377739189211313)
          ·
            refine ⟨27364823446783304391908485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36486431262377739189211313 27364823446783304391908485)
            ·
              refine ⟨5130904396271869573482841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27364823446783304391908485 5130904396271869573482841)
              ·
                refine ⟨3848178297203902180112131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130904396271869573482841 3848178297203902180112131)
                ·
                  refine ⟨5772267445805853270168197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848178297203902180112131 5772267445805853270168197)
                  ·
                    refine ⟨1082300146088597488156537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772267445805853270168197 1082300146088597488156537)
                    ·
                      rfl

theorem cell22_3161658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_3161658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161658 prefixEnd_3161658 := by exact prefixLift 3161658
  have htrace : WordTrace (prefixWord ++ tailWord_3161658) baseStart_3161658 baseEnd_3161658 := by
    simpa [prefixWord, tailWord_3161658, baseEnd_3161658] using wordTrace_append hprefix tailTrace_3161658
  have hstable : (prefixWord ++ tailWord_3161658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161658).length < 2 ^ (prefixWord ++ tailWord_3161658).sum := by decide
  have hdescent : baseEnd_3161658 < baseStart_3161658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161688 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_3161688 : Nat := 118140960795 + 3161688 * 2 ^ 59
def prefixEnd_3161688 : Nat := 4983230072969 + 3 ^ 40 * 3161688 * 2
def baseEnd_3161688 : Nat := 1082310415701687409906445

theorem tailTrace_3161688 : CollatzResearch.WordTrace tailWord_3161688 prefixEnd_3161688 1082310415701687409906445 := by
  unfold tailWord_3161688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57658117484875912083018859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76877489979834549444025145 57658117484875912083018859)
  ·
    refine ⟨86487176227313868124528289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57658117484875912083018859 86487176227313868124528289)
    ·
      refine ⟨64865382170485401093396217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86487176227313868124528289 64865382170485401093396217)
      ·
        refine ⟨48649036627864050820047163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64865382170485401093396217 48649036627864050820047163)
        ·
          refine ⟨72973554941796076230070745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48649036627864050820047163 72973554941796076230070745)
          ·
            refine ⟨54730166206347057172553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72973554941796076230070745 54730166206347057172553059)
            ·
              refine ⟨82095249309520585758829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54730166206347057172553059 82095249309520585758829589)
              ·
                refine ⟨3848214811383777457445137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82095249309520585758829589 3848214811383777457445137)
                ·
                  refine ⟨2886161108537833093083853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848214811383777457445137 2886161108537833093083853)
                  ·
                    refine ⟨1082310415701687409906445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886161108537833093083853 1082310415701687409906445)
                    ·
                      rfl

theorem cell22_3161688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_3161688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161688 prefixEnd_3161688 := by exact prefixLift 3161688
  have htrace : WordTrace (prefixWord ++ tailWord_3161688) baseStart_3161688 baseEnd_3161688 := by
    simpa [prefixWord, tailWord_3161688, baseEnd_3161688] using wordTrace_append hprefix tailTrace_3161688
  have hstable : (prefixWord ++ tailWord_3161688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161688).length < 2 ^ (prefixWord ++ tailWord_3161688).sum := by decide
  have hdescent : baseEnd_3161688 < baseStart_3161688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161701 : List Nat := [1, 3, 1, 3, 3, 1, 1, 9]
def baseStart_3161701 : Nat := 118140960795 + 3161701 * 2 ^ 59
def prefixEnd_3161701 : Nat := 4983230072969 + 3 ^ 40 * 3161701 * 2
def baseEnd_3161701 : Nat := 120257207318595523259045

theorem tailTrace_3161701 : CollatzResearch.WordTrace tailWord_3161701 prefixEnd_3161701 120257207318595523259045 := by
  unfold tailWord_3161701
  simp only [CollatzResearch.WordTrace]
  refine ⟨115316709118704727386260957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76877806079136484924173971 115316709118704727386260957)
  ·
    refine ⟨43243765919514272769847859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115316709118704727386260957 43243765919514272769847859)
    ·
      refine ⟨64865648879271409154771789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43243765919514272769847859 64865648879271409154771789)
      ·
        refine ⟨24324618329726778433039421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64865648879271409154771789 24324618329726778433039421)
        ·
          refine ⟨9121731873647541912389783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24324618329726778433039421 9121731873647541912389783)
          ·
            refine ⟨13682597810471312868584675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121731873647541912389783 13682597810471312868584675)
            ·
              refine ⟨20523896715706969302877013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13682597810471312868584675 20523896715706969302877013)
              ·
                refine ⟨120257207318595523259045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20523896715706969302877013 120257207318595523259045)
                ·
                  rfl

theorem cell22_3161701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 9].length) (baseStart_3161701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161701 prefixEnd_3161701 := by exact prefixLift 3161701
  have htrace : WordTrace (prefixWord ++ tailWord_3161701) baseStart_3161701 baseEnd_3161701 := by
    simpa [prefixWord, tailWord_3161701, baseEnd_3161701] using wordTrace_append hprefix tailTrace_3161701
  have hstable : (prefixWord ++ tailWord_3161701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161701).length < 2 ^ (prefixWord ++ tailWord_3161701).sum := by decide
  have hdescent : baseEnd_3161701 < baseStart_3161701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161705 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_3161705 : Nat := 118140960795 + 3161705 * 2 ^ 59
def prefixEnd_3161705 : Nat := 4983230072969 + 3 ^ 40 * 3161705 * 2
def baseEnd_3161705 : Nat := 1082316235149105032231393

theorem tailTrace_3161705 : CollatzResearch.WordTrace tailWord_3161705 prefixEnd_3161705 1082316235149105032231393 := by
  unfold tailWord_3161705
  simp only [CollatzResearch.WordTrace]
  refine ⟨115316855010690236069406569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76877903340460157379604379 115316855010690236069406569)
  ·
    refine ⟨86487641258017677052054927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115316855010690236069406569 86487641258017677052054927)
    ·
      refine ⟨129731461887026515578082391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86487641258017677052054927 129731461887026515578082391)
      ·
        refine ⟨194597192830539773367123587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129731461887026515578082391 194597192830539773367123587)
        ·
          refine ⟨291895789245809660050685381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194597192830539773367123587 291895789245809660050685381)
          ·
            refine ⟨54730460483589311259503509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291895789245809660050685381 54730460483589311259503509)
            ·
              refine ⟨2565490335168248965289227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54730460483589311259503509 2565490335168248965289227)
              ·
                refine ⟨3848235502752373447933841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565490335168248965289227 3848235502752373447933841)
                ·
                  refine ⟨2886176627064280085950381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848235502752373447933841 2886176627064280085950381)
                  ·
                    refine ⟨1082316235149105032231393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886176627064280085950381 1082316235149105032231393)
                    ·
                      rfl

theorem cell22_3161705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_3161705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161705 prefixEnd_3161705 := by exact prefixLift 3161705
  have htrace : WordTrace (prefixWord ++ tailWord_3161705) baseStart_3161705 baseEnd_3161705 := by
    simpa [prefixWord, tailWord_3161705, baseEnd_3161705] using wordTrace_append hprefix tailTrace_3161705
  have hstable : (prefixWord ++ tailWord_3161705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161705).length < 2 ^ (prefixWord ++ tailWord_3161705).sum := by decide
  have hdescent : baseEnd_3161705 < baseStart_3161705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161718 : List Nat := [5, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3161718 : Nat := 118140960795 + 3161718 * 2 ^ 59
def prefixEnd_3161718 : Nat := 4983230072969 + 3 ^ 40 * 3161718 * 2
def baseEnd_3161718 : Nat := 120257853923864147961817

theorem tailTrace_3161718 : CollatzResearch.WordTrace tailWord_3161718 prefixEnd_3161718 120257853923864147961817 := by
  unfold tailWord_3161718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207333072477696205601863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76878219439762092859753205 7207333072477696205601863)
  ·
    refine ⟨10810999608716544308402795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207333072477696205601863 10810999608716544308402795)
    ·
      refine ⟨16216499413074816462604193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810999608716544308402795 16216499413074816462604193)
      ·
        refine ⟨12162374559806112346953145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16216499413074816462604193 12162374559806112346953145)
        ·
          refine ⟨9121780919854584260214859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12162374559806112346953145 9121780919854584260214859)
          ·
            refine ⟨13682671379781876390322289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121780919854584260214859 13682671379781876390322289)
            ·
              refine ⟨10262003534836407292741717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13682671379781876390322289 10262003534836407292741717)
              ·
                refine ⟨120257853923864147961817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10262003534836407292741717 120257853923864147961817)
                ·
                  rfl

theorem cell22_3161718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3161718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161718 prefixEnd_3161718 := by exact prefixLift 3161718
  have htrace : WordTrace (prefixWord ++ tailWord_3161718) baseStart_3161718 baseEnd_3161718 := by
    simpa [prefixWord, tailWord_3161718, baseEnd_3161718] using wordTrace_append hprefix tailTrace_3161718
  have hstable : (prefixWord ++ tailWord_3161718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161718).length < 2 ^ (prefixWord ++ tailWord_3161718).sum := by decide
  have hdescent : baseEnd_3161718 < baseStart_3161718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161791 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 8]
def baseStart_3161791 : Nat := 118140960795 + 3161791 * 2 ^ 59
def prefixEnd_3161791 : Nat := 4983230072969 + 3 ^ 40 * 3161791 * 2
def baseEnd_3161791 : Nat := 360781891568876491527043

theorem tailTrace_3161791 : CollatzResearch.WordTrace tailWord_3161791 prefixEnd_3161791 360781891568876491527043 := by
  unfold tailWord_3161791
  simp only [CollatzResearch.WordTrace]
  refine ⟨115319991688378672757037227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76879994458919115171358151 115319991688378672757037227)
  ·
    refine ⟨172979987532568009135555841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115319991688378672757037227 172979987532568009135555841)
    ·
      refine ⟨129734990649426006851666881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172979987532568009135555841 129734990649426006851666881)
      ·
        refine ⟨97301242987069505138750161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129734990649426006851666881 97301242987069505138750161)
        ·
          refine ⟨72975932240302128854062621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97301242987069505138750161 72975932240302128854062621)
          ·
            refine ⟨27365974590113298320273483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72975932240302128854062621 27365974590113298320273483)
            ·
              refine ⟨41048961885169947480410225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27365974590113298320273483 41048961885169947480410225)
              ·
                refine ⟨30786721413877460610307669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41048961885169947480410225 30786721413877460610307669)
                ·
                  refine ⟨360781891568876491527043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30786721413877460610307669 360781891568876491527043)
                  ·
                    rfl

theorem cell22_3161791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_3161791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161791 prefixEnd_3161791 := by exact prefixLift 3161791
  have htrace : WordTrace (prefixWord ++ tailWord_3161791) baseStart_3161791 baseEnd_3161791 := by
    simpa [prefixWord, tailWord_3161791, baseEnd_3161791] using wordTrace_append hprefix tailTrace_3161791
  have hstable : (prefixWord ++ tailWord_3161791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161791).length < 2 ^ (prefixWord ++ tailWord_3161791).sum := by decide
  have hdescent : baseEnd_3161791 < baseStart_3161791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161827 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 1, 4]
def baseStart_3161827 : Nat := 118140960795 + 3161827 * 2 ^ 59
def prefixEnd_3161827 : Nat := 4983230072969 + 3 ^ 40 * 3161827 * 2
def baseEnd_3161827 : Nat := 1082357998242337380681019

theorem tailTrace_3161827 : CollatzResearch.WordTrace tailWord_3161827 prefixEnd_3161827 1082357998242337380681019 := by
  unfold tailWord_3161827
  simp only [CollatzResearch.WordTrace]
  refine ⟨115321304716248250905347735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76880869810832167270231823 115321304716248250905347735)
  ·
    refine ⟨172981957074372376358021603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115321304716248250905347735 172981957074372376358021603)
    ·
      refine ⟨259472935611558564537032405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172981957074372376358021603 259472935611558564537032405)
      ·
        refine ⟨6081396928395903856336697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 259472935611558564537032405 6081396928395903856336697)
        ·
          refine ⟨4561047696296927892252523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081396928395903856336697 4561047696296927892252523)
          ·
            refine ⟨6841571544445391838378785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561047696296927892252523 6841571544445391838378785)
            ·
              refine ⟨5131178658334043878784089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841571544445391838378785 5131178658334043878784089)
              ·
                refine ⟨3848383993750532909088067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5131178658334043878784089 3848383993750532909088067)
                ·
                  refine ⟨5772575990625799363632101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848383993750532909088067 5772575990625799363632101)
                  ·
                    refine ⟨1082357998242337380681019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772575990625799363632101 1082357998242337380681019)
                    ·
                      rfl

theorem cell22_3161827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_3161827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161827 prefixEnd_3161827 := by exact prefixLift 3161827
  have htrace : WordTrace (prefixWord ++ tailWord_3161827) baseStart_3161827 baseEnd_3161827 := by
    simpa [prefixWord, tailWord_3161827, baseEnd_3161827] using wordTrace_append hprefix tailTrace_3161827
  have hstable : (prefixWord ++ tailWord_3161827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161827).length < 2 ^ (prefixWord ++ tailWord_3161827).sum := by decide
  have hdescent : baseEnd_3161827 < baseStart_3161827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161838 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3161838 : Nat := 118140960795 + 3161838 * 2 ^ 59
def prefixEnd_3161838 : Nat := 4983230072969 + 3 ^ 40 * 3161838 * 2
def baseEnd_3161838 : Nat := 1082361763767137018655985

theorem tailTrace_3161838 : CollatzResearch.WordTrace tailWord_3161838 prefixEnd_3161838 1082361763767137018655985 := by
  unfold tailWord_3161838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415213239901049972999771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76881137279472266522665445 14415213239901049972999771)
  ·
    refine ⟨21622819859851574959499657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14415213239901049972999771 21622819859851574959499657)
    ·
      refine ⟨16217114894888681219624743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21622819859851574959499657 16217114894888681219624743)
      ·
        refine ⟨24325672342333021829437115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217114894888681219624743 24325672342333021829437115)
        ·
          refine ⟨36488508513499532744155673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24325672342333021829437115 36488508513499532744155673)
          ·
            refine ⟨27366381385124649558116755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36488508513499532744155673 27366381385124649558116755)
            ·
              refine ⟨41049572077686974337175133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27366381385124649558116755 41049572077686974337175133)
              ·
                refine ⟨15393589529132615376440675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41049572077686974337175133 15393589529132615376440675)
                ·
                  refine ⟨23090384293698923064661013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15393589529132615376440675 23090384293698923064661013)
                  ·
                    refine ⟨1082361763767137018655985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23090384293698923064661013 1082361763767137018655985)
                    ·
                      rfl

theorem cell22_3161838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3161838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161838 prefixEnd_3161838 := by exact prefixLift 3161838
  have htrace : WordTrace (prefixWord ++ tailWord_3161838) baseStart_3161838 baseEnd_3161838 := by
    simpa [prefixWord, tailWord_3161838, baseEnd_3161838] using wordTrace_append hprefix tailTrace_3161838
  have hstable : (prefixWord ++ tailWord_3161838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161838).length < 2 ^ (prefixWord ++ tailWord_3161838).sum := by decide
  have hdescent : baseEnd_3161838 < baseStart_3161838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161844 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3161844 : Nat := 118140960795 + 3161844 * 2 ^ 59
def prefixEnd_3161844 : Nat := 4983230072969 + 3 ^ 40 * 3161844 * 2
def baseEnd_3161844 : Nat := 1082363817689755003005967

theorem tailTrace_3161844 : CollatzResearch.WordTrace tailWord_3161844 prefixEnd_3161844 1082363817689755003005967 := by
  unfold tailWord_3161844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57660962378593331404358293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76881283171457775205811057 57660962378593331404358293)
  ·
    refine ⟨2702857611496562409579295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57660962378593331404358293 2702857611496562409579295)
    ·
      refine ⟨4054286417244843614368943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702857611496562409579295 4054286417244843614368943)
      ·
        refine ⟨6081429625867265421553415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054286417244843614368943 6081429625867265421553415)
        ·
          refine ⟨9122144438800898132330123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081429625867265421553415 9122144438800898132330123)
          ·
            refine ⟨13683216658201347198495185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122144438800898132330123 13683216658201347198495185)
            ·
              refine ⟨10262412493651010398871389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13683216658201347198495185 10262412493651010398871389)
              ·
                refine ⟨3848404685119128899576771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10262412493651010398871389 3848404685119128899576771)
                ·
                  refine ⟨5772607027678693349365157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848404685119128899576771 5772607027678693349365157)
                  ·
                    refine ⟨1082363817689755003005967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772607027678693349365157 1082363817689755003005967)
                    ·
                      rfl

theorem cell22_3161844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3161844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161844 prefixEnd_3161844 := by exact prefixLift 3161844
  have htrace : WordTrace (prefixWord ++ tailWord_3161844) baseStart_3161844 baseEnd_3161844 := by
    simpa [prefixWord, tailWord_3161844, baseEnd_3161844] using wordTrace_append hprefix tailTrace_3161844
  have hstable : (prefixWord ++ tailWord_3161844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161844).length < 2 ^ (prefixWord ++ tailWord_3161844).sum := by decide
  have hdescent : baseEnd_3161844 < baseStart_3161844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161874 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3161874 : Nat := 118140960795 + 3161874 * 2 ^ 59
def prefixEnd_3161874 : Nat := 4983230072969 + 3 ^ 40 * 3161874 * 2
def baseEnd_3161874 : Nat := 1082374087302844924755875

theorem tailTrace_3161874 : CollatzResearch.WordTrace tailWord_3161874 prefixEnd_3161874 1082374087302844924755875 := by
  unfold tailWord_3161874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28830754736769494483077169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76882012631385318621539117 28830754736769494483077169)
  ·
    refine ⟨21623066052577120862307877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28830754736769494483077169 21623066052577120862307877)
    ·
      refine ⟨4054324884858210161682727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21623066052577120862307877 4054324884858210161682727)
      ·
        refine ⟨6081487327287315242524091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054324884858210161682727 6081487327287315242524091)
        ·
          refine ⟨9122230990930972863786137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081487327287315242524091 9122230990930972863786137)
          ·
            refine ⟨6841673243198229647839603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122230990930972863786137 6841673243198229647839603)
            ·
              refine ⟨10262509864797344471759405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841673243198229647839603 10262509864797344471759405)
              ·
                refine ⟨3848441199299004176909777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10262509864797344471759405 3848441199299004176909777)
                ·
                  refine ⟨2886330899474253132682333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848441199299004176909777 2886330899474253132682333)
                  ·
                    refine ⟨1082374087302844924755875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886330899474253132682333 1082374087302844924755875)
                    ·
                      rfl

theorem cell22_3161874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3161874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161874 prefixEnd_3161874 := by exact prefixLift 3161874
  have htrace : WordTrace (prefixWord ++ tailWord_3161874) baseStart_3161874 baseEnd_3161874 := by
    simpa [prefixWord, tailWord_3161874, baseEnd_3161874] using wordTrace_append hprefix tailTrace_3161874
  have hstable : (prefixWord ++ tailWord_3161874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161874).length < 2 ^ (prefixWord ++ tailWord_3161874).sum := by decide
  have hdescent : baseEnd_3161874 < baseStart_3161874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161919 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 1, 3]
def baseStart_3161919 : Nat := 118140960795 + 3161919 * 2 ^ 59
def prefixEnd_3161919 : Nat := 4983230072969 + 3 ^ 40 * 3161919 * 2
def baseEnd_3161919 : Nat := 1082389491722479807380737

theorem tailTrace_3161919 : CollatzResearch.WordTrace tailWord_3161919 prefixEnd_3161919 1082389491722479807380737 := by
  unfold tailWord_3161919
  simp only [CollatzResearch.WordTrace]
  refine ⟨115324660231914950617696811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76883106821276633745131207 115324660231914950617696811)
  ·
    refine ⟨172986990347872425926545217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115324660231914950617696811 172986990347872425926545217)
    ·
      refine ⟨129740242760904319444908913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172986990347872425926545217 129740242760904319444908913)
      ·
        refine ⟨97305182070678239583681685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129740242760904319444908913 97305182070678239583681685)
        ·
          refine ⟨4561180409563042480485079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97305182070678239583681685 4561180409563042480485079)
          ·
            refine ⟨6841770614344563720727619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561180409563042480485079 6841770614344563720727619)
            ·
              refine ⟨10262655921516845581091429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841770614344563720727619 10262655921516845581091429)
              ·
                refine ⟨1924247985284408546454643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10262655921516845581091429 1924247985284408546454643)
                ·
                  refine ⟨2886371977926612819681965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924247985284408546454643 2886371977926612819681965)
                  ·
                    refine ⟨1082389491722479807380737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886371977926612819681965 1082389491722479807380737)
                    ·
                      rfl

theorem cell22_3161919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_3161919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161919 prefixEnd_3161919 := by exact prefixLift 3161919
  have htrace : WordTrace (prefixWord ++ tailWord_3161919) baseStart_3161919 baseEnd_3161919 := by
    simpa [prefixWord, tailWord_3161919, baseEnd_3161919] using wordTrace_append hprefix tailTrace_3161919
  have hstable : (prefixWord ++ tailWord_3161919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161919).length < 2 ^ (prefixWord ++ tailWord_3161919).sum := by decide
  have hdescent : baseEnd_3161919 < baseStart_3161919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161945 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_3161945 : Nat := 118140960795 + 3161945 * 2 ^ 59
def prefixEnd_3161945 : Nat := 4983230072969 + 3 ^ 40 * 3161945 * 2
def baseEnd_3161945 : Nat := 1082398392053824406230657

theorem tailTrace_3161945 : CollatzResearch.WordTrace tailWord_3161945 prefixEnd_3161945 1082398392053824406230657 := by
  unfold tailWord_3161945
  simp only [CollatzResearch.WordTrace]
  refine ⟨115325608529820757058143289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76883739019880504705428859 115325608529820757058143289)
  ·
    refine ⟨86494206397365567793607467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115325608529820757058143289 86494206397365567793607467)
    ·
      refine ⟨129741309596048351690411201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86494206397365567793607467 129741309596048351690411201)
      ·
        refine ⟨97305982197036263767808401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129741309596048351690411201 97305982197036263767808401)
        ·
          refine ⟨72979486647777197825856301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97305982197036263767808401 72979486647777197825856301)
          ·
            refine ⟨27367307492916449184696113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72979486647777197825856301 27367307492916449184696113)
            ·
              refine ⟨20525480619687336888522085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27367307492916449184696113 20525480619687336888522085)
              ·
                refine ⟨3848527616191375666597891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20525480619687336888522085 3848527616191375666597891)
                ·
                  refine ⟨5772791424287063499896837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848527616191375666597891 5772791424287063499896837)
                  ·
                    refine ⟨1082398392053824406230657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772791424287063499896837 1082398392053824406230657)
                    ·
                      rfl

theorem cell22_3161945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_3161945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3161945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3161945 prefixEnd_3161945 := by exact prefixLift 3161945
  have htrace : WordTrace (prefixWord ++ tailWord_3161945) baseStart_3161945 baseEnd_3161945 := by
    simpa [prefixWord, tailWord_3161945, baseEnd_3161945] using wordTrace_append hprefix tailTrace_3161945
  have hstable : (prefixWord ++ tailWord_3161945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161945).length < 2 ^ (prefixWord ++ tailWord_3161945).sum := by decide
  have hdescent : baseEnd_3161945 < baseStart_3161945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162095 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 6]
def baseStart_3162095 : Nat := 118140960795 + 3162095 * 2 ^ 59
def prefixEnd_3162095 : Nat := 4983230072969 + 3 ^ 40 * 3162095 * 2
def baseEnd_3162095 : Nat := 360816580039758004993399

theorem tailTrace_3162095 : CollatzResearch.WordTrace tailWord_3162095 prefixEnd_3162095 360816580039758004993399 := by
  unfold tailWord_3162095
  simp only [CollatzResearch.WordTrace]
  refine ⟨115331079479277332676103739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76887386319518221784069159 115331079479277332676103739)
  ·
    refine ⟨172996619218915999014155609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115331079479277332676103739 172996619218915999014155609)
    ·
      refine ⟨129747464414186999260616707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172996619218915999014155609 129747464414186999260616707)
      ·
        refine ⟨194621196621280498890925061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129747464414186999260616707 194621196621280498890925061)
        ·
          refine ⟨36491474366490093542048449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194621196621280498890925061 36491474366490093542048449)
          ·
            refine ⟨27368605774867570156536337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36491474366490093542048449 27368605774867570156536337)
            ·
              refine ⟨20526454331150677617402253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27368605774867570156536337 20526454331150677617402253)
              ·
                refine ⟨7697420374181504106525845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20526454331150677617402253 7697420374181504106525845)
                ·
                  refine ⟨360816580039758004993399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7697420374181504106525845 360816580039758004993399)
                  ·
                    rfl

theorem cell22_3162095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_3162095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162095 prefixEnd_3162095 := by exact prefixLift 3162095
  have htrace : WordTrace (prefixWord ++ tailWord_3162095) baseStart_3162095 baseEnd_3162095 := by
    simpa [prefixWord, tailWord_3162095, baseEnd_3162095] using wordTrace_append hprefix tailTrace_3162095
  have hstable : (prefixWord ++ tailWord_3162095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162095).length < 2 ^ (prefixWord ++ tailWord_3162095).sum := by decide
  have hdescent : baseEnd_3162095 < baseStart_3162095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162161 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_3162161 : Nat := 118140960795 + 3162161 * 2 ^ 59
def prefixEnd_3162161 : Nat := 4983230072969 + 3 ^ 40 * 3162161 * 2
def baseEnd_3162161 : Nat := 1082472333268071842829995

theorem tailTrace_3162161 : CollatzResearch.WordTrace tailWord_3162161 prefixEnd_3162161 1082472333268071842829995 := by
  unfold tailWord_3162161
  simp only [CollatzResearch.WordTrace]
  refine ⟨115333486697038225948006337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76888991131358817298670891 115333486697038225948006337)
  ·
    refine ⟨86500115022778669461004753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115333486697038225948006337 86500115022778669461004753)
    ·
      refine ⟨64875086267084002095753565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86500115022778669461004753 64875086267084002095753565)
      ·
        refine ⟨24328157350156500785907587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64875086267084002095753565 24328157350156500785907587)
        ·
          refine ⟨36492236025234751178861381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24328157350156500785907587 36492236025234751178861381)
          ·
            refine ⟨6842294254731515846036509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36492236025234751178861381 6842294254731515846036509)
            ·
              refine ⟨2565860345524318442263691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6842294254731515846036509 2565860345524318442263691)
              ·
                refine ⟨3848790518286477663395537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565860345524318442263691 3848790518286477663395537)
                ·
                  refine ⟨2886592888714858247546653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848790518286477663395537 2886592888714858247546653)
                  ·
                    refine ⟨1082472333268071842829995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886592888714858247546653 1082472333268071842829995)
                    ·
                      rfl

theorem cell22_3162161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_3162161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162161 prefixEnd_3162161 := by exact prefixLift 3162161
  have htrace : WordTrace (prefixWord ++ tailWord_3162161) baseStart_3162161 baseEnd_3162161 := by
    simpa [prefixWord, tailWord_3162161, baseEnd_3162161] using wordTrace_append hprefix tailTrace_3162161
  have hstable : (prefixWord ++ tailWord_3162161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162161).length < 2 ^ (prefixWord ++ tailWord_3162161).sum := by decide
  have hdescent : baseEnd_3162161 < baseStart_3162161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162174 : List Nat := [4, 2, 1, 3, 2, 1, 1, 8]
def baseStart_3162174 : Nat := 118140960795 + 3162174 * 2 ^ 59
def prefixEnd_3162174 : Nat := 4983230072969 + 3 ^ 40 * 3162174 * 2
def baseEnd_3162174 : Nat := 120275198159304904694995

theorem tailTrace_3162174 : CollatzResearch.WordTrace tailWord_3162174 prefixEnd_3162174 120275198159304904694995 := by
  unfold tailWord_3162174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416745105748891146028697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76889307230660752778819717 14416745105748891146028697)
  ·
    refine ⟨10812558829311668359521523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14416745105748891146028697 10812558829311668359521523)
    ·
      refine ⟨16218838243967502539282285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10812558829311668359521523 16218838243967502539282285)
      ·
        refine ⟨6082064341487813452230857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16218838243967502539282285 6082064341487813452230857)
        ·
          refine ⟨4561548256115860089173143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6082064341487813452230857 4561548256115860089173143)
          ·
            refine ⟨6842322384173790133759715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561548256115860089173143 6842322384173790133759715)
            ·
              refine ⟨10263483576260685200639573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842322384173790133759715 10263483576260685200639573)
              ·
                refine ⟨120275198159304904694995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10263483576260685200639573 120275198159304904694995)
                ·
                  rfl

theorem cell22_3162174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_3162174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162174 prefixEnd_3162174 := by exact prefixLift 3162174
  have htrace : WordTrace (prefixWord ++ tailWord_3162174) baseStart_3162174 baseEnd_3162174 := by
    simpa [prefixWord, tailWord_3162174, baseEnd_3162174] using wordTrace_append hprefix tailTrace_3162174
  have hstable : (prefixWord ++ tailWord_3162174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162174).length < 2 ^ (prefixWord ++ tailWord_3162174).sum := by decide
  have hdescent : baseEnd_3162174 < baseStart_3162174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162185 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 9]
def baseStart_3162185 : Nat := 118140960795 + 3162185 * 2 ^ 59
def prefixEnd_3162185 : Nat := 4983230072969 + 3 ^ 40 * 3162185 * 2
def baseEnd_3162185 : Nat := 360826849652847926743307

theorem tailTrace_3162185 : CollatzResearch.WordTrace tailWord_3162185 prefixEnd_3162185 360826849652847926743307 := by
  unfold tailWord_3162185
  simp only [CollatzResearch.WordTrace]
  refine ⟨115334362048951278046880009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76889574699300852031253339 115334362048951278046880009)
  ·
    refine ⟨86500771536713458535160007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115334362048951278046880009 86500771536713458535160007)
    ·
      refine ⟨129751157305070187802740011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86500771536713458535160007 129751157305070187802740011)
      ·
        refine ⟨194626735957605281704110017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129751157305070187802740011 194626735957605281704110017)
        ·
          refine ⟨145970051968203961278082513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194626735957605281704110017 145970051968203961278082513)
          ·
            refine ⟨109477538976152970958561885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145970051968203961278082513 109477538976152970958561885)
            ·
              refine ⟨41054077116057364109460707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109477538976152970958561885 41054077116057364109460707)
              ·
                refine ⟨61581115674086046164191061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41054077116057364109460707 61581115674086046164191061)
                ·
                  refine ⟨360826849652847926743307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61581115674086046164191061 360826849652847926743307)
                  ·
                    rfl

theorem cell22_3162185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_3162185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162185 prefixEnd_3162185 := by exact prefixLift 3162185
  have htrace : WordTrace (prefixWord ++ tailWord_3162185) baseStart_3162185 baseEnd_3162185 := by
    simpa [prefixWord, tailWord_3162185, baseEnd_3162185] using wordTrace_append hprefix tailTrace_3162185
  have hstable : (prefixWord ++ tailWord_3162185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162185).length < 2 ^ (prefixWord ++ tailWord_3162185).sum := by decide
  have hdescent : baseEnd_3162185 < baseStart_3162185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162202 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_3162202 : Nat := 118140960795 + 3162202 * 2 ^ 59
def prefixEnd_3162202 : Nat := 4983230072969 + 3 ^ 40 * 3162202 * 2
def baseEnd_3162202 : Nat := 360828789468653800851623

theorem tailTrace_3162202 : CollatzResearch.WordTrace tailWord_3162202 prefixEnd_3162202 360828789468653800851623 := by
  unfold tailWord_3162202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833745522472422487562215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76889988059926459966832573 28833745522472422487562215)
  ·
    refine ⟨43250618283708633731343323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833745522472422487562215 43250618283708633731343323)
    ·
      refine ⟨64875927425562950597014985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43250618283708633731343323 64875927425562950597014985)
      ·
        refine ⟨48656945569172212947761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64875927425562950597014985 48656945569172212947761239)
        ·
          refine ⟨72985418353758319421641859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48656945569172212947761239 72985418353758319421641859)
          ·
            refine ⟨109478127530637479132462789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72985418353758319421641859 109478127530637479132462789)
            ·
              refine ⟨20527148911994527337336773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109478127530637479132462789 20527148911994527337336773)
              ·
                refine ⟨3848840420998973875750645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20527148911994527337336773 3848840420998973875750645)
                ·
                  refine ⟨360828789468653800851623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848840420998973875750645 360828789468653800851623)
                  ·
                    rfl

theorem cell22_3162202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_3162202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162202 prefixEnd_3162202 := by exact prefixLift 3162202
  have htrace : WordTrace (prefixWord ++ tailWord_3162202) baseStart_3162202 baseEnd_3162202 := by
    simpa [prefixWord, tailWord_3162202, baseEnd_3162202] using wordTrace_append hprefix tailTrace_3162202
  have hstable : (prefixWord ++ tailWord_3162202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162202).length < 2 ^ (prefixWord ++ tailWord_3162202).sum := by decide
  have hdescent : baseEnd_3162202 < baseStart_3162202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162277 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3162277 : Nat := 118140960795 + 3162277 * 2 ^ 59
def prefixEnd_3162277 : Nat := 4983230072969 + 3 ^ 40 * 3162277 * 2
def baseEnd_3162277 : Nat := 1082512042438686206929639

theorem tailTrace_3162277 : CollatzResearch.WordTrace tailWord_3162277 prefixEnd_3162277 1082512042438686206929639 := by
  unfold tailWord_3162277
  simp only [CollatzResearch.WordTrace]
  refine ⟨115337717564617977759229085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76891811709745318506152723 115337717564617977759229085)
  ·
    refine ⟨43251644086731741659710907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115337717564617977759229085 43251644086731741659710907)
    ·
      refine ⟨64877466130097612489566361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43251644086731741659710907 64877466130097612489566361)
      ·
        refine ⟨48658099597573209367174771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64877466130097612489566361 48658099597573209367174771)
        ·
          refine ⟨72987149396359814050762157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48658099597573209367174771 72987149396359814050762157)
          ·
            refine ⟨27370181023634930269035809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72987149396359814050762157 27370181023634930269035809)
            ·
              refine ⟨20527635767726197701776857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27370181023634930269035809 20527635767726197701776857)
              ·
                refine ⟨15395726825794648276332643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20527635767726197701776857 15395726825794648276332643)
                ·
                  refine ⟨23093590238691972414498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15395726825794648276332643 23093590238691972414498965)
                  ·
                    refine ⟨1082512042438686206929639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23093590238691972414498965 1082512042438686206929639)
                    ·
                      rfl

theorem cell22_3162277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3162277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162277 prefixEnd_3162277 := by exact prefixLift 3162277
  have htrace : WordTrace (prefixWord ++ tailWord_3162277) baseStart_3162277 baseEnd_3162277 := by
    simpa [prefixWord, tailWord_3162277, baseEnd_3162277] using wordTrace_append hprefix tailTrace_3162277
  have hstable : (prefixWord ++ tailWord_3162277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162277).length < 2 ^ (prefixWord ++ tailWord_3162277).sum := by decide
  have hdescent : baseEnd_3162277 < baseStart_3162277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162300 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_3162300 : Nat := 118140960795 + 3162300 * 2 ^ 59
def prefixEnd_3162300 : Nat := 4983230072969 + 3 ^ 40 * 3162300 * 2
def baseEnd_3162300 : Nat := 1082519915808721813604569

theorem tailTrace_3162300 : CollatzResearch.WordTrace tailWord_3162300 prefixEnd_3162300 1082519915808721813604569 := by
  unfold tailWord_3162300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57669278221767326343658177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76892370962356435124877569 57669278221767326343658177)
  ·
    refine ⟨43251958666325494757743633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57669278221767326343658177 43251958666325494757743633)
    ·
      refine ⟨32438968999744121068307725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43251958666325494757743633 32438968999744121068307725)
      ·
        refine ⟨12164613374904045400615397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32438968999744121068307725 12164613374904045400615397)
        ·
          refine ⟨2280865007794508512615387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12164613374904045400615397 2280865007794508512615387)
          ·
            refine ⟨3421297511691762768923081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280865007794508512615387 3421297511691762768923081)
            ·
              refine ⟨2565973133768822076692311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421297511691762768923081 2565973133768822076692311)
              ·
                refine ⟨3848959700653233115038467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565973133768822076692311 3848959700653233115038467)
                ·
                  refine ⟨5773439550979849672557701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848959700653233115038467 5773439550979849672557701)
                  ·
                    refine ⟨1082519915808721813604569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5773439550979849672557701 1082519915808721813604569)
                    ·
                      rfl

theorem cell22_3162300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_3162300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162300 prefixEnd_3162300 := by exact prefixLift 3162300
  have htrace : WordTrace (prefixWord ++ tailWord_3162300) baseStart_3162300 baseEnd_3162300 := by
    simpa [prefixWord, tailWord_3162300, baseEnd_3162300] using wordTrace_append hprefix tailTrace_3162300
  have hstable : (prefixWord ++ tailWord_3162300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162300).length < 2 ^ (prefixWord ++ tailWord_3162300).sum := by decide
  have hdescent : baseEnd_3162300 < baseStart_3162300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162341 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_3162341 : Nat := 118140960795 + 3162341 * 2 ^ 59
def prefixEnd_3162341 : Nat := 4983230072969 + 3 ^ 40 * 3162341 * 2
def baseEnd_3162341 : Nat := 1082533950946611373329443

theorem tailTrace_3162341 : CollatzResearch.WordTrace tailWord_3162341 prefixEnd_3162341 1082533950946611373329443 := by
  unfold tailWord_3162341
  simp only [CollatzResearch.WordTrace]
  refine ⟨115340051836386116689558877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76893367890924077793039251 115340051836386116689558877)
  ·
    refine ⟨43252519438644793758584579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115340051836386116689558877 43252519438644793758584579)
    ·
      refine ⟨64878779157967190637876869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43252519438644793758584579 64878779157967190637876869)
      ·
        refine ⟨12164771092118848244601913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64878779157967190637876869 12164771092118848244601913)
        ·
          refine ⟨9123578319089136183451435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12164771092118848244601913 9123578319089136183451435)
          ·
            refine ⟨13685367478633704275177153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123578319089136183451435 13685367478633704275177153)
            ·
              refine ⟨10264025608975278206382865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13685367478633704275177153 10264025608975278206382865)
              ·
                refine ⟨7698019206731458654787149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10264025608975278206382865 7698019206731458654787149)
                ·
                  refine ⟨2886757202524296995545181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7698019206731458654787149 2886757202524296995545181)
                  ·
                    refine ⟨1082533950946611373329443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886757202524296995545181 1082533950946611373329443)
                    ·
                      rfl

theorem cell22_3162341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_3162341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162341 prefixEnd_3162341 := by exact prefixLift 3162341
  have htrace : WordTrace (prefixWord ++ tailWord_3162341) baseStart_3162341 baseEnd_3162341 := by
    simpa [prefixWord, tailWord_3162341, baseEnd_3162341] using wordTrace_append hprefix tailTrace_3162341
  have hstable : (prefixWord ++ tailWord_3162341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162341).length < 2 ^ (prefixWord ++ tailWord_3162341).sum := by decide
  have hdescent : baseEnd_3162341 < baseStart_3162341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162352 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_3162352 : Nat := 118140960795 + 3162352 * 2 ^ 59
def prefixEnd_3162352 : Nat := 4983230072969 + 3 ^ 40 * 3162352 * 2
def baseEnd_3162352 : Nat := 1082537716471411011304409

theorem tailTrace_3162352 : CollatzResearch.WordTrace tailWord_3162352 prefixEnd_3162352 1082537716471411011304409 := by
  unfold tailWord_3162352
  simp only [CollatzResearch.WordTrace]
  refine ⟨57670226519673132784104655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76893635359564177045472873 57670226519673132784104655)
  ·
    refine ⟨86505339779509699176156983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57670226519673132784104655 86505339779509699176156983)
    ·
      refine ⟨129758009669264548764235475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86505339779509699176156983 129758009669264548764235475)
      ·
        refine ⟨194637014503896823146353213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129758009669264548764235475 194637014503896823146353213)
        ·
          refine ⟨72988880438961308679882455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194637014503896823146353213 72988880438961308679882455)
          ·
            refine ⟨109483320658441963019823683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72988880438961308679882455 109483320658441963019823683)
            ·
              refine ⟨164224980987662944529735525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109483320658441963019823683 164224980987662944529735525)
              ·
                refine ⟨30792183935186802099325411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164224980987662944529735525 30792183935186802099325411)
                ·
                  refine ⟨46188275902780203148988117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30792183935186802099325411 46188275902780203148988117)
                  ·
                    refine ⟨1082537716471411011304409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46188275902780203148988117 1082537716471411011304409)
                    ·
                      rfl

theorem cell22_3162352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_3162352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162352 prefixEnd_3162352 := by exact prefixLift 3162352
  have htrace : WordTrace (prefixWord ++ tailWord_3162352) baseStart_3162352 baseEnd_3162352 := by
    simpa [prefixWord, tailWord_3162352, baseEnd_3162352] using wordTrace_append hprefix tailTrace_3162352
  have hstable : (prefixWord ++ tailWord_3162352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162352).length < 2 ^ (prefixWord ++ tailWord_3162352).sum := by decide
  have hdescent : baseEnd_3162352 < baseStart_3162352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162354 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3162354 : Nat := 118140960795 + 3162354 * 2 ^ 59
def prefixEnd_3162354 : Nat := 4983230072969 + 3 ^ 40 * 3162354 * 2
def baseEnd_3162354 : Nat := 360846133704094557584801

theorem tailTrace_3162354 : CollatzResearch.WordTrace tailWord_3162354 prefixEnd_3162354 360846133704094557584801 := by
  unfold tailWord_3162354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28835131496334754977445529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76893683990226013273188077 28835131496334754977445529)
  ·
    refine ⟨21626348622251066233084147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28835131496334754977445529 21626348622251066233084147)
    ·
      refine ⟨32439522933376599349626221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21626348622251066233084147 32439522933376599349626221)
      ·
        refine ⟨12164821100016224756109833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32439522933376599349626221 12164821100016224756109833)
        ·
          refine ⟨9123615825012168567082375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12164821100016224756109833 9123615825012168567082375)
          ·
            refine ⟨13685423737518252850623563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123615825012168567082375 13685423737518252850623563)
            ·
              refine ⟨20528135606277379275935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13685423737518252850623563 20528135606277379275935345)
              ·
                refine ⟨15396101704708034456951509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20528135606277379275935345 15396101704708034456951509)
                ·
                  refine ⟨360846133704094557584801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15396101704708034456951509 360846133704094557584801)
                  ·
                    rfl

theorem cell22_3162354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3162354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162354 prefixEnd_3162354 := by exact prefixLift 3162354
  have htrace : WordTrace (prefixWord ++ tailWord_3162354) baseStart_3162354 baseEnd_3162354 := by
    simpa [prefixWord, tailWord_3162354, baseEnd_3162354] using wordTrace_append hprefix tailTrace_3162354
  have hstable : (prefixWord ++ tailWord_3162354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162354).length < 2 ^ (prefixWord ++ tailWord_3162354).sum := by decide
  have hdescent : baseEnd_3162354 < baseStart_3162354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162375 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3162375 : Nat := 118140960795 + 3162375 * 2 ^ 59
def prefixEnd_3162375 : Nat := 4983230072969 + 3 ^ 40 * 3162375 * 2
def baseEnd_3162375 : Nat := 1082545589841446617979339

theorem tailTrace_3162375 : CollatzResearch.WordTrace tailWord_3162375 prefixEnd_3162375 1082545589841446617979339 := by
  unfold tailWord_3162375
  simp only [CollatzResearch.WordTrace]
  refine ⟨115341291918262940496296579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76894194612175293664197719 115341291918262940496296579)
  ·
    refine ⟨173011937877394410744444869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115341291918262940496296579 173011937877394410744444869)
    ·
      refine ⟨32439738352011452014583413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173011937877394410744444869 32439738352011452014583413)
      ·
        refine ⟨3041225470501073626367195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32439738352011452014583413 3041225470501073626367195)
        ·
          refine ⟨4561838205751610439550793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041225470501073626367195 4561838205751610439550793)
          ·
            refine ⟨3421378654313707829663095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4561838205751610439550793 3421378654313707829663095)
            ·
              refine ⟨5132067981470561744494643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421378654313707829663095 5132067981470561744494643)
              ·
                refine ⟨7698101972205842616741965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132067981470561744494643 7698101972205842616741965)
                ·
                  refine ⟨2886788239577190981278237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7698101972205842616741965 2886788239577190981278237)
                  ·
                    refine ⟨1082545589841446617979339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886788239577190981278237 1082545589841446617979339)
                    ·
                      rfl

theorem cell22_3162375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3162375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162375 prefixEnd_3162375 := by exact prefixLift 3162375
  have htrace : WordTrace (prefixWord ++ tailWord_3162375) baseStart_3162375 baseEnd_3162375 := by
    simpa [prefixWord, tailWord_3162375, baseEnd_3162375] using wordTrace_append hprefix tailTrace_3162375
  have hstable : (prefixWord ++ tailWord_3162375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162375).length < 2 ^ (prefixWord ++ tailWord_3162375).sum := by decide
  have hdescent : baseEnd_3162375 < baseStart_3162375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162401 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3162401 : Nat := 118140960795 + 3162401 * 2 ^ 59
def prefixEnd_3162401 : Nat := 4983230072969 + 3 ^ 40 * 3162401 * 2
def baseEnd_3162401 : Nat := 1082554490172791216829259

theorem tailTrace_3162401 : CollatzResearch.WordTrace tailWord_3162401 prefixEnd_3162401 1082554490172791216829259 := by
  unfold tailWord_3162401
  simp only [CollatzResearch.WordTrace]
  refine ⟨115342240216168746936743057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76894826810779164624495371 115342240216168746936743057)
  ·
    refine ⟨86506680162126560202557293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115342240216168746936743057 86506680162126560202557293)
    ·
      refine ⟨32440005060797460075958985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86506680162126560202557293 32440005060797460075958985)
      ·
        refine ⟨24330003795598095056969239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32440005060797460075958985 24330003795598095056969239)
        ·
          refine ⟨36495005693397142585453859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330003795598095056969239 36495005693397142585453859)
          ·
            refine ⟨54742508540095713878180789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36495005693397142585453859 54742508540095713878180789)
            ·
              refine ⟨5132110175633973176079449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54742508540095713878180789 5132110175633973176079449)
              ·
                refine ⟨3849082631725479882059587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132110175633973176079449 3849082631725479882059587)
                ·
                  refine ⟨5773623947588219823089381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849082631725479882059587 5773623947588219823089381)
                  ·
                    refine ⟨1082554490172791216829259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5773623947588219823089381 1082554490172791216829259)
                    ·
                      rfl

theorem cell22_3162401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3162401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162401 prefixEnd_3162401 := by exact prefixLift 3162401
  have htrace : WordTrace (prefixWord ++ tailWord_3162401) baseStart_3162401 baseEnd_3162401 := by
    simpa [prefixWord, tailWord_3162401, baseEnd_3162401] using wordTrace_append hprefix tailTrace_3162401
  have hstable : (prefixWord ++ tailWord_3162401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162401).length < 2 ^ (prefixWord ++ tailWord_3162401).sum := by decide
  have hdescent : baseEnd_3162401 < baseStart_3162401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162493 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_3162493 : Nat := 118140960795 + 3162493 * 2 ^ 59
def prefixEnd_3162493 : Nat := 4983230072969 + 3 ^ 40 * 3162493 * 2
def baseEnd_3162493 : Nat := 1082585983652933643528977

theorem tailTrace_3162493 : CollatzResearch.WordTrace tailWord_3162493 prefixEnd_3162493 1082585983652933643528977 := by
  unfold tailWord_3162493
  simp only [CollatzResearch.WordTrace]
  refine ⟨115345595731835446649092133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76897063821223631099394755 115345595731835446649092133)
  ·
    refine ⟨21627299199719146246704775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115345595731835446649092133 21627299199719146246704775)
    ·
      refine ⟨32440948799578719370057163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21627299199719146246704775 32440948799578719370057163)
      ·
        refine ⟨48661423199368079055085745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32440948799578719370057163 48661423199368079055085745)
        ·
          refine ⟨36496067399526059291314309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48661423199368079055085745 36496067399526059291314309)
          ·
            refine ⟨6843012637411136117121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36496067399526059291314309 6843012637411136117121433)
            ·
              refine ⟨5132259478058352087841075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6843012637411136117121433 5132259478058352087841075)
              ·
                refine ⟨7698389217087528131761613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132259478058352087841075 7698389217087528131761613)
                ·
                  refine ⟨2886895956407823049410605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7698389217087528131761613 2886895956407823049410605)
                  ·
                    refine ⟨1082585983652933643528977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886895956407823049410605 1082585983652933643528977)
                    ·
                      rfl

theorem cell22_3162493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_3162493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162493 prefixEnd_3162493 := by exact prefixLift 3162493
  have htrace : WordTrace (prefixWord ++ tailWord_3162493) baseStart_3162493 baseEnd_3162493 := by
    simpa [prefixWord, tailWord_3162493, baseEnd_3162493] using wordTrace_append hprefix tailTrace_3162493
  have hstable : (prefixWord ++ tailWord_3162493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162493).length < 2 ^ (prefixWord ++ tailWord_3162493).sum := by decide
  have hdescent : baseEnd_3162493 < baseStart_3162493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162551 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 6]
def baseStart_3162551 : Nat := 118140960795 + 3162551 * 2 ^ 59
def prefixEnd_3162551 : Nat := 4983230072969 + 3 ^ 40 * 3162551 * 2
def baseEnd_3162551 : Nat := 360868612746080275192933

theorem tailTrace_3162551 : CollatzResearch.WordTrace tailWord_3162551 prefixEnd_3162551 360868612746080275192933 := by
  unfold tailWord_3162551
  simp only [CollatzResearch.WordTrace]
  refine ⟨115347711165625322554703507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76898474110416881703135671 115347711165625322554703507)
  ·
    refine ⟨173021566748437983832055261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115347711165625322554703507 173021566748437983832055261)
    ·
      refine ⟨64883087530664243937020723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173021566748437983832055261 64883087530664243937020723)
      ·
        refine ⟨97324631295996365905531085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64883087530664243937020723 97324631295996365905531085)
        ·
          refine ⟨36496736735998637214574157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97324631295996365905531085 36496736735998637214574157)
          ·
            refine ⟨13686276275999488955465309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36496736735998637214574157 13686276275999488955465309)
            ·
              refine ⟨5132353603499808358299491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13686276275999488955465309 5132353603499808358299491)
              ·
                refine ⟨7698530405249712537449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132353603499808358299491 7698530405249712537449237)
                ·
                  refine ⟨360868612746080275192933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7698530405249712537449237 360868612746080275192933)
                  ·
                    rfl

theorem cell22_3162551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_3162551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162551 prefixEnd_3162551 := by exact prefixLift 3162551
  have htrace : WordTrace (prefixWord ++ tailWord_3162551) baseStart_3162551 baseEnd_3162551 := by
    simpa [prefixWord, tailWord_3162551, baseEnd_3162551] using wordTrace_append hprefix tailTrace_3162551
  have hstable : (prefixWord ++ tailWord_3162551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162551).length < 2 ^ (prefixWord ++ tailWord_3162551).sum := by decide
  have hdescent : baseEnd_3162551 < baseStart_3162551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162600 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3162600 : Nat := 118140960795 + 3162600 * 2 ^ 59
def prefixEnd_3162600 : Nat := 4983230072969 + 3 ^ 40 * 3162600 * 2
def baseEnd_3162600 : Nat := 1082622611939621031103649

theorem tailTrace_3162600 : CollatzResearch.WordTrace tailWord_3162600 prefixEnd_3162600 1082622611939621031103649 := by
  unfold tailWord_3162600
  simp only [CollatzResearch.WordTrace]
  refine ⟨57674749171223901961618627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76899665561631869282158169 57674749171223901961618627)
  ·
    refine ⟨86512123756835852942427941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57674749171223901961618627 86512123756835852942427941)
    ·
      refine ⟨16221023204406722426705239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86512123756835852942427941 16221023204406722426705239)
      ·
        refine ⟨24331534806610083640057859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16221023204406722426705239 24331534806610083640057859)
        ·
          refine ⟨36497302209915125460086789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24331534806610083640057859 36497302209915125460086789)
          ·
            refine ⟨6843244164359086023766273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36497302209915125460086789 6843244164359086023766273)
            ·
              refine ⟨5132433123269314517824705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6843244164359086023766273 5132433123269314517824705)
              ·
                refine ⟨3849324842451985888368529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132433123269314517824705 3849324842451985888368529)
                ·
                  refine ⟨2886993631838989416276397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849324842451985888368529 2886993631838989416276397)
                  ·
                    refine ⟨1082622611939621031103649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886993631838989416276397 1082622611939621031103649)
                    ·
                      rfl

theorem cell22_3162600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3162600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162600 prefixEnd_3162600 := by exact prefixLift 3162600
  have htrace : WordTrace (prefixWord ++ tailWord_3162600) baseStart_3162600 baseEnd_3162600 := by
    simpa [prefixWord, tailWord_3162600, baseEnd_3162600] using wordTrace_append hprefix tailTrace_3162600
  have hstable : (prefixWord ++ tailWord_3162600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162600).length < 2 ^ (prefixWord ++ tailWord_3162600).sum := by decide
  have hdescent : baseEnd_3162600 < baseStart_3162600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162602 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_3162602 : Nat := 118140960795 + 3162602 * 2 ^ 59
def prefixEnd_3162602 : Nat := 4983230072969 + 3 ^ 40 * 3162602 * 2
def baseEnd_3162602 : Nat := 360874432193497897517881

theorem tailTrace_3162602 : CollatzResearch.WordTrace tailWord_3162602 prefixEnd_3162602 360874432193497897517881 := by
  unfold tailWord_3162602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837392822110139566202515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76899714192293705509873373 28837392822110139566202515)
  ·
    refine ⟨43256089233165209349303773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28837392822110139566202515 43256089233165209349303773)
    ·
      refine ⟨16221033462436953505988915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43256089233165209349303773 16221033462436953505988915)
      ·
        refine ⟨24331550193655430258983373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16221033462436953505988915 24331550193655430258983373)
        ·
          refine ⟨9124331322620786347118765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24331550193655430258983373 9124331322620786347118765)
          ·
            refine ⟨3421624245982794880169537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9124331322620786347118765 3421624245982794880169537)
            ·
              refine ⟨2566218184487096160127153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421624245982794880169537 2566218184487096160127153)
              ·
                refine ⟨1924663638365322120095365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566218184487096160127153 1924663638365322120095365)
                ·
                  refine ⟨360874432193497897517881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924663638365322120095365 360874432193497897517881)
                  ·
                    rfl

theorem cell22_3162602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_3162602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162602 prefixEnd_3162602 := by exact prefixLift 3162602
  have htrace : WordTrace (prefixWord ++ tailWord_3162602) baseStart_3162602 baseEnd_3162602 := by
    simpa [prefixWord, tailWord_3162602, baseEnd_3162602] using wordTrace_append hprefix tailTrace_3162602
  have hstable : (prefixWord ++ tailWord_3162602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162602).length < 2 ^ (prefixWord ++ tailWord_3162602).sum := by decide
  have hdescent : baseEnd_3162602 < baseStart_3162602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162688 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_3162688 : Nat := 118140960795 + 3162688 * 2 ^ 59
def prefixEnd_3162688 : Nat := 4983230072969 + 3 ^ 40 * 3162688 * 2
def baseEnd_3162688 : Nat := 1082652736138018134903379

theorem tailTrace_3162688 : CollatzResearch.WordTrace tailWord_3162688 prefixEnd_3162688 1082652736138018134903379 := by
  unfold tailWord_3162688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57676353983064497476220359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76901805310752663301627145 57676353983064497476220359)
  ·
    refine ⟨86514530974596746214330539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57676353983064497476220359 86514530974596746214330539)
    ·
      refine ⟨129771796461895119321495809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86514530974596746214330539 129771796461895119321495809)
      ·
        refine ⟨97328847346421339491121857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129771796461895119321495809 97328847346421339491121857)
        ·
          refine ⟨72996635509816004618341393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97328847346421339491121857 72996635509816004618341393)
          ·
            refine ⟨54747476632362003463756045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72996635509816004618341393 54747476632362003463756045)
            ·
              refine ⟨20530303737135751298908517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54747476632362003463756045 20530303737135751298908517)
              ·
                refine ⟨3849431950712953368545347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20530303737135751298908517 3849431950712953368545347)
                ·
                  refine ⟨5774147926069430052818021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849431950712953368545347 5774147926069430052818021)
                  ·
                    refine ⟨1082652736138018134903379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5774147926069430052818021 1082652736138018134903379)
                    ·
                      rfl

theorem cell22_3162688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_3162688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162688 prefixEnd_3162688 := by exact prefixLift 3162688
  have htrace : WordTrace (prefixWord ++ tailWord_3162688) baseStart_3162688 baseEnd_3162688 := by
    simpa [prefixWord, tailWord_3162688, baseEnd_3162688] using wordTrace_append hprefix tailTrace_3162688
  have hstable : (prefixWord ++ tailWord_3162688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162688).length < 2 ^ (prefixWord ++ tailWord_3162688).sum := by decide
  have hdescent : baseEnd_3162688 < baseStart_3162688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162763 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 7, 3]
def baseStart_3162763 : Nat := 118140960795 + 3162763 * 2 ^ 59
def prefixEnd_3162763 : Nat := 4983230072969 + 3 ^ 40 * 3162763 * 2
def baseEnd_3162763 : Nat := 1082678410170742939278149

theorem tailTrace_3162763 : CollatzResearch.WordTrace tailWord_3162763 prefixEnd_3162763 1082678410170742939278149 := by
  unfold tailWord_3162763
  simp only [CollatzResearch.WordTrace]
  refine ⟨115355443440857282761420943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76903628960571521840947295 115355443440857282761420943)
  ·
    refine ⟨173033165161285924142131415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115355443440857282761420943 173033165161285924142131415)
    ·
      refine ⟨259549747741928886213197123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173033165161285924142131415 259549747741928886213197123)
      ·
        refine ⟨389324621612893329319795685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259549747741928886213197123 389324621612893329319795685)
        ·
          refine ⟨72998366552417499247461691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389324621612893329319795685 72998366552417499247461691)
          ·
            refine ⟨109497549828626248871192537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72998366552417499247461691 109497549828626248871192537)
            ·
              refine ⟨82123162371469686653394403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109497549828626248871192537 82123162371469686653394403)
              ·
                refine ⟨123184743557204529980091605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82123162371469686653394403 123184743557204529980091605)
                ·
                  refine ⟨2887142427121981171408397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123184743557204529980091605 2887142427121981171408397)
                  ·
                    refine ⟨1082678410170742939278149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887142427121981171408397 1082678410170742939278149)
                    ·
                      rfl

theorem cell22_3162763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].length) (baseStart_3162763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162763 prefixEnd_3162763 := by exact prefixLift 3162763
  have htrace : WordTrace (prefixWord ++ tailWord_3162763) baseStart_3162763 baseEnd_3162763 := by
    simpa [prefixWord, tailWord_3162763, baseEnd_3162763] using wordTrace_append hprefix tailTrace_3162763
  have hstable : (prefixWord ++ tailWord_3162763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162763).length < 2 ^ (prefixWord ++ tailWord_3162763).sum := by decide
  have hdescent : baseEnd_3162763 < baseStart_3162763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162797 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3162797 : Nat := 118140960795 + 3162797 * 2 ^ 59
def prefixEnd_3162797 : Nat := 4983230072969 + 3 ^ 40 * 3162797 * 2
def baseEnd_3162797 : Nat := 1082690049065578183928045

theorem tailTrace_3162797 : CollatzResearch.WordTrace tailWord_3162797 prefixEnd_3162797 1082690049065578183928045 := by
  unfold tailWord_3162797
  simp only [CollatzResearch.WordTrace]
  refine ⟨115356683522734106568158645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76904455681822737712105763 115356683522734106568158645)
  ·
    refine ⟨10814689080256322490764873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115356683522734106568158645 10814689080256322490764873)
    ·
      refine ⟨8111016810192241868073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10814689080256322490764873 8111016810192241868073655)
      ·
        refine ⟨12166525215288362802110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8111016810192241868073655 12166525215288362802110483)
        ·
          refine ⟨18249787822932544203165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12166525215288362802110483 18249787822932544203165725)
          ·
            refine ⟨6843670433599704076187147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18249787822932544203165725 6843670433599704076187147)
            ·
              refine ⟨10265505650399556114280721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843670433599704076187147 10265505650399556114280721)
              ·
                refine ⟨7699129237799667085710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10265505650399556114280721 7699129237799667085710541)
                ·
                  refine ⟨2887173464174875157141453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7699129237799667085710541 2887173464174875157141453)
                  ·
                    refine ⟨1082690049065578183928045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887173464174875157141453 1082690049065578183928045)
                    ·
                      rfl

theorem cell22_3162797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3162797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162797 prefixEnd_3162797 := by exact prefixLift 3162797
  have htrace : WordTrace (prefixWord ++ tailWord_3162797) baseStart_3162797 baseEnd_3162797 := by
    simpa [prefixWord, tailWord_3162797, baseEnd_3162797] using wordTrace_append hprefix tailTrace_3162797
  have hstable : (prefixWord ++ tailWord_3162797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162797).length < 2 ^ (prefixWord ++ tailWord_3162797).sum := by decide
  have hdescent : baseEnd_3162797 < baseStart_3162797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162814 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3162814 : Nat := 118140960795 + 3162814 * 2 ^ 59
def prefixEnd_3162814 : Nat := 4983230072969 + 3 ^ 40 * 3162814 * 2
def baseEnd_3162814 : Nat := 1082695868512995806252993

theorem tailTrace_3162814 : CollatzResearch.WordTrace tailWord_3162814 prefixEnd_3162814 1082695868512995806252993 := by
  unfold tailWord_3162814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419662945459064808940937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76904869042448345647684997 14419662945459064808940937)
  ·
    refine ⟨10814747209094298606705703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14419662945459064808940937 10814747209094298606705703)
    ·
      refine ⟨16222120813641447910058555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10814747209094298606705703 16222120813641447910058555)
      ·
        refine ⟨24333181220462171865087833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16222120813641447910058555 24333181220462171865087833)
        ·
          refine ⟨18249885915346628898815875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24333181220462171865087833 18249885915346628898815875)
          ·
            refine ⟨27374828873019943348223813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249885915346628898815875 27374828873019943348223813)
            ·
              refine ⟨5132780413691239377791965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27374828873019943348223813 5132780413691239377791965)
              ·
                refine ⟨1924792655134214766671987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5132780413691239377791965 1924792655134214766671987)
                ·
                  refine ⟨2887188982701322150007981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924792655134214766671987 2887188982701322150007981)
                  ·
                    refine ⟨1082695868512995806252993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887188982701322150007981 1082695868512995806252993)
                    ·
                      rfl

theorem cell22_3162814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3162814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162814 prefixEnd_3162814 := by exact prefixLift 3162814
  have htrace : WordTrace (prefixWord ++ tailWord_3162814) baseStart_3162814 baseEnd_3162814 := by
    simpa [prefixWord, tailWord_3162814, baseEnd_3162814] using wordTrace_append hprefix tailTrace_3162814
  have hstable : (prefixWord ++ tailWord_3162814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162814).length < 2 ^ (prefixWord ++ tailWord_3162814).sum := by decide
  have hdescent : baseEnd_3162814 < baseStart_3162814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162823 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3162823 : Nat := 118140960795 + 3162823 * 2 ^ 59
def prefixEnd_3162823 : Nat := 4983230072969 + 3 ^ 40 * 3162823 * 2
def baseEnd_3162823 : Nat := 1082698949396922782777965

theorem tailTrace_3162823 : CollatzResearch.WordTrace tailWord_3162823 prefixEnd_3162823 1082698949396922782777965 := by
  unfold tailWord_3162823
  simp only [CollatzResearch.WordTrace]
  refine ⟨115357631820639913008605123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76905087880426608672403415 115357631820639913008605123)
  ·
    refine ⟨173036447730959869512907685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115357631820639913008605123 173036447730959869512907685)
    ·
      refine ⟨32444333949554975533670191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173036447730959869512907685 32444333949554975533670191)
      ·
        refine ⟨48666500924332463300505287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32444333949554975533670191 48666500924332463300505287)
        ·
          refine ⟨72999751386498694950757931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48666500924332463300505287 72999751386498694950757931)
          ·
            refine ⟨109499627079748042426136897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72999751386498694950757931 109499627079748042426136897)
            ·
              refine ⟨82124720309811031819602673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109499627079748042426136897 82124720309811031819602673)
              ·
                refine ⟨61593540232358273864702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82124720309811031819602673 61593540232358273864702005)
                ·
                  refine ⟨5774394396783588174815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61593540232358273864702005 5774394396783588174815813)
                  ·
                    refine ⟨1082698949396922782777965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5774394396783588174815813 1082698949396922782777965)
                    ·
                      rfl

theorem cell22_3162823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3162823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162823 prefixEnd_3162823 := by exact prefixLift 3162823
  have htrace : WordTrace (prefixWord ++ tailWord_3162823) baseStart_3162823 baseEnd_3162823 := by
    simpa [prefixWord, tailWord_3162823, baseEnd_3162823] using wordTrace_append hprefix tailTrace_3162823
  have hstable : (prefixWord ++ tailWord_3162823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162823).length < 2 ^ (prefixWord ++ tailWord_3162823).sum := by decide
  have hdescent : baseEnd_3162823 < baseStart_3162823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162844 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_3162844 : Nat := 118140960795 + 3162844 * 2 ^ 59
def prefixEnd_3162844 : Nat := 4983230072969 + 3 ^ 40 * 3162844 * 2
def baseEnd_3162844 : Nat := 360902046042028576000967

theorem tailTrace_3162844 : CollatzResearch.WordTrace tailWord_3162844 prefixEnd_3162844 360902046042028576000967 := by
  unfold tailWord_3162844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57679198876781916797559793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76905598502375889063413057 57679198876781916797559793)
  ·
    refine ⟨43259399157586437598169845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57679198876781916797559793 43259399157586437598169845)
    ·
      refine ⟨4055568671023728524828423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43259399157586437598169845 4055568671023728524828423)
      ·
        refine ⟨6083353006535592787242635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055568671023728524828423 6083353006535592787242635)
        ·
          refine ⟨9125029509803389180863953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083353006535592787242635 9125029509803389180863953)
          ·
            refine ⟨6843772132352541885647965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9125029509803389180863953 6843772132352541885647965)
            ·
              refine ⟨2566414549632203207117987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6843772132352541885647965 2566414549632203207117987)
              ·
                refine ⟨3849621824448304810676981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566414549632203207117987 3849621824448304810676981)
                ·
                  refine ⟨360902046042028576000967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849621824448304810676981 360902046042028576000967)
                  ·
                    rfl

theorem cell22_3162844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_3162844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162844 prefixEnd_3162844 := by exact prefixLift 3162844
  have htrace : WordTrace (prefixWord ++ tailWord_3162844) baseStart_3162844 baseEnd_3162844 := by
    simpa [prefixWord, tailWord_3162844, baseEnd_3162844] using wordTrace_append hprefix tailTrace_3162844
  have hstable : (prefixWord ++ tailWord_3162844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162844).length < 2 ^ (prefixWord ++ tailWord_3162844).sum := by decide
  have hdescent : baseEnd_3162844 < baseStart_3162844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162870 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3162870 : Nat := 118140960795 + 3162870 * 2 ^ 59
def prefixEnd_3162870 : Nat := 4983230072969 + 3 ^ 40 * 3162870 * 2
def baseEnd_3162870 : Nat := 1082715038457430326852821

theorem tailTrace_3162870 : CollatzResearch.WordTrace tailWord_3162870 prefixEnd_3162870 1082715038457430326852821 := by
  unfold tailWord_3162870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209959128216852502222879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76906230700979760023710709 7209959128216852502222879)
  ·
    refine ⟨10814938692325278753334319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209959128216852502222879 10814938692325278753334319)
    ·
      refine ⟨16222408038487918130001479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10814938692325278753334319 16222408038487918130001479)
      ·
        refine ⟨24333612057731877195002219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16222408038487918130001479 24333612057731877195002219)
        ·
          refine ⟨36500418086597815792503329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24333612057731877195002219 36500418086597815792503329)
          ·
            refine ⟨27375313564948361844377497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36500418086597815792503329 27375313564948361844377497)
            ·
              refine ⟨20531485173711271383283123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27375313564948361844377497 20531485173711271383283123)
              ·
                refine ⟨30797227760566907074924685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20531485173711271383283123 30797227760566907074924685)
                ·
                  refine ⟨11548960410212590153096757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30797227760566907074924685 11548960410212590153096757)
                  ·
                    refine ⟨1082715038457430326852821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11548960410212590153096757 1082715038457430326852821)
                    ·
                      rfl

theorem cell22_3162870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3162870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162870 prefixEnd_3162870 := by exact prefixLift 3162870
  have htrace : WordTrace (prefixWord ++ tailWord_3162870) baseStart_3162870 baseEnd_3162870 := by
    simpa [prefixWord, tailWord_3162870, baseEnd_3162870] using wordTrace_append hprefix tailTrace_3162870
  have hstable : (prefixWord ++ tailWord_3162870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162870).length < 2 ^ (prefixWord ++ tailWord_3162870).sum := by decide
  have hdescent : baseEnd_3162870 < baseStart_3162870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162887 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3162887 : Nat := 118140960795 + 3162887 * 2 ^ 59
def prefixEnd_3162887 : Nat := 4983230072969 + 3 ^ 40 * 3162887 * 2
def baseEnd_3162887 : Nat := 1082720857904847949177769

theorem tailTrace_3162887 : CollatzResearch.WordTrace tailWord_3162887 prefixEnd_3162887 1082720857904847949177769 := by
  unfold tailWord_3162887
  simp only [CollatzResearch.WordTrace]
  refine ⟨115359966092408051938934915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76906644061605367959289943 115359966092408051938934915)
  ·
    refine ⟨173039949138612077908402373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115359966092408051938934915 173039949138612077908402373)
    ·
      refine ⟨32444990463489764607825445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173039949138612077908402373 32444990463489764607825445)
      ·
        refine ⟨6083435711904330863967271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32444990463489764607825445 6083435711904330863967271)
        ·
          refine ⟨9125153567856496295950907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083435711904330863967271 9125153567856496295950907)
          ·
            refine ⟨13687730351784744443926361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125153567856496295950907 13687730351784744443926361)
            ·
              refine ⟨10265797763838558332944771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13687730351784744443926361 10265797763838558332944771)
              ·
                refine ⟨15398696645757837499417157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10265797763838558332944771 15398696645757837499417157)
                ·
                  refine ⟨2887255621079594531140717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15398696645757837499417157 2887255621079594531140717)
                  ·
                    refine ⟨1082720857904847949177769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887255621079594531140717 1082720857904847949177769)
                    ·
                      rfl

theorem cell22_3162887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3162887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162887 prefixEnd_3162887 := by exact prefixLift 3162887
  have htrace : WordTrace (prefixWord ++ tailWord_3162887) baseStart_3162887 baseEnd_3162887 := by
    simpa [prefixWord, tailWord_3162887, baseEnd_3162887] using wordTrace_append hprefix tailTrace_3162887
  have hstable : (prefixWord ++ tailWord_3162887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162887).length < 2 ^ (prefixWord ++ tailWord_3162887).sum := by decide
  have hdescent : baseEnd_3162887 < baseStart_3162887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162915 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 5, 3]
def baseStart_3162915 : Nat := 118140960795 + 3162915 * 2 ^ 59
def prefixEnd_3162915 : Nat := 4983230072969 + 3 ^ 40 * 3162915 * 2
def baseEnd_3162915 : Nat := 1082730442877065209477683

theorem tailTrace_3162915 : CollatzResearch.WordTrace tailWord_3162915 prefixEnd_3162915 1082730442877065209477683 := by
  unfold tailWord_3162915
  simp only [CollatzResearch.WordTrace]
  refine ⟨115360987336306612720954199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76907324890871075147302799 115360987336306612720954199)
  ·
    refine ⟨173041481004459919081431299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115360987336306612720954199 173041481004459919081431299)
    ·
      refine ⟨259562221506689878622146949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173041481004459919081431299 259562221506689878622146949)
      ·
        refine ⟨48667916532504352241652553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259562221506689878622146949 48667916532504352241652553)
        ·
          refine ⟨36500937399378264181239415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48667916532504352241652553 36500937399378264181239415)
          ·
            refine ⟨54751406099067396271859123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36500937399378264181239415 54751406099067396271859123)
            ·
              refine ⟨82127109148601094407788685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54751406099067396271859123 82127109148601094407788685)
              ·
                refine ⟨30797665930725410402920757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82127109148601094407788685 30797665930725410402920757)
                ·
                  refine ⟨2887281181005507225273821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30797665930725410402920757 2887281181005507225273821)
                  ·
                    refine ⟨1082730442877065209477683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887281181005507225273821 1082730442877065209477683)
                    ·
                      rfl

theorem cell22_3162915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].length) (baseStart_3162915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162915 prefixEnd_3162915 := by exact prefixLift 3162915
  have htrace : WordTrace (prefixWord ++ tailWord_3162915) baseStart_3162915 baseEnd_3162915 := by
    simpa [prefixWord, tailWord_3162915, baseEnd_3162915] using wordTrace_append hprefix tailTrace_3162915
  have hstable : (prefixWord ++ tailWord_3162915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162915).length < 2 ^ (prefixWord ++ tailWord_3162915).sum := by decide
  have hdescent : baseEnd_3162915 < baseStart_3162915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162928 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_3162928 : Nat := 118140960795 + 3162928 * 2 ^ 59
def prefixEnd_3162928 : Nat := 4983230072969 + 3 ^ 40 * 3162928 * 2
def baseEnd_3162928 : Nat := 360911631014245836300881

theorem tailTrace_3162928 : CollatzResearch.WordTrace tailWord_3162928 prefixEnd_3162928 360911631014245836300881 := by
  unfold tailWord_3162928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57680730742629757970588719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76907640990173010627451625 57680730742629757970588719)
  ·
    refine ⟨86521096113944636955883079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57680730742629757970588719 86521096113944636955883079)
    ·
      refine ⟨129781644170916955433824619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86521096113944636955883079 129781644170916955433824619)
      ·
        refine ⟨194672466256375433150736929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129781644170916955433824619 194672466256375433150736929)
        ·
          refine ⟨146004349692281574863052697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194672466256375433150736929 146004349692281574863052697)
          ·
            refine ⟨109503262269211181147289523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146004349692281574863052697 109503262269211181147289523)
            ·
              refine ⟨164254893403816771720934285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109503262269211181147289523 164254893403816771720934285)
              ·
                refine ⟨61595585026431289395350357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164254893403816771720934285 61595585026431289395350357)
                ·
                  refine ⟨360911631014245836300881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61595585026431289395350357 360911631014245836300881)
                  ·
                    rfl

theorem cell22_3162928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_3162928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162928 prefixEnd_3162928 := by exact prefixLift 3162928
  have htrace : WordTrace (prefixWord ++ tailWord_3162928) baseStart_3162928 baseEnd_3162928 := by
    simpa [prefixWord, tailWord_3162928, baseEnd_3162928] using wordTrace_append hprefix tailTrace_3162928
  have hstable : (prefixWord ++ tailWord_3162928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162928).length < 2 ^ (prefixWord ++ tailWord_3162928).sum := by decide
  have hdescent : baseEnd_3162928 < baseStart_3162928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162975 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_3162975 : Nat := 118140960795 + 3162975 * 2 ^ 59
def prefixEnd_3162975 : Nat := 4983230072969 + 3 ^ 40 * 3162975 * 2
def baseEnd_3162975 : Nat := 1082750982103245052977499

theorem tailTrace_3162975 : CollatzResearch.WordTrace tailWord_3162975 prefixEnd_3162975 1082750982103245052977499 := by
  unfold tailWord_3162975
  simp only [CollatzResearch.WordTrace]
  refine ⟨115363175716089242968138379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76908783810726161978758919 115363175716089242968138379)
  ·
    refine ⟨173044763574133864452207569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115363175716089242968138379 173044763574133864452207569)
    ·
      refine ⟨129783572680600398339155677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173044763574133864452207569 129783572680600398339155677)
      ·
        refine ⟨48668839755225149377183379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129783572680600398339155677 48668839755225149377183379)
        ·
          refine ⟨73003259632837724065775069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48668839755225149377183379 73003259632837724065775069)
          ·
            refine ⟨27376222362314146524665651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73003259632837724065775069 27376222362314146524665651)
            ·
              refine ⟨41064333543471219786998477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27376222362314146524665651 41064333543471219786998477)
              ·
                refine ⟨15399125078801707420124429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41064333543471219786998477 15399125078801707420124429)
                ·
                  refine ⟨5774671904550640282546661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15399125078801707420124429 5774671904550640282546661)
                  ·
                    refine ⟨1082750982103245052977499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5774671904550640282546661 1082750982103245052977499)
                    ·
                      rfl

theorem cell22_3162975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_3162975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3162975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3162975 prefixEnd_3162975 := by exact prefixLift 3162975
  have htrace : WordTrace (prefixWord ++ tailWord_3162975) baseStart_3162975 baseEnd_3162975 := by
    simpa [prefixWord, tailWord_3162975, baseEnd_3162975] using wordTrace_append hprefix tailTrace_3162975
  have hstable : (prefixWord ++ tailWord_3162975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162975).length < 2 ^ (prefixWord ++ tailWord_3162975).sum := by decide
  have hdescent : baseEnd_3162975 < baseStart_3162975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163005 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3163005 : Nat := 118140960795 + 3163005 * 2 ^ 59
def prefixEnd_3163005 : Nat := 4983230072969 + 3 ^ 40 * 3163005 * 2
def baseEnd_3163005 : Nat := 1082761251716334974727407

theorem tailTrace_3163005 : CollatzResearch.WordTrace tailWord_3163005 prefixEnd_3163005 1082761251716334974727407 := by
  unfold tailWord_3163005
  simp only [CollatzResearch.WordTrace]
  refine ⟨115364269905980558091730469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76909513270653705394486979 115364269905980558091730469)
  ·
    refine ⟨21630800607371354642199463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115364269905980558091730469 21630800607371354642199463)
    ·
      refine ⟨32446200911057031963299195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21630800607371354642199463 32446200911057031963299195)
      ·
        refine ⟨48669301366585547944948793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32446200911057031963299195 48669301366585547944948793)
        ·
          refine ⟨36501976024939160958711595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48669301366585547944948793 36501976024939160958711595)
          ·
            refine ⟨54752964037408741438067393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36501976024939160958711595 54752964037408741438067393)
            ·
              refine ⟨41064723028056556078550545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54752964037408741438067393 41064723028056556078550545)
              ·
                refine ⟨30798542271042417058912909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41064723028056556078550545 30798542271042417058912909)
                ·
                  refine ⟨11549453351640906397092341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30798542271042417058912909 11549453351640906397092341)
                  ·
                    refine ⟨1082761251716334974727407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11549453351640906397092341 1082761251716334974727407)
                    ·
                      rfl

theorem cell22_3163005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3163005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163005 prefixEnd_3163005 := by exact prefixLift 3163005
  have htrace : WordTrace (prefixWord ++ tailWord_3163005) baseStart_3163005 baseEnd_3163005 := by
    simpa [prefixWord, tailWord_3163005, baseEnd_3163005] using wordTrace_append hprefix tailTrace_3163005
  have hstable : (prefixWord ++ tailWord_3163005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163005).length < 2 ^ (prefixWord ++ tailWord_3163005).sum := by decide
  have hdescent : baseEnd_3163005 < baseStart_3163005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163007 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 4]
def baseStart_3163007 : Nat := 118140960795 + 3163007 * 2 ^ 59
def prefixEnd_3163007 : Nat := 4983230072969 + 3 ^ 40 * 3163007 * 2
def baseEnd_3163007 : Nat := 360920645452402545392467

theorem tailTrace_3163007 : CollatzResearch.WordTrace tailWord_3163007 prefixEnd_3163007 360920645452402545392467 := by
  unfold tailWord_3163007
  simp only [CollatzResearch.WordTrace]
  refine ⟨115364342851973312433303275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76909561901315541622202183 115364342851973312433303275)
  ·
    refine ⟨173046514277959968649954913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115364342851973312433303275 173046514277959968649954913)
    ·
      refine ⟨129784885708469976487466185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173046514277959968649954913 129784885708469976487466185)
      ·
        refine ⟨97338664281352482365599639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129784885708469976487466185 97338664281352482365599639)
        ·
          refine ⟨146007996422028723548399459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97338664281352482365599639 146007996422028723548399459)
          ·
            refine ⟨219011994633043085322599189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146007996422028723548399459 219011994633043085322599189)
            ·
              refine ⟨10266187248423894624496837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219011994633043085322599189 10266187248423894624496837)
              ·
                refine ⟨1924910109079480242093157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10266187248423894624496837 1924910109079480242093157)
                ·
                  refine ⟨360920645452402545392467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924910109079480242093157 360920645452402545392467)
                  ·
                    rfl

theorem cell22_3163007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 4].length) (baseStart_3163007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163007 prefixEnd_3163007 := by exact prefixLift 3163007
  have htrace : WordTrace (prefixWord ++ tailWord_3163007) baseStart_3163007 baseEnd_3163007 := by
    simpa [prefixWord, tailWord_3163007, baseEnd_3163007] using wordTrace_append hprefix tailTrace_3163007
  have hstable : (prefixWord ++ tailWord_3163007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163007).length < 2 ^ (prefixWord ++ tailWord_3163007).sum := by decide
  have hdescent : baseEnd_3163007 < baseStart_3163007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163020 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_3163020 : Nat := 118140960795 + 3163020 * 2 ^ 59
def prefixEnd_3163020 : Nat := 4983230072969 + 3 ^ 40 * 3163020 * 2
def baseEnd_3163020 : Nat := 1082766386522879935602361

theorem tailTrace_3163020 : CollatzResearch.WordTrace tailWord_3163020 prefixEnd_3163020 1082766386522879935602361 := by
  unfold tailWord_3163020
  simp only [CollatzResearch.WordTrace]
  refine ⟨57682408500463107826763257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76909878000617477102351009 57682408500463107826763257)
  ·
    refine ⟨43261806375347330870072443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57682408500463107826763257 43261806375347330870072443)
    ·
      refine ⟨64892709563020996305108665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43261806375347330870072443 64892709563020996305108665)
      ·
        refine ⟨48669532172265747228831499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64892709563020996305108665 48669532172265747228831499)
        ·
          refine ⟨73004298258398620843247249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48669532172265747228831499 73004298258398620843247249)
          ·
            refine ⟨54753223693798965632435437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73004298258398620843247249 54753223693798965632435437)
            ·
              refine ⟨20532458885174612112163289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54753223693798965632435437 20532458885174612112163289)
              ·
                refine ⟨15399344163880959084122467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20532458885174612112163289 15399344163880959084122467)
                ·
                  refine ⟨23099016245821438626183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15399344163880959084122467 23099016245821438626183701)
                  ·
                    refine ⟨1082766386522879935602361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23099016245821438626183701 1082766386522879935602361)
                    ·
                      rfl

theorem cell22_3163020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_3163020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163020 prefixEnd_3163020 := by exact prefixLift 3163020
  have htrace : WordTrace (prefixWord ++ tailWord_3163020) baseStart_3163020 baseEnd_3163020 := by
    simpa [prefixWord, tailWord_3163020, baseEnd_3163020] using wordTrace_append hprefix tailTrace_3163020
  have hstable : (prefixWord ++ tailWord_3163020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163020).length < 2 ^ (prefixWord ++ tailWord_3163020).sum := by decide
  have hdescent : baseEnd_3163020 < baseStart_3163020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163026 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3163026 : Nat := 118140960795 + 3163026 * 2 ^ 59
def prefixEnd_3163026 : Nat := 4983230072969 + 3 ^ 40 * 3163026 * 2
def baseEnd_3163026 : Nat := 1082768440445497919952343

theorem tailTrace_3163026 : CollatzResearch.WordTrace tailWord_3163026 prefixEnd_3163026 1082768440445497919952343 := by
  unfold tailWord_3163026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841258959726119669561233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76910023892602985785496621 28841258959726119669561233)
  ·
    refine ⟨21630944219794589752170925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28841258959726119669561233 21630944219794589752170925)
    ·
      refine ⟨8111604082422971157064097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21630944219794589752170925 8111604082422971157064097)
      ·
        refine ⟨6083703061817228367798073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8111604082422971157064097 6083703061817228367798073)
        ·
          refine ⟨4562777296362921275848555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6083703061817228367798073 4562777296362921275848555)
          ·
            refine ⟨6844165944544381913772833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562777296362921275848555 6844165944544381913772833)
            ·
              refine ⟨5133124458408286435329625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844165944544381913772833 5133124458408286435329625)
              ·
                refine ⟨3849843343806214826497219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133124458408286435329625 3849843343806214826497219)
                ·
                  refine ⟨5774765015709322239745829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849843343806214826497219 5774765015709322239745829)
                  ·
                    refine ⟨1082768440445497919952343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5774765015709322239745829 1082768440445497919952343)
                    ·
                      rfl

theorem cell22_3163026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3163026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163026 prefixEnd_3163026 := by exact prefixLift 3163026
  have htrace : WordTrace (prefixWord ++ tailWord_3163026) baseStart_3163026 baseEnd_3163026 := by
    simpa [prefixWord, tailWord_3163026, baseEnd_3163026] using wordTrace_append hprefix tailTrace_3163026
  have hstable : (prefixWord ++ tailWord_3163026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163026).length < 2 ^ (prefixWord ++ tailWord_3163026).sum := by decide
  have hdescent : baseEnd_3163026 < baseStart_3163026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163037 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3163037 : Nat := 118140960795 + 3163037 * 2 ^ 59
def prefixEnd_3163037 : Nat := 4983230072969 + 3 ^ 40 * 3163037 * 2
def baseEnd_3163037 : Nat := 1082772205970297557927309

theorem tailTrace_3163037 : CollatzResearch.WordTrace tailWord_3163037 prefixEnd_3163037 1082772205970297557927309 := by
  unfold tailWord_3163037
  simp only [CollatzResearch.WordTrace]
  refine ⟨115365437041864627556895365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76910291361243085037930243 115365437041864627556895365)
  ·
    refine ⟨21631019445349617666917881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115365437041864627556895365 21631019445349617666917881)
    ·
      refine ⟨16223264584012213250188411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21631019445349617666917881 16223264584012213250188411)
      ·
        refine ⟨24334896876018319875282617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16223264584012213250188411 24334896876018319875282617)
        ·
          refine ⟨18251172657013739906461963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24334896876018319875282617 18251172657013739906461963)
          ·
            refine ⟨27376758985520609859692945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18251172657013739906461963 27376758985520609859692945)
            ·
              refine ⟨20532569239140457394769709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27376758985520609859692945 20532569239140457394769709)
              ·
                refine ⟨7699713464677671523038641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20532569239140457394769709 7699713464677671523038641)
                ·
                  refine ⟨5774785098508253642278981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7699713464677671523038641 5774785098508253642278981)
                  ·
                    refine ⟨1082772205970297557927309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5774785098508253642278981 1082772205970297557927309)
                    ·
                      rfl

theorem cell22_3163037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3163037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163037 prefixEnd_3163037 := by exact prefixLift 3163037
  have htrace : WordTrace (prefixWord ++ tailWord_3163037) baseStart_3163037 baseEnd_3163037 := by
    simpa [prefixWord, tailWord_3163037, baseEnd_3163037] using wordTrace_append hprefix tailTrace_3163037
  have hstable : (prefixWord ++ tailWord_3163037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163037).length < 2 ^ (prefixWord ++ tailWord_3163037).sum := by decide
  have hdescent : baseEnd_3163037 < baseStart_3163037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163041 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 4]
def baseStart_3163041 : Nat := 118140960795 + 3163041 * 2 ^ 59
def prefixEnd_3163041 : Nat := 4983230072969 + 3 ^ 40 * 3163041 * 2
def baseEnd_3163041 : Nat := 360924525084014293609099

theorem tailTrace_3163041 : CollatzResearch.WordTrace tailWord_3163041 prefixEnd_3163041 360924525084014293609099 := by
  unfold tailWord_3163041
  simp only [CollatzResearch.WordTrace]
  refine ⟨115365582933850136240040977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76910388622566757493360651 115365582933850136240040977)
  ·
    refine ⟨86524187200387602180030733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115365582933850136240040977 86524187200387602180030733)
    ·
      refine ⟨32446570200145350817511525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86524187200387602180030733 32446570200145350817511525)
      ·
        refine ⟨6083731912527253278283411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32446570200145350817511525 6083731912527253278283411)
        ·
          refine ⟨9125597868790879917425117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083731912527253278283411 9125597868790879917425117)
          ·
            refine ⟨3422099200796579969034419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9125597868790879917425117 3422099200796579969034419)
            ·
              refine ⟨5133148801194869953551629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422099200796579969034419 5133148801194869953551629)
              ·
                refine ⟨1924930800448076232581861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5133148801194869953551629 1924930800448076232581861)
                ·
                  refine ⟨360924525084014293609099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924930800448076232581861 360924525084014293609099)
                  ·
                    rfl

theorem cell22_3163041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_3163041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163041 prefixEnd_3163041 := by exact prefixLift 3163041
  have htrace : WordTrace (prefixWord ++ tailWord_3163041) baseStart_3163041 baseEnd_3163041 := by
    simpa [prefixWord, tailWord_3163041, baseEnd_3163041] using wordTrace_append hprefix tailTrace_3163041
  have hstable : (prefixWord ++ tailWord_3163041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163041).length < 2 ^ (prefixWord ++ tailWord_3163041).sum := by decide
  have hdescent : baseEnd_3163041 < baseStart_3163041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163095 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3163095 : Nat := 118140960795 + 3163095 * 2 ^ 59
def prefixEnd_3163095 : Nat := 4983230072969 + 3 ^ 40 * 3163095 * 2
def baseEnd_3163095 : Nat := 1082792060555604739977131

theorem tailTrace_3163095 : CollatzResearch.WordTrace tailWord_3163095 prefixEnd_3163095 1082792060555604739977131 := by
  unfold tailWord_3163095
  simp only [CollatzResearch.WordTrace]
  refine ⟨115367552475654503462506739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76911701650436335641671159 115367552475654503462506739)
  ·
    refine ⟨173051328713481755193760109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115367552475654503462506739 173051328713481755193760109)
    ·
      refine ⟨64894248267555658197660041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173051328713481755193760109 64894248267555658197660041)
      ·
        refine ⟨48670686200666743648245031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64894248267555658197660041 48670686200666743648245031)
        ·
          refine ⟨73006029301000115472367547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48670686200666743648245031 73006029301000115472367547)
          ·
            refine ⟨109509043951500173208551321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73006029301000115472367547 109509043951500173208551321)
            ·
              refine ⟨82131782963625129906413491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109509043951500173208551321 82131782963625129906413491)
              ·
                refine ⟨123197674445437694859620237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82131782963625129906413491 123197674445437694859620237)
                ·
                  refine ⟨46199127917039135572357589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123197674445437694859620237 46199127917039135572357589)
                  ·
                    refine ⟨1082792060555604739977131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46199127917039135572357589 1082792060555604739977131)
                    ·
                      rfl

theorem cell22_3163095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3163095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163095 prefixEnd_3163095 := by exact prefixLift 3163095
  have htrace : WordTrace (prefixWord ++ tailWord_3163095) baseStart_3163095 baseEnd_3163095 := by
    simpa [prefixWord, tailWord_3163095, baseEnd_3163095] using wordTrace_append hprefix tailTrace_3163095
  have hstable : (prefixWord ++ tailWord_3163095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163095).length < 2 ^ (prefixWord ++ tailWord_3163095).sum := by decide
  have hdescent : baseEnd_3163095 < baseStart_3163095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163114 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_3163114 : Nat := 118140960795 + 3163114 * 2 ^ 59
def prefixEnd_3163114 : Nat := 4983230072969 + 3 ^ 40 * 3163114 * 2
def baseEnd_3163114 : Nat := 360932854881298341250691

theorem tailTrace_3163114 : CollatzResearch.WordTrace tailWord_3163114 prefixEnd_3163114 360932854881298341250691 := by
  unfold tailWord_3163114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842061365646417426862099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76912163641723779804965597 28842061365646417426862099)
  ·
    refine ⟨43263092048469626140293149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28842061365646417426862099 43263092048469626140293149)
    ·
      refine ⟨16223659518176109802609931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43263092048469626140293149 16223659518176109802609931)
      ·
        refine ⟨24335489277264164703914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16223659518176109802609931 24335489277264164703914897)
        ·
          refine ⟨18251616957948123527936173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24335489277264164703914897 18251616957948123527936173)
          ·
            refine ⟨6844356359230546322976065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18251616957948123527936173 6844356359230546322976065)
            ·
              refine ⟨5133267269422909742232049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844356359230546322976065 5133267269422909742232049)
              ·
                refine ⟨3849950452067182306674037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133267269422909742232049 3849950452067182306674037)
                ·
                  refine ⟨360932854881298341250691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849950452067182306674037 360932854881298341250691)
                  ·
                    rfl

theorem cell22_3163114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_3163114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163114 prefixEnd_3163114 := by exact prefixLift 3163114
  have htrace : WordTrace (prefixWord ++ tailWord_3163114) baseStart_3163114 baseEnd_3163114 := by
    simpa [prefixWord, tailWord_3163114, baseEnd_3163114] using wordTrace_append hprefix tailTrace_3163114
  have hstable : (prefixWord ++ tailWord_3163114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163114).length < 2 ^ (prefixWord ++ tailWord_3163114).sum := by decide
  have hdescent : baseEnd_3163114 < baseStart_3163114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163118 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3163118 : Nat := 118140960795 + 3163118 * 2 ^ 59
def prefixEnd_3163118 : Nat := 4983230072969 + 3 ^ 40 * 3163118 * 2
def baseEnd_3163118 : Nat := 1082799933925640346652061

theorem tailTrace_3163118 : CollatzResearch.WordTrace tailWord_3163118 prefixEnd_3163118 1082799933925640346652061 := by
  unfold tailWord_3163118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421048919321397298824251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76912260903047452260396005 14421048919321397298824251)
  ·
    refine ⟨21631573378982095948236377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14421048919321397298824251 21631573378982095948236377)
    ·
      refine ⟨16223680034236571961177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21631573378982095948236377 16223680034236571961177283)
      ·
        refine ⟨24335520051354857941765925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16223680034236571961177283 24335520051354857941765925)
        ·
          refine ⟨4562910009629035864081111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24335520051354857941765925 4562910009629035864081111)
          ·
            refine ⟨6844365014443553796121667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562910009629035864081111 6844365014443553796121667)
            ·
              refine ⟨10266547521665330694182501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844365014443553796121667 10266547521665330694182501)
              ·
                refine ⟨1924977660312249505159219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10266547521665330694182501 1924977660312249505159219)
                ·
                  refine ⟨2887466490468374257738829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924977660312249505159219 2887466490468374257738829)
                  ·
                    refine ⟨1082799933925640346652061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887466490468374257738829 1082799933925640346652061)
                    ·
                      rfl

theorem cell22_3163118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3163118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163118 prefixEnd_3163118 := by exact prefixLift 3163118
  have htrace : WordTrace (prefixWord ++ tailWord_3163118) baseStart_3163118 baseEnd_3163118 := by
    simpa [prefixWord, tailWord_3163118, baseEnd_3163118] using wordTrace_append hprefix tailTrace_3163118
  have hstable : (prefixWord ++ tailWord_3163118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163118).length < 2 ^ (prefixWord ++ tailWord_3163118).sum := by decide
  have hdescent : baseEnd_3163118 < baseStart_3163118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163206 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3163206 : Nat := 118140960795 + 3163206 * 2 ^ 59
def prefixEnd_3163206 : Nat := 4983230072969 + 3 ^ 40 * 3163206 * 2
def baseEnd_3163206 : Nat := 1082830058124037450451791

theorem tailTrace_3163206 : CollatzResearch.WordTrace tailWord_3163206 prefixEnd_3163206 1082830058124037450451791 := by
  unfold tailWord_3163206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605362530570386544368671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76914400652168246279864981 3605362530570386544368671)
  ·
    refine ⟨5408043795855579816553007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605362530570386544368671 5408043795855579816553007)
    ·
      refine ⟨8112065693783369724829511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408043795855579816553007 8112065693783369724829511)
      ·
        refine ⟨12168098540675054587244267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8112065693783369724829511 12168098540675054587244267)
        ·
          refine ⟨18252147811012581880866401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168098540675054587244267 18252147811012581880866401)
          ·
            refine ⟨13689110858259436410649801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18252147811012581880866401 13689110858259436410649801)
            ·
              refine ⟨10266833143694577307987351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13689110858259436410649801 10266833143694577307987351)
              ·
                refine ⟨15400249715541865961981027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10266833143694577307987351 15400249715541865961981027)
                ·
                  refine ⟨23100374573312798942971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15400249715541865961981027 23100374573312798942971541)
                  ·
                    refine ⟨1082830058124037450451791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23100374573312798942971541 1082830058124037450451791)
                    ·
                      rfl

theorem cell22_3163206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3163206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163206 prefixEnd_3163206 := by exact prefixLift 3163206
  have htrace : WordTrace (prefixWord ++ tailWord_3163206) baseStart_3163206 baseEnd_3163206 := by
    simpa [prefixWord, tailWord_3163206, baseEnd_3163206] using wordTrace_append hprefix tailTrace_3163206
  have hstable : (prefixWord ++ tailWord_3163206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163206).length < 2 ^ (prefixWord ++ tailWord_3163206).sum := by decide
  have hdescent : baseEnd_3163206 < baseStart_3163206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163232 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_3163232 : Nat := 118140960795 + 3163232 * 2 ^ 59
def prefixEnd_3163232 : Nat := 4983230072969 + 3 ^ 40 * 3163232 * 2
def baseEnd_3163232 : Nat := 360946319485127349767237

theorem tailTrace_3163232 : CollatzResearch.WordTrace tailWord_3163232 prefixEnd_3163232 360946319485127349767237 := by
  unfold tailWord_3163232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57686274638079087930121975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76915032850772117240162633 57686274638079087930121975)
  ·
    refine ⟨86529411957118631895182963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57686274638079087930121975 86529411957118631895182963)
    ·
      refine ⟨129794117935677947842774445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86529411957118631895182963 129794117935677947842774445)
      ·
        refine ⟨48672794225879230441040417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129794117935677947842774445 48672794225879230441040417)
        ·
          refine ⟨36504595669409422830780313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48672794225879230441040417 36504595669409422830780313)
          ·
            refine ⟨27378446752057067123085235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36504595669409422830780313 27378446752057067123085235)
            ·
              refine ⟨41067670128085600684627853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27378446752057067123085235 41067670128085600684627853)
              ·
                refine ⟨15400376298032100256735445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41067670128085600684627853 15400376298032100256735445)
                ·
                  refine ⟨360946319485127349767237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15400376298032100256735445 360946319485127349767237)
                  ·
                    rfl

theorem cell22_3163232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_3163232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163232 prefixEnd_3163232 := by exact prefixLift 3163232
  have htrace : WordTrace (prefixWord ++ tailWord_3163232) baseStart_3163232 baseEnd_3163232 := by
    simpa [prefixWord, tailWord_3163232, baseEnd_3163232] using wordTrace_append hprefix tailTrace_3163232
  have hstable : (prefixWord ++ tailWord_3163232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163232).length < 2 ^ (prefixWord ++ tailWord_3163232).sum := by decide
  have hdescent : baseEnd_3163232 < baseStart_3163232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163247 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3163247 : Nat := 118140960795 + 3163247 * 2 ^ 59
def prefixEnd_3163247 : Nat := 4983230072969 + 3 ^ 40 * 3163247 * 2
def baseEnd_3163247 : Nat := 1082844093261927010176665

theorem tailTrace_3163247 : CollatzResearch.WordTrace tailWord_3163247 prefixEnd_3163247 1082844093261927010176665 := by
  unfold tailWord_3163247
  simp only [CollatzResearch.WordTrace]
  refine ⟨115373096371103833422039995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76915397580735888948026663 115373096371103833422039995)
  ·
    refine ⟨173059644556655750133059993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115373096371103833422039995 173059644556655750133059993)
    ·
      refine ⟨129794733417491812599794995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173059644556655750133059993 129794733417491812599794995)
      ·
        refine ⟨194692100126237718899692493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129794733417491812599794995 194692100126237718899692493)
        ·
          refine ⟨73009537547339144587384685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194692100126237718899692493 73009537547339144587384685)
          ·
            refine ⟨27378576580252179220269257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73009537547339144587384685 27378576580252179220269257)
            ·
              refine ⟨20533932435189134415201943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27378576580252179220269257 20533932435189134415201943)
              ·
                refine ⟨30800898652783701622802915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20533932435189134415201943 30800898652783701622802915)
                ·
                  refine ⟨46201347979175552434204373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30800898652783701622802915 46201347979175552434204373)
                  ·
                    refine ⟨1082844093261927010176665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46201347979175552434204373 1082844093261927010176665)
                    ·
                      rfl

theorem cell22_3163247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3163247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163247 prefixEnd_3163247 := by exact prefixLift 3163247
  have htrace : WordTrace (prefixWord ++ tailWord_3163247) baseStart_3163247 baseEnd_3163247 := by
    simpa [prefixWord, tailWord_3163247, baseEnd_3163247] using wordTrace_append hprefix tailTrace_3163247
  have hstable : (prefixWord ++ tailWord_3163247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163247).length < 2 ^ (prefixWord ++ tailWord_3163247).sum := by decide
  have hdescent : baseEnd_3163247 < baseStart_3163247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163326 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_3163326 : Nat := 118140960795 + 3163326 * 2 ^ 59
def prefixEnd_3163326 : Nat := 4983230072969 + 3 ^ 40 * 3163326 * 2
def baseEnd_3163326 : Nat := 1082871136576397137451423

theorem tailTrace_3163326 : CollatzResearch.WordTrace tailWord_3163326 prefixEnd_3163326 1082871136576397137451423 := by
  unfold tailWord_3163326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421997217227203739270729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76917318491878419942777221 14421997217227203739270729)
  ·
    refine ⟨10816497912920402804453047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14421997217227203739270729 10816497912920402804453047)
    ·
      refine ⟨16224746869380604206679571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10816497912920402804453047 16224746869380604206679571)
      ·
        refine ⟨24337120304070906310019357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16224746869380604206679571 24337120304070906310019357)
        ·
          refine ⟨9126420114026589866257259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24337120304070906310019357 9126420114026589866257259)
          ·
            refine ⟨13689630171039884799385889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126420114026589866257259 13689630171039884799385889)
            ·
              refine ⟨10267222628279913599539417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13689630171039884799385889 10267222628279913599539417)
              ·
                refine ⟨7700416971209935199654563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267222628279913599539417 7700416971209935199654563)
                ·
                  refine ⟨11550625456814902799481845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700416971209935199654563 11550625456814902799481845)
                  ·
                    refine ⟨1082871136576397137451423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11550625456814902799481845 1082871136576397137451423)
                    ·
                      rfl

theorem cell22_3163326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_3163326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163326 prefixEnd_3163326 := by exact prefixLift 3163326
  have htrace : WordTrace (prefixWord ++ tailWord_3163326) baseStart_3163326 baseEnd_3163326 := by
    simpa [prefixWord, tailWord_3163326, baseEnd_3163326] using wordTrace_append hprefix tailTrace_3163326
  have hstable : (prefixWord ++ tailWord_3163326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163326).length < 2 ^ (prefixWord ++ tailWord_3163326).sum := by decide
  have hdescent : baseEnd_3163326 < baseStart_3163326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163328 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_3163328 : Nat := 118140960795 + 3163328 * 2 ^ 59
def prefixEnd_3163328 : Nat := 4983230072969 + 3 ^ 40 * 3163328 * 2
def baseEnd_3163328 : Nat := 360957273739089932967139

theorem tailTrace_3163328 : CollatzResearch.WordTrace tailWord_3163328 prefixEnd_3163328 360957273739089932967139 := by
  unfold tailWord_3163328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57688025341905192127869319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76917367122540256170492425 57688025341905192127869319)
  ·
    refine ⟨86532038012857788191803979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57688025341905192127869319 86532038012857788191803979)
    ·
      refine ⟨129798057019286682287705969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86532038012857788191803979 129798057019286682287705969)
      ·
        refine ⟨97348542764465011715779477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129798057019286682287705969 97348542764465011715779477)
        ·
          refine ⟨4563212942084297424177163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97348542764465011715779477 4563212942084297424177163)
          ·
            refine ⟨6844819413126446136265745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563212942084297424177163 6844819413126446136265745)
            ·
              refine ⟨5133614559844834602199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844819413126446136265745 5133614559844834602199309)
              ·
                refine ⟨1925105459941812975824741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5133614559844834602199309 1925105459941812975824741)
                ·
                  refine ⟨360957273739089932967139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925105459941812975824741 360957273739089932967139)
                  ·
                    rfl

theorem cell22_3163328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_3163328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163328 prefixEnd_3163328 := by exact prefixLift 3163328
  have htrace : WordTrace (prefixWord ++ tailWord_3163328) baseStart_3163328 baseEnd_3163328 := by
    simpa [prefixWord, tailWord_3163328, baseEnd_3163328] using wordTrace_append hprefix tailTrace_3163328
  have hstable : (prefixWord ++ tailWord_3163328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163328).length < 2 ^ (prefixWord ++ tailWord_3163328).sum := by decide
  have hdescent : baseEnd_3163328 < baseStart_3163328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163334 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3163334 : Nat := 118140960795 + 3163334 * 2 ^ 59
def prefixEnd_3163334 : Nat := 4983230072969 + 3 ^ 40 * 3163334 * 2
def baseEnd_3163334 : Nat := 360957958379962594417133

theorem tailTrace_3163334 : CollatzResearch.WordTrace tailWord_3163334 prefixEnd_3163334 360957958379962594417133 := by
  unfold tailWord_3163334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605508422555895227514283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76917513014525764853638037 3605508422555895227514283)
  ·
    refine ⟨5408262633833842841271425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605508422555895227514283 5408262633833842841271425)
    ·
      refine ⟨4056196975375382130953569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5408262633833842841271425 4056196975375382130953569)
      ·
        refine ⟨3042147731531536598215177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4056196975375382130953569 3042147731531536598215177)
        ·
          refine ⟨2281610798648652448661383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3042147731531536598215177 2281610798648652448661383)
          ·
            refine ⟨3422416197972978672992075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281610798648652448661383 3422416197972978672992075)
            ·
              refine ⟨5133624296959468009488113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422416197972978672992075 5133624296959468009488113)
              ·
                refine ⟨3850218222719601007116085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133624296959468009488113 3850218222719601007116085)
                ·
                  refine ⟨360957958379962594417133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850218222719601007116085 360957958379962594417133)
                  ·
                    rfl

theorem cell22_3163334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3163334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163334 prefixEnd_3163334 := by exact prefixLift 3163334
  have htrace : WordTrace (prefixWord ++ tailWord_3163334) baseStart_3163334 baseEnd_3163334 := by
    simpa [prefixWord, tailWord_3163334, baseEnd_3163334] using wordTrace_append hprefix tailTrace_3163334
  have hstable : (prefixWord ++ tailWord_3163334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163334).length < 2 ^ (prefixWord ++ tailWord_3163334).sum := by decide
  have hdescent : baseEnd_3163334 < baseStart_3163334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163371 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 3, 3]
def baseStart_3163371 : Nat := 118140960795 + 3163371 * 2 ^ 59
def prefixEnd_3163371 : Nat := 4983230072969 + 3 ^ 40 * 3163371 * 2
def baseEnd_3163371 : Nat := 1082886540996032020076285

theorem tailTrace_3163371 : CollatzResearch.WordTrace tailWord_3163371 prefixEnd_3163371 1082886540996032020076285 := by
  unfold tailWord_3163371
  simp only [CollatzResearch.WordTrace]
  refine ⟨115377619022654602599553967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76918412681769735066369311 115377619022654602599553967)
  ·
    refine ⟨173066428533981903899330951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115377619022654602599553967 173066428533981903899330951)
    ·
      refine ⟨259599642800972855848996427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173066428533981903899330951 259599642800972855848996427)
      ·
        refine ⟨389399464201459283773494641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259599642800972855848996427 389399464201459283773494641)
        ·
          refine ⟨292049598151094462830120981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389399464201459283773494641 292049598151094462830120981)
          ·
            refine ⟨13689824913332552945161921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292049598151094462830120981 13689824913332552945161921)
            ·
              refine ⟨10267368684999414708871441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13689824913332552945161921 10267368684999414708871441)
              ·
                refine ⟨7700526513749561031653581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267368684999414708871441 7700526513749561031653581)
                ·
                  refine ⟨2887697442656085386870093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7700526513749561031653581 2887697442656085386870093)
                  ·
                    refine ⟨1082886540996032020076285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887697442656085386870093 1082886540996032020076285)
                    ·
                      rfl

theorem cell22_3163371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].length) (baseStart_3163371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163371 prefixEnd_3163371 := by exact prefixLift 3163371
  have htrace : WordTrace (prefixWord ++ tailWord_3163371) baseStart_3163371 baseEnd_3163371 := by
    simpa [prefixWord, tailWord_3163371, baseEnd_3163371] using wordTrace_append hprefix tailTrace_3163371
  have hstable : (prefixWord ++ tailWord_3163371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163371).length < 2 ^ (prefixWord ++ tailWord_3163371).sum := by decide
  have hdescent : baseEnd_3163371 < baseStart_3163371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163373 : List Nat := [1, 5, 1, 2, 2, 3, 2, 6]
def baseStart_3163373 : Nat := 118140960795 + 3163373 * 2 ^ 59
def prefixEnd_3163373 : Nat := 4983230072969 + 3 ^ 40 * 3163373 * 2
def baseEnd_3163373 : Nat := 120320802848544964614031

theorem tailTrace_3163373 : CollatzResearch.WordTrace tailWord_3163373 prefixEnd_3163373 120320802848544964614031 := by
  unfold tailWord_3163373
  simp only [CollatzResearch.WordTrace]
  refine ⟨115377691968647356941126773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76918461312431571294084515 115377691968647356941126773)
  ·
    refine ⟨10816658622060689713230635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115377691968647356941126773 10816658622060689713230635)
    ·
      refine ⟨16224987933091034569845953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10816658622060689713230635 16224987933091034569845953)
      ·
        refine ⟨12168740949818275927384465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16224987933091034569845953 12168740949818275927384465)
        ·
          refine ⟨9126555712363706945538349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12168740949818275927384465 9126555712363706945538349)
          ·
            refine ⟨3422458392136390104576881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9126555712363706945538349 3422458392136390104576881)
            ·
              refine ⟨2566843794102292578432661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422458392136390104576881 2566843794102292578432661)
              ·
                refine ⟨120320802848544964614031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2566843794102292578432661 120320802848544964614031)
                ·
                  rfl

theorem cell22_3163373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 6].length) (baseStart_3163373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163373 prefixEnd_3163373 := by exact prefixLift 3163373
  have htrace : WordTrace (prefixWord ++ tailWord_3163373) baseStart_3163373 baseEnd_3163373 := by
    simpa [prefixWord, tailWord_3163373, baseEnd_3163373] using wordTrace_append hprefix tailTrace_3163373
  have hstable : (prefixWord ++ tailWord_3163373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163373).length < 2 ^ (prefixWord ++ tailWord_3163373).sum := by decide
  have hdescent : baseEnd_3163373 < baseStart_3163373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163418 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_3163418 : Nat := 118140960795 + 3163418 * 2 ^ 59
def prefixEnd_3163418 : Nat := 4983230072969 + 3 ^ 40 * 3163418 * 2
def baseEnd_3163418 : Nat := 360967543352179854717047

theorem tailTrace_3163418 : CollatzResearch.WordTrace tailWord_3163418 prefixEnd_3163418 360967543352179854717047 := by
  unfold tailWord_3163418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844833313371082406628727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76919555502322886417676605 28844833313371082406628727)
  ·
    refine ⟨43267249970056623609943091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28844833313371082406628727 43267249970056623609943091)
    ·
      refine ⟨64900874955084935414914637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43267249970056623609943091 64900874955084935414914637)
      ·
        refine ⟨24337828108156850780592989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64900874955084935414914637 24337828108156850780592989)
        ·
          refine ⟨9126685540558819042722371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24337828108156850780592989 9126685540558819042722371)
          ·
            refine ⟨13690028310838228564083557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126685540558819042722371 13690028310838228564083557)
            ·
              refine ⟨2566880308282167855765667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13690028310838228564083557 2566880308282167855765667)
              ·
                refine ⟨3850320462423251783648501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566880308282167855765667 3850320462423251783648501)
                ·
                  refine ⟨360967543352179854717047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850320462423251783648501 360967543352179854717047)
                  ·
                    rfl

theorem cell22_3163418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_3163418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163418 prefixEnd_3163418 := by exact prefixLift 3163418
  have htrace : WordTrace (prefixWord ++ tailWord_3163418) baseStart_3163418 baseEnd_3163418 := by
    simpa [prefixWord, tailWord_3163418, baseEnd_3163418] using wordTrace_append hprefix tailTrace_3163418
  have hstable : (prefixWord ++ tailWord_3163418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163418).length < 2 ^ (prefixWord ++ tailWord_3163418).sum := by decide
  have hdescent : baseEnd_3163418 < baseStart_3163418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163459 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_3163459 : Nat := 118140960795 + 3163459 * 2 ^ 59
def prefixEnd_3163459 : Nat := 4983230072969 + 3 ^ 40 * 3163459 * 2
def baseEnd_3163459 : Nat := 1082916665194429123876015

theorem tailTrace_3163459 : CollatzResearch.WordTrace tailWord_3163459 prefixEnd_3163459 1082916665194429123876015 := by
  unfold tailWord_3163459
  simp only [CollatzResearch.WordTrace]
  refine ⟨115380828646335793628757431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76920552430890529085838287 115380828646335793628757431)
  ·
    refine ⟨173071242969503690443136147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115380828646335793628757431 173071242969503690443136147)
    ·
      refine ⟨259606864454255535664704221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173071242969503690443136147 259606864454255535664704221)
      ·
        refine ⟨97352574170345825874264083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259606864454255535664704221 97352574170345825874264083)
        ·
          refine ⟨146028861255518738811396125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97352574170345825874264083 146028861255518738811396125)
          ·
            refine ⟨54760822970819527054273547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146028861255518738811396125 54760822970819527054273547)
            ·
              refine ⟨82141234456229290581410321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54760822970819527054273547 82141234456229290581410321)
              ·
                refine ⟨61605925842171967936057741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82141234456229290581410321 61605925842171967936057741)
                ·
                  refine ⟨23102222190814487976021653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61605925842171967936057741 23102222190814487976021653)
                  ·
                    refine ⟨1082916665194429123876015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23102222190814487976021653 1082916665194429123876015)
                    ·
                      rfl

theorem cell22_3163459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_3163459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163459 prefixEnd_3163459 := by exact prefixLift 3163459
  have htrace : WordTrace (prefixWord ++ tailWord_3163459) baseStart_3163459 baseEnd_3163459 := by
    simpa [prefixWord, tailWord_3163459, baseEnd_3163459] using wordTrace_append hprefix tailTrace_3163459
  have hstable : (prefixWord ++ tailWord_3163459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163459).length < 2 ^ (prefixWord ++ tailWord_3163459).sum := by decide
  have hdescent : baseEnd_3163459 < baseStart_3163459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163461 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_3163461 : Nat := 118140960795 + 3163461 * 2 ^ 59
def prefixEnd_3163461 : Nat := 4983230072969 + 3 ^ 40 * 3163461 * 2
def baseEnd_3163461 : Nat := 1082917349835301785326009

theorem tailTrace_3163461 : CollatzResearch.WordTrace tailWord_3163461 prefixEnd_3163461 1082917349835301785326009 := by
  unfold tailWord_3163461
  simp only [CollatzResearch.WordTrace]
  refine ⟨115380901592328547970330237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76920601061552365313553491 115380901592328547970330237)
  ·
    refine ⟨43267838097123205488873839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115380901592328547970330237 43267838097123205488873839)
    ·
      refine ⟨64901757145684808233310759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43267838097123205488873839 64901757145684808233310759)
      ·
        refine ⟨97352635718527212349966139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64901757145684808233310759 97352635718527212349966139)
        ·
          refine ⟨146028953577790818524949209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97352635718527212349966139 146028953577790818524949209)
          ·
            refine ⟨109521715183343113893711907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146028953577790818524949209 109521715183343113893711907)
            ·
              refine ⟨164282572775014670840567861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109521715183343113893711907 164282572775014670840567861)
              ·
                refine ⟨15401491197657625391303237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164282572775014670840567861 15401491197657625391303237)
                ·
                  refine ⟨2887779599560804760869357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15401491197657625391303237 2887779599560804760869357)
                  ·
                    refine ⟨1082917349835301785326009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887779599560804760869357 1082917349835301785326009)
                    ·
                      rfl

theorem cell22_3163461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_3163461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163461 prefixEnd_3163461 := by exact prefixLift 3163461
  have htrace : WordTrace (prefixWord ++ tailWord_3163461) baseStart_3163461 baseEnd_3163461 := by
    simpa [prefixWord, tailWord_3163461, baseEnd_3163461] using wordTrace_append hprefix tailTrace_3163461
  have hstable : (prefixWord ++ tailWord_3163461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163461).length < 2 ^ (prefixWord ++ tailWord_3163461).sum := by decide
  have hdescent : baseEnd_3163461 < baseStart_3163461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163463 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 4]
def baseStart_3163463 : Nat := 118140960795 + 3163463 * 2 ^ 59
def prefixEnd_3163463 : Nat := 4983230072969 + 3 ^ 40 * 3163463 * 2
def baseEnd_3163463 : Nat := 360972678158724815592001

theorem tailTrace_3163463 : CollatzResearch.WordTrace tailWord_3163463 prefixEnd_3163463 360972678158724815592001 := by
  unfold tailWord_3163463
  simp only [CollatzResearch.WordTrace]
  refine ⟨115380974538321302311903043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76920649692214201541268695 115380974538321302311903043)
  ·
    refine ⟨173071461807481953467854565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115380974538321302311903043 173071461807481953467854565)
    ·
      refine ⟨32450899088902866275222731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173071461807481953467854565 32450899088902866275222731)
      ·
        refine ⟨48676348633354299412834097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32450899088902866275222731 48676348633354299412834097)
        ·
          refine ⟨36507261475015724559625573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48676348633354299412834097 36507261475015724559625573)
          ·
            refine ⟨6845111526565448354929795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36507261475015724559625573 6845111526565448354929795)
            ·
              refine ⟨10267667289848172532394693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845111526565448354929795 10267667289848172532394693)
              ·
                refine ⟨1925187616846532349824005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10267667289848172532394693 1925187616846532349824005)
                ·
                  refine ⟨360972678158724815592001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925187616846532349824005 360972678158724815592001)
                  ·
                    rfl

theorem cell22_3163463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 4].length) (baseStart_3163463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163463 prefixEnd_3163463 := by exact prefixLift 3163463
  have htrace : WordTrace (prefixWord ++ tailWord_3163463) baseStart_3163463 baseEnd_3163463 := by
    simpa [prefixWord, tailWord_3163463, baseEnd_3163463] using wordTrace_append hprefix tailTrace_3163463
  have hstable : (prefixWord ++ tailWord_3163463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163463).length < 2 ^ (prefixWord ++ tailWord_3163463).sum := by decide
  have hdescent : baseEnd_3163463 < baseStart_3163463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163476 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3163476 : Nat := 118140960795 + 3163476 * 2 ^ 59
def prefixEnd_3163476 : Nat := 4983230072969 + 3 ^ 40 * 3163476 * 2
def baseEnd_3163476 : Nat := 1082922484641846746200963

theorem tailTrace_3163476 : CollatzResearch.WordTrace tailWord_3163476 prefixEnd_3163476 1082922484641846746200963 := by
  unfold tailWord_3163476
  simp only [CollatzResearch.WordTrace]
  refine ⟨57690724343637102766063141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76920965791516137021417521 57690724343637102766063141)
  ·
    refine ⟨10817010814431956768636839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57690724343637102766063141 10817010814431956768636839)
    ·
      refine ⟨16225516221647935152955259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817010814431956768636839 16225516221647935152955259)
      ·
        refine ⟨24338274332471902729432889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16225516221647935152955259 24338274332471902729432889)
        ·
          refine ⟨18253705749353927047074667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24338274332471902729432889 18253705749353927047074667)
          ·
            refine ⟨27380558624030890570612001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18253705749353927047074667 27380558624030890570612001)
            ·
              refine ⟨20535418968023167927959001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27380558624030890570612001 20535418968023167927959001)
              ·
                refine ⟨15401564226017375945969251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20535418968023167927959001 15401564226017375945969251)
                ·
                  refine ⟨23102346339026063918953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15401564226017375945969251 23102346339026063918953877)
                  ·
                    refine ⟨1082922484641846746200963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23102346339026063918953877 1082922484641846746200963)
                    ·
                      rfl

theorem cell22_3163476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3163476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163476 prefixEnd_3163476 := by exact prefixLift 3163476
  have htrace : WordTrace (prefixWord ++ tailWord_3163476) baseStart_3163476 baseEnd_3163476 := by
    simpa [prefixWord, tailWord_3163476, baseEnd_3163476] using wordTrace_append hprefix tailTrace_3163476
  have hstable : (prefixWord ++ tailWord_3163476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163476).length < 2 ^ (prefixWord ++ tailWord_3163476).sum := by decide
  have hdescent : baseEnd_3163476 < baseStart_3163476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163523 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 3, 3]
def baseStart_3163523 : Nat := 118140960795 + 3163523 * 2 ^ 59
def prefixEnd_3163523 : Nat := 4983230072969 + 3 ^ 40 * 3163523 * 2
def baseEnd_3163523 : Nat := 1082938573702354290275819

theorem tailTrace_3163523 : CollatzResearch.WordTrace tailWord_3163523 prefixEnd_3163523 1082938573702354290275819 := by
  unfold tailWord_3163523
  simp only [CollatzResearch.WordTrace]
  refine ⟨115383162918103932559087223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76922108612069288372724815 115383162918103932559087223)
  ·
    refine ⟨173074744377155898838630835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115383162918103932559087223 173074744377155898838630835)
    ·
      refine ⟨259612116565733848257946253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173074744377155898838630835 259612116565733848257946253)
      ·
        refine ⟨97354543712150193096729845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259612116565733848257946253 97354543712150193096729845)
        ·
          refine ⟨9126988473014080602818423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97354543712150193096729845 9126988473014080602818423)
          ·
            refine ⟨13690482709521120904227635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126988473014080602818423 13690482709521120904227635)
            ·
              refine ⟨20535724064281681356341453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690482709521120904227635 20535724064281681356341453)
              ·
                refine ⟨7700896524105630508628045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20535724064281681356341453 7700896524105630508628045)
                ·
                  refine ⟨2887836196539611440735517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7700896524105630508628045 2887836196539611440735517)
                  ·
                    refine ⟨1082938573702354290275819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887836196539611440735517 1082938573702354290275819)
                    ·
                      rfl

theorem cell22_3163523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].length) (baseStart_3163523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163523 prefixEnd_3163523 := by exact prefixLift 3163523
  have htrace : WordTrace (prefixWord ++ tailWord_3163523) baseStart_3163523 baseEnd_3163523 := by
    simpa [prefixWord, tailWord_3163523, baseEnd_3163523] using wordTrace_append hprefix tailTrace_3163523
  have hstable : (prefixWord ++ tailWord_3163523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163523).length < 2 ^ (prefixWord ++ tailWord_3163523).sum := by decide
  have hdescent : baseEnd_3163523 < baseStart_3163523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163540 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3163540 : Nat := 118140960795 + 3163540 * 2 ^ 59
def prefixEnd_3163540 : Nat := 4983230072969 + 3 ^ 40 * 3163540 * 2
def baseEnd_3163540 : Nat := 1082944393149771912600767

theorem tailTrace_3163540 : CollatzResearch.WordTrace tailWord_3163540 prefixEnd_3163540 1082944393149771912600767 := by
  unfold tailWord_3163540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57691891479521172231228037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76922521972694896308304049 57691891479521172231228037)
  ·
    refine ⟨10817229652410219793355257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57691891479521172231228037 10817229652410219793355257)
    ·
      refine ⟨8112922239307664845016443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10817229652410219793355257 8112922239307664845016443)
      ·
        refine ⟨12169383358961497267524665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8112922239307664845016443 12169383358961497267524665)
        ·
          refine ⟨9127037519221122950643499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12169383358961497267524665 9127037519221122950643499)
          ·
            refine ⟨13690556278831684425965249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9127037519221122950643499 13690556278831684425965249)
            ·
              refine ⟨10267917209123763319473937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13690556278831684425965249 10267917209123763319473937)
              ·
                refine ⟨7700937906842822489605453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267917209123763319473937 7700937906842822489605453)
                ·
                  refine ⟨2887851715066058433602045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7700937906842822489605453 2887851715066058433602045)
                  ·
                    refine ⟨1082944393149771912600767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887851715066058433602045 1082944393149771912600767)
                    ·
                      rfl

theorem cell22_3163540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3163540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163540 prefixEnd_3163540 := by exact prefixLift 3163540
  have htrace : WordTrace (prefixWord ++ tailWord_3163540) baseStart_3163540 baseEnd_3163540 := by
    simpa [prefixWord, tailWord_3163540, baseEnd_3163540] using wordTrace_append hprefix tailTrace_3163540
  have hstable : (prefixWord ++ tailWord_3163540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163540).length < 2 ^ (prefixWord ++ tailWord_3163540).sum := by decide
  have hdescent : baseEnd_3163540 < baseStart_3163540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163613 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3163613 : Nat := 118140960795 + 3163613 * 2 ^ 59
def prefixEnd_3163613 : Nat := 4983230072969 + 3 ^ 40 * 3163613 * 2
def baseEnd_3163613 : Nat := 1082969382541624055525543

theorem tailTrace_3163613 : CollatzResearch.WordTrace tailWord_3163613 prefixEnd_3163613 1082969382541624055525543 := by
  unfold tailWord_3163613
  simp only [CollatzResearch.WordTrace]
  refine ⟨115386445487777877929863493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76924296991851918619908995 115386445487777877929863493)
  ·
    refine ⟨21634958528958352111849405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115386445487777877929863493 21634958528958352111849405)
    ·
      refine ⟨8113109448359382041943527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21634958528958352111849405 8113109448359382041943527)
      ·
        refine ⟨12169664172539073062915291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113109448359382041943527 12169664172539073062915291)
        ·
          refine ⟨18254496258808609594372937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12169664172539073062915291 18254496258808609594372937)
          ·
            refine ⟨13690872194106457195779703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18254496258808609594372937 13690872194106457195779703)
            ·
              refine ⟨20536308291159685793669555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690872194106457195779703 20536308291159685793669555)
              ·
                refine ⟨30804462436739528690504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20536308291159685793669555 30804462436739528690504333)
                ·
                  refine ⟨11551673413777323258939125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30804462436739528690504333 11551673413777323258939125)
                  ·
                    refine ⟨1082969382541624055525543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11551673413777323258939125 1082969382541624055525543)
                    ·
                      rfl

theorem cell22_3163613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3163613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163613 prefixEnd_3163613 := by exact prefixLift 3163613
  have htrace : WordTrace (prefixWord ++ tailWord_3163613) baseStart_3163613 baseEnd_3163613 := by
    simpa [prefixWord, tailWord_3163613, baseEnd_3163613] using wordTrace_append hprefix tailTrace_3163613
  have hstable : (prefixWord ++ tailWord_3163613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163613).length < 2 ^ (prefixWord ++ tailWord_3163613).sum := by decide
  have hdescent : baseEnd_3163613 < baseStart_3163613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163626 : List Nat := [3, 1, 3, 1, 14]
def baseStart_3163626 : Nat := 118140960795 + 3163626 * 2 ^ 59
def prefixEnd_3163626 : Nat := 4983230072969 + 3 ^ 40 * 3163626 * 2
def baseEnd_3163626 : Nat := 4456682439124676357821

theorem tailTrace_3163626 : CollatzResearch.WordTrace tailWord_3163626 prefixEnd_3163626 4456682439124676357821 := by
  unfold tailWord_3163626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846729909182695287521683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76924613091153854100057821 28846729909182695287521683)
  ·
    refine ⟨43270094863774042931282525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28846729909182695287521683 43270094863774042931282525)
    ·
      refine ⟨16226285573915266099230947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43270094863774042931282525 16226285573915266099230947)
      ·
        refine ⟨24339428360872899148846421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226285573915266099230947 24339428360872899148846421)
        ·
          refine ⟨4456682439124676357821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24339428360872899148846421 4456682439124676357821)
          ·
            rfl

theorem cell22_3163626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 14].length) (baseStart_3163626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163626 prefixEnd_3163626 := by exact prefixLift 3163626
  have htrace : WordTrace (prefixWord ++ tailWord_3163626) baseStart_3163626 baseEnd_3163626 := by
    simpa [prefixWord, tailWord_3163626, baseEnd_3163626] using wordTrace_append hprefix tailTrace_3163626
  have hstable : (prefixWord ++ tailWord_3163626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163626).length < 2 ^ (prefixWord ++ tailWord_3163626).sum := by decide
  have hdescent : baseEnd_3163626 < baseStart_3163626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163632 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_3163632 : Nat := 118140960795 + 3163632 * 2 ^ 59
def prefixEnd_3163632 : Nat := 4983230072969 + 3 ^ 40 * 3163632 * 2
def baseEnd_3163632 : Nat := 360991962209971446433495

theorem tailTrace_3163632 : CollatzResearch.WordTrace tailWord_3163632 prefixEnd_3163632 360991962209971446433495 := by
  unfold tailWord_3163632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57693569237354522087402575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76924758983139362783203433 57693569237354522087402575)
  ·
    refine ⟨86540353856031783131103863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57693569237354522087402575 86540353856031783131103863)
    ·
      refine ⟨129810530784047674696655795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86540353856031783131103863 129810530784047674696655795)
      ·
        refine ⟨194715796176071512044983693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129810530784047674696655795 194715796176071512044983693)
        ·
          refine ⟨73018423566026817016868885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194715796176071512044983693 73018423566026817016868885)
          ·
            refine ⟨3422738604657507047665729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73018423566026817016868885 3422738604657507047665729)
            ·
              refine ⟨2567053953493130285749297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422738604657507047665729 2567053953493130285749297)
              ·
                refine ⟨1925290465119847714311973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567053953493130285749297 1925290465119847714311973)
                ·
                  refine ⟨360991962209971446433495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925290465119847714311973 360991962209971446433495)
                  ·
                    rfl

theorem cell22_3163632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_3163632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163632 prefixEnd_3163632 := by exact prefixLift 3163632
  have htrace : WordTrace (prefixWord ++ tailWord_3163632) baseStart_3163632 baseEnd_3163632 := by
    simpa [prefixWord, tailWord_3163632, baseEnd_3163632] using wordTrace_append hprefix tailTrace_3163632
  have hstable : (prefixWord ++ tailWord_3163632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163632).length < 2 ^ (prefixWord ++ tailWord_3163632).sum := by decide
  have hdescent : baseEnd_3163632 < baseStart_3163632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163641 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3163641 : Nat := 118140960795 + 3163641 * 2 ^ 59
def prefixEnd_3163641 : Nat := 4983230072969 + 3 ^ 40 * 3163641 * 2
def baseEnd_3163641 : Nat := 1082978967513841315825457

theorem tailTrace_3163641 : CollatzResearch.WordTrace tailWord_3163641 prefixEnd_3163641 1082978967513841315825457 := by
  unfold tailWord_3163641
  simp only [CollatzResearch.WordTrace]
  refine ⟨115387466731676438711882777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76924977821117625807921851 115387466731676438711882777)
  ·
    refine ⟨86540600048757329033912083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115387466731676438711882777 86540600048757329033912083)
    ·
      refine ⟨129810900073135993550868125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86540600048757329033912083 129810900073135993550868125)
      ·
        refine ⟨48679087527425997581575547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129810900073135993550868125 48679087527425997581575547)
        ·
          refine ⟨73018631291138996372363321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48679087527425997581575547 73018631291138996372363321)
          ·
            refine ⟨54763973468354247279272491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73018631291138996372363321 54763973468354247279272491)
            ·
              refine ⟨82145960202531370918908737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54763973468354247279272491 82145960202531370918908737)
              ·
                refine ⟨61609470151898528189181553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82145960202531370918908737 61609470151898528189181553)
                ·
                  refine ⟨46207102613923896141886165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61609470151898528189181553 46207102613923896141886165)
                  ·
                    refine ⟨1082978967513841315825457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46207102613923896141886165 1082978967513841315825457)
                    ·
                      rfl

theorem cell22_3163641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3163641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163641 prefixEnd_3163641 := by exact prefixLift 3163641
  have htrace : WordTrace (prefixWord ++ tailWord_3163641) baseStart_3163641 baseEnd_3163641 := by
    simpa [prefixWord, tailWord_3163641, baseEnd_3163641] using wordTrace_append hprefix tailTrace_3163641
  have hstable : (prefixWord ++ tailWord_3163641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163641).length < 2 ^ (prefixWord ++ tailWord_3163641).sum := by decide
  have hdescent : baseEnd_3163641 < baseStart_3163641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163660 : List Nat := [2, 2, 1, 2, 5, 1, 3, 6]
def baseStart_3163660 : Nat := 118140960795 + 3163660 * 2 ^ 59
def prefixEnd_3163660 : Nat := 4983230072969 + 3 ^ 40 * 3163660 * 2
def baseEnd_3163660 : Nat := 120331719066903511066711

theorem tailTrace_3163660 : CollatzResearch.WordTrace tailWord_3163660 prefixEnd_3163660 120331719066903511066711 := by
  unfold tailWord_3163660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57694079859303802478412217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76925439812405069971216289 57694079859303802478412217)
  ·
    refine ⟨43270559894477851858809163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57694079859303802478412217 43270559894477851858809163)
    ·
      refine ⟨64905839841716777788213745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43270559894477851858809163 64905839841716777788213745)
      ·
        refine ⟨48679379881287583341160309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64905839841716777788213745 48679379881287583341160309)
        ·
          refine ⟨4563691863870710938233779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48679379881287583341160309 4563691863870710938233779)
          ·
            refine ⟨6845537795806066407350669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563691863870710938233779 6845537795806066407350669)
            ·
              refine ⟨2567076673427274902756501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6845537795806066407350669 2567076673427274902756501)
              ·
                refine ⟨120331719066903511066711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2567076673427274902756501 120331719066903511066711)
                ·
                  rfl

theorem cell22_3163660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_3163660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163660 prefixEnd_3163660 := by exact prefixLift 3163660
  have htrace : WordTrace (prefixWord ++ tailWord_3163660) baseStart_3163660 baseEnd_3163660 := by
    simpa [prefixWord, tailWord_3163660, baseEnd_3163660] using wordTrace_append hprefix tailTrace_3163660
  have hstable : (prefixWord ++ tailWord_3163660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163660).length < 2 ^ (prefixWord ++ tailWord_3163660).sum := by decide
  have hdescent : baseEnd_3163660 < baseStart_3163660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163662 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3163662 : Nat := 118140960795 + 3163662 * 2 ^ 59
def prefixEnd_3163662 : Nat := 4983230072969 + 3 ^ 40 * 3163662 * 2
def baseEnd_3163662 : Nat := 1082986156243004261050393

theorem tailTrace_3163662 : CollatzResearch.WordTrace tailWord_3163662 prefixEnd_3163662 1082986156243004261050393 := by
  unfold tailWord_3163662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14423529083075044912299655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76925488443066906198931493 14423529083075044912299655)
  ·
    refine ⟨21635293624612567368449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14423529083075044912299655 21635293624612567368449483)
    ·
      refine ⟨32452940436918851052674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21635293624612567368449483 32452940436918851052674225)
      ·
        refine ⟨24339705327689138289505669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32452940436918851052674225 24339705327689138289505669)
        ·
          refine ⟨4563694748941713429282313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24339705327689138289505669 4563694748941713429282313)
          ·
            refine ⟨3422771061706285071961735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563694748941713429282313 3422771061706285071961735)
            ·
              refine ⟨5134156592559427607942603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422771061706285071961735 5134156592559427607942603)
              ·
                refine ⟨7701234888839141411913905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134156592559427607942603 7701234888839141411913905)
                ·
                  refine ⟨5775926166629356058935429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7701234888839141411913905 5775926166629356058935429)
                  ·
                    refine ⟨1082986156243004261050393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5775926166629356058935429 1082986156243004261050393)
                    ·
                      rfl

theorem cell22_3163662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3163662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163662 prefixEnd_3163662 := by exact prefixLift 3163662
  have htrace : WordTrace (prefixWord ++ tailWord_3163662) baseStart_3163662 baseEnd_3163662 := by
    simpa [prefixWord, tailWord_3163662, baseEnd_3163662] using wordTrace_append hprefix tailTrace_3163662
  have hstable : (prefixWord ++ tailWord_3163662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163662).length < 2 ^ (prefixWord ++ tailWord_3163662).sum := by decide
  have hdescent : baseEnd_3163662 < baseStart_3163662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163703 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3163703 : Nat := 118140960795 + 3163703 * 2 ^ 59
def prefixEnd_3163703 : Nat := 4983230072969 + 3 ^ 40 * 3163703 * 2
def baseEnd_3163703 : Nat := 1083000191380893820775267

theorem tailTrace_3163703 : CollatzResearch.WordTrace tailWord_3163703 prefixEnd_3163703 1083000191380893820775267 := by
  unfold tailWord_3163703
  simp only [CollatzResearch.WordTrace]
  refine ⟨115389728057451823300639763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76926485371634548867093175 115389728057451823300639763)
  ·
    refine ⟨173084592086177734950959645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115389728057451823300639763 173084592086177734950959645)
    ·
      refine ⟨64906722032316650606609867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173084592086177734950959645 64906722032316650606609867)
      ·
        refine ⟨97360083048474975909914801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64906722032316650606609867 97360083048474975909914801)
        ·
          refine ⟨73020062286356231932436101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97360083048474975909914801 73020062286356231932436101)
          ·
            refine ⟨13691261678691793487331769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73020062286356231932436101 13691261678691793487331769)
            ·
              refine ⟨10268446259018845115498827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13691261678691793487331769 10268446259018845115498827)
              ·
                refine ⟨15402669388528267673248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268446259018845115498827 15402669388528267673248241)
                ·
                  refine ⟨11552002041396200754936181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15402669388528267673248241 11552002041396200754936181)
                  ·
                    refine ⟨1083000191380893820775267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11552002041396200754936181 1083000191380893820775267)
                    ·
                      rfl

theorem cell22_3163703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3163703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163703 prefixEnd_3163703 := by exact prefixLift 3163703
  have htrace : WordTrace (prefixWord ++ tailWord_3163703) baseStart_3163703 baseEnd_3163703 := by
    simpa [prefixWord, tailWord_3163703, baseEnd_3163703] using wordTrace_append hprefix tailTrace_3163703
  have hstable : (prefixWord ++ tailWord_3163703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163703).length < 2 ^ (prefixWord ++ tailWord_3163703).sum := by decide
  have hdescent : baseEnd_3163703 < baseStart_3163703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163735 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3163735 : Nat := 118140960795 + 3163735 * 2 ^ 59
def prefixEnd_3163735 : Nat := 4983230072969 + 3 ^ 40 * 3163735 * 2
def baseEnd_3163735 : Nat := 1083011145634856403975169

theorem tailTrace_3163735 : CollatzResearch.WordTrace tailWord_3163735 prefixEnd_3163735 1083011145634856403975169 := by
  unfold tailWord_3163735
  simp only [CollatzResearch.WordTrace]
  refine ⟨115390895193335892765804659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76927263462223928510536439 115390895193335892765804659)
  ·
    refine ⟨173086342790003839148706989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115390895193335892765804659 173086342790003839148706989)
    ·
      refine ⟨64907378546251439680765121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173086342790003839148706989 64907378546251439680765121)
      ·
        refine ⟨48680533909688579760573841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64907378546251439680765121 48680533909688579760573841)
        ·
          refine ⟨36510400432266434820430381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48680533909688579760573841 36510400432266434820430381)
          ·
            refine ⟨13691400162099913057661393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36510400432266434820430381 13691400162099913057661393)
            ·
              refine ⟨10268550121574934793246045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13691400162099913057661393 10268550121574934793246045)
              ·
                refine ⟨3850706295590600547467267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10268550121574934793246045 3850706295590600547467267)
                ·
                  refine ⟨5776059443385900821200901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850706295590600547467267 5776059443385900821200901)
                  ·
                    refine ⟨1083011145634856403975169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776059443385900821200901 1083011145634856403975169)
                    ·
                      rfl

theorem cell22_3163735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3163735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163735 prefixEnd_3163735 := by exact prefixLift 3163735
  have htrace : WordTrace (prefixWord ++ tailWord_3163735) baseStart_3163735 baseEnd_3163735 := by
    simpa [prefixWord, tailWord_3163735, baseEnd_3163735] using wordTrace_append hprefix tailTrace_3163735
  have hstable : (prefixWord ++ tailWord_3163735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163735).length < 2 ^ (prefixWord ++ tailWord_3163735).sum := by decide
  have hdescent : baseEnd_3163735 < baseStart_3163735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163816 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3163816 : Nat := 118140960795 + 3163816 * 2 ^ 59
def prefixEnd_3163816 : Nat := 4983230072969 + 3 ^ 40 * 3163816 * 2
def baseEnd_3163816 : Nat := 1083038873590199192699921

theorem tailTrace_3163816 : CollatzResearch.WordTrace tailWord_3163816 prefixEnd_3163816 1083038873590199192699921 := by
  unfold tailWord_3163816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57696924753021221799751651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76929233004028295733002201 57696924753021221799751651)
  ·
    refine ⟨86545387129531832699627477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57696924753021221799751651 86545387129531832699627477)
    ·
      refine ⟨2028407510848402328897519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86545387129531832699627477 2028407510848402328897519)
      ·
        refine ⟨3042611266272603493346279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028407510848402328897519 3042611266272603493346279)
        ·
          refine ⟨4563916899408905240019419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042611266272603493346279 4563916899408905240019419)
          ·
            refine ⟨6845875349113357860029129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563916899408905240019419 6845875349113357860029129)
            ·
              refine ⟨5134406511835018395021847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845875349113357860029129 5134406511835018395021847)
              ·
                refine ⟨7701609767752527592532771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134406511835018395021847 7701609767752527592532771)
                ·
                  refine ⟨11552414651628791388799157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7701609767752527592532771 11552414651628791388799157)
                  ·
                    refine ⟨1083038873590199192699921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11552414651628791388799157 1083038873590199192699921)
                    ·
                      rfl

theorem cell22_3163816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3163816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163816 prefixEnd_3163816 := by exact prefixLift 3163816
  have htrace : WordTrace (prefixWord ++ tailWord_3163816) baseStart_3163816 baseEnd_3163816 := by
    simpa [prefixWord, tailWord_3163816, baseEnd_3163816] using wordTrace_append hprefix tailTrace_3163816
  have hstable : (prefixWord ++ tailWord_3163816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163816).length < 2 ^ (prefixWord ++ tailWord_3163816).sum := by decide
  have hdescent : baseEnd_3163816 < baseStart_3163816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163857 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 5]
def baseStart_3163857 : Nat := 118140960795 + 3163857 * 2 ^ 59
def prefixEnd_3163857 : Nat := 4983230072969 + 3 ^ 40 * 3163857 * 2
def baseEnd_3163857 : Nat := 361017636242696250808265

theorem tailTrace_3163857 : CollatzResearch.WordTrace tailWord_3163857 prefixEnd_3163857 361017636242696250808265 := by
  unfold tailWord_3163857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115395344898893907601745825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76930229932595938401163883 115395344898893907601745825)
  ·
    refine ⟨86546508674170430701309369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115395344898893907601745825 86546508674170430701309369)
    ·
      refine ⟨64909881505627823025982027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86546508674170430701309369 64909881505627823025982027)
      ·
        refine ⟨97364822258441734538973041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64909881505627823025982027 97364822258441734538973041)
        ·
          refine ⟨73023616693831300904229781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97364822258441734538973041 73023616693831300904229781)
          ·
            refine ⟨3422982032523342229885771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73023616693831300904229781 3422982032523342229885771)
            ·
              refine ⟨5134473048785013344828657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422982032523342229885771 5134473048785013344828657)
              ·
                refine ⟨3850854786588760008621493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134473048785013344828657 3850854786588760008621493)
                ·
                  refine ⟨361017636242696250808265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850854786588760008621493 361017636242696250808265)
                  ·
                    rfl

theorem cell22_3163857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_3163857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163857 prefixEnd_3163857 := by exact prefixLift 3163857
  have htrace : WordTrace (prefixWord ++ tailWord_3163857) baseStart_3163857 baseEnd_3163857 := by
    simpa [prefixWord, tailWord_3163857, baseEnd_3163857] using wordTrace_append hprefix tailTrace_3163857
  have hstable : (prefixWord ++ tailWord_3163857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163857).length < 2 ^ (prefixWord ++ tailWord_3163857).sum := by decide
  have hdescent : baseEnd_3163857 < baseStart_3163857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163887 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 1, 4]
def baseStart_3163887 : Nat := 118140960795 + 3163887 * 2 ^ 59
def prefixEnd_3163887 : Nat := 4983230072969 + 3 ^ 40 * 3163887 * 2
def baseEnd_3163887 : Nat := 1083063178341178674174703

theorem tailTrace_3163887 : CollatzResearch.WordTrace tailWord_3163887 prefixEnd_3163887 1083063178341178674174703 := by
  unfold tailWord_3163887
  simp only [CollatzResearch.WordTrace]
  refine ⟨115396439088785222725337915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76930959392523481816891943 115396439088785222725337915)
  ·
    refine ⟨173094658633177834088006873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115396439088785222725337915 173094658633177834088006873)
    ·
      refine ⟨129820993974883375566005155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173094658633177834088006873 129820993974883375566005155)
      ·
        refine ⟨194731490962325063349007733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129820993974883375566005155 194731490962325063349007733)
        ·
          refine ⟨18256077277717974688969475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194731490962325063349007733 18256077277717974688969475)
          ·
            refine ⟨27384115916576962033454213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18256077277717974688969475 27384115916576962033454213)
            ·
              refine ⟨5134521734358180381272665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27384115916576962033454213 5134521734358180381272665)
              ·
                refine ⟨3850891300768635285954499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134521734358180381272665 3850891300768635285954499)
                ·
                  refine ⟨5776336951152952928931749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850891300768635285954499 5776336951152952928931749)
                  ·
                    refine ⟨1083063178341178674174703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776336951152952928931749 1083063178341178674174703)
                    ·
                      rfl

theorem cell22_3163887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_3163887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163887 prefixEnd_3163887 := by exact prefixLift 3163887
  have htrace : WordTrace (prefixWord ++ tailWord_3163887) baseStart_3163887 baseEnd_3163887 := by
    simpa [prefixWord, tailWord_3163887, baseEnd_3163887] using wordTrace_append hprefix tailTrace_3163887
  have hstable : (prefixWord ++ tailWord_3163887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163887).length < 2 ^ (prefixWord ++ tailWord_3163887).sum := by decide
  have hdescent : baseEnd_3163887 < baseStart_3163887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163900 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3163900 : Nat := 118140960795 + 3163900 * 2 ^ 59
def prefixEnd_3163900 : Nat := 4983230072969 + 3 ^ 40 * 3163900 * 2
def baseEnd_3163900 : Nat := 1083067628506850973599663

theorem tailTrace_3163900 : CollatzResearch.WordTrace tailWord_3163900 prefixEnd_3163900 1083067628506850973599663 := by
  unfold tailWord_3163900
  simp only [CollatzResearch.WordTrace]
  refine ⟨57698456618869062972780577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76931275491825417297040769 57698456618869062972780577)
  ·
    refine ⟨43273842464151797229585433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57698456618869062972780577 43273842464151797229585433)
    ·
      refine ⟨32455381848113847922189075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43273842464151797229585433 32455381848113847922189075)
      ·
        refine ⟨48683072772170771883283613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32455381848113847922189075 48683072772170771883283613)
        ·
          refine ⟨18256152289564039456231355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48683072772170771883283613 18256152289564039456231355)
          ·
            refine ⟨27384228434346059184347033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18256152289564039456231355 27384228434346059184347033)
            ·
              refine ⟨20538171325759544388260275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27384228434346059184347033 20538171325759544388260275)
              ·
                refine ⟨30807256988639316582390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20538171325759544388260275 30807256988639316582390413)
                ·
                  refine ⟨11552721370739743718396405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30807256988639316582390413 11552721370739743718396405)
                  ·
                    refine ⟨1083067628506850973599663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11552721370739743718396405 1083067628506850973599663)
                    ·
                      rfl

theorem cell22_3163900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3163900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163900 prefixEnd_3163900 := by exact prefixLift 3163900
  have htrace : WordTrace (prefixWord ++ tailWord_3163900) baseStart_3163900 baseEnd_3163900 := by
    simpa [prefixWord, tailWord_3163900, baseEnd_3163900] using wordTrace_append hprefix tailTrace_3163900
  have hstable : (prefixWord ++ tailWord_3163900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163900).length < 2 ^ (prefixWord ++ tailWord_3163900).sum := by decide
  have hdescent : baseEnd_3163900 < baseStart_3163900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163915 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_3163915 : Nat := 118140960795 + 3163915 * 2 ^ 59
def prefixEnd_3163915 : Nat := 4983230072969 + 3 ^ 40 * 3163915 * 2
def baseEnd_3163915 : Nat := 1083072763313395934474617

theorem tailTrace_3163915 : CollatzResearch.WordTrace tailWord_3163915 prefixEnd_3163915 1083072763313395934474617 := by
  unfold tailWord_3163915
  simp only [CollatzResearch.WordTrace]
  refine ⟨115397460332683783507357199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76931640221789189004904799 115397460332683783507357199)
  ·
    refine ⟨173096190499025675261035799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115397460332683783507357199 173096190499025675261035799)
    ·
      refine ⟨259644285748538512891553699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173096190499025675261035799 259644285748538512891553699)
      ·
        refine ⟨389466428622807769337330549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259644285748538512891553699 389466428622807769337330549)
        ·
          refine ⟨36512477683388228375374739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 389466428622807769337330549 36512477683388228375374739)
          ·
            refine ⟨54768716525082342563062109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36512477683388228375374739 54768716525082342563062109)
            ·
              refine ⟨20538268696905878461148291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54768716525082342563062109 20538268696905878461148291)
              ·
                refine ⟨30807403045358817691722437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20538268696905878461148291 30807403045358817691722437)
                ·
                  refine ⟨5776388071004778317197957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30807403045358817691722437 5776388071004778317197957)
                  ·
                    refine ⟨1083072763313395934474617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776388071004778317197957 1083072763313395934474617)
                    ·
                      rfl

theorem cell22_3163915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_3163915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163915 prefixEnd_3163915 := by exact prefixLift 3163915
  have htrace : WordTrace (prefixWord ++ tailWord_3163915) baseStart_3163915 baseEnd_3163915 := by
    simpa [prefixWord, tailWord_3163915, baseEnd_3163915] using wordTrace_append hprefix tailTrace_3163915
  have hstable : (prefixWord ++ tailWord_3163915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163915).length < 2 ^ (prefixWord ++ tailWord_3163915).sum := by decide
  have hdescent : baseEnd_3163915 < baseStart_3163915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163930 : List Nat := [3, 1, 1, 3, 2, 2, 1, 9]
def baseStart_3163930 : Nat := 118140960795 + 3163930 * 2 ^ 59
def prefixEnd_3163930 : Nat := 4983230072969 + 3 ^ 40 * 3163930 * 2
def baseEnd_3163930 : Nat := 120341988679993432816619

theorem tailTrace_3163930 : CollatzResearch.WordTrace tailWord_3163930 prefixEnd_3163930 120341988679993432816619 := by
  unfold tailWord_3163930
  simp only [CollatzResearch.WordTrace]
  refine ⟨28849501856907360267288311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76932004951752960712768829 28849501856907360267288311)
  ·
    refine ⟨43274252785361040400932467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28849501856907360267288311 43274252785361040400932467)
    ·
      refine ⟨64911379178041560601398701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43274252785361040400932467 64911379178041560601398701)
      ·
        refine ⟨24341767191765585225524513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64911379178041560601398701 24341767191765585225524513)
        ·
          refine ⟨18256325393824188919143385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24341767191765585225524513 18256325393824188919143385)
          ·
            refine ⟨13692244045368141689357539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18256325393824188919143385 13692244045368141689357539)
            ·
              refine ⟨20538366068052212534036309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13692244045368141689357539 20538366068052212534036309)
              ·
                refine ⟨120341988679993432816619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20538366068052212534036309 120341988679993432816619)
                ·
                  rfl

theorem cell22_3163930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_3163930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163930 prefixEnd_3163930 := by exact prefixLift 3163930
  have htrace : WordTrace (prefixWord ++ tailWord_3163930) baseStart_3163930 baseEnd_3163930 := by
    simpa [prefixWord, tailWord_3163930, baseEnd_3163930] using wordTrace_append hprefix tailTrace_3163930
  have hstable : (prefixWord ++ tailWord_3163930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163930).length < 2 ^ (prefixWord ++ tailWord_3163930).sum := by decide
  have hdescent : baseEnd_3163930 < baseStart_3163930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163975 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 7]
def baseStart_3163975 : Nat := 118140960795 + 3163975 * 2 ^ 59
def prefixEnd_3163975 : Nat := 4983230072969 + 3 ^ 40 * 3163975 * 2
def baseEnd_3163975 : Nat := 361031100846525259324811

theorem tailTrace_3163975 : CollatzResearch.WordTrace tailWord_3163975 prefixEnd_3163975 361031100846525259324811 := by
  unfold tailWord_3163975
  simp only [CollatzResearch.WordTrace]
  refine ⟨115399648712466413754541379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76933099141644275836360919 115399648712466413754541379)
  ·
    refine ⟨173099473068699620631812069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115399648712466413754541379 173099473068699620631812069)
    ·
      refine ⟨32456151200381178868464763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173099473068699620631812069 32456151200381178868464763)
      ·
        refine ⟨48684226800571768302697145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32456151200381178868464763 48684226800571768302697145)
        ·
          refine ⟨36513170100428826227022859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48684226800571768302697145 36513170100428826227022859)
          ·
            refine ⟨54769755150643239340534289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36513170100428826227022859 54769755150643239340534289)
            ·
              refine ⟨41077316362982429505400717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54769755150643239340534289 41077316362982429505400717)
              ·
                refine ⟨15403993636118411064525269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41077316362982429505400717 15403993636118411064525269)
                ·
                  refine ⟨361031100846525259324811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15403993636118411064525269 361031100846525259324811)
                  ·
                    rfl

theorem cell22_3163975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_3163975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163975 prefixEnd_3163975 := by exact prefixLift 3163975
  have htrace : WordTrace (prefixWord ++ tailWord_3163975) baseStart_3163975 baseEnd_3163975 := by
    simpa [prefixWord, tailWord_3163975, baseEnd_3163975] using wordTrace_append hprefix tailTrace_3163975
  have hstable : (prefixWord ++ tailWord_3163975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163975).length < 2 ^ (prefixWord ++ tailWord_3163975).sum := by decide
  have hdescent : baseEnd_3163975 < baseStart_3163975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163996 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3163996 : Nat := 118140960795 + 3163996 * 2 ^ 59
def prefixEnd_3163996 : Nat := 4983230072969 + 3 ^ 40 * 3163996 * 2
def baseEnd_3163996 : Nat := 1083100491268738723199369

theorem tailTrace_3163996 : CollatzResearch.WordTrace tailWord_3163996 prefixEnd_3163996 1083100491268738723199369 := by
  unfold tailWord_3163996
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700207322695167170527921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76933609763593556227370561 57700207322695167170527921)
  ·
    refine ⟨43275155492021375377895941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57700207322695167170527921 43275155492021375377895941)
    ·
      refine ⟨8114091654754007883355489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43275155492021375377895941 8114091654754007883355489)
      ·
        refine ⟨6085568741065505912516617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8114091654754007883355489 6085568741065505912516617)
        ·
          refine ⟨4564176555799129434387463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6085568741065505912516617 4564176555799129434387463)
          ·
            refine ⟨6846264833698694151581195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564176555799129434387463 6846264833698694151581195)
            ·
              refine ⟨10269397250548041227371793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846264833698694151581195 10269397250548041227371793)
              ·
                refine ⟨7702047937911030920528845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10269397250548041227371793 7702047937911030920528845)
                ·
                  refine ⟨2888267976716636595198317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7702047937911030920528845 2888267976716636595198317)
                  ·
                    refine ⟨1083100491268738723199369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888267976716636595198317 1083100491268738723199369)
                    ·
                      rfl

theorem cell22_3163996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3163996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3163996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3163996 prefixEnd_3163996 := by exact prefixLift 3163996
  have htrace : WordTrace (prefixWord ++ tailWord_3163996) baseStart_3163996 baseEnd_3163996 := by
    simpa [prefixWord, tailWord_3163996, baseEnd_3163996] using wordTrace_append hprefix tailTrace_3163996
  have hstable : (prefixWord ++ tailWord_3163996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163996).length < 2 ^ (prefixWord ++ tailWord_3163996).sum := by decide
  have hdescent : baseEnd_3163996 < baseStart_3163996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164037 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 6]
def baseStart_3164037 : Nat := 118140960795 + 3164037 * 2 ^ 59
def prefixEnd_3164037 : Nat := 4983230072969 + 3 ^ 40 * 3164037 * 2
def baseEnd_3164037 : Nat := 361038175468876094308081

theorem tailTrace_3164037 : CollatzResearch.WordTrace tailWord_3164037 prefixEnd_3164037 361038175468876094308081 := by
  unfold tailWord_3164037
  simp only [CollatzResearch.WordTrace]
  refine ⟨115401910038241798343298365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76934606692161198895532243 115401910038241798343298365)
  ·
    refine ⟨43275716264340674378736887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115401910038241798343298365 43275716264340674378736887)
    ·
      refine ⟨64913574396511011568105331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43275716264340674378736887 64913574396511011568105331)
      ·
        refine ⟨97370361594766517352157997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64913574396511011568105331 97370361594766517352157997)
        ·
          refine ⟨36513885598037444007059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97370361594766517352157997 36513885598037444007059249)
          ·
            refine ⟨27385414198528083005294437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36513885598037444007059249 27385414198528083005294437)
            ·
              refine ⟨5134765162224015563492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27385414198528083005294437 5134765162224015563492707)
              ·
                refine ⟨7702147743336023345239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134765162224015563492707 7702147743336023345239061)
                ·
                  refine ⟨361038175468876094308081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7702147743336023345239061 361038175468876094308081)
                  ·
                    rfl

theorem cell22_3164037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_3164037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164037 prefixEnd_3164037 := by exact prefixLift 3164037
  have htrace : WordTrace (prefixWord ++ tailWord_3164037) baseStart_3164037 baseEnd_3164037 := by
    simpa [prefixWord, tailWord_3164037, baseEnd_3164037] using wordTrace_append hprefix tailTrace_3164037
  have hstable : (prefixWord ++ tailWord_3164037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164037).length < 2 ^ (prefixWord ++ tailWord_3164037).sum := by decide
  have hdescent : baseEnd_3164037 < baseStart_3164037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164067 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_3164067 : Nat := 118140960795 + 3164067 * 2 ^ 59
def prefixEnd_3164067 : Nat := 4983230072969 + 3 ^ 40 * 3164067 * 2
def baseEnd_3164067 : Nat := 1083124796019718204674151

theorem tailTrace_3164067 : CollatzResearch.WordTrace tailWord_3164067 prefixEnd_3164067 1083124796019718204674151 := by
  unfold tailWord_3164067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115403004228133113466890455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76935336152088742311260303 115403004228133113466890455)
  ·
    refine ⟨173104506342199670200335683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115403004228133113466890455 173104506342199670200335683)
    ·
      refine ⟨259656759513299505300503525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173104506342199670200335683 259656759513299505300503525)
      ·
        refine ⟨48685642408743657243844411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259656759513299505300503525 48685642408743657243844411)
        ·
          refine ⟨73028463613115485865766617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48685642408743657243844411 73028463613115485865766617)
          ·
            refine ⟨54771347709836614399324963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73028463613115485865766617 54771347709836614399324963)
            ·
              refine ⟨82157021564754921598987445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54771347709836614399324963 82157021564754921598987445)
              ·
                refine ⟨7702220771695773899905073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82157021564754921598987445 7702220771695773899905073)
                ·
                  refine ⟨5776665578771830424928805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702220771695773899905073 5776665578771830424928805)
                  ·
                    refine ⟨1083124796019718204674151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776665578771830424928805 1083124796019718204674151)
                    ·
                      rfl

theorem cell22_3164067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_3164067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164067 prefixEnd_3164067 := by exact prefixLift 3164067
  have htrace : WordTrace (prefixWord ++ tailWord_3164067) baseStart_3164067 baseEnd_3164067 := by
    simpa [prefixWord, tailWord_3164067, baseEnd_3164067] using wordTrace_append hprefix tailTrace_3164067
  have hstable : (prefixWord ++ tailWord_3164067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164067).length < 2 ^ (prefixWord ++ tailWord_3164067).sum := by decide
  have hdescent : baseEnd_3164067 < baseStart_3164067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164071 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 4]
def baseStart_3164071 : Nat := 118140960795 + 3164071 * 2 ^ 59
def prefixEnd_3164071 : Nat := 4983230072969 + 3 ^ 40 * 3164071 * 2
def baseEnd_3164071 : Nat := 361042055100487842524713

theorem tailTrace_3164071 : CollatzResearch.WordTrace tailWord_3164071 prefixEnd_3164071 361042055100487842524713 := by
  unfold tailWord_3164071
  simp only [CollatzResearch.WordTrace]
  refine ⟨115403150120118622150036067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76935433413412414766690711 115403150120118622150036067)
  ·
    refine ⟨173104725180177933225054101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115403150120118622150036067 173104725180177933225054101)
    ·
      refine ⟨8114283992820840619924411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173104725180177933225054101 8114283992820840619924411)
      ·
        refine ⟨12171425989231260929886617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114283992820840619924411 12171425989231260929886617)
        ·
          refine ⟨9128569491923445697414963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12171425989231260929886617 9128569491923445697414963)
          ·
            refine ⟨13692854237885168546122445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128569491923445697414963 13692854237885168546122445)
            ·
              refine ⟨5134820339206938204795917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13692854237885168546122445 5134820339206938204795917)
              ·
                refine ⟨1925557627202601826798469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5134820339206938204795917 1925557627202601826798469)
                ·
                  refine ⟨361042055100487842524713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925557627202601826798469 361042055100487842524713)
                  ·
                    rfl

theorem cell22_3164071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 4].length) (baseStart_3164071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164071 prefixEnd_3164071 := by exact prefixLift 3164071
  have htrace : WordTrace (prefixWord ++ tailWord_3164071) baseStart_3164071 baseEnd_3164071 := by
    simpa [prefixWord, tailWord_3164071, baseEnd_3164071] using wordTrace_append hprefix tailTrace_3164071
  have hstable : (prefixWord ++ tailWord_3164071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164071).length < 2 ^ (prefixWord ++ tailWord_3164071).sum := by decide
  have hdescent : baseEnd_3164071 < baseStart_3164071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164118 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3164118 : Nat := 118140960795 + 3164118 * 2 ^ 59
def prefixEnd_3164118 : Nat := 4983230072969 + 3 ^ 40 * 3164118 * 2
def baseEnd_3164118 : Nat := 1083142254361971071648995

theorem tailTrace_3164118 : CollatzResearch.WordTrace tailWord_3164118 prefixEnd_3164118 1083142254361971071648995 := by
  unfold tailWord_3164118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212804021934271823562313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76936576233965566117998005 7212804021934271823562313)
  ·
    refine ⟨5409603016450703867671735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7212804021934271823562313 5409603016450703867671735)
    ·
      refine ⟨8114404524676055801507603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5409603016450703867671735 8114404524676055801507603)
      ·
        refine ⟨12171606787014083702261405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114404524676055801507603 12171606787014083702261405)
        ·
          refine ⟨4564352545130281388348027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12171606787014083702261405 4564352545130281388348027)
          ·
            refine ⟨6846528817695422082522041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564352545130281388348027 6846528817695422082522041)
            ·
              refine ⟨5134896613271566561891531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846528817695422082522041 5134896613271566561891531)
              ·
                refine ⟨7702344919907349842837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134896613271566561891531 7702344919907349842837297)
                ·
                  refine ⟨5776758689930512382127973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702344919907349842837297 5776758689930512382127973)
                  ·
                    refine ⟨1083142254361971071648995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776758689930512382127973 1083142254361971071648995)
                    ·
                      rfl

theorem cell22_3164118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3164118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164118 prefixEnd_3164118 := by exact prefixLift 3164118
  have htrace : WordTrace (prefixWord ++ tailWord_3164118) baseStart_3164118 baseEnd_3164118 := by
    simpa [prefixWord, tailWord_3164118, baseEnd_3164118] using wordTrace_append hprefix tailTrace_3164118
  have hstable : (prefixWord ++ tailWord_3164118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164118).length < 2 ^ (prefixWord ++ tailWord_3164118).sum := by decide
  have hdescent : baseEnd_3164118 < baseStart_3164118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164174 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3164174 : Nat := 118140960795 + 3164174 * 2 ^ 59
def prefixEnd_3164174 : Nat := 4983230072969 + 3 ^ 40 * 3164174 * 2
def baseEnd_3164174 : Nat := 1083161424306405592248823

theorem tailTrace_3164174 : CollatzResearch.WordTrace tailWord_3164174 prefixEnd_3164174 1083161424306405592248823 := by
  unfold tailWord_3164174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14425863354843183842629447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76937937892496980494023717 14425863354843183842629447)
  ·
    refine ⟨21638795032264775763944171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14425863354843183842629447 21638795032264775763944171)
    ·
      refine ⟨32458192548397163645916257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21638795032264775763944171 32458192548397163645916257)
      ·
        refine ⟨24343644411297872734437193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32458192548397163645916257 24343644411297872734437193)
        ·
          refine ⟨18257733308473404550827895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24343644411297872734437193 18257733308473404550827895)
          ·
            refine ⟨27386599962710106826241843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18257733308473404550827895 27386599962710106826241843)
            ·
              refine ⟨41079899944065160239362765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386599962710106826241843 41079899944065160239362765)
              ·
                refine ⟨15404962479024435089761037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41079899944065160239362765 15404962479024435089761037)
                ·
                  refine ⟨5776860929634163158660389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15404962479024435089761037 5776860929634163158660389)
                  ·
                    refine ⟨1083161424306405592248823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776860929634163158660389 1083161424306405592248823)
                    ·
                      rfl

theorem cell22_3164174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3164174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164174 prefixEnd_3164174 := by exact prefixLift 3164174
  have htrace : WordTrace (prefixWord ++ tailWord_3164174) baseStart_3164174 baseEnd_3164174 := by
    simpa [prefixWord, tailWord_3164174, baseEnd_3164174] using wordTrace_append hprefix tailTrace_3164174
  have hstable : (prefixWord ++ tailWord_3164174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164174).length < 2 ^ (prefixWord ++ tailWord_3164174).sum := by decide
  have hdescent : baseEnd_3164174 < baseStart_3164174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164187 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_3164187 : Nat := 118140960795 + 3164187 * 2 ^ 59
def prefixEnd_3164187 : Nat := 4983230072969 + 3 ^ 40 * 3164187 * 2
def baseEnd_3164187 : Nat := 1083165874472077891673783

theorem tailTrace_3164187 : CollatzResearch.WordTrace tailWord_3164187 prefixEnd_3164187 1083165874472077891673783 := by
  unfold tailWord_3164187
  simp only [CollatzResearch.WordTrace]
  refine ⟨115407380987698373961258815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76938253991798915974172543 115407380987698373961258815)
  ·
    refine ⟨173111071481547560941888223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115407380987698373961258815 173111071481547560941888223)
    ·
      refine ⟨259666607222321341412832335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173111071481547560941888223 259666607222321341412832335)
      ·
        refine ⟨389499910833482012119248503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259666607222321341412832335 389499910833482012119248503)
        ·
          refine ⟨584249866250223018178872755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389499910833482012119248503 584249866250223018178872755)
          ·
            refine ⟨876374799375334527268309133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584249866250223018178872755 876374799375334527268309133)
            ·
              refine ⟨328640549765750447725615925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876374799375334527268309133 328640549765750447725615925)
              ·
                refine ⟨30810051540539104474276493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328640549765750447725615925 30810051540539104474276493)
                ·
                  refine ⟨11553769327702164177853685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30810051540539104474276493 11553769327702164177853685)
                  ·
                    refine ⟨1083165874472077891673783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11553769327702164177853685 1083165874472077891673783)
                    ·
                      rfl

theorem cell22_3164187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_3164187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164187 prefixEnd_3164187 := by exact prefixLift 3164187
  have htrace : WordTrace (prefixWord ++ tailWord_3164187) baseStart_3164187 baseEnd_3164187 := by
    simpa [prefixWord, tailWord_3164187, baseEnd_3164187] using wordTrace_append hprefix tailTrace_3164187
  have hstable : (prefixWord ++ tailWord_3164187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164187).length < 2 ^ (prefixWord ++ tailWord_3164187).sum := by decide
  have hdescent : baseEnd_3164187 < baseStart_3164187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164206 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3164206 : Nat := 118140960795 + 3164206 * 2 ^ 59
def prefixEnd_3164206 : Nat := 4983230072969 + 3 ^ 40 * 3164206 * 2
def baseEnd_3164206 : Nat := 361057459520122725149575

theorem tailTrace_3164206 : CollatzResearch.WordTrace tailWord_3164206 prefixEnd_3164206 361057459520122725149575 := by
  unfold tailWord_3164206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426009246828692525775059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76938715983086360137466981 14426009246828692525775059)
  ·
    refine ⟨21639013870243038788662589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426009246828692525775059 21639013870243038788662589)
    ·
      refine ⟨8114630201341139545748471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21639013870243038788662589 8114630201341139545748471)
      ·
        refine ⟨12171945302011709318622707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114630201341139545748471 12171945302011709318622707)
        ·
          refine ⟨18257917953017563977934061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171945302011709318622707 18257917953017563977934061)
          ·
            refine ⟨6846719232381586491725273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18257917953017563977934061 6846719232381586491725273)
            ·
              refine ⟨5135039424286189868793955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846719232381586491725273 5135039424286189868793955)
              ·
                refine ⟨7702559136429284803190933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135039424286189868793955 7702559136429284803190933)
                ·
                  refine ⟨361057459520122725149575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7702559136429284803190933 361057459520122725149575)
                  ·
                    rfl

theorem cell22_3164206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3164206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164206 prefixEnd_3164206 := by exact prefixLift 3164206
  have htrace : WordTrace (prefixWord ++ tailWord_3164206) baseStart_3164206 baseEnd_3164206 := by
    simpa [prefixWord, tailWord_3164206, baseEnd_3164206] using wordTrace_append hprefix tailTrace_3164206
  have hstable : (prefixWord ++ tailWord_3164206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164206).length < 2 ^ (prefixWord ++ tailWord_3164206).sum := by decide
  have hdescent : baseEnd_3164206 < baseStart_3164206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164253 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3164253 : Nat := 118140960795 + 3164253 * 2 ^ 59
def prefixEnd_3164253 : Nat := 4983230072969 + 3 ^ 40 * 3164253 * 2
def baseEnd_3164253 : Nat := 1083188467620875719523581

theorem tailTrace_3164253 : CollatzResearch.WordTrace tailWord_3164253 prefixEnd_3164253 1083188467620875719523581 := by
  unfold tailWord_3164253
  simp only [CollatzResearch.WordTrace]
  refine ⟨115409788205459267233161413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76939858803639511488774275 115409788205459267233161413)
  ·
    refine ⟨21639335288523612606217765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115409788205459267233161413 21639335288523612606217765)
    ·
      refine ⟨4057375366598177363665831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21639335288523612606217765 4057375366598177363665831)
      ·
        refine ⟨6086063049897266045498747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057375366598177363665831 6086063049897266045498747)
        ·
          refine ⟨9129094574845899068248121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086063049897266045498747 9129094574845899068248121)
          ·
            refine ⟨6846820931134424301186091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9129094574845899068248121 6846820931134424301186091)
            ·
              refine ⟨10270231396701636451779137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846820931134424301186091 10270231396701636451779137)
              ·
                refine ⟨7702673547526227338834353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10270231396701636451779137 7702673547526227338834353)
                ·
                  refine ⟨5777005160644670504125765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702673547526227338834353 5777005160644670504125765)
                  ·
                    refine ⟨1083188467620875719523581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777005160644670504125765 1083188467620875719523581)
                    ·
                      rfl

theorem cell22_3164253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3164253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164253 prefixEnd_3164253 := by exact prefixLift 3164253
  have htrace : WordTrace (prefixWord ++ tailWord_3164253) baseStart_3164253 baseEnd_3164253 := by
    simpa [prefixWord, tailWord_3164253, baseEnd_3164253] using wordTrace_append hprefix tailTrace_3164253
  have hstable : (prefixWord ++ tailWord_3164253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164253).length < 2 ^ (prefixWord ++ tailWord_3164253).sum := by decide
  have hdescent : baseEnd_3164253 < baseStart_3164253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164317 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_3164317 : Nat := 118140960795 + 3164317 * 2 ^ 59
def prefixEnd_3164317 : Nat := 4983230072969 + 3 ^ 40 * 3164317 * 2
def baseEnd_3164317 : Nat := 1083210376128800885923385

theorem tailTrace_3164317 : CollatzResearch.WordTrace tailWord_3164317 prefixEnd_3164317 1083210376128800885923385 := by
  unfold tailWord_3164317
  simp only [CollatzResearch.WordTrace]
  refine ⟨115412122477227406163491205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76941414984818270775660803 115412122477227406163491205)
  ·
    refine ⟨21639772964480138655654601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115412122477227406163491205 21639772964480138655654601)
    ·
      refine ⟨16229829723360103991740951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21639772964480138655654601 16229829723360103991740951)
      ·
        refine ⟨24344744585040155987611427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16229829723360103991740951 24344744585040155987611427)
        ·
          refine ⟨36517116877560233981417141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24344744585040155987611427 36517116877560233981417141)
          ·
            refine ⟨3423479707271271935757857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36517116877560233981417141 3423479707271271935757857)
            ·
              refine ⟨2567609780453453951818393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423479707271271935757857 2567609780453453951818393)
              ·
                refine ⟨1925707335340090463863795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567609780453453951818393 1925707335340090463863795)
                ·
                  refine ⟨2888561003010135695795693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925707335340090463863795 2888561003010135695795693)
                  ·
                    refine ⟨1083210376128800885923385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888561003010135695795693 1083210376128800885923385)
                    ·
                      rfl

theorem cell22_3164317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_3164317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164317 prefixEnd_3164317 := by exact prefixLift 3164317
  have htrace : WordTrace (prefixWord ++ tailWord_3164317) baseStart_3164317 baseEnd_3164317 := by
    simpa [prefixWord, tailWord_3164317, baseEnd_3164317] using wordTrace_append hprefix tailTrace_3164317
  have hstable : (prefixWord ++ tailWord_3164317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164317).length < 2 ^ (prefixWord ++ tailWord_3164317).sum := by decide
  have hdescent : baseEnd_3164317 < baseStart_3164317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164448 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_3164448 : Nat := 118140960795 + 3164448 * 2 ^ 59
def prefixEnd_3164448 : Nat := 4983230072969 + 3 ^ 40 * 3164448 * 2
def baseEnd_3164448 : Nat := 361085073368653403632661

theorem tailTrace_3164448 : CollatzResearch.WordTrace tailWord_3164448 prefixEnd_3164448 361085073368653403632661 := by
  unfold tailWord_3164448
  simp only [CollatzResearch.WordTrace]
  refine ⟨57708450219876407768254999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76944600293168543691006665 57708450219876407768254999)
  ·
    refine ⟨86562675329814611652382499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57708450219876407768254999 86562675329814611652382499)
    ·
      refine ⟨129844012994721917478573749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86562675329814611652382499 129844012994721917478573749)
      ·
        refine ⟨12172876218255179763616289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129844012994721917478573749 12172876218255179763616289)
        ·
          refine ⟨9129657163691384822712217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12172876218255179763616289 9129657163691384822712217)
          ·
            refine ⟨6847242872768538617034163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9129657163691384822712217 6847242872768538617034163)
            ·
              refine ⟨10270864309152807925551245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6847242872768538617034163 10270864309152807925551245)
              ·
                refine ⟨3851574115932302972081717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10270864309152807925551245 3851574115932302972081717)
                ·
                  refine ⟨361085073368653403632661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851574115932302972081717 361085073368653403632661)
                  ·
                    rfl

theorem cell22_3164448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_3164448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164448 prefixEnd_3164448 := by exact prefixLift 3164448
  have htrace : WordTrace (prefixWord ++ tailWord_3164448) baseStart_3164448 baseEnd_3164448 := by
    simpa [prefixWord, tailWord_3164448, baseEnd_3164448] using wordTrace_append hprefix tailTrace_3164448
  have hstable : (prefixWord ++ tailWord_3164448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164448).length < 2 ^ (prefixWord ++ tailWord_3164448).sum := by decide
  have hdescent : baseEnd_3164448 < baseStart_3164448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164506 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_3164506 : Nat := 118140960795 + 3164506 * 2 ^ 59
def prefixEnd_3164506 : Nat := 4983230072969 + 3 ^ 40 * 3164506 * 2
def baseEnd_3164506 : Nat := 1083275074691267392947805

theorem tailTrace_3164506 : CollatzResearch.WordTrace tailWord_3164506 prefixEnd_3164506 1083275074691267392947805 := by
  unfold tailWord_3164506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28854753968385672860530343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76946010582361794294747581 28854753968385672860530343)
  ·
    refine ⟨43282130952578509290795515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28854753968385672860530343 43282130952578509290795515)
    ·
      refine ⟨64923196428867763936193273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43282130952578509290795515 64923196428867763936193273)
      ·
        refine ⟨48692397321650822952144955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64923196428867763936193273 48692397321650822952144955)
        ·
          refine ⟨73038595982476234428217433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48692397321650822952144955 73038595982476234428217433)
          ·
            refine ⟨54778946986857175821163075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73038595982476234428217433 54778946986857175821163075)
            ·
              refine ⟨82168420480285763731744613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54778946986857175821163075 82168420480285763731744613)
              ·
                refine ⟨15406578840053580699702115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82168420480285763731744613 15406578840053580699702115)
                ·
                  refine ⟨23109868260080371049553173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15406578840053580699702115 23109868260080371049553173)
                  ·
                    refine ⟨1083275074691267392947805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23109868260080371049553173 1083275074691267392947805)
                    ·
                      rfl

theorem cell22_3164506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_3164506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164506 prefixEnd_3164506 := by exact prefixLift 3164506
  have htrace : WordTrace (prefixWord ++ tailWord_3164506) baseStart_3164506 baseEnd_3164506 := by
    simpa [prefixWord, tailWord_3164506, baseEnd_3164506] using wordTrace_append hprefix tailTrace_3164506
  have hstable : (prefixWord ++ tailWord_3164506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164506).length < 2 ^ (prefixWord ++ tailWord_3164506).sum := by decide
  have hdescent : baseEnd_3164506 < baseStart_3164506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164570 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_3164570 : Nat := 118140960795 + 3164570 * 2 ^ 59
def prefixEnd_3164570 : Nat := 4983230072969 + 3 ^ 40 * 3164570 * 2
def baseEnd_3164570 : Nat := 1083296983199192559347609

theorem tailTrace_3164570 : CollatzResearch.WordTrace tailWord_3164570 prefixEnd_3164570 1083296983199192559347609 := by
  unfold tailWord_3164570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855337536327707593112791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76947566763540553581634109 28855337536327707593112791)
  ·
    refine ⟨43283006304491561389669187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28855337536327707593112791 43283006304491561389669187)
    ·
      refine ⟨64924509456737342084503781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43283006304491561389669187 64924509456737342084503781)
      ·
        refine ⟨12173345523138251640844459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64924509456737342084503781 12173345523138251640844459)
        ·
          refine ⟨18260018284707377461266689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173345523138251640844459 18260018284707377461266689)
          ·
            refine ⟨13695013713530533095950017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18260018284707377461266689 13695013713530533095950017)
            ·
              refine ⟨10271260285147899821962513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13695013713530533095950017 10271260285147899821962513)
              ·
                refine ⟨7703445213860924866471885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10271260285147899821962513 7703445213860924866471885)
                ·
                  refine ⟨2888791955197846824926957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7703445213860924866471885 2888791955197846824926957)
                  ·
                    refine ⟨1083296983199192559347609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888791955197846824926957 1083296983199192559347609)
                    ·
                      rfl

theorem cell22_3164570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_3164570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164570 prefixEnd_3164570 := by exact prefixLift 3164570
  have htrace : WordTrace (prefixWord ++ tailWord_3164570) baseStart_3164570 baseEnd_3164570 := by
    simpa [prefixWord, tailWord_3164570, baseEnd_3164570] using wordTrace_append hprefix tailTrace_3164570
  have hstable : (prefixWord ++ tailWord_3164570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164570).length < 2 ^ (prefixWord ++ tailWord_3164570).sum := by decide
  have hdescent : baseEnd_3164570 < baseStart_3164570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164583 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 7]
def baseStart_3164583 : Nat := 118140960795 + 3164583 * 2 ^ 59
def prefixEnd_3164583 : Nat := 4983230072969 + 3 ^ 40 * 3164583 * 2
def baseEnd_3164583 : Nat := 361100477788288286257523

theorem tailTrace_3164583 : CollatzResearch.WordTrace tailWord_3164583 prefixEnd_3164583 361100477788288286257523 := by
  unfold tailWord_3164583
  simp only [CollatzResearch.WordTrace]
  refine ⟨115421824294263733592674403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76947882862842489061782935 115421824294263733592674403)
  ·
    refine ⟨173132736441395600389011605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115421824294263733592674403 173132736441395600389011605)
    ·
      refine ⟨8115597020690418768234919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173132736441395600389011605 8115597020690418768234919)
      ·
        refine ⟨12173395531035628152352379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115597020690418768234919 12173395531035628152352379)
        ·
          refine ⟨18260093296553442228528569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173395531035628152352379 18260093296553442228528569)
          ·
            refine ⟨13695069972415081671396427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18260093296553442228528569 13695069972415081671396427)
            ·
              refine ⟨20542604958622622507094641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13695069972415081671396427 20542604958622622507094641)
              ·
                refine ⟨15406953718966966880320981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20542604958622622507094641 15406953718966966880320981)
                ·
                  refine ⟨361100477788288286257523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15406953718966966880320981 361100477788288286257523)
                  ·
                    rfl

theorem cell22_3164583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_3164583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164583 prefixEnd_3164583 := by exact prefixLift 3164583
  have htrace : WordTrace (prefixWord ++ tailWord_3164583) baseStart_3164583 baseEnd_3164583 := by
    simpa [prefixWord, tailWord_3164583, baseEnd_3164583] using wordTrace_append hprefix tailTrace_3164583
  have hstable : (prefixWord ++ tailWord_3164583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164583).length < 2 ^ (prefixWord ++ tailWord_3164583).sum := by decide
  have hdescent : baseEnd_3164583 < baseStart_3164583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164647 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3164647 : Nat := 118140960795 + 3164647 * 2 ^ 59
def prefixEnd_3164647 : Nat := 4983230072969 + 3 ^ 40 * 3164647 * 2
def baseEnd_3164647 : Nat := 1083323341872790025172373

theorem tailTrace_3164647 : CollatzResearch.WordTrace tailWord_3164647 prefixEnd_3164647 1083323341872790025172373 := by
  unfold tailWord_3164647
  simp only [CollatzResearch.WordTrace]
  refine ⟨115424158566031872523004195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76949439044021248348669463 115424158566031872523004195)
  ·
    refine ⟨173136237849047808784506293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115424158566031872523004195 173136237849047808784506293)
    ·
      refine ⟨16231522298348232073547465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173136237849047808784506293 16231522298348232073547465)
      ·
        refine ⟨12173641723761174055160599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16231522298348232073547465 12173641723761174055160599)
        ·
          refine ⟨18260462585641761082740899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173641723761174055160599 18260462585641761082740899)
          ·
            refine ⟨27390693878462641624111349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18260462585641761082740899 27390693878462641624111349)
            ·
              refine ⟨2567877551105872652260439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27390693878462641624111349 2567877551105872652260439)
              ·
                refine ⟨3851816326658808978390659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567877551105872652260439 3851816326658808978390659)
                ·
                  refine ⟨5777724489988213467585989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851816326658808978390659 5777724489988213467585989)
                  ·
                    refine ⟨1083323341872790025172373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777724489988213467585989 1083323341872790025172373)
                    ·
                      rfl

theorem cell22_3164647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3164647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164647 prefixEnd_3164647 := by exact prefixLift 3164647
  have htrace : WordTrace (prefixWord ++ tailWord_3164647) baseStart_3164647 baseEnd_3164647 := by
    simpa [prefixWord, tailWord_3164647, baseEnd_3164647] using wordTrace_append hprefix tailTrace_3164647
  have hstable : (prefixWord ++ tailWord_3164647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164647).length < 2 ^ (prefixWord ++ tailWord_3164647).sum := by decide
  have hdescent : baseEnd_3164647 < baseStart_3164647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164662 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3164662 : Nat := 118140960795 + 3164662 * 2 ^ 59
def prefixEnd_3164662 : Nat := 4983230072969 + 3 ^ 40 * 3164662 * 2
def baseEnd_3164662 : Nat := 361109492226444995349109

theorem tailTrace_3164662 : CollatzResearch.WordTrace tailWord_3164662 prefixEnd_3164662 361109492226444995349109 := by
  unfold tailWord_3164662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214044103811095630300015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76949803773985020056533493 7214044103811095630300015)
  ·
    refine ⟨10821066155716643445450023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7214044103811095630300015 10821066155716643445450023)
    ·
      refine ⟨16231599233574965168175035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10821066155716643445450023 16231599233574965168175035)
      ·
        refine ⟨24347398850362447752262553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16231599233574965168175035 24347398850362447752262553)
        ·
          refine ⟨18260549137771835814196915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24347398850362447752262553 18260549137771835814196915)
          ·
            refine ⟨27390823706657753721295373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18260549137771835814196915 27390823706657753721295373)
            ·
              refine ⟨10271558889996657645485765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27390823706657753721295373 10271558889996657645485765)
              ·
                refine ⟨1925917291874373308528581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10271558889996657645485765 1925917291874373308528581)
                ·
                  refine ⟨361109492226444995349109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925917291874373308528581 361109492226444995349109)
                  ·
                    rfl

theorem cell22_3164662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3164662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164662 prefixEnd_3164662 := by exact prefixLift 3164662
  have htrace : WordTrace (prefixWord ++ tailWord_3164662) baseStart_3164662 baseEnd_3164662 := by
    simpa [prefixWord, tailWord_3164662, baseEnd_3164662] using wordTrace_append hprefix tailTrace_3164662
  have hstable : (prefixWord ++ tailWord_3164662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164662).length < 2 ^ (prefixWord ++ tailWord_3164662).sum := by decide
  have hdescent : baseEnd_3164662 < baseStart_3164662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164692 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3164692 : Nat := 118140960795 + 3164692 * 2 ^ 59
def prefixEnd_3164692 : Nat := 4983230072969 + 3 ^ 40 * 3164692 * 2
def baseEnd_3164692 : Nat := 1083338746292424907797235

theorem tailTrace_3164692 : CollatzResearch.WordTrace tailWord_3164692 prefixEnd_3164692 1083338746292424907797235 := by
  unfold tailWord_3164692
  simp only [CollatzResearch.WordTrace]
  refine ⟨57712899925434422604196165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76950533233912563472261553 57712899925434422604196165)
  ·
    refine ⟨10821168736018954238286781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57712899925434422604196165 10821168736018954238286781)
    ·
      refine ⟨4057938276007107839357543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10821168736018954238286781 4057938276007107839357543)
      ·
        refine ⟨6086907414010661759036315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057938276007107839357543 6086907414010661759036315)
        ·
          refine ⟨9130361121015992638554473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086907414010661759036315 9130361121015992638554473)
          ·
            refine ⟨6847770840761994478915855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9130361121015992638554473 6847770840761994478915855)
            ·
              refine ⟨10271656261142991718373783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6847770840761994478915855 10271656261142991718373783)
              ·
                refine ⟨15407484391714487577560675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10271656261142991718373783 15407484391714487577560675)
                ·
                  refine ⟨23111226587571731366341013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15407484391714487577560675 23111226587571731366341013)
                  ·
                    refine ⟨1083338746292424907797235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23111226587571731366341013 1083338746292424907797235)
                    ·
                      rfl

theorem cell22_3164692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3164692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164692 prefixEnd_3164692 := by exact prefixLift 3164692
  have htrace : WordTrace (prefixWord ++ tailWord_3164692) baseStart_3164692 baseEnd_3164692 := by
    simpa [prefixWord, tailWord_3164692, baseEnd_3164692] using wordTrace_append hprefix tailTrace_3164692
  have hstable : (prefixWord ++ tailWord_3164692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164692).length < 2 ^ (prefixWord ++ tailWord_3164692).sum := by decide
  have hdescent : baseEnd_3164692 < baseStart_3164692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164705 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3164705 : Nat := 118140960795 + 3164705 * 2 ^ 59
def prefixEnd_3164705 : Nat := 4983230072969 + 3 ^ 40 * 3164705 * 2
def baseEnd_3164705 : Nat := 1083343196458097207222195

theorem tailTrace_3164705 : CollatzResearch.WordTrace tailWord_3164705 prefixEnd_3164705 1083343196458097207222195 := by
  unfold tailWord_3164705
  simp only [CollatzResearch.WordTrace]
  refine ⟨115426273999821748428615569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76950849333214498952410379 115426273999821748428615569)
  ·
    refine ⟨86569705499866311321461677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115426273999821748428615569 86569705499866311321461677)
    ·
      refine ⟨32463639562449866745548129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86569705499866311321461677 32463639562449866745548129)
      ·
        refine ⟨24347729671837400059161097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32463639562449866745548129 24347729671837400059161097)
        ·
          refine ⟨18260797253878050044370823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24347729671837400059161097 18260797253878050044370823)
          ·
            refine ⟨27391195880817075066556235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18260797253878050044370823 27391195880817075066556235)
            ·
              refine ⟨41086793821225612599834353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27391195880817075066556235 41086793821225612599834353)
              ·
                refine ⟨30815095365919209449875765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41086793821225612599834353 30815095365919209449875765)
                ·
                  refine ⟨2888915190554925885925853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30815095365919209449875765 2888915190554925885925853)
                  ·
                    refine ⟨1083343196458097207222195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888915190554925885925853 1083343196458097207222195)
                    ·
                      rfl

theorem cell22_3164705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3164705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164705 prefixEnd_3164705 := by exact prefixLift 3164705
  have htrace : WordTrace (prefixWord ++ tailWord_3164705) baseStart_3164705 baseEnd_3164705 := by
    simpa [prefixWord, tailWord_3164705, baseEnd_3164705] using wordTrace_append hprefix tailTrace_3164705
  have hstable : (prefixWord ++ tailWord_3164705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164705).length < 2 ^ (prefixWord ++ tailWord_3164705).sum := by decide
  have hdescent : baseEnd_3164705 < baseStart_3164705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164756 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3164756 : Nat := 118140960795 + 3164756 * 2 ^ 59
def prefixEnd_3164756 : Nat := 4983230072969 + 3 ^ 40 * 3164756 * 2
def baseEnd_3164756 : Nat := 1083360654800350074197039

theorem tailTrace_3164756 : CollatzResearch.WordTrace tailWord_3164756 prefixEnd_3164756 1083360654800350074197039 := by
  unfold tailWord_3164756
  simp only [CollatzResearch.WordTrace]
  refine ⟨57714067061318492069361061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76952089415091322759148081 57714067061318492069361061)
  ·
    refine ⟨10821387573997217263005199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57714067061318492069361061 10821387573997217263005199)
    ·
      refine ⟨16232081360995825894507799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10821387573997217263005199 16232081360995825894507799)
      ·
        refine ⟨24348122041493738841761699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16232081360995825894507799 24348122041493738841761699)
        ·
          refine ⟨36522183062240608262642549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24348122041493738841761699 36522183062240608262642549)
          ·
            refine ⟨3423954662085057024622739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36522183062240608262642549 3423954662085057024622739)
            ·
              refine ⟨5135931993127585536934109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423954662085057024622739 5135931993127585536934109)
              ·
                refine ⟨1925974497422844576350291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5135931993127585536934109 1925974497422844576350291)
                ·
                  refine ⟨2888961746134266864525437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925974497422844576350291 2888961746134266864525437)
                  ·
                    refine ⟨1083360654800350074197039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888961746134266864525437 1083360654800350074197039)
                    ·
                      rfl

theorem cell22_3164756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3164756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164756 prefixEnd_3164756 := by exact prefixLift 3164756
  have htrace : WordTrace (prefixWord ++ tailWord_3164756) baseStart_3164756 baseEnd_3164756 := by
    simpa [prefixWord, tailWord_3164756, baseEnd_3164756] using wordTrace_append hprefix tailTrace_3164756
  have hstable : (prefixWord ++ tailWord_3164756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164756).length < 2 ^ (prefixWord ++ tailWord_3164756).sum := by decide
  have hdescent : baseEnd_3164756 < baseStart_3164756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164780 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_3164780 : Nat := 118140960795 + 3164780 * 2 ^ 59
def prefixEnd_3164780 : Nat := 4983230072969 + 3 ^ 40 * 3164780 * 2
def baseEnd_3164780 : Nat := 361122956830274003865655

theorem tailTrace_3164780 : CollatzResearch.WordTrace tailWord_3164780 prefixEnd_3164780 361122956830274003865655 := by
  unfold tailWord_3164780
  simp only [CollatzResearch.WordTrace]
  refine ⟨57714504737275018118797897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76952672983033357491730529 57714504737275018118797897)
  ·
    refine ⟨43285878552956263589098423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57714504737275018118797897 43285878552956263589098423)
    ·
      refine ⟨64928817829434395383647635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43285878552956263589098423 64928817829434395383647635)
      ·
        refine ⟨97393226744151593075471453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64928817829434395383647635 97393226744151593075471453)
        ·
          refine ⟨36522460029056847403301795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97393226744151593075471453 36522460029056847403301795)
          ·
            refine ⟨54783690043585271104952693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36522460029056847403301795 54783690043585271104952693)
            ·
              refine ⟨5135970941586119166089315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54783690043585271104952693 5135970941586119166089315)
              ·
                refine ⟨7703956412379178749133973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135970941586119166089315 7703956412379178749133973)
                ·
                  refine ⟨361122956830274003865655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7703956412379178749133973 361122956830274003865655)
                  ·
                    rfl

theorem cell22_3164780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_3164780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164780 prefixEnd_3164780 := by exact prefixLift 3164780
  have htrace : WordTrace (prefixWord ++ tailWord_3164780) baseStart_3164780 baseEnd_3164780 := by
    simpa [prefixWord, tailWord_3164780, baseEnd_3164780] using wordTrace_append hprefix tailTrace_3164780
  have hstable : (prefixWord ++ tailWord_3164780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164780).length < 2 ^ (prefixWord ++ tailWord_3164780).sum := by decide
  have hdescent : baseEnd_3164780 < baseStart_3164780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164786 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3164786 : Nat := 118140960795 + 3164786 * 2 ^ 59
def prefixEnd_3164786 : Nat := 4983230072969 + 3 ^ 40 * 3164786 * 2
def baseEnd_3164786 : Nat := 361123641471146665315649

theorem tailTrace_3164786 : CollatzResearch.WordTrace tailWord_3164786 prefixEnd_3164786 361123641471146665315649 := by
  unfold tailWord_3164786
  simp only [CollatzResearch.WordTrace]
  refine ⟨28857307078132074815578553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76952818875018866174876141 28857307078132074815578553)
  ·
    refine ⟨21642980308599056111683915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28857307078132074815578553 21642980308599056111683915)
    ·
      refine ⟨32464470462898584167525873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21642980308599056111683915 32464470462898584167525873)
      ·
        refine ⟨24348352847173938125644405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32464470462898584167525873 24348352847173938125644405)
        ·
          refine ⟨2282658079422556699279163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24348352847173938125644405 2282658079422556699279163)
          ·
            refine ⟨3423987119133835048918745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282658079422556699279163 3423987119133835048918745)
            ·
              refine ⟨2567990339350376286689059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423987119133835048918745 2567990339350376286689059)
              ·
                refine ⟨3851985509025564430033589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567990339350376286689059 3851985509025564430033589)
                ·
                  refine ⟨361123641471146665315649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851985509025564430033589 361123641471146665315649)
                  ·
                    rfl

theorem cell22_3164786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3164786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164786 prefixEnd_3164786 := by exact prefixLift 3164786
  have htrace : WordTrace (prefixWord ++ tailWord_3164786) baseStart_3164786 baseEnd_3164786 := by
    simpa [prefixWord, tailWord_3164786, baseEnd_3164786] using wordTrace_append hprefix tailTrace_3164786
  have hstable : (prefixWord ++ tailWord_3164786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164786).length < 2 ^ (prefixWord ++ tailWord_3164786).sum := by decide
  have hdescent : baseEnd_3164786 < baseStart_3164786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164795 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 6, 3]
def baseStart_3164795 : Nat := 118140960795 + 3164795 * 2 ^ 59
def prefixEnd_3164795 : Nat := 4983230072969 + 3 ^ 40 * 3164795 * 2
def baseEnd_3164795 : Nat := 1083374005297366972471919

theorem tailTrace_3164795 : CollatzResearch.WordTrace tailWord_3164795 prefixEnd_3164795 1083374005297366972471919 := by
  unfold tailWord_3164795
  simp only [CollatzResearch.WordTrace]
  refine ⟨115429556569495693799391839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76953037712997129199594559 115429556569495693799391839)
  ·
    refine ⟨173144334854243540699087759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115429556569495693799391839 173144334854243540699087759)
    ·
      refine ⟨259716502281365311048631639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173144334854243540699087759 259716502281365311048631639)
      ·
        refine ⟨389574753422047966572947459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259716502281365311048631639 389574753422047966572947459)
        ·
          refine ⟨584362130133071949859421189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389574753422047966572947459 584362130133071949859421189)
          ·
            refine ⟨109567899399950990598641473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 584362130133071949859421189 109567899399950990598641473)
            ·
              refine ⟨82175924549963242948981105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109567899399950990598641473 82175924549963242948981105)
              ·
                refine ⟨61631943412472432211735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82175924549963242948981105 61631943412472432211735829)
                ·
                  refine ⟨2888997347459645259925117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61631943412472432211735829 2888997347459645259925117)
                  ·
                    refine ⟨1083374005297366972471919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2888997347459645259925117 1083374005297366972471919)
                    ·
                      rfl

theorem cell22_3164795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].length) (baseStart_3164795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164795 prefixEnd_3164795 := by exact prefixLift 3164795
  have htrace : WordTrace (prefixWord ++ tailWord_3164795) baseStart_3164795 baseEnd_3164795 := by
    simpa [prefixWord, tailWord_3164795, baseEnd_3164795] using wordTrace_append hprefix tailTrace_3164795
  have hstable : (prefixWord ++ tailWord_3164795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164795).length < 2 ^ (prefixWord ++ tailWord_3164795).sum := by decide
  have hdescent : baseEnd_3164795 < baseStart_3164795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164846 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3164846 : Nat := 118140960795 + 3164846 * 2 ^ 59
def prefixEnd_3164846 : Nat := 4983230072969 + 3 ^ 40 * 3164846 * 2
def baseEnd_3164846 : Nat := 1083391463639619839446763

theorem tailTrace_3164846 : CollatzResearch.WordTrace tailWord_3164846 prefixEnd_3164846 1083391463639619839446763 := by
  unfold tailWord_3164846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428927086538866188687299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76954277794873953006332261 14428927086538866188687299)
  ·
    refine ⟨21643390629808299283030949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14428927086538866188687299 21643390629808299283030949)
    ·
      refine ⟨4058135743089056115568303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21643390629808299283030949 4058135743089056115568303)
      ·
        refine ⟨6087203614633584173352455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058135743089056115568303 6087203614633584173352455)
        ·
          refine ⟨9130805421950376260028683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087203614633584173352455 9130805421950376260028683)
          ·
            refine ⟨13696208132925564390043025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130805421950376260028683 13696208132925564390043025)
            ·
              refine ⟨10272156099694173292532269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13696208132925564390043025 10272156099694173292532269)
              ·
                refine ⟨3852058537385314984699601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10272156099694173292532269 3852058537385314984699601)
                ·
                  refine ⟨2889043903038986238524701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852058537385314984699601 2889043903038986238524701)
                  ·
                    refine ⟨1083391463639619839446763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889043903038986238524701 1083391463639619839446763)
                    ·
                      rfl

theorem cell22_3164846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3164846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164846 prefixEnd_3164846 := by exact prefixLift 3164846
  have htrace : WordTrace (prefixWord ++ tailWord_3164846) baseStart_3164846 baseEnd_3164846 := by
    simpa [prefixWord, tailWord_3164846, baseEnd_3164846] using wordTrace_append hprefix tailTrace_3164846
  have hstable : (prefixWord ++ tailWord_3164846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164846).length < 2 ^ (prefixWord ++ tailWord_3164846).sum := by decide
  have hdescent : baseEnd_3164846 < baseStart_3164846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164887 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 5]
def baseStart_3164887 : Nat := 118140960795 + 3164887 * 2 ^ 59
def prefixEnd_3164887 : Nat := 4983230072969 + 3 ^ 40 * 3164887 * 2
def baseEnd_3164887 : Nat := 361135166259169799723879

theorem tailTrace_3164887 : CollatzResearch.WordTrace tailWord_3164887 prefixEnd_3164887 361135166259169799723879 := by
  unfold tailWord_3164887
  simp only [CollatzResearch.WordTrace]
  refine ⟨115432912085162393511740915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76955274723441595674493943 115432912085162393511740915)
  ·
    refine ⟨173149368127743590267611373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115432912085162393511740915 173149368127743590267611373)
    ·
      refine ⟨64931013047903846350354265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173149368127743590267611373 64931013047903846350354265)
      ·
        refine ⟨48698259785927884762765699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64931013047903846350354265 48698259785927884762765699)
        ·
          refine ⟨73047389678891827144148549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48698259785927884762765699 73047389678891827144148549)
          ·
            refine ⟨13696385564792217589527853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73047389678891827144148549 13696385564792217589527853)
            ·
              refine ⟨5136144586797081596072945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13696385564792217589527853 5136144586797081596072945)
              ·
                refine ⟨3852108440097811197054709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136144586797081596072945 3852108440097811197054709)
                ·
                  refine ⟨361135166259169799723879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3852108440097811197054709 361135166259169799723879)
                  ·
                    rfl

theorem cell22_3164887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].length) (baseStart_3164887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164887 prefixEnd_3164887 := by exact prefixLift 3164887
  have htrace : WordTrace (prefixWord ++ tailWord_3164887) baseStart_3164887 baseEnd_3164887 := by
    simpa [prefixWord, tailWord_3164887, baseEnd_3164887] using wordTrace_append hprefix tailTrace_3164887
  have hstable : (prefixWord ++ tailWord_3164887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164887).length < 2 ^ (prefixWord ++ tailWord_3164887).sum := by decide
  have hdescent : baseEnd_3164887 < baseStart_3164887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164947 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 4, 3]
def baseStart_3164947 : Nat := 118140960795 + 3164947 * 2 ^ 59
def prefixEnd_3164947 : Nat := 4983230072969 + 3 ^ 40 * 3164947 * 2
def baseEnd_3164947 : Nat := 1083426038003689242671453

theorem tailTrace_3164947 : CollatzResearch.WordTrace tailWord_3164947 prefixEnd_3164947 1083426038003689242671453 := by
  unfold tailWord_3164947
  simp only [CollatzResearch.WordTrace]
  refine ⟨115435100464945023758925095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76956733643296682505950063 115435100464945023758925095)
  ·
    refine ⟨173152650697417535638387643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115435100464945023758925095 173152650697417535638387643)
    ·
      refine ⟨259728976046126303457581465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173152650697417535638387643 259728976046126303457581465)
      ·
        refine ⟨194796732034594727593186099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259728976046126303457581465 194796732034594727593186099)
        ·
          refine ⟨292195098051892091389779149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194796732034594727593186099 292195098051892091389779149)
          ·
            refine ⟨109573161769459534271167181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292195098051892091389779149 109573161769459534271167181)
            ·
              refine ⟨41089935663547325351687693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109573161769459534271167181 41089935663547325351687693)
              ·
                refine ⟨15408725873830247006882885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41089935663547325351687693 15408725873830247006882885)
                ·
                  refine ⟨2889136101343171313790541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15408725873830247006882885 2889136101343171313790541)
                  ·
                    refine ⟨1083426038003689242671453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889136101343171313790541 1083426038003689242671453)
                    ·
                      rfl

theorem cell22_3164947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].length) (baseStart_3164947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164947 prefixEnd_3164947 := by exact prefixLift 3164947
  have htrace : WordTrace (prefixWord ++ tailWord_3164947) baseStart_3164947 baseEnd_3164947 := by
    simpa [prefixWord, tailWord_3164947, baseEnd_3164947] using wordTrace_append hprefix tailTrace_3164947
  have hstable : (prefixWord ++ tailWord_3164947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164947).length < 2 ^ (prefixWord ++ tailWord_3164947).sum := by decide
  have hdescent : baseEnd_3164947 < baseStart_3164947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164979 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_3164979 : Nat := 118140960795 + 3164979 * 2 ^ 59
def prefixEnd_3164979 : Nat := 4983230072969 + 3 ^ 40 * 3164979 * 2
def baseEnd_3164979 : Nat := 1083436992257651825871355

theorem tailTrace_3164979 : CollatzResearch.WordTrace tailWord_3164979 prefixEnd_3164979 1083436992257651825871355 := by
  unfold tailWord_3164979
  simp only [CollatzResearch.WordTrace]
  refine ⟨115436267600829093224089991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76957511733886062149393327 115436267600829093224089991)
  ·
    refine ⟨173154401401243639836134987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115436267600829093224089991 173154401401243639836134987)
    ·
      refine ⟨259731602101865459754202481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173154401401243639836134987 259731602101865459754202481)
      ·
        refine ⟨194798701576399094815651861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259731602101865459754202481 194798701576399094815651861)
        ·
          refine ⟨9131189136393707569483681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194798701576399094815651861 9131189136393707569483681)
          ·
            refine ⟨6848391852295280677112761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131189136393707569483681 6848391852295280677112761)
            ·
              refine ⟨5136293889221460507834571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848391852295280677112761 5136293889221460507834571)
              ·
                refine ⟨7704440833832190761751857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136293889221460507834571 7704440833832190761751857)
                ·
                  refine ⟨5778330625374143071313893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704440833832190761751857 5778330625374143071313893)
                  ·
                    refine ⟨1083436992257651825871355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778330625374143071313893 1083436992257651825871355)
                    ·
                      rfl

theorem cell22_3164979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_3164979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3164979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3164979 prefixEnd_3164979 := by exact prefixLift 3164979
  have htrace : WordTrace (prefixWord ++ tailWord_3164979) baseStart_3164979 baseEnd_3164979 := by
    simpa [prefixWord, tailWord_3164979, baseEnd_3164979] using wordTrace_append hprefix tailTrace_3164979
  have hstable : (prefixWord ++ tailWord_3164979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164979).length < 2 ^ (prefixWord ++ tailWord_3164979).sum := by decide
  have hdescent : baseEnd_3164979 < baseStart_3164979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3165037 : Nat := 118140960795 + 3165037 * 2 ^ 59
def prefixEnd_3165037 : Nat := 4983230072969 + 3 ^ 40 * 3165037 * 2
def baseEnd_3165037 : Nat := 1083456846842959007921177

theorem tailTrace_3165037 : CollatzResearch.WordTrace tailWord_3165037 prefixEnd_3165037 1083456846842959007921177 := by
  unfold tailWord_3165037
  simp only [CollatzResearch.WordTrace]
  refine ⟨115438383034618969129701365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76958922023079312753134243 115438383034618969129701365)
  ·
    refine ⟨10822348409495528355909503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115438383034618969129701365 10822348409495528355909503)
    ·
      refine ⟨16233522614243292533864255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822348409495528355909503 16233522614243292533864255)
      ·
        refine ⟨24350283921364938800796383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233522614243292533864255 24350283921364938800796383)
        ·
          refine ⟨36525425882047408201194575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24350283921364938800796383 36525425882047408201194575)
          ·
            refine ⟨54788138823071112301791863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36525425882047408201194575 54788138823071112301791863)
            ·
              refine ⟨82182208234606668452687795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54788138823071112301791863 82182208234606668452687795)
              ·
                refine ⟨123273312351910002679031693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82182208234606668452687795 123273312351910002679031693)
                ·
                  refine ⟨46227492131966251004636885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123273312351910002679031693 46227492131966251004636885)
                  ·
                    refine ⟨1083456846842959007921177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46227492131966251004636885 1083456846842959007921177)
                    ·
                      rfl

theorem cell22_3165037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3165037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165037 prefixEnd_3165037 := by exact prefixLift 3165037
  have htrace : WordTrace (prefixWord ++ tailWord_3165037) baseStart_3165037 baseEnd_3165037 := by
    simpa [prefixWord, tailWord_3165037, baseEnd_3165037] using wordTrace_append hprefix tailTrace_3165037
  have hstable : (prefixWord ++ tailWord_3165037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165037).length < 2 ^ (prefixWord ++ tailWord_3165037).sum := by decide
  have hdescent : baseEnd_3165037 < baseStart_3165037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165067 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 6]
def baseStart_3165067 : Nat := 118140960795 + 3165067 * 2 ^ 59
def prefixEnd_3165067 : Nat := 4983230072969 + 3 ^ 40 * 3165067 * 2
def baseEnd_3165067 : Nat := 361155705485349643223695

theorem tailTrace_3165067 : CollatzResearch.WordTrace tailWord_3165067 prefixEnd_3165067 361155705485349643223695 := by
  unfold tailWord_3165067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115439477224510284253293455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76959651483006856168862303 115439477224510284253293455)
  ·
    refine ⟨173159215836765426379940183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115439477224510284253293455 173159215836765426379940183)
    ·
      refine ⟨259738823755148139569910275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173159215836765426379940183 259738823755148139569910275)
      ·
        refine ⟨389608235632722209354865413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259738823755148139569910275 389608235632722209354865413)
        ·
          refine ⟨73051544181135414254037265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389608235632722209354865413 73051544181135414254037265)
          ·
            refine ⟨54788658135851560690527949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73051544181135414254037265 54788658135851560690527949)
            ·
              refine ⟨20545746800944335258947981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54788658135851560690527949 20545746800944335258947981)
              ·
                refine ⟨7704655050354125722105493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545746800944335258947981 7704655050354125722105493)
                ·
                  refine ⟨361155705485349643223695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7704655050354125722105493 361155705485349643223695)
                  ·
                    rfl

theorem cell22_3165067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_3165067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165067 prefixEnd_3165067 := by exact prefixLift 3165067
  have htrace : WordTrace (prefixWord ++ tailWord_3165067) baseStart_3165067 baseEnd_3165067 := by
    simpa [prefixWord, tailWord_3165067, baseEnd_3165067] using wordTrace_append hprefix tailTrace_3165067
  have hstable : (prefixWord ++ tailWord_3165067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165067).length < 2 ^ (prefixWord ++ tailWord_3165067).sum := by decide
  have hdescent : baseEnd_3165067 < baseStart_3165067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165097 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3165097 : Nat := 118140960795 + 3165097 * 2 ^ 59
def prefixEnd_3165097 : Nat := 4983230072969 + 3 ^ 40 * 3165097 * 2
def baseEnd_3165097 : Nat := 1083477386069138851420993

theorem tailTrace_3165097 : CollatzResearch.WordTrace tailWord_3165097 prefixEnd_3165097 1083477386069138851420993 := by
  unfold tailWord_3165097
  simp only [CollatzResearch.WordTrace]
  refine ⟨115440571414401599376885545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76960380942934399584590363 115440571414401599376885545)
  ·
    refine ⟨86580428560801199532664159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115440571414401599376885545 86580428560801199532664159)
    ·
      refine ⟨129870642841201799298996239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86580428560801199532664159 129870642841201799298996239)
      ·
        refine ⟨194805964261802698948494359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129870642841201799298996239 194805964261802698948494359)
        ·
          refine ⟨292208946392704048422741539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194805964261802698948494359 292208946392704048422741539)
          ·
            refine ⟨438313419589056072634112309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292208946392704048422741539 438313419589056072634112309)
            ·
              refine ⟨41091883086474006809448029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438313419589056072634112309 41091883086474006809448029)
              ·
                refine ⟨15409456157427752553543011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41091883086474006809448029 15409456157427752553543011)
                ·
                  refine ⟨23114184236141628830314517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15409456157427752553543011 23114184236141628830314517)
                  ·
                    refine ⟨1083477386069138851420993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23114184236141628830314517 1083477386069138851420993)
                    ·
                      rfl

theorem cell22_3165097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3165097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165097 prefixEnd_3165097 := by exact prefixLift 3165097
  have htrace : WordTrace (prefixWord ++ tailWord_3165097) baseStart_3165097 baseEnd_3165097 := by
    simpa [prefixWord, tailWord_3165097, baseEnd_3165097] using wordTrace_append hprefix tailTrace_3165097
  have hstable : (prefixWord ++ tailWord_3165097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165097).length < 2 ^ (prefixWord ++ tailWord_3165097).sum := by decide
  have hdescent : baseEnd_3165097 < baseStart_3165097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165112 : List Nat := [2, 1, 2, 1, 2, 4, 10]
def baseStart_3165112 : Nat := 118140960795 + 3165112 * 2 ^ 59
def prefixEnd_3165112 : Nat := 4983230072969 + 3 ^ 40 * 3165112 * 2
def baseEnd_3165112 : Nat := 40128982254654956010961

theorem tailTrace_3165112 : CollatzResearch.WordTrace tailWord_3165112 prefixEnd_3165112 40128982254654956010961 := by
  unfold tailWord_3165112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57720559254673628469340795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76960745672898171292454393 57720559254673628469340795)
  ·
    refine ⟨86580838882010442704011193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57720559254673628469340795 86580838882010442704011193)
    ·
      refine ⟨64935629161507832028008395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86580838882010442704011193 64935629161507832028008395)
      ·
        refine ⟨97403443742261748042012593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64935629161507832028008395 97403443742261748042012593)
        ·
          refine ⟨73052582806696311031509445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97403443742261748042012593 73052582806696311031509445)
          ·
            refine ⟨13697359276255558318408021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73052582806696311031509445 13697359276255558318408021)
            ·
              refine ⟨40128982254654956010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13697359276255558318408021 40128982254654956010961)
              ·
                rfl

theorem cell22_3165112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 10].length) (baseStart_3165112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165112 prefixEnd_3165112 := by exact prefixLift 3165112
  have htrace : WordTrace (prefixWord ++ tailWord_3165112) baseStart_3165112 baseEnd_3165112 := by
    simpa [prefixWord, tailWord_3165112, baseEnd_3165112] using wordTrace_append hprefix tailTrace_3165112
  have hstable : (prefixWord ++ tailWord_3165112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165112).length < 2 ^ (prefixWord ++ tailWord_3165112).sum := by decide
  have hdescent : baseEnd_3165112 < baseStart_3165112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165114 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_3165114 : Nat := 118140960795 + 3165114 * 2 ^ 59
def prefixEnd_3165114 : Nat := 4983230072969 + 3 ^ 40 * 3165114 * 2
def baseEnd_3165114 : Nat := 1083483205516556473745941

theorem tailTrace_3165114 : CollatzResearch.WordTrace tailWord_3165114 prefixEnd_3165114 1083483205516556473745941 := by
  unfold tailWord_3165114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28860297863835002820063599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76960794303560007520169597 28860297863835002820063599)
  ·
    refine ⟨43290446795752504230095399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28860297863835002820063599 43290446795752504230095399)
    ·
      refine ⟨64935670193628756345143099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43290446795752504230095399 64935670193628756345143099)
      ·
        refine ⟨97403505290443134517714649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64935670193628756345143099 97403505290443134517714649)
        ·
          refine ⟨73052628967832350888285987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97403505290443134517714649 73052628967832350888285987)
          ·
            refine ⟨109578943451748526332428981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73052628967832350888285987 109578943451748526332428981)
            ·
              refine ⟨10273025948601424343665217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109578943451748526332428981 10273025948601424343665217)
              ·
                refine ⟨7704769461451068257748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10273025948601424343665217 7704769461451068257748913)
                ·
                  refine ⟨5778577096088301193311685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7704769461451068257748913 5778577096088301193311685)
                  ·
                    refine ⟨1083483205516556473745941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778577096088301193311685 1083483205516556473745941)
                    ·
                      rfl

theorem cell22_3165114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_3165114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165114 prefixEnd_3165114 := by exact prefixLift 3165114
  have htrace : WordTrace (prefixWord ++ tailWord_3165114) baseStart_3165114 baseEnd_3165114 := by
    simpa [prefixWord, tailWord_3165114, baseEnd_3165114] using wordTrace_append hprefix tailTrace_3165114
  have hstable : (prefixWord ++ tailWord_3165114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165114).length < 2 ^ (prefixWord ++ tailWord_3165114).sum := by decide
  have hdescent : baseEnd_3165114 < baseStart_3165114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165118 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3165118 : Nat := 118140960795 + 3165118 * 2 ^ 59
def prefixEnd_3165118 : Nat := 4983230072969 + 3 ^ 40 * 3165118 * 2
def baseEnd_3165118 : Nat := 361161524932767265548643

theorem tailTrace_3165118 : CollatzResearch.WordTrace tailWord_3165118 prefixEnd_3165118 361161524932767265548643 := by
  unfold tailWord_3165118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430167168415689995425001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76960891564883679975600005 14430167168415689995425001)
  ·
    refine ⟨10822625376311767496568751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14430167168415689995425001 10822625376311767496568751)
    ·
      refine ⟨16233938064467651244853127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822625376311767496568751 16233938064467651244853127)
      ·
        refine ⟨24350907096701476867279691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233938064467651244853127 24350907096701476867279691)
        ·
          refine ⟨36526360645052215300919537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24350907096701476867279691 36526360645052215300919537)
          ·
            refine ⟨27394770483789161475689653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36526360645052215300919537 27394770483789161475689653)
            ·
              refine ⟨2568259732855233888345905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27394770483789161475689653 2568259732855233888345905)
              ·
                refine ⟨1926194799641425416259429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568259732855233888345905 1926194799641425416259429)
                ·
                  refine ⟨361161524932767265548643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926194799641425416259429 361161524932767265548643)
                  ·
                    rfl

theorem cell22_3165118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3165118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165118 prefixEnd_3165118 := by exact prefixLift 3165118
  have htrace : WordTrace (prefixWord ++ tailWord_3165118) baseStart_3165118 baseEnd_3165118 := by
    simpa [prefixWord, tailWord_3165118, baseEnd_3165118] using wordTrace_append hprefix tailTrace_3165118
  have hstable : (prefixWord ++ tailWord_3165118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165118).length < 2 ^ (prefixWord ++ tailWord_3165118).sum := by decide
  have hdescent : baseEnd_3165118 < baseStart_3165118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165189 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3165189 : Nat := 118140960795 + 3165189 * 2 ^ 59
def prefixEnd_3165189 : Nat := 4983230072969 + 3 ^ 40 * 3165189 * 2
def baseEnd_3165189 : Nat := 1083508879549281278120711

theorem tailTrace_3165189 : CollatzResearch.WordTrace tailWord_3165189 prefixEnd_3165189 1083508879549281278120711 := by
  unfold tailWord_3165189
  simp only [CollatzResearch.WordTrace]
  refine ⟨115443926930068299089234621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76962617953378866059489747 115443926930068299089234621)
  ·
    refine ⟨43291472598775612158462983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115443926930068299089234621 43291472598775612158462983)
    ·
      refine ⟨64937208898163418237694475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43291472598775612158462983 64937208898163418237694475)
      ·
        refine ⟨97405813347245127356541713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64937208898163418237694475 97405813347245127356541713)
        ·
          refine ⟨73054360010433845517406285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97405813347245127356541713 73054360010433845517406285)
          ·
            refine ⟨27395385003912692069027357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73054360010433845517406285 27395385003912692069027357)
            ·
              refine ⟨10273269376467259525885259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27395385003912692069027357 10273269376467259525885259)
              ·
                refine ⟨15409904064700889288827889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273269376467259525885259 15409904064700889288827889)
                ·
                  refine ⟨11557428048525666966620917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15409904064700889288827889 11557428048525666966620917)
                  ·
                    refine ⟨1083508879549281278120711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11557428048525666966620917 1083508879549281278120711)
                    ·
                      rfl

theorem cell22_3165189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3165189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165189 prefixEnd_3165189 := by exact prefixLift 3165189
  have htrace : WordTrace (prefixWord ++ tailWord_3165189) baseStart_3165189 baseEnd_3165189 := by
    simpa [prefixWord, tailWord_3165189, baseEnd_3165189] using wordTrace_append hprefix tailTrace_3165189
  have hstable : (prefixWord ++ tailWord_3165189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165189).length < 2 ^ (prefixWord ++ tailWord_3165189).sum := by decide
  have hdescent : baseEnd_3165189 < baseStart_3165189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165221 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_3165221 : Nat := 118140960795 + 3165221 * 2 ^ 59
def prefixEnd_3165221 : Nat := 4983230072969 + 3 ^ 40 * 3165221 * 2
def baseEnd_3165221 : Nat := 1083519833803243861320613

theorem tailTrace_3165221 : CollatzResearch.WordTrace tailWord_3165221 prefixEnd_3165221 1083519833803243861320613 := by
  unfold tailWord_3165221
  simp only [CollatzResearch.WordTrace]
  refine ⟨115445094065952368554399517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76963396043968245702933011 115445094065952368554399517)
  ·
    refine ⟨43291910274732138207899819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115445094065952368554399517 43291910274732138207899819)
    ·
      refine ⟨64937865412098207311849729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43291910274732138207899819 64937865412098207311849729)
      ·
        refine ⟨48703399059073655483887297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64937865412098207311849729 48703399059073655483887297)
        ·
          refine ⟨36527549294305241612915473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48703399059073655483887297 36527549294305241612915473)
          ·
            refine ⟨27395661970728931209686605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36527549294305241612915473 27395661970728931209686605)
            ·
              refine ⟨10273373239023349203632477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27395661970728931209686605 10273373239023349203632477)
              ·
                refine ⟨3852514964633755951362179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10273373239023349203632477 3852514964633755951362179)
                ·
                  refine ⟨5778772446950633927043269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852514964633755951362179 5778772446950633927043269)
                  ·
                    refine ⟨1083519833803243861320613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778772446950633927043269 1083519833803243861320613)
                    ·
                      rfl

theorem cell22_3165221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_3165221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165221 prefixEnd_3165221 := by exact prefixLift 3165221
  have htrace : WordTrace (prefixWord ++ tailWord_3165221) baseStart_3165221 baseEnd_3165221 := by
    simpa [prefixWord, tailWord_3165221, baseEnd_3165221] using wordTrace_append hprefix tailTrace_3165221
  have hstable : (prefixWord ++ tailWord_3165221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165221).length < 2 ^ (prefixWord ++ tailWord_3165221).sum := by decide
  have hdescent : baseEnd_3165221 < baseStart_3165221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165266 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3165266 : Nat := 118140960795 + 3165266 * 2 ^ 59
def prefixEnd_3165266 : Nat := 4983230072969 + 3 ^ 40 * 3165266 * 2
def baseEnd_3165266 : Nat := 1083535238222878743945475

theorem tailTrace_3165266 : CollatzResearch.WordTrace tailWord_3165266 prefixEnd_3165266 1083535238222878743945475 := by
  unfold tailWord_3165266
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861683837697335309946913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76964490233859560826525101 28861683837697335309946913)
  ·
    refine ⟨21646262878273001482460185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28861683837697335309946913 21646262878273001482460185)
    ·
      refine ⟨16234697158704751111845139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21646262878273001482460185 16234697158704751111845139)
      ·
        refine ⟨24352045738057126667767709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16234697158704751111845139 24352045738057126667767709)
        ·
          refine ⟨9132017151771422500412891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24352045738057126667767709 9132017151771422500412891)
          ·
            refine ⟨13698025727657133750619337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132017151771422500412891 13698025727657133750619337)
            ·
              refine ⟨10273519295742850312964503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13698025727657133750619337 10273519295742850312964503)
              ·
                refine ⟨15410278943614275469446755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273519295742850312964503 15410278943614275469446755)
                ·
                  refine ⟨23115418415421413204170133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15410278943614275469446755 23115418415421413204170133)
                  ·
                    refine ⟨1083535238222878743945475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23115418415421413204170133 1083535238222878743945475)
                    ·
                      rfl

theorem cell22_3165266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3165266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165266 prefixEnd_3165266 := by exact prefixLift 3165266
  have htrace : WordTrace (prefixWord ++ tailWord_3165266) baseStart_3165266 baseEnd_3165266 := by
    simpa [prefixWord, tailWord_3165266, baseEnd_3165266] using wordTrace_append hprefix tailTrace_3165266
  have hstable : (prefixWord ++ tailWord_3165266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165266).length < 2 ^ (prefixWord ++ tailWord_3165266).sum := by decide
  have hdescent : baseEnd_3165266 < baseStart_3165266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165341 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3165341 : Nat := 118140960795 + 3165341 * 2 ^ 59
def prefixEnd_3165341 : Nat := 4983230072969 + 3 ^ 40 * 3165341 * 2
def baseEnd_3165341 : Nat := 1083560912255603548320245

theorem tailTrace_3165341 : CollatzResearch.WordTrace tailWord_3165341 prefixEnd_3165341 1083560912255603548320245 := by
  unfold tailWord_3165341
  simp only [CollatzResearch.WordTrace]
  refine ⟨115449470825517629048767877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76966313883678419365845251 115449470825517629048767877)
  ·
    refine ⟨21646775779784555446643977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115449470825517629048767877 21646775779784555446643977)
    ·
      refine ⟨16235081834838416584982983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21646775779784555446643977 16235081834838416584982983)
      ·
        refine ⟨24352622752257624877474475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235081834838416584982983 24352622752257624877474475)
        ·
          refine ⟨36528934128386437316211713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24352622752257624877474475 36528934128386437316211713)
          ·
            refine ⟨27396700596289827987158785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36528934128386437316211713 27396700596289827987158785)
            ·
              refine ⟨20547525447217370990369089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27396700596289827987158785 20547525447217370990369089)
              ·
                refine ⟨15410644085413028242776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20547525447217370990369089 15410644085413028242776817)
                ·
                  refine ⟨11557983064059771182082613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15410644085413028242776817 11557983064059771182082613)
                  ·
                    refine ⟨1083560912255603548320245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11557983064059771182082613 1083560912255603548320245)
                    ·
                      rfl

theorem cell22_3165341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3165341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165341 prefixEnd_3165341 := by exact prefixLift 3165341
  have htrace : WordTrace (prefixWord ++ tailWord_3165341) baseStart_3165341 baseEnd_3165341 := by
    simpa [prefixWord, tailWord_3165341, baseEnd_3165341] using wordTrace_append hprefix tailTrace_3165341
  have hstable : (prefixWord ++ tailWord_3165341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165341).length < 2 ^ (prefixWord ++ tailWord_3165341).sum := by decide
  have hdescent : baseEnd_3165341 < baseStart_3165341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165390 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3165390 : Nat := 118140960795 + 3165390 * 2 ^ 59
def prefixEnd_3165390 : Nat := 4983230072969 + 3 ^ 40 * 3165390 * 2
def baseEnd_3165390 : Nat := 1083577685956983753845095

theorem tailTrace_3165390 : CollatzResearch.WordTrace tailWord_3165390 prefixEnd_3165390 1083577685956983753845095 := by
  unfold tailWord_3165390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14431407250292513802162703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76967505334893406944867749 14431407250292513802162703)
  ·
    refine ⟨21647110875438770703244055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14431407250292513802162703 21647110875438770703244055)
    ·
      refine ⟨32470666313158156054866083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21647110875438770703244055 32470666313158156054866083)
      ·
        refine ⟨48705999469737234082299125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32470666313158156054866083 48705999469737234082299125)
        ·
          refine ⟨4566187450287865695215543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48705999469737234082299125 4566187450287865695215543)
          ·
            refine ⟨6849281175431798542823315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566187450287865695215543 6849281175431798542823315)
            ·
              refine ⟨10273921763147697814234973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849281175431798542823315 10273921763147697814234973)
              ·
                refine ⟨3852720661180386680338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10273921763147697814234973 3852720661180386680338115)
                ·
                  refine ⟨5779080991770580020507173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852720661180386680338115 5779080991770580020507173)
                  ·
                    refine ⟨1083577685956983753845095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5779080991770580020507173 1083577685956983753845095)
                    ·
                      rfl

theorem cell22_3165390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3165390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165390 prefixEnd_3165390 := by exact prefixLift 3165390
  have htrace : WordTrace (prefixWord ++ tailWord_3165390) baseStart_3165390 baseEnd_3165390 := by
    simpa [prefixWord, tailWord_3165390, baseEnd_3165390] using wordTrace_append hprefix tailTrace_3165390
  have hstable : (prefixWord ++ tailWord_3165390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165390).length < 2 ^ (prefixWord ++ tailWord_3165390).sum := by decide
  have hdescent : baseEnd_3165390 < baseStart_3165390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165401 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_3165401 : Nat := 118140960795 + 3165401 * 2 ^ 59
def prefixEnd_3165401 : Nat := 4983230072969 + 3 ^ 40 * 3165401 * 2
def baseEnd_3165401 : Nat := 1083581451481783391820061

theorem tailTrace_3165401 : CollatzResearch.WordTrace tailWord_3165401 prefixEnd_3165401 1083581451481783391820061 := by
  unfold tailWord_3165401
  simp only [CollatzResearch.WordTrace]
  refine ⟨115451659205300259295952057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76967772803533506197301371 115451659205300259295952057)
  ·
    refine ⟨86588744403975194471964043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115451659205300259295952057 86588744403975194471964043)
    ·
      refine ⟨129883116605962791707946065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86588744403975194471964043 129883116605962791707946065)
      ·
        refine ⟨97412337454472093780959549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129883116605962791707946065 97412337454472093780959549)
        ·
          refine ⟨36529626545427035167859831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97412337454472093780959549 36529626545427035167859831)
          ·
            refine ⟨54794439818140552751789747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36529626545427035167859831 54794439818140552751789747)
            ·
              refine ⟨82191659727210829127684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54794439818140552751789747 82191659727210829127684621)
              ·
                refine ⟨30821872397704060922881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82191659727210829127684621 30821872397704060922881733)
                ·
                  refine ⟨5779101074569511423040325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30821872397704060922881733 5779101074569511423040325)
                  ·
                    refine ⟨1083581451481783391820061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5779101074569511423040325 1083581451481783391820061)
                    ·
                      rfl

theorem cell22_3165401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_3165401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165401 prefixEnd_3165401 := by exact prefixLift 3165401
  have htrace : WordTrace (prefixWord ++ tailWord_3165401) baseStart_3165401 baseEnd_3165401 := by
    simpa [prefixWord, tailWord_3165401, baseEnd_3165401] using wordTrace_append hprefix tailTrace_3165401
  have hstable : (prefixWord ++ tailWord_3165401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165401).length < 2 ^ (prefixWord ++ tailWord_3165401).sum := by decide
  have hdescent : baseEnd_3165401 < baseStart_3165401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165405 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3165405 : Nat := 118140960795 + 3165405 * 2 ^ 59
def prefixEnd_3165405 : Nat := 4983230072969 + 3 ^ 40 * 3165405 * 2
def baseEnd_3165405 : Nat := 361194273587842904906683

theorem tailTrace_3165405 : CollatzResearch.WordTrace tailWord_3165405 prefixEnd_3165405 361194273587842904906683 := by
  unfold tailWord_3165405
  simp only [CollatzResearch.WordTrace]
  refine ⟨115451805097285767979097669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76967870064857178652731779 115451805097285767979097669)
  ·
    refine ⟨21647213455741081496080813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115451805097285767979097669 21647213455741081496080813)
    ·
      refine ⟨8117705045902905561030305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21647213455741081496080813 8117705045902905561030305)
      ·
        refine ⟨6088278784427179170772729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117705045902905561030305 6088278784427179170772729)
        ·
          refine ⟨4566209088320384378079547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088278784427179170772729 4566209088320384378079547)
          ·
            refine ⟨6849313632480576567119321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566209088320384378079547 6849313632480576567119321)
            ·
              refine ⟨5136985224360432425339491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6849313632480576567119321 5136985224360432425339491)
              ·
                refine ⟨7705477836540648638009237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136985224360432425339491 7705477836540648638009237)
                ·
                  refine ⟨361194273587842904906683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7705477836540648638009237 361194273587842904906683)
                  ·
                    rfl

theorem cell22_3165405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3165405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165405 prefixEnd_3165405 := by exact prefixLift 3165405
  have htrace : WordTrace (prefixWord ++ tailWord_3165405) baseStart_3165405 baseEnd_3165405 := by
    simpa [prefixWord, tailWord_3165405, baseEnd_3165405] using wordTrace_append hprefix tailTrace_3165405
  have hstable : (prefixWord ++ tailWord_3165405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165405).length < 2 ^ (prefixWord ++ tailWord_3165405).sum := by decide
  have hdescent : baseEnd_3165405 < baseStart_3165405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165416 : List Nat := [2, 1, 4, 1, 2, 1, 2, 9]
def baseStart_3165416 : Nat := 118140960795 + 3165416 * 2 ^ 59
def prefixEnd_3165416 : Nat := 4983230072969 + 3 ^ 40 * 3165416 * 2
def baseEnd_3165416 : Nat := 120398509587592039188335

theorem tailTrace_3165416 : CollatzResearch.WordTrace tailWord_3165416 prefixEnd_3165416 120398509587592039188335 := by
  unfold tailWord_3165416
  simp only [CollatzResearch.WordTrace]
  refine ⟨57726103150122958428874051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76968137533497277905165401 57726103150122958428874051)
  ·
    refine ⟨86589154725184437643311077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57726103150122958428874051 86589154725184437643311077)
    ·
      refine ⟨16235466510972082058120827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86589154725184437643311077 16235466510972082058120827)
      ·
        refine ⟨24353199766458123087181241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235466510972082058120827 24353199766458123087181241)
        ·
          refine ⟨18264899824843592315385931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24353199766458123087181241 18264899824843592315385931)
          ·
            refine ⟨27397349737265388473078897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18264899824843592315385931 27397349737265388473078897)
            ·
              refine ⟨20548012302949041354809173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27397349737265388473078897 20548012302949041354809173)
              ·
                refine ⟨120398509587592039188335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20548012302949041354809173 120398509587592039188335)
                ·
                  rfl

theorem cell22_3165416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_3165416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165416 prefixEnd_3165416 := by exact prefixLift 3165416
  have htrace : WordTrace (prefixWord ++ tailWord_3165416) baseStart_3165416 baseEnd_3165416 := by
    simpa [prefixWord, tailWord_3165416, baseEnd_3165416] using wordTrace_append hprefix tailTrace_3165416
  have hstable : (prefixWord ++ tailWord_3165416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165416).length < 2 ^ (prefixWord ++ tailWord_3165416).sum := by decide
  have hdescent : baseEnd_3165416 < baseStart_3165416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165572 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3165572 : Nat := 118140960795 + 3165572 * 2 ^ 59
def prefixEnd_3165572 : Nat := 4983230072969 + 3 ^ 40 * 3165572 * 2
def baseEnd_3165572 : Nat := 1083639988276395945794537

theorem tailTrace_3165572 : CollatzResearch.WordTrace tailWord_3165572 prefixEnd_3165572 1083639988276395945794537 := by
  unfold tailWord_3165572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728948043840377750213485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76971930725120503666951313 57728948043840377750213485)
  ·
    refine ⟨21648355516440141656330057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57728948043840377750213485 21648355516440141656330057)
    ·
      refine ⟨16236266637330106242247543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21648355516440141656330057 16236266637330106242247543)
      ·
        refine ⟨24354399955995159363371315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236266637330106242247543 24354399955995159363371315)
        ·
          refine ⟨36531599933992739045056973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24354399955995159363371315 36531599933992739045056973)
          ·
            refine ⟨13699349975247277141896365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36531599933992739045056973 13699349975247277141896365)
            ·
              refine ⟨5137256240717728928211137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13699349975247277141896365 5137256240717728928211137)
              ·
                refine ⟨3852942180538296696158353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137256240717728928211137 3852942180538296696158353)
                ·
                  refine ⟨2889706635403722522118765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852942180538296696158353 2889706635403722522118765)
                  ·
                    refine ⟨1083639988276395945794537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889706635403722522118765 1083639988276395945794537)
                    ·
                      rfl

theorem cell22_3165572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3165572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165572 prefixEnd_3165572 := by exact prefixLift 3165572
  have htrace : WordTrace (prefixWord ++ tailWord_3165572) baseStart_3165572 baseEnd_3165572 := by
    simpa [prefixWord, tailWord_3165572, baseEnd_3165572] using wordTrace_append hprefix tailTrace_3165572
  have hstable : (prefixWord ++ tailWord_3165572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165572).length < 2 ^ (prefixWord ++ tailWord_3165572).sum := by decide
  have hdescent : baseEnd_3165572 < baseStart_3165572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165600 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_3165600 : Nat := 118140960795 + 3165600 * 2 ^ 59
def prefixEnd_3165600 : Nat := 4983230072969 + 3 ^ 40 * 3165600 * 2
def baseEnd_3165600 : Nat := 1083649573248613206094451

theorem tailTrace_3165600 : CollatzResearch.WordTrace tailWord_3165600 prefixEnd_3165600 1083649573248613206094451 := by
  unfold tailWord_3165600
  simp only [CollatzResearch.WordTrace]
  refine ⟨57729458665789658141223127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76972611554386210854964169 57729458665789658141223127)
  ·
    refine ⟨86594187998684487211834691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57729458665789658141223127 86594187998684487211834691)
    ·
      refine ⟨129891281998026730817752037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86594187998684487211834691 129891281998026730817752037)
      ·
        refine ⟨24354615374630012028328507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129891281998026730817752037 24354615374630012028328507)
        ·
          refine ⟨36531923061945018042492761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24354615374630012028328507 36531923061945018042492761)
          ·
            refine ⟨27398942296458763531869571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36531923061945018042492761 27398942296458763531869571)
            ·
              refine ⟨41098413444688145297804357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27398942296458763531869571 41098413444688145297804357)
              ·
                refine ⟨7705952520879027243338317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41098413444688145297804357 7705952520879027243338317)
                ·
                  refine ⟨2889732195329635216251869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7705952520879027243338317 2889732195329635216251869)
                  ·
                    refine ⟨1083649573248613206094451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889732195329635216251869 1083649573248613206094451)
                    ·
                      rfl

theorem cell22_3165600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_3165600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165600 prefixEnd_3165600 := by exact prefixLift 3165600
  have htrace : WordTrace (prefixWord ++ tailWord_3165600) baseStart_3165600 baseEnd_3165600 := by
    simpa [prefixWord, tailWord_3165600, baseEnd_3165600] using wordTrace_append hprefix tailTrace_3165600
  have hstable : (prefixWord ++ tailWord_3165600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165600).length < 2 ^ (prefixWord ++ tailWord_3165600).sum := by decide
  have hdescent : baseEnd_3165600 < baseStart_3165600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165602 : List Nat := [3, 3, 1, 2, 1, 4, 2, 6]
def baseStart_3165602 : Nat := 118140960795 + 3165602 * 2 ^ 59
def prefixEnd_3165602 : Nat := 4983230072969 + 3 ^ 40 * 3165602 * 2
def baseEnd_3165602 : Nat := 120405584209942874171605

theorem tailTrace_3165602 : CollatzResearch.WordTrace tailWord_3165602 prefixEnd_3165602 120405584209942874171605 := by
  unfold tailWord_3165602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28864747569393017656004765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76972660185048047082679373 28864747569393017656004765)
  ·
    refine ⟨10824280338522381621001787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28864747569393017656004765 10824280338522381621001787)
    ·
      refine ⟨16236420507783572431502681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10824280338522381621001787 16236420507783572431502681)
      ·
        refine ⟨12177315380837679323627011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16236420507783572431502681 12177315380837679323627011)
        ·
          refine ⟨18265973071256518985440517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12177315380837679323627011 18265973071256518985440517)
          ·
            refine ⟨3424869950860597309770097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18265973071256518985440517 3424869950860597309770097)
            ·
              refine ⟨2568652463145447982327573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424869950860597309770097 2568652463145447982327573)
              ·
                refine ⟨120405584209942874171605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2568652463145447982327573 120405584209942874171605)
                ·
                  rfl

theorem cell22_3165602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_3165602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165602 prefixEnd_3165602 := by exact prefixLift 3165602
  have htrace : WordTrace (prefixWord ++ tailWord_3165602) baseStart_3165602 baseEnd_3165602 := by
    simpa [prefixWord, tailWord_3165602, baseEnd_3165602] using wordTrace_append hprefix tailTrace_3165602
  have hstable : (prefixWord ++ tailWord_3165602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165602).length < 2 ^ (prefixWord ++ tailWord_3165602).sum := by decide
  have hdescent : baseEnd_3165602 < baseStart_3165602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165630 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3165630 : Nat := 118140960795 + 3165630 * 2 ^ 59
def prefixEnd_3165630 : Nat := 4983230072969 + 3 ^ 40 * 3165630 * 2
def baseEnd_3165630 : Nat := 361219947620567709281453

theorem tailTrace_3165630 : CollatzResearch.WordTrace tailWord_3165630 prefixEnd_3165630 361219947620567709281453 := by
  unfold tailWord_3165630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432501440183828925754793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76973341014313754270692229 14432501440183828925754793)
  ·
    refine ⟨10824376080137871694316095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14432501440183828925754793 10824376080137871694316095)
    ·
      refine ⟨16236564120206807541474143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10824376080137871694316095 16236564120206807541474143)
      ·
        refine ⟨24354846180310211312211215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236564120206807541474143 24354846180310211312211215)
        ·
          refine ⟨36532269270465316968316823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24354846180310211312211215 36532269270465316968316823)
          ·
            refine ⟨54798403905697975452475235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36532269270465316968316823 54798403905697975452475235)
            ·
              refine ⟨82197605858546963178712853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54798403905697975452475235 82197605858546963178712853)
              ·
                refine ⟨3853012774619388899002165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82197605858546963178712853 3853012774619388899002165)
                ·
                  refine ⟨361219947620567709281453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3853012774619388899002165 361219947620567709281453)
                  ·
                    rfl

theorem cell22_3165630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3165630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165630 prefixEnd_3165630 := by exact prefixLift 3165630
  have htrace : WordTrace (prefixWord ++ tailWord_3165630) baseStart_3165630 baseEnd_3165630 := by
    simpa [prefixWord, tailWord_3165630, baseEnd_3165630] using wordTrace_append hprefix tailTrace_3165630
  have hstable : (prefixWord ++ tailWord_3165630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165630).length < 2 ^ (prefixWord ++ tailWord_3165630).sum := by decide
  have hdescent : baseEnd_3165630 < baseStart_3165630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165707 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_3165707 : Nat := 118140960795 + 3165707 * 2 ^ 59
def prefixEnd_3165707 : Nat := 4983230072969 + 3 ^ 40 * 3165707 * 2
def baseEnd_3165707 : Nat := 1083686201535300593669123

theorem tailTrace_3165707 : CollatzResearch.WordTrace tailWord_3165707 prefixEnd_3165707 1083686201535300593669123 := by
  unfold tailWord_3165707
  simp only [CollatzResearch.WordTrace]
  refine ⟨115462819942191673556591375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76975213294794449037727583 115462819942191673556591375)
  ·
    refine ⟨173194229913287510334887063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115462819942191673556591375 173194229913287510334887063)
    ·
      refine ⟨259791344869931265502330595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173194229913287510334887063 259791344869931265502330595)
      ·
        refine ⟨389687017304896898253495893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259791344869931265502330595 389687017304896898253495893)
        ·
          refine ⟨4566644734041760526408155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 389687017304896898253495893 4566644734041760526408155)
          ·
            refine ⟨6849967101062640789612233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566644734041760526408155 6849967101062640789612233)
            ·
              refine ⟨5137475325796980592209175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6849967101062640789612233 5137475325796980592209175)
              ·
                refine ⟨7706212988695470888313763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137475325796980592209175 7706212988695470888313763)
                ·
                  refine ⟨11559319483043206332470645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706212988695470888313763 11559319483043206332470645)
                  ·
                    refine ⟨1083686201535300593669123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11559319483043206332470645 1083686201535300593669123)
                    ·
                      rfl

theorem cell22_3165707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_3165707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165707 prefixEnd_3165707 := by exact prefixLift 3165707
  have htrace : WordTrace (prefixWord ++ tailWord_3165707) baseStart_3165707 baseEnd_3165707 := by
    simpa [prefixWord, tailWord_3165707, baseEnd_3165707] using wordTrace_append hprefix tailTrace_3165707
  have hstable : (prefixWord ++ tailWord_3165707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165707).length < 2 ^ (prefixWord ++ tailWord_3165707).sum := by decide
  have hdescent : baseEnd_3165707 < baseStart_3165707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165752 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_3165752 : Nat := 118140960795 + 3165752 * 2 ^ 59
def prefixEnd_3165752 : Nat := 4983230072969 + 3 ^ 40 * 3165752 * 2
def baseEnd_3165752 : Nat := 1083701605954935476293985

theorem tailTrace_3165752 : CollatzResearch.WordTrace tailWord_3165752 prefixEnd_3165752 1083701605954935476293985 := by
  unfold tailWord_3165752
  simp only [CollatzResearch.WordTrace]
  refine ⟨57732230613514323120989755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76976307484685764161319673 57732230613514323120989755)
  ·
    refine ⟨86598345920271484681484633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57732230613514323120989755 86598345920271484681484633)
    ·
      refine ⟨64948759440203613511113475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86598345920271484681484633 64948759440203613511113475)
      ·
        refine ⟨97423139160305420266670213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64948759440203613511113475 97423139160305420266670213)
        ·
          refine ⟨18266838592557266300000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97423139160305420266670213 18266838592557266300000665)
          ·
            refine ⟨13700128944417949725000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18266838592557266300000665 13700128944417949725000499)
            ·
              refine ⟨20550193416626924587500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700128944417949725000499 20550193416626924587500749)
              ·
                refine ⟨7706322531235096720312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20550193416626924587500749 7706322531235096720312781)
                ·
                  refine ⟨2889870949213161270117293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7706322531235096720312781 2889870949213161270117293)
                  ·
                    refine ⟨1083701605954935476293985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889870949213161270117293 1083701605954935476293985)
                    ·
                      rfl

theorem cell22_3165752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_3165752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165752 prefixEnd_3165752 := by exact prefixLift 3165752
  have htrace : WordTrace (prefixWord ++ tailWord_3165752) baseStart_3165752 baseEnd_3165752 := by
    simpa [prefixWord, tailWord_3165752, baseEnd_3165752] using wordTrace_append hprefix tailTrace_3165752
  have hstable : (prefixWord ++ tailWord_3165752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165752).length < 2 ^ (prefixWord ++ tailWord_3165752).sum := by decide
  have hdescent : baseEnd_3165752 < baseStart_3165752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165840 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_3165840 : Nat := 118140960795 + 3165840 * 2 ^ 59
def prefixEnd_3165840 : Nat := 4983230072969 + 3 ^ 40 * 3165840 * 2
def baseEnd_3165840 : Nat := 1083731730153332580093715

theorem tailTrace_3165840 : CollatzResearch.WordTrace tailWord_3165840 prefixEnd_3165840 1083731730153332580093715 := by
  unfold tailWord_3165840
  simp only [CollatzResearch.WordTrace]
  refine ⟨57733835425354918635591487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76978447233806558180788649 57733835425354918635591487)
  ·
    refine ⟨86600753138032377953387231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57733835425354918635591487 86600753138032377953387231)
    ·
      refine ⟨129901129707048566930080847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86600753138032377953387231 129901129707048566930080847)
      ·
        refine ⟨194851694560572850395121271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129901129707048566930080847 194851694560572850395121271)
        ·
          refine ⟨292277541840859275592681907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194851694560572850395121271 292277541840859275592681907)
          ·
            refine ⟨438416312761288913389022861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292277541840859275592681907 438416312761288913389022861)
            ·
              refine ⟨164406117285483342520883573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438416312761288913389022861 164406117285483342520883573)
              ·
                refine ⟨15413073495514063361332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164406117285483342520883573 15413073495514063361332835)
                ·
                  refine ⟨23119610243271095041999253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15413073495514063361332835 23119610243271095041999253)
                  ·
                    refine ⟨1083731730153332580093715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23119610243271095041999253 1083731730153332580093715)
                    ·
                      rfl

theorem cell22_3165840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_3165840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165840 prefixEnd_3165840 := by exact prefixLift 3165840
  have htrace : WordTrace (prefixWord ++ tailWord_3165840) baseStart_3165840 baseEnd_3165840 := by
    simpa [prefixWord, tailWord_3165840, baseEnd_3165840] using wordTrace_append hprefix tailTrace_3165840
  have hstable : (prefixWord ++ tailWord_3165840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165840).length < 2 ^ (prefixWord ++ tailWord_3165840).sum := by decide
  have hdescent : baseEnd_3165840 < baseStart_3165840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165859 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 2, 3]
def baseStart_3165859 : Nat := 118140960795 + 3165859 * 2 ^ 59
def prefixEnd_3165859 : Nat := 4983230072969 + 3 ^ 40 * 3165859 * 2
def baseEnd_3165859 : Nat := 1083738234241622863868657

theorem tailTrace_3165859 : CollatzResearch.WordTrace tailWord_3165859 prefixEnd_3165859 1083738234241622863868657 := by
  unfold tailWord_3165859
  simp only [CollatzResearch.WordTrace]
  refine ⟨115468363837641003516124631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76978909225094002344083087 115468363837641003516124631)
  ·
    refine ⟨173202545756461505274186947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115468363837641003516124631 173202545756461505274186947)
    ·
      refine ⟨259803818634692257911280421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173202545756461505274186947 259803818634692257911280421)
      ·
        refine ⟨48713215994004798358365079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259803818634692257911280421 48713215994004798358365079)
        ·
          refine ⟨73069823991007197537547619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48713215994004798358365079 73069823991007197537547619)
          ·
            refine ⟨109604735986510796306321429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73069823991007197537547619 109604735986510796306321429)
            ·
              refine ⟨5137721999367693576858817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109604735986510796306321429 5137721999367693576858817)
              ·
                refine ⟨3853291499525770182644113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137721999367693576858817 3853291499525770182644113)
                ·
                  refine ⟨2889968624644327636983085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853291499525770182644113 2889968624644327636983085)
                  ·
                    refine ⟨1083738234241622863868657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889968624644327636983085 1083738234241622863868657)
                    ·
                      rfl

theorem cell22_3165859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].length) (baseStart_3165859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165859 prefixEnd_3165859 := by exact prefixLift 3165859
  have htrace : WordTrace (prefixWord ++ tailWord_3165859) baseStart_3165859 baseEnd_3165859 := by
    simpa [prefixWord, tailWord_3165859, baseEnd_3165859] using wordTrace_append hprefix tailTrace_3165859
  have hstable : (prefixWord ++ tailWord_3165859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165859).length < 2 ^ (prefixWord ++ tailWord_3165859).sum := by decide
  have hdescent : baseEnd_3165859 < baseStart_3165859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165921 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3165921 : Nat := 118140960795 + 3165921 * 2 ^ 59
def prefixEnd_3165921 : Nat := 4983230072969 + 3 ^ 40 * 3165921 * 2
def baseEnd_3165921 : Nat := 1083759458108675368818467

theorem tailTrace_3165921 : CollatzResearch.WordTrace tailWord_3165921 prefixEnd_3165921 1083759458108675368818467 := by
  unfold tailWord_3165921
  simp only [CollatzResearch.WordTrace]
  refine ⟨115470625163416388104881617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76980416775610925403254411 115470625163416388104881617)
  ·
    refine ⟨86602968872562291078661213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115470625163416388104881617 86602968872562291078661213)
    ·
      refine ⟨32476113327210859154497955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86602968872562291078661213 32476113327210859154497955)
      ·
        refine ⟨48714169990816288731746933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32476113327210859154497955 48714169990816288731746933)
        ·
          refine ⟨4566953436639027068601275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48714169990816288731746933 4566953436639027068601275)
          ·
            refine ⟨6850430154958540602901913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566953436639027068601275 6850430154958540602901913)
            ·
              refine ⟨5137822616218905452176435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850430154958540602901913 5137822616218905452176435)
              ·
                refine ⟨7706733924328358178264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137822616218905452176435 7706733924328358178264653)
                ·
                  refine ⟨2890025221623134316849245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7706733924328358178264653 2890025221623134316849245)
                  ·
                    refine ⟨1083759458108675368818467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890025221623134316849245 1083759458108675368818467)
                    ·
                      rfl

theorem cell22_3165921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3165921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165921 prefixEnd_3165921 := by exact prefixLift 3165921
  have htrace : WordTrace (prefixWord ++ tailWord_3165921) baseStart_3165921 baseEnd_3165921 := by
    simpa [prefixWord, tailWord_3165921, baseEnd_3165921] using wordTrace_append hprefix tailTrace_3165921
  have hstable : (prefixWord ++ tailWord_3165921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165921).length < 2 ^ (prefixWord ++ tailWord_3165921).sum := by decide
  have hdescent : baseEnd_3165921 < baseStart_3165921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165932 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_3165932 : Nat := 118140960795 + 3165932 * 2 ^ 59
def prefixEnd_3165932 : Nat := 4983230072969 + 3 ^ 40 * 3165932 * 2
def baseEnd_3165932 : Nat := 1083763223633475006793433

theorem tailTrace_3165932 : CollatzResearch.WordTrace tailWord_3165932 prefixEnd_3165932 1083763223633475006793433 := by
  unfold tailWord_3165932
  simp only [CollatzResearch.WordTrace]
  refine ⟨57735513183188268491766025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76980684244251024655688033 57735513183188268491766025)
  ·
    refine ⟨43301634887391201368824519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57735513183188268491766025 43301634887391201368824519)
    ·
      refine ⟨64952452331086802053236779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43301634887391201368824519 64952452331086802053236779)
      ·
        refine ⟨97428678496630203079855169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64952452331086802053236779 97428678496630203079855169)
        ·
          refine ⟨73071508872472652309891377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97428678496630203079855169 73071508872472652309891377)
          ·
            refine ⟨54803631654354489232418533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73071508872472652309891377 54803631654354489232418533)
            ·
              refine ⟨10275680935191466731078475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54803631654354489232418533 10275680935191466731078475)
              ·
                refine ⟨15413521402787200096617713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10275680935191466731078475 15413521402787200096617713)
                ·
                  refine ⟨11560141052090400072463285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15413521402787200096617713 11560141052090400072463285)
                  ·
                    refine ⟨1083763223633475006793433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11560141052090400072463285 1083763223633475006793433)
                    ·
                      rfl

theorem cell22_3165932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_3165932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165932 prefixEnd_3165932 := by exact prefixLift 3165932
  have htrace : WordTrace (prefixWord ++ tailWord_3165932) baseStart_3165932 baseEnd_3165932 := by
    simpa [prefixWord, tailWord_3165932, baseEnd_3165932] using wordTrace_append hprefix tailTrace_3165932
  have hstable : (prefixWord ++ tailWord_3165932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165932).length < 2 ^ (prefixWord ++ tailWord_3165932).sum := by decide
  have hdescent : baseEnd_3165932 < baseStart_3165932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165964 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_3165964 : Nat := 118140960795 + 3165964 * 2 ^ 59
def prefixEnd_3165964 : Nat := 4983230072969 + 3 ^ 40 * 3165964 * 2
def baseEnd_3165964 : Nat := 1083774177887437589993335

theorem tailTrace_3165964 : CollatzResearch.WordTrace tailWord_3165964 prefixEnd_3165964 1083774177887437589993335 := by
  unfold tailWord_3165964
  simp only [CollatzResearch.WordTrace]
  refine ⟨57736096751130303224348473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76981462334840404299131297 57736096751130303224348473)
  ·
    refine ⟨43302072563347727418261355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57736096751130303224348473 43302072563347727418261355)
    ·
      refine ⟨64953108845021591127392033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43302072563347727418261355 64953108845021591127392033)
      ·
        refine ⟨48714831633766193345544025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64953108845021591127392033 48714831633766193345544025)
        ·
          refine ⟨36536123725324645009158019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48714831633766193345544025 36536123725324645009158019)
          ·
            refine ⟨54804185587986967513737029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36536123725324645009158019 54804185587986967513737029)
            ·
              refine ⟨10275784797747556408825693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54804185587986967513737029 10275784797747556408825693)
              ·
                refine ⟨3853419299155333653309635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10275784797747556408825693 3853419299155333653309635)
                ·
                  refine ⟨5780128948733000479964453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853419299155333653309635 5780128948733000479964453)
                  ·
                    refine ⟨1083774177887437589993335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780128948733000479964453 1083774177887437589993335)
                    ·
                      rfl

theorem cell22_3165964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_3165964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165964 prefixEnd_3165964 := by exact prefixLift 3165964
  have htrace : WordTrace (prefixWord ++ tailWord_3165964) baseStart_3165964 baseEnd_3165964 := by
    simpa [prefixWord, tailWord_3165964, baseEnd_3165964] using wordTrace_append hprefix tailTrace_3165964
  have hstable : (prefixWord ++ tailWord_3165964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165964).length < 2 ^ (prefixWord ++ tailWord_3165964).sum := by decide
  have hdescent : baseEnd_3165964 < baseStart_3165964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165972 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3165972 : Nat := 118140960795 + 3165972 * 2 ^ 59
def prefixEnd_3165972 : Nat := 4983230072969 + 3 ^ 40 * 3165972 * 2
def baseEnd_3165972 : Nat := 1083776916450928235793311

theorem tailTrace_3165972 : CollatzResearch.WordTrace tailWord_3165972 prefixEnd_3165972 1083776916450928235793311 := by
  unfold tailWord_3165972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57736242643115811907494085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76981656857487749209992113 57736242643115811907494085)
  ·
    refine ⟨10825545495584214732655141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57736242643115811907494085 10825545495584214732655141)
    ·
      refine ⟨2029789780422040262372839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10825545495584214732655141 2029789780422040262372839)
      ·
        refine ⟨3044684670633060393559259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029789780422040262372839 3044684670633060393559259)
        ·
          refine ⟨4567027005949590590338889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044684670633060393559259 4567027005949590590338889)
          ·
            refine ⟨3425270254462192942754167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567027005949590590338889 3425270254462192942754167)
            ·
              refine ⟨5137905381693289414131251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425270254462192942754167 5137905381693289414131251)
              ·
                refine ⟨7706858072539934121196877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137905381693289414131251 7706858072539934121196877)
                ·
                  refine ⟨2890071777202475295448829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7706858072539934121196877 2890071777202475295448829)
                  ·
                    refine ⟨1083776916450928235793311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890071777202475295448829 1083776916450928235793311)
                    ·
                      rfl

theorem cell22_3165972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3165972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3165972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3165972 prefixEnd_3165972 := by exact prefixLift 3165972
  have htrace : WordTrace (prefixWord ++ tailWord_3165972) baseStart_3165972 baseEnd_3165972 := by
    simpa [prefixWord, tailWord_3165972, baseEnd_3165972] using wordTrace_append hprefix tailTrace_3165972
  have hstable : (prefixWord ++ tailWord_3165972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165972).length < 2 ^ (prefixWord ++ tailWord_3165972).sum := by decide
  have hdescent : baseEnd_3165972 < baseStart_3165972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166028 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_3166028 : Nat := 118140960795 + 3166028 * 2 ^ 59
def prefixEnd_3166028 : Nat := 4983230072969 + 3 ^ 40 * 3166028 * 2
def baseEnd_3166028 : Nat := 1083796086395362756393139

theorem tailTrace_3166028 : CollatzResearch.WordTrace tailWord_3166028 prefixEnd_3166028 1083796086395362756393139 := by
  unfold tailWord_3166028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57737263887014372689513369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76983018516019163586017825 57737263887014372689513369)
  ·
    refine ⟨43302947915260779517135027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57737263887014372689513369 43302947915260779517135027)
    ·
      refine ⟨64954421872891169275702541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43302947915260779517135027 64954421872891169275702541)
      ·
        refine ⟨24357908202334188478388453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64954421872891169275702541 24357908202334188478388453)
        ·
          refine ⟨4567107787937660339697835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24357908202334188478388453 4567107787937660339697835)
          ·
            refine ⟨6850661681906490509546753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567107787937660339697835 6850661681906490509546753)
            ·
              refine ⟨5137996261429867882160065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850661681906490509546753 5137996261429867882160065)
              ·
                refine ⟨3853497196072400911620049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137996261429867882160065 3853497196072400911620049)
                ·
                  refine ⟨2890122897054300683715037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853497196072400911620049 2890122897054300683715037)
                  ·
                    refine ⟨1083796086395362756393139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890122897054300683715037 1083796086395362756393139)
                    ·
                      rfl

theorem cell22_3166028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_3166028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166028 prefixEnd_3166028 := by exact prefixLift 3166028
  have htrace : WordTrace (prefixWord ++ tailWord_3166028) baseStart_3166028 baseEnd_3166028 := by
    simpa [prefixWord, tailWord_3166028, baseEnd_3166028] using wordTrace_append hprefix tailTrace_3166028
  have hstable : (prefixWord ++ tailWord_3166028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166028).length < 2 ^ (prefixWord ++ tailWord_3166028).sum := by decide
  have hdescent : baseEnd_3166028 < baseStart_3166028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166056 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3166056 : Nat := 118140960795 + 3166056 * 2 ^ 59
def prefixEnd_3166056 : Nat := 4983230072969 + 3 ^ 40 * 3166056 * 2
def baseEnd_3166056 : Nat := 1083805671367580016693053

theorem tailTrace_3166056 : CollatzResearch.WordTrace tailWord_3166056 prefixEnd_3166056 1083805671367580016693053 := by
  unfold tailWord_3166056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57737774508963653080523011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76983699345284870774030681 57737774508963653080523011)
  ·
    refine ⟨86606661763445479620784517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57737774508963653080523011 86606661763445479620784517)
    ·
      refine ⟨16238749080646027428897097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86606661763445479620784517 16238749080646027428897097)
      ·
        refine ⟨12179061810484520571672823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16238749080646027428897097 12179061810484520571672823)
        ·
          refine ⟨18268592715726780857509235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12179061810484520571672823 18268592715726780857509235)
          ·
            refine ⟨27402889073590171286263853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18268592715726780857509235 27402889073590171286263853)
            ·
              refine ⟨10276083402596314232348945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27402889073590171286263853 10276083402596314232348945)
              ·
                refine ⟨7707062551947235674261709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10276083402596314232348945 7707062551947235674261709)
                ·
                  refine ⟨2890148456980213377848141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7707062551947235674261709 2890148456980213377848141)
                  ·
                    refine ⟨1083805671367580016693053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890148456980213377848141 1083805671367580016693053)
                    ·
                      rfl

theorem cell22_3166056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3166056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166056 prefixEnd_3166056 := by exact prefixLift 3166056
  have htrace : WordTrace (prefixWord ++ tailWord_3166056) baseStart_3166056 baseEnd_3166056 := by
    simpa [prefixWord, tailWord_3166056, baseEnd_3166056] using wordTrace_append hprefix tailTrace_3166056
  have hstable : (prefixWord ++ tailWord_3166056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166056).length < 2 ^ (prefixWord ++ tailWord_3166056).sum := by decide
  have hdescent : baseEnd_3166056 < baseStart_3166056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166058 : List Nat := [3, 1, 3, 4, 1, 1, 3, 6]
def baseStart_3166058 : Nat := 118140960795 + 3166058 * 2 ^ 59
def prefixEnd_3166058 : Nat := 4983230072969 + 3 ^ 40 * 3166058 * 2
def baseEnd_3166058 : Nat := 120422928445383630904783

theorem tailTrace_3166058 : CollatzResearch.WordTrace tailWord_3166058 prefixEnd_3166058 120422928445383630904783 := by
  unfold tailWord_3166058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28868905490980015125654707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76983747975946707001745885 28868905490980015125654707)
  ·
    refine ⟨43303358236470022688482061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28868905490980015125654707 43303358236470022688482061)
    ·
      refine ⟨16238759338676258508180773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43303358236470022688482061 16238759338676258508180773)
      ·
        refine ⟨3044767376001798470283895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16238759338676258508180773 3044767376001798470283895)
        ·
          refine ⟨4567151064002697705425843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044767376001798470283895 4567151064002697705425843)
          ·
            refine ⟨6850726596004046558138765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567151064002697705425843 6850726596004046558138765)
            ·
              refine ⟨2569022473501517459302037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6850726596004046558138765 2569022473501517459302037)
              ·
                refine ⟨120422928445383630904783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2569022473501517459302037 120422928445383630904783)
                ·
                  rfl

theorem cell22_3166058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_3166058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166058 prefixEnd_3166058 := by exact prefixLift 3166058
  have htrace : WordTrace (prefixWord ++ tailWord_3166058) baseStart_3166058 baseEnd_3166058 := by
    simpa [prefixWord, tailWord_3166058, baseEnd_3166058] using wordTrace_append hprefix tailTrace_3166058
  have hstable : (prefixWord ++ tailWord_3166058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166058).length < 2 ^ (prefixWord ++ tailWord_3166058).sum := by decide
  have hdescent : baseEnd_3166058 < baseStart_3166058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166067 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_3166067 : Nat := 118140960795 + 3166067 * 2 ^ 59
def prefixEnd_3166067 : Nat := 4983230072969 + 3 ^ 40 * 3166067 * 2
def baseEnd_3166067 : Nat := 1083809436892379654668019

theorem tailTrace_3166067 : CollatzResearch.WordTrace tailWord_3166067 prefixEnd_3166067 1083809436892379654668019 := by
  unfold tailWord_3166067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115475950220887455039696455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76983966813924970026464303 115475950220887455039696455)
  ·
    refine ⟨173213925331331182559544683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115475950220887455039696455 173213925331331182559544683)
    ·
      refine ⟨259820887996996773839317025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173213925331331182559544683 259820887996996773839317025)
      ·
        refine ⟨194865665997747580379487769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259820887996996773839317025 194865665997747580379487769)
        ·
          refine ⟨146149249498310685284615827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194865665997747580379487769 146149249498310685284615827)
          ·
            refine ⟨219223874247466027926923741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146149249498310685284615827 219223874247466027926923741)
            ·
              refine ⟨82208952842799760472596403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219223874247466027926923741 82208952842799760472596403)
              ·
                refine ⟨123313429264199640708894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82208952842799760472596403 123313429264199640708894605)
                ·
                  refine ⟨46242535974074865265835477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123313429264199640708894605 46242535974074865265835477)
                  ·
                    refine ⟨1083809436892379654668019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46242535974074865265835477 1083809436892379654668019)
                    ·
                      rfl

theorem cell22_3166067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_3166067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166067 prefixEnd_3166067 := by exact prefixLift 3166067
  have htrace : WordTrace (prefixWord ++ tailWord_3166067) baseStart_3166067 baseEnd_3166067 := by
    simpa [prefixWord, tailWord_3166067, baseEnd_3166067] using wordTrace_append hprefix tailTrace_3166067
  have hstable : (prefixWord ++ tailWord_3166067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166067).length < 2 ^ (prefixWord ++ tailWord_3166067).sum := by decide
  have hdescent : baseEnd_3166067 < baseStart_3166067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166069 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 7]
def baseStart_3166069 : Nat := 118140960795 + 3166069 * 2 ^ 59
def prefixEnd_3166069 : Nat := 4983230072969 + 3 ^ 40 * 3166069 * 2
def baseEnd_3166069 : Nat := 361270040511084105372671

theorem tailTrace_3166069 : CollatzResearch.WordTrace tailWord_3166069 prefixEnd_3166069 361270040511084105372671 := by
  unfold tailWord_3166069
  simp only [CollatzResearch.WordTrace]
  refine ⟨115476023166880209381269261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76984015444586806254179507 115476023166880209381269261)
  ·
    refine ⟨43303508687580078517975973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115476023166880209381269261 43303508687580078517975973)
    ·
      refine ⟨8119407878921264722120495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43303508687580078517975973 8119407878921264722120495)
      ·
        refine ⟨12179111818381897083180743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119407878921264722120495 12179111818381897083180743)
        ·
          refine ⟨18268667727572845624771115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12179111818381897083180743 18268667727572845624771115)
          ·
            refine ⟨27403001591359268437156673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18268667727572845624771115 27403001591359268437156673)
            ·
              refine ⟨20552251193519451327867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27403001591359268437156673 20552251193519451327867505)
              ·
                refine ⟨15414188395139588495900629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20552251193519451327867505 15414188395139588495900629)
                ·
                  refine ⟨361270040511084105372671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15414188395139588495900629 361270040511084105372671)
                  ·
                    rfl

theorem cell22_3166069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_3166069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166069 prefixEnd_3166069 := by exact prefixLift 3166069
  have htrace : WordTrace (prefixWord ++ tailWord_3166069) baseStart_3166069 baseEnd_3166069 := by
    simpa [prefixWord, tailWord_3166069, baseEnd_3166069] using wordTrace_append hprefix tailTrace_3166069
  have hstable : (prefixWord ++ tailWord_3166069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166069).length < 2 ^ (prefixWord ++ tailWord_3166069).sum := by decide
  have hdescent : baseEnd_3166069 < baseStart_3166069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166073 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_3166073 : Nat := 118140960795 + 3166073 * 2 ^ 59
def prefixEnd_3166073 : Nat := 4983230072969 + 3 ^ 40 * 3166073 * 2
def baseEnd_3166073 : Nat := 1083811490814997639018001

theorem tailTrace_3166073 : CollatzResearch.WordTrace tailWord_3166073 prefixEnd_3166073 1083811490814997639018001 := by
  unfold tailWord_3166073
  simp only [CollatzResearch.WordTrace]
  refine ⟨115476169058865718064414873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76984112705910478709609915 115476169058865718064414873)
  ·
    refine ⟨86607126794149288548311155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115476169058865718064414873 86607126794149288548311155)
    ·
      refine ⟨129910690191223932822466733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86607126794149288548311155 129910690191223932822466733)
      ·
        refine ⟨48716508821708974808425025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129910690191223932822466733 48716508821708974808425025)
        ·
          refine ⟨36537381616281731106318769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48716508821708974808425025 36537381616281731106318769)
          ·
            refine ⟨27403036212211298329739077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36537381616281731106318769 27403036212211298329739077)
            ·
              refine ⟨5138069289789618436826077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27403036212211298329739077 5138069289789618436826077)
              ·
                refine ⟨1926775983671106913809779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5138069289789618436826077 1926775983671106913809779)
                ·
                  refine ⟨2890163975506660370714669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926775983671106913809779 2890163975506660370714669)
                  ·
                    refine ⟨1083811490814997639018001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890163975506660370714669 1083811490814997639018001)
                    ·
                      rfl

theorem cell22_3166073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_3166073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166073 prefixEnd_3166073 := by exact prefixLift 3166073
  have htrace : WordTrace (prefixWord ++ tailWord_3166073) baseStart_3166073 baseEnd_3166073 := by
    simpa [prefixWord, tailWord_3166073, baseEnd_3166073] using wordTrace_append hprefix tailTrace_3166073
  have hstable : (prefixWord ++ tailWord_3166073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166073).length < 2 ^ (prefixWord ++ tailWord_3166073).sum := by decide
  have hdescent : baseEnd_3166073 < baseStart_3166073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166084 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3166084 : Nat := 118140960795 + 3166084 * 2 ^ 59
def prefixEnd_3166084 : Nat := 4983230072969 + 3 ^ 40 * 3166084 * 2
def baseEnd_3166084 : Nat := 1083815256339797276992967

theorem tailTrace_3166084 : CollatzResearch.WordTrace tailWord_3166084 prefixEnd_3166084 1083815256339797276992967 := by
  unfold tailWord_3166084
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738285130912933471532653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76984380174550577962043537 57738285130912933471532653)
  ·
    refine ⟨21651856924092350051824745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57738285130912933471532653 21651856924092350051824745)
    ·
      refine ⟨16238892693069262538868559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21651856924092350051824745 16238892693069262538868559)
      ·
        refine ⟨24358339039603893808302839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238892693069262538868559 24358339039603893808302839)
        ·
          refine ⟨36537508559405840712454259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24358339039603893808302839 36537508559405840712454259)
          ·
            refine ⟨54806262839108761068681389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537508559405840712454259 54806262839108761068681389)
            ·
              refine ⟨20552348564665785400755521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54806262839108761068681389 20552348564665785400755521)
              ·
                refine ⟨15414261423499339050566641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20552348564665785400755521 15414261423499339050566641)
                ·
                  refine ⟨11560696067624504287924981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15414261423499339050566641 11560696067624504287924981)
                  ·
                    refine ⟨1083815256339797276992967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11560696067624504287924981 1083815256339797276992967)
                    ·
                      rfl

theorem cell22_3166084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3166084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166084 prefixEnd_3166084 := by exact prefixLift 3166084
  have htrace : WordTrace (prefixWord ++ tailWord_3166084) baseStart_3166084 baseEnd_3166084 := by
    simpa [prefixWord, tailWord_3166084, baseEnd_3166084] using wordTrace_append hprefix tailTrace_3166084
  have hstable : (prefixWord ++ tailWord_3166084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166084).length < 2 ^ (prefixWord ++ tailWord_3166084).sum := by decide
  have hdescent : baseEnd_3166084 < baseStart_3166084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166116 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_3166116 : Nat := 118140960795 + 3166116 * 2 ^ 59
def prefixEnd_3166116 : Nat := 4983230072969 + 3 ^ 40 * 3166116 * 2
def baseEnd_3166116 : Nat := 1083826210593759860192869

theorem tailTrace_3166116 : CollatzResearch.WordTrace tailWord_3166116 prefixEnd_3166116 1083826210593759860192869 := by
  unfold tailWord_3166116
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738868698854968204115101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76985158265139957605486801 57738868698854968204115101)
  ·
    refine ⟨21652075762070613076543163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57738868698854968204115101 21652075762070613076543163)
    ·
      refine ⟨32478113643105919614814745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21652075762070613076543163 32478113643105919614814745)
      ·
        refine ⟨24358585232329439711111059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32478113643105919614814745 24358585232329439711111059)
        ·
          refine ⟨36537877848494159566666589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24358585232329439711111059 36537877848494159566666589)
          ·
            refine ⟨13701704193185309837499971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36537877848494159566666589 13701704193185309837499971)
            ·
              refine ⟨20552556289777964756249957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13701704193185309837499971 20552556289777964756249957)
              ·
                refine ⟨3853604304333368391796867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20552556289777964756249957 3853604304333368391796867)
                ·
                  refine ⟨5780406456500052587695301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853604304333368391796867 5780406456500052587695301)
                  ·
                    refine ⟨1083826210593759860192869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780406456500052587695301 1083826210593759860192869)
                    ·
                      rfl

theorem cell22_3166116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_3166116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166116 prefixEnd_3166116 := by exact prefixLift 3166116
  have htrace : WordTrace (prefixWord ++ tailWord_3166116) baseStart_3166116 baseEnd_3166116 := by
    simpa [prefixWord, tailWord_3166116, baseEnd_3166116] using wordTrace_append hprefix tailTrace_3166116
  have hstable : (prefixWord ++ tailWord_3166116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166116).length < 2 ^ (prefixWord ++ tailWord_3166116).sum := by decide
  have hdescent : baseEnd_3166116 < baseStart_3166116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166159 : List Nat := [1, 1, 2, 1, 1, 5, 4, 7]
def baseStart_3166159 : Nat := 118140960795 + 3166159 * 2 ^ 59
def prefixEnd_3166159 : Nat := 4983230072969 + 3 ^ 40 * 3166159 * 2
def baseEnd_3166159 : Nat := 120426770041391342374193

theorem tailTrace_3166159 : CollatzResearch.WordTrace tailWord_3166159 prefixEnd_3166159 120426770041391342374193 := by
  unfold tailWord_3166159
  simp only [CollatzResearch.WordTrace]
  refine ⟨115479305736554154752045531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76986203824369436501363687 115479305736554154752045531)
  ·
    refine ⟨173218958604831232128068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115479305736554154752045531 173218958604831232128068297)
    ·
      refine ⟨129914218953623424096051223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173218958604831232128068297 129914218953623424096051223)
      ·
        refine ⟨194871328430435136144076835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129914218953623424096051223 194871328430435136144076835)
        ·
          refine ⟨292306992645652704216115253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194871328430435136144076835 292306992645652704216115253)
          ·
            refine ⟨27403780560529941020260805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292306992645652704216115253 27403780560529941020260805)
            ·
              refine ⟨5138208855099363941298901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27403780560529941020260805 5138208855099363941298901)
              ·
                refine ⟨120426770041391342374193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5138208855099363941298901 120426770041391342374193)
                ·
                  rfl

theorem cell22_3166159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 7].length) (baseStart_3166159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166159 prefixEnd_3166159 := by exact prefixLift 3166159
  have htrace : WordTrace (prefixWord ++ tailWord_3166159) baseStart_3166159 baseEnd_3166159 := by
    simpa [prefixWord, tailWord_3166159, baseEnd_3166159] using wordTrace_append hprefix tailTrace_3166159
  have hstable : (prefixWord ++ tailWord_3166159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166159).length < 2 ^ (prefixWord ++ tailWord_3166159).sum := by decide
  have hdescent : baseEnd_3166159 < baseStart_3166159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166214 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3166214 : Nat := 118140960795 + 3166214 * 2 ^ 59
def prefixEnd_3166214 : Nat := 4983230072969 + 3 ^ 40 * 3166214 * 2
def baseEnd_3166214 : Nat := 1083859757996520271242569

theorem tailTrace_3166214 : CollatzResearch.WordTrace tailWord_3166214 prefixEnd_3166214 1083859757996520271242569 := by
  unfold tailWord_3166214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608790992229840598290553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76987541167569932763531797 3608790992229840598290553)
  ·
    refine ⟨2706593244172380448717915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3608790992229840598290553 2706593244172380448717915)
    ·
      refine ⟨4059889866258570673076873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706593244172380448717915 4059889866258570673076873)
      ·
        refine ⟨3044917399693928004807655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059889866258570673076873 3044917399693928004807655)
        ·
          refine ⟨4567376099540892007211483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044917399693928004807655 4567376099540892007211483)
          ·
            refine ⟨6851064149311338010817225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567376099540892007211483 6851064149311338010817225)
            ·
              refine ⟨5138298111983503508112919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851064149311338010817225 5138298111983503508112919)
              ·
                refine ⟨7707447167975255262169379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138298111983503508112919 7707447167975255262169379)
                ·
                  refine ⟨11561170751962882893254069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707447167975255262169379 11561170751962882893254069)
                  ·
                    refine ⟨1083859757996520271242569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11561170751962882893254069 1083859757996520271242569)
                    ·
                      rfl

theorem cell22_3166214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3166214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166214 prefixEnd_3166214 := by exact prefixLift 3166214
  have htrace : WordTrace (prefixWord ++ tailWord_3166214) baseStart_3166214 baseEnd_3166214 := by
    simpa [prefixWord, tailWord_3166214, baseEnd_3166214] using wordTrace_append hprefix tailTrace_3166214
  have hstable : (prefixWord ++ tailWord_3166214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166214).length < 2 ^ (prefixWord ++ tailWord_3166214).sum := by decide
  have hdescent : baseEnd_3166214 < baseStart_3166214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166285 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3166285 : Nat := 118140960795 + 3166285 * 2 ^ 59
def prefixEnd_3166285 : Nat := 4983230072969 + 3 ^ 40 * 3166285 * 2
def baseEnd_3166285 : Nat := 1083884062747499752717351

theorem tailTrace_3166285 : CollatzResearch.WordTrace tailWord_3166285 prefixEnd_3166285 1083884062747499752717351 := by
  unfold tailWord_3166285
  simp only [CollatzResearch.WordTrace]
  refine ⟨115483901334097678271132309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76989267556065118847421539 115483901334097678271132309)
  ·
    refine ⟨5413307875035828668959327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115483901334097678271132309 5413307875035828668959327)
    ·
      refine ⟨8119961812553743003438991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413307875035828668959327 8119961812553743003438991)
      ·
        refine ⟨12179942718830614505158487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119961812553743003438991 12179942718830614505158487)
        ·
          refine ⟨18269914078245921757737731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12179942718830614505158487 18269914078245921757737731)
          ·
            refine ⟨27404871117368882636606597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18269914078245921757737731 27404871117368882636606597)
            ·
              refine ⟨5138413334506665494363737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27404871117368882636606597 5138413334506665494363737)
              ·
                refine ⟨3853810000879999120772803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138413334506665494363737 3853810000879999120772803)
                ·
                  refine ⟨5780715001319998681159205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853810000879999120772803 5780715001319998681159205)
                  ·
                    refine ⟨1083884062747499752717351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780715001319998681159205 1083884062747499752717351)
                    ·
                      rfl

theorem cell22_3166285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3166285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166285 prefixEnd_3166285 := by exact prefixLift 3166285
  have htrace : WordTrace (prefixWord ++ tailWord_3166285) baseStart_3166285 baseEnd_3166285 := by
    simpa [prefixWord, tailWord_3166285, baseEnd_3166285] using wordTrace_append hprefix tailTrace_3166285
  have hstable : (prefixWord ++ tailWord_3166285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166285).length < 2 ^ (prefixWord ++ tailWord_3166285).sum := by decide
  have hdescent : baseEnd_3166285 < baseStart_3166285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166296 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3166296 : Nat := 118140960795 + 3166296 * 2 ^ 59
def prefixEnd_3166296 : Nat := 4983230072969 + 3 ^ 40 * 3166296 * 2
def baseEnd_3166296 : Nat := 1083887828272299390692317

theorem tailTrace_3166296 : CollatzResearch.WordTrace tailWord_3166296 prefixEnd_3166296 1083887828272299390692317 := by
  unfold tailWord_3166296
  simp only [CollatzResearch.WordTrace]
  refine ⟨57742151268528913574891371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76989535024705218099855161 57742151268528913574891371)
  ·
    refine ⟨86613226902793370362337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57742151268528913574891371 86613226902793370362337057)
    ·
      refine ⟨64959920177095027771752793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86613226902793370362337057 64959920177095027771752793)
      ·
        refine ⟨48719940132821270828814595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64959920177095027771752793 48719940132821270828814595)
        ·
          refine ⟨73079910199231906243221893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48719940132821270828814595 73079910199231906243221893)
          ·
            refine ⟨13702483162355982420604105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73079910199231906243221893 13702483162355982420604105)
            ·
              refine ⟨10276862371766986815453079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13702483162355982420604105 10276862371766986815453079)
              ·
                refine ⟨15415293557650480223179619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10276862371766986815453079 15415293557650480223179619)
                ·
                  refine ⟨23122940336475720334769429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15415293557650480223179619 23122940336475720334769429)
                  ·
                    refine ⟨1083887828272299390692317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23122940336475720334769429 1083887828272299390692317)
                    ·
                      rfl

theorem cell22_3166296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3166296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166296 prefixEnd_3166296 := by exact prefixLift 3166296
  have htrace : WordTrace (prefixWord ++ tailWord_3166296) baseStart_3166296 baseEnd_3166296 := by
    simpa [prefixWord, tailWord_3166296, baseEnd_3166296] using wordTrace_append hprefix tailTrace_3166296
  have hstable : (prefixWord ++ tailWord_3166296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166296).length < 2 ^ (prefixWord ++ tailWord_3166296).sum := by decide
  have hdescent : baseEnd_3166296 < baseStart_3166296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166300 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_3166300 : Nat := 118140960795 + 3166300 * 2 ^ 59
def prefixEnd_3166300 : Nat := 4983230072969 + 3 ^ 40 * 3166300 * 2
def baseEnd_3166300 : Nat := 361296399184681571197435

theorem tailTrace_3166300 : CollatzResearch.WordTrace tailWord_3166300 prefixEnd_3166300 361296399184681571197435 := by
  unfold tailWord_3166300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57742224214521667916464177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76989632286028890555285569 57742224214521667916464177)
  ·
    refine ⟨43306668160891250937348133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57742224214521667916464177 43306668160891250937348133)
    ·
      refine ⟨8120000280167109550752775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43306668160891250937348133 8120000280167109550752775)
      ·
        refine ⟨12180000420250664326129163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120000280167109550752775 12180000420250664326129163)
        ·
          refine ⟨18270000630375996489193745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180000420250664326129163 18270000630375996489193745)
          ·
            refine ⟨13702500472781997366895309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18270000630375996489193745 13702500472781997366895309)
            ·
              refine ⟨5138437677293249012585741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13702500472781997366895309 5138437677293249012585741)
              ·
                refine ⟨1926914128984968379719653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5138437677293249012585741 1926914128984968379719653)
                ·
                  refine ⟨361296399184681571197435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926914128984968379719653 361296399184681571197435)
                  ·
                    rfl

theorem cell22_3166300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_3166300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166300 prefixEnd_3166300 := by exact prefixLift 3166300
  have htrace : WordTrace (prefixWord ++ tailWord_3166300) baseStart_3166300 baseEnd_3166300 := by
    simpa [prefixWord, tailWord_3166300, baseEnd_3166300] using wordTrace_append hprefix tailTrace_3166300
  have hstable : (prefixWord ++ tailWord_3166300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166300).length < 2 ^ (prefixWord ++ tailWord_3166300).sum := by decide
  have hdescent : baseEnd_3166300 < baseStart_3166300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166332 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_3166332 : Nat := 118140960795 + 3166332 * 2 ^ 59
def prefixEnd_3166332 : Nat := 4983230072969 + 3 ^ 40 * 3166332 * 2
def baseEnd_3166332 : Nat := 1083900151808007296792207

theorem tailTrace_3166332 : CollatzResearch.WordTrace tailWord_3166332 prefixEnd_3166332 1083900151808007296792207 := by
  unfold tailWord_3166332
  simp only [CollatzResearch.WordTrace]
  refine ⟨57742807782463702649046625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76990410376618270198728833 57742807782463702649046625)
  ·
    refine ⟨43307105836847776986784969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57742807782463702649046625 43307105836847776986784969)
    ·
      refine ⟨32480329377635832740088727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43307105836847776986784969 32480329377635832740088727)
      ·
        refine ⟨48720494066453749110133091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32480329377635832740088727 48720494066453749110133091)
        ·
          refine ⟨73080741099680623665199637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48720494066453749110133091 73080741099680623665199637)
          ·
            refine ⟨3425659739047529234306233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73080741099680623665199637 3425659739047529234306233)
            ·
              refine ⟨2569244804285646925729675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425659739047529234306233 2569244804285646925729675)
              ·
                refine ⟨3853867206428470388594513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569244804285646925729675 3853867206428470388594513)
                ·
                  refine ⟨2890400404821352791445885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853867206428470388594513 2890400404821352791445885)
                  ·
                    refine ⟨1083900151808007296792207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890400404821352791445885 1083900151808007296792207)
                    ·
                      rfl

theorem cell22_3166332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_3166332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166332 prefixEnd_3166332 := by exact prefixLift 3166332
  have htrace : WordTrace (prefixWord ++ tailWord_3166332) baseStart_3166332 baseEnd_3166332 := by
    simpa [prefixWord, tailWord_3166332, baseEnd_3166332] using wordTrace_append hprefix tailTrace_3166332
  have hstable : (prefixWord ++ tailWord_3166332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166332).length < 2 ^ (prefixWord ++ tailWord_3166332).sum := by decide
  have hdescent : baseEnd_3166332 < baseStart_3166332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166343 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3166343 : Nat := 118140960795 + 3166343 * 2 ^ 59
def prefixEnd_3166343 : Nat := 4983230072969 + 3 ^ 40 * 3166343 * 2
def baseEnd_3166343 : Nat := 1083903917332806934767173

theorem tailTrace_3166343 : CollatzResearch.WordTrace tailWord_3166343 prefixEnd_3166343 1083903917332806934767173 := by
  unfold tailWord_3166343
  simp only [CollatzResearch.WordTrace]
  refine ⟨115486016767887554176743683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76990677845258369451162455 115486016767887554176743683)
  ·
    refine ⟨173229025151831331265115525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115486016767887554176743683 173229025151831331265115525)
    ·
      refine ⟨32480442215968374612209161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173229025151831331265115525 32480442215968374612209161)
      ·
        refine ⟨24360331661976280959156871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32480442215968374612209161 24360331661976280959156871)
        ·
          refine ⟨36540497492964421438735307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24360331661976280959156871 36540497492964421438735307)
          ·
            refine ⟨54810746239446632158102961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36540497492964421438735307 54810746239446632158102961)
            ·
              refine ⟨41108059679584974118577221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54810746239446632158102961 41108059679584974118577221)
              ·
                refine ⟨7707761189922182647233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41108059679584974118577221 7707761189922182647233229)
                ·
                  refine ⟨2890410446220818492712461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7707761189922182647233229 2890410446220818492712461)
                  ·
                    refine ⟨1083903917332806934767173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890410446220818492712461 1083903917332806934767173)
                    ·
                      rfl

theorem cell22_3166343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3166343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166343 prefixEnd_3166343 := by exact prefixLift 3166343
  have htrace : WordTrace (prefixWord ++ tailWord_3166343) baseStart_3166343 baseEnd_3166343 := by
    simpa [prefixWord, tailWord_3166343, baseEnd_3166343] using wordTrace_append hprefix tailTrace_3166343
  have hstable : (prefixWord ++ tailWord_3166343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166343).length < 2 ^ (prefixWord ++ tailWord_3166343).sum := by decide
  have hdescent : baseEnd_3166343 < baseStart_3166343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166373 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 5]
def baseStart_3166373 : Nat := 118140960795 + 3166373 * 2 ^ 59
def prefixEnd_3166373 : Nat := 4983230072969 + 3 ^ 40 * 3166373 * 2
def baseEnd_3166373 : Nat := 361304728981965618839027

theorem tailTrace_3166373 : CollatzResearch.WordTrace tailWord_3166373 prefixEnd_3166373 361304728981965618839027 := by
  unfold tailWord_3166373
  simp only [CollatzResearch.WordTrace]
  refine ⟨115487110957778869300335773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76991407305185912866890515 115487110957778869300335773)
  ·
    refine ⟨43307666609167075987625915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115487110957778869300335773 43307666609167075987625915)
    ·
      refine ⟨64961499913750613981438873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43307666609167075987625915 64961499913750613981438873)
      ·
        refine ⟨48721124935312960486079155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64961499913750613981438873 48721124935312960486079155)
        ·
          refine ⟨73081687402969440729118733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48721124935312960486079155 73081687402969440729118733)
          ·
            refine ⟨27405632776113540273419525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73081687402969440729118733 27405632776113540273419525)
            ·
              refine ⟨5138556145521288801266161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27405632776113540273419525 5138556145521288801266161)
              ·
                refine ⟨3853917109140966600949621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138556145521288801266161 3853917109140966600949621)
                ·
                  refine ⟨361304728981965618839027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3853917109140966600949621 361304728981965618839027)
                  ·
                    rfl

theorem cell22_3166373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_3166373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166373 prefixEnd_3166373 := by exact prefixLift 3166373
  have htrace : WordTrace (prefixWord ++ tailWord_3166373) baseStart_3166373 baseEnd_3166373 := by
    simpa [prefixWord, tailWord_3166373, baseEnd_3166373] using wordTrace_append hprefix tailTrace_3166373
  have hstable : (prefixWord ++ tailWord_3166373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166373).length < 2 ^ (prefixWord ++ tailWord_3166373).sum := by decide
  have hdescent : baseEnd_3166373 < baseStart_3166373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166450 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3166450 : Nat := 118140960795 + 3166450 * 2 ^ 59
def prefixEnd_3166450 : Nat := 4983230072969 + 3 ^ 40 * 3166450 * 2
def baseEnd_3166450 : Nat := 1083940545619494322341845

theorem tailTrace_3166450 : CollatzResearch.WordTrace tailWord_3166450 prefixEnd_3166450 1083940545619494322341845 := by
  unfold tailWord_3166450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872479844624977862722201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76993279585666607633925869 28872479844624977862722201)
  ·
    refine ⟨21654359883468733397041651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28872479844624977862722201 21654359883468733397041651)
    ·
      refine ⟨32481539825203100095562477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21654359883468733397041651 32481539825203100095562477)
      ·
        refine ⟨12180577434451162535835929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32481539825203100095562477 12180577434451162535835929)
        ·
          refine ⟨9135433075838371901876947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12180577434451162535835929 9135433075838371901876947)
          ·
            refine ⟨13703149613757557852815421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135433075838371901876947 13703149613757557852815421)
            ·
              refine ⟨5138681105159084194805783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13703149613757557852815421 5138681105159084194805783)
              ·
                refine ⟨7708021657738626292208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138681105159084194805783 7708021657738626292208675)
                ·
                  refine ⟨11562032486607939438313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708021657738626292208675 11562032486607939438313013)
                  ·
                    refine ⟨1083940545619494322341845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11562032486607939438313013 1083940545619494322341845)
                    ·
                      rfl

theorem cell22_3166450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3166450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166450 prefixEnd_3166450 := by exact prefixLift 3166450
  have htrace : WordTrace (prefixWord ++ tailWord_3166450) baseStart_3166450 baseEnd_3166450 := by
    simpa [prefixWord, tailWord_3166450, baseEnd_3166450] using wordTrace_append hprefix tailTrace_3166450
  have hstable : (prefixWord ++ tailWord_3166450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166450).length < 2 ^ (prefixWord ++ tailWord_3166450).sum := by decide
  have hdescent : baseEnd_3166450 < baseStart_3166450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166501 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_3166501 : Nat := 118140960795 + 3166501 * 2 ^ 59
def prefixEnd_3166501 : Nat := 4983230072969 + 3 ^ 40 * 3166501 * 2
def baseEnd_3166501 : Nat := 1083958003961747189316689

theorem tailTrace_3166501 : CollatzResearch.WordTrace tailWord_3166501 prefixEnd_3166501 1083958003961747189316689 := by
  unfold tailWord_3166501
  simp only [CollatzResearch.WordTrace]
  refine ⟨115491779501315147160995357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76994519667543431440663571 115491779501315147160995357)
  ·
    refine ⟨43309417312993180185373259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115491779501315147160995357 43309417312993180185373259)
    ·
      refine ⟨64964125969489770278059889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43309417312993180185373259 64964125969489770278059889)
      ·
        refine ⟨48723094477117327708544917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64964125969489770278059889 48723094477117327708544917)
        ·
          refine ⟨2283895053614874736338043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48723094477117327708544917 2283895053614874736338043)
          ·
            refine ⟨3425842580422312104507065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283895053614874736338043 3425842580422312104507065)
            ·
              refine ⟨2569381935316734078380299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425842580422312104507065 2569381935316734078380299)
              ·
                refine ⟨3854072902975101117570449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569381935316734078380299 3854072902975101117570449)
                ·
                  refine ⟨2890554677231325838177837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854072902975101117570449 2890554677231325838177837)
                  ·
                    refine ⟨1083958003961747189316689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890554677231325838177837 1083958003961747189316689)
                    ·
                      rfl

theorem cell22_3166501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_3166501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166501 prefixEnd_3166501 := by exact prefixLift 3166501
  have htrace : WordTrace (prefixWord ++ tailWord_3166501) baseStart_3166501 baseEnd_3166501 := by
    simpa [prefixWord, tailWord_3166501, baseEnd_3166501] using wordTrace_append hprefix tailTrace_3166501
  have hstable : (prefixWord ++ tailWord_3166501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166501).length < 2 ^ (prefixWord ++ tailWord_3166501).sum := by decide
  have hdescent : baseEnd_3166501 < baseStart_3166501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166553 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 6]
def baseStart_3166553 : Nat := 118140960795 + 3166553 * 2 ^ 59
def prefixEnd_3166553 : Nat := 4983230072969 + 3 ^ 40 * 3166553 * 2
def baseEnd_3166553 : Nat := 361325268208145462338843

theorem tailTrace_3166553 : CollatzResearch.WordTrace tailWord_3166553 prefixEnd_3166553 361325268208145462338843 := by
  unfold tailWord_3166553
  simp only [CollatzResearch.WordTrace]
  refine ⟨115493676097126760041888313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76995784064751173361258875 115493676097126760041888313)
  ·
    refine ⟨86620257072845070031416235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115493676097126760041888313 86620257072845070031416235)
    ·
      refine ⟨129930385609267605047124353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86620257072845070031416235 129930385609267605047124353)
      ·
        refine ⟨97447789206950703785343265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129930385609267605047124353 97447789206950703785343265)
        ·
          refine ⟨73085841905213027839007449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97447789206950703785343265 73085841905213027839007449)
          ·
            refine ⟨54814381428909770879255587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73085841905213027839007449 54814381428909770879255587)
            ·
              refine ⟨82221572143364656318883381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54814381428909770879255587 82221572143364656318883381)
              ·
                refine ⟨7708272388440436529895317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82221572143364656318883381 7708272388440436529895317)
                ·
                  refine ⟨361325268208145462338843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7708272388440436529895317 361325268208145462338843)
                  ·
                    rfl

theorem cell22_3166553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_3166553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166553 prefixEnd_3166553 := by exact prefixLift 3166553
  have htrace : WordTrace (prefixWord ++ tailWord_3166553) baseStart_3166553 baseEnd_3166553 := by
    simpa [prefixWord, tailWord_3166553, baseEnd_3166553] using wordTrace_append hprefix tailTrace_3166553
  have hstable : (prefixWord ++ tailWord_3166553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166553).length < 2 ^ (prefixWord ++ tailWord_3166553).sum := by decide
  have hdescent : baseEnd_3166553 < baseStart_3166553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166570 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_3166570 : Nat := 118140960795 + 3166570 * 2 ^ 59
def prefixEnd_3166570 : Nat := 4983230072969 + 3 ^ 40 * 3166570 * 2
def baseEnd_3166570 : Nat := 361327208023951336447159

theorem tailTrace_3166570 : CollatzResearch.WordTrace tailWord_3166570 prefixEnd_3166570 361327208023951336447159 := by
  unfold tailWord_3166570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873574034516292986314291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76996197425376781296838109 28873574034516292986314291)
  ·
    refine ⟨43310361051774439479471437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28873574034516292986314291 43310361051774439479471437)
    ·
      refine ⟨16241385394415414804801789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43310361051774439479471437 16241385394415414804801789)
      ·
        refine ⟨6090519522905780551800671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16241385394415414804801789 6090519522905780551800671)
        ·
          refine ⟨9135779284358670827701007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090519522905780551800671 9135779284358670827701007)
          ·
            refine ⟨13703668926538006241551511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135779284358670827701007 13703668926538006241551511)
            ·
              refine ⟨20555503389807009362327267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703668926538006241551511 20555503389807009362327267)
              ·
                refine ⟨30833255084710514043490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20555503389807009362327267 30833255084710514043490901)
                ·
                  refine ⟨361327208023951336447159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30833255084710514043490901 361327208023951336447159)
                  ·
                    rfl

theorem cell22_3166570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_3166570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166570 prefixEnd_3166570 := by exact prefixLift 3166570
  have htrace : WordTrace (prefixWord ++ tailWord_3166570) baseStart_3166570 baseEnd_3166570 := by
    simpa [prefixWord, tailWord_3166570, baseEnd_3166570] using wordTrace_append hprefix tailTrace_3166570
  have hstable : (prefixWord ++ tailWord_3166570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166570).length < 2 ^ (prefixWord ++ tailWord_3166570).sum := by decide
  have hdescent : baseEnd_3166570 < baseStart_3166570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166585 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_3166585 : Nat := 118140960795 + 3166585 * 2 ^ 59
def prefixEnd_3166585 : Nat := 4983230072969 + 3 ^ 40 * 3166585 * 2
def baseEnd_3166585 : Nat := 1083986758878398970216431

theorem tailTrace_3166585 : CollatzResearch.WordTrace tailWord_3166585 prefixEnd_3166585 1083986758878398970216431 := by
  unfold tailWord_3166585
  simp only [CollatzResearch.WordTrace]
  refine ⟨115494843233010829507053209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76996562155340553004702139 115494843233010829507053209)
  ·
    refine ⟨86621132424758122130289907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115494843233010829507053209 86621132424758122130289907)
    ·
      refine ⟨129931698637137183195434861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86621132424758122130289907 129931698637137183195434861)
      ·
        refine ⟨48724386988926443698288073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129931698637137183195434861 48724386988926443698288073)
        ·
          refine ⟨36543290241694832773716055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48724386988926443698288073 36543290241694832773716055)
          ·
            refine ⟨54814935362542249160574083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36543290241694832773716055 54814935362542249160574083)
            ·
              refine ⟨82222403043813373740861125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54814935362542249160574083 82222403043813373740861125)
              ·
                refine ⟨15416700570715007576411461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82222403043813373740861125 15416700570715007576411461)
                ·
                  refine ⟨2890631357009063920577149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15416700570715007576411461 2890631357009063920577149)
                  ·
                    refine ⟨1083986758878398970216431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890631357009063920577149 1083986758878398970216431)
                    ·
                      rfl

theorem cell22_3166585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_3166585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166585 prefixEnd_3166585 := by exact prefixLift 3166585
  have htrace : WordTrace (prefixWord ++ tailWord_3166585) baseStart_3166585 baseEnd_3166585 := by
    simpa [prefixWord, tailWord_3166585, baseEnd_3166585] using wordTrace_append hprefix tailTrace_3166585
  have hstable : (prefixWord ++ tailWord_3166585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166585).length < 2 ^ (prefixWord ++ tailWord_3166585).sum := by decide
  have hdescent : baseEnd_3166585 < baseStart_3166585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166587 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 4]
def baseStart_3166587 : Nat := 118140960795 + 3166587 * 2 ^ 59
def prefixEnd_3166587 : Nat := 4983230072969 + 3 ^ 40 * 3166587 * 2
def baseEnd_3166587 : Nat := 361329147839757210555475

theorem tailTrace_3166587 : CollatzResearch.WordTrace tailWord_3166587 prefixEnd_3166587 361329147839757210555475 := by
  unfold tailWord_3166587
  simp only [CollatzResearch.WordTrace]
  refine ⟨115494916179003583848626015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76996610786002389232417343 115494916179003583848626015)
  ·
    refine ⟨173242374268505375772939023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115494916179003583848626015 173242374268505375772939023)
    ·
      refine ⟨259863561402758063659408535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173242374268505375772939023 259863561402758063659408535)
      ·
        refine ⟨389795342104137095489112803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259863561402758063659408535 389795342104137095489112803)
        ·
          refine ⟨584693013156205643233669205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389795342104137095489112803 584693013156205643233669205)
          ·
            refine ⟨6851871247924284881644561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 584693013156205643233669205 6851871247924284881644561)
            ·
              refine ⟨5138903435943213661233421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851871247924284881644561 5138903435943213661233421)
              ·
                refine ⟨1927088788478705122962533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5138903435943213661233421 1927088788478705122962533)
                ·
                  refine ⟨361329147839757210555475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927088788478705122962533 361329147839757210555475)
                  ·
                    rfl

theorem cell22_3166587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 4].length) (baseStart_3166587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166587 prefixEnd_3166587 := by exact prefixLift 3166587
  have htrace : WordTrace (prefixWord ++ tailWord_3166587) baseStart_3166587 baseEnd_3166587 := by
    simpa [prefixWord, tailWord_3166587, baseEnd_3166587] using wordTrace_append hprefix tailTrace_3166587
  have hstable : (prefixWord ++ tailWord_3166587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166587).length < 2 ^ (prefixWord ++ tailWord_3166587).sum := by decide
  have hdescent : baseEnd_3166587 < baseStart_3166587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166589 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_3166589 : Nat := 118140960795 + 3166589 * 2 ^ 59
def prefixEnd_3166589 : Nat := 4983230072969 + 3 ^ 40 * 3166589 * 2
def baseEnd_3166589 : Nat := 1083988128160144293116419

theorem tailTrace_3166589 : CollatzResearch.WordTrace tailWord_3166589 prefixEnd_3166589 1083988128160144293116419 := by
  unfold tailWord_3166589
  simp only [CollatzResearch.WordTrace]
  refine ⟨115494989124996338190198821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76996659416664225460132547 115494989124996338190198821)
  ·
    refine ⟨21655310460936813410662279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115494989124996338190198821 21655310460936813410662279)
    ·
      refine ⟨32482965691405220115993419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655310460936813410662279 32482965691405220115993419)
      ·
        refine ⟨48724448537107830173990129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32482965691405220115993419 48724448537107830173990129)
        ·
          refine ⟨36543336402830872630492597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48724448537107830173990129 36543336402830872630492597)
          ·
            refine ⟨3425937787765394309108681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36543336402830872630492597 3425937787765394309108681)
            ·
              refine ⟨2569453340824045731831511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425937787765394309108681 2569453340824045731831511)
              ·
                refine ⟨3854180011236068597747267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569453340824045731831511 3854180011236068597747267)
                ·
                  refine ⟨5781270016854102896620901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854180011236068597747267 5781270016854102896620901)
                  ·
                    refine ⟨1083988128160144293116419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5781270016854102896620901 1083988128160144293116419)
                    ·
                      rfl

theorem cell22_3166589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_3166589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166589 prefixEnd_3166589 := by exact prefixLift 3166589
  have htrace : WordTrace (prefixWord ++ tailWord_3166589) baseStart_3166589 baseEnd_3166589 := by
    simpa [prefixWord, tailWord_3166589, baseEnd_3166589] using wordTrace_append hprefix tailTrace_3166589
  have hstable : (prefixWord ++ tailWord_3166589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166589).length < 2 ^ (prefixWord ++ tailWord_3166589).sum := by decide
  have hdescent : baseEnd_3166589 < baseStart_3166589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166600 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3166600 : Nat := 118140960795 + 3166600 * 2 ^ 59
def prefixEnd_3166600 : Nat := 4983230072969 + 3 ^ 40 * 3166600 * 2
def baseEnd_3166600 : Nat := 1083991893684943931091385

theorem tailTrace_3166600 : CollatzResearch.WordTrace tailWord_3166600 prefixEnd_3166600 1083991893684943931091385 := by
  unfold tailWord_3166600
  simp only [CollatzResearch.WordTrace]
  refine ⟨57747695163978243534424627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76996926885304324712566169 57747695163978243534424627)
  ·
    refine ⟨86621542745967365301636941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57747695163978243534424627 86621542745967365301636941)
    ·
      refine ⟨32483078529737761988113853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86621542745967365301636941 32483078529737761988113853)
      ·
        refine ⟨12181154448651660745542695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32483078529737761988113853 12181154448651660745542695)
        ·
          refine ⟨18271731672977491118314043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181154448651660745542695 18271731672977491118314043)
          ·
            refine ⟨27407597509466236677471065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271731672977491118314043 27407597509466236677471065)
            ·
              refine ⟨20555698132099677508103299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27407597509466236677471065 20555698132099677508103299)
              ·
                refine ⟨30833547198149516262154949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20555698132099677508103299 30833547198149516262154949)
                ·
                  refine ⟨5781290099653034299154053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30833547198149516262154949 5781290099653034299154053)
                  ·
                    refine ⟨1083991893684943931091385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5781290099653034299154053 1083991893684943931091385)
                    ·
                      rfl

theorem cell22_3166600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3166600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166600 prefixEnd_3166600 := by exact prefixLift 3166600
  have htrace : WordTrace (prefixWord ++ tailWord_3166600) baseStart_3166600 baseEnd_3166600 := by
    simpa [prefixWord, tailWord_3166600, baseEnd_3166600] using wordTrace_append hprefix tailTrace_3166600
  have hstable : (prefixWord ++ tailWord_3166600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166600).length < 2 ^ (prefixWord ++ tailWord_3166600).sum := by decide
  have hdescent : baseEnd_3166600 < baseStart_3166600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166632 : List Nat := [2, 1, 6, 1, 1, 2, 1, 8]
def baseStart_3166632 : Nat := 118140960795 + 3166632 * 2 ^ 59
def prefixEnd_3166632 : Nat := 4983230072969 + 3 ^ 40 * 3166632 * 2
def baseEnd_3166632 : Nat := 120444760882100723810143

theorem tailTrace_3166632 : CollatzResearch.WordTrace tailWord_3166632 prefixEnd_3166632 120444760882100723810143 := by
  unfold tailWord_3166632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57748278731920278267007075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76997704975893704356009433 57748278731920278267007075)
  ·
    refine ⟨86622418097880417400510613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57748278731920278267007075 86622418097880417400510613)
    ·
      refine ⟨4060425848338144565648935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86622418097880417400510613 4060425848338144565648935)
      ·
        refine ⟨6090638772507216848473403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060425848338144565648935 6090638772507216848473403)
        ·
          refine ⟨9135958158760825272710105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090638772507216848473403 9135958158760825272710105)
          ·
            refine ⟨6851968619070618954532579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9135958158760825272710105 6851968619070618954532579)
            ·
              refine ⟨10277952928605928431798869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851968619070618954532579 10277952928605928431798869)
              ·
                refine ⟨120444760882100723810143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10277952928605928431798869 120444760882100723810143)
                ·
                  rfl

theorem cell22_3166632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_3166632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166632 prefixEnd_3166632 := by exact prefixLift 3166632
  have htrace : WordTrace (prefixWord ++ tailWord_3166632) baseStart_3166632 baseEnd_3166632 := by
    simpa [prefixWord, tailWord_3166632, baseEnd_3166632] using wordTrace_append hprefix tailTrace_3166632
  have hstable : (prefixWord ++ tailWord_3166632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166632).length < 2 ^ (prefixWord ++ tailWord_3166632).sum := by decide
  have hdescent : baseEnd_3166632 < baseStart_3166632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166664 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3166664 : Nat := 118140960795 + 3166664 * 2 ^ 59
def prefixEnd_3166664 : Nat := 4983230072969 + 3 ^ 40 * 3166664 * 2
def baseEnd_3166664 : Nat := 1084013802192869097491189

theorem tailTrace_3166664 : CollatzResearch.WordTrace tailWord_3166664 prefixEnd_3166664 1084013802192869097491189 := by
  unfold tailWord_3166664
  simp only [CollatzResearch.WordTrace]
  refine ⟨57748862299862312999589523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76998483066483083999452697 57748862299862312999589523)
  ·
    refine ⟨86623293449793469499384285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57748862299862312999589523 86623293449793469499384285)
    ·
      refine ⟨32483735043672551062269107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86623293449793469499384285 32483735043672551062269107)
      ·
        refine ⟨48725602565508826593403661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32483735043672551062269107 48725602565508826593403661)
        ·
          refine ⟨18272100962065809972526373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48725602565508826593403661 18272100962065809972526373)
          ·
            refine ⟨3426018930387339369848695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18272100962065809972526373 3426018930387339369848695)
            ·
              refine ⟨5139028395581009054773043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426018930387339369848695 5139028395581009054773043)
              ·
                refine ⟨7708542593371513582159565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139028395581009054773043 7708542593371513582159565)
                ·
                  refine ⟨2890703472514317593309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7708542593371513582159565 2890703472514317593309837)
                  ·
                    refine ⟨1084013802192869097491189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890703472514317593309837 1084013802192869097491189)
                    ·
                      rfl

theorem cell22_3166664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3166664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166664 prefixEnd_3166664 := by exact prefixLift 3166664
  have htrace : WordTrace (prefixWord ++ tailWord_3166664) baseStart_3166664 baseEnd_3166664 := by
    simpa [prefixWord, tailWord_3166664, baseEnd_3166664] using wordTrace_append hprefix tailTrace_3166664
  have hstable : (prefixWord ++ tailWord_3166664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166664).length < 2 ^ (prefixWord ++ tailWord_3166664).sum := by decide
  have hdescent : baseEnd_3166664 < baseStart_3166664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166677 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3166677 : Nat := 118140960795 + 3166677 * 2 ^ 59
def prefixEnd_3166677 : Nat := 4983230072969 + 3 ^ 40 * 3166677 * 2
def baseEnd_3166677 : Nat := 361339417452847132305383

theorem tailTrace_3166677 : CollatzResearch.WordTrace tailWord_3166677 prefixEnd_3166677 361339417452847132305383 := by
  unfold tailWord_3166677
  simp only [CollatzResearch.WordTrace]
  refine ⟨115498198748677529219402285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76998799165785019479601523 115498198748677529219402285)
  ·
    refine ⟨43311824530754073457275857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115498198748677529219402285 43311824530754073457275857)
    ·
      refine ⟨32483868398065555092956893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43311824530754073457275857 32483868398065555092956893)
      ·
        refine ⟨12181450649274583159858835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32483868398065555092956893 12181450649274583159858835)
        ·
          refine ⟨18272175973911874739788253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181450649274583159858835 18272175973911874739788253)
          ·
            refine ⟨6852065990216953027420595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18272175973911874739788253 6852065990216953027420595)
            ·
              refine ⟨10278098985325429541130893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852065990216953027420595 10278098985325429541130893)
              ·
                refine ⟨3854287119497036077924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10278098985325429541130893 3854287119497036077924085)
                ·
                  refine ⟨361339417452847132305383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854287119497036077924085 361339417452847132305383)
                  ·
                    rfl

theorem cell22_3166677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3166677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166677 prefixEnd_3166677 := by exact prefixLift 3166677
  have htrace : WordTrace (prefixWord ++ tailWord_3166677) baseStart_3166677 baseEnd_3166677 := by
    simpa [prefixWord, tailWord_3166677, baseEnd_3166677] using wordTrace_append hprefix tailTrace_3166677
  have hstable : (prefixWord ++ tailWord_3166677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166677).length < 2 ^ (prefixWord ++ tailWord_3166677).sum := by decide
  have hdescent : baseEnd_3166677 < baseStart_3166677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166726 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3166726 : Nat := 118140960795 + 3166726 * 2 ^ 59
def prefixEnd_3166726 : Nat := 4983230072969 + 3 ^ 40 * 3166726 * 2
def baseEnd_3166726 : Nat := 1084035026059921602440999

theorem tailTrace_3166726 : CollatzResearch.WordTrace tailWord_3166726 prefixEnd_3166726 1084035026059921602440999 := by
  unfold tailWord_3166726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609374560171875330873001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76999990617000007058624021 3609374560171875330873001)
  ·
    refine ⟨2707030920128906498154751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3609374560171875330873001 2707030920128906498154751)
    ·
      refine ⟨4060546380193359747232127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707030920128906498154751 4060546380193359747232127)
      ·
        refine ⟨6090819570290039620848191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060546380193359747232127 6090819570290039620848191)
        ·
          refine ⟨9136229355435059431272287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090819570290039620848191 9136229355435059431272287)
          ·
            refine ⟨13704344033152589146908431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9136229355435059431272287 13704344033152589146908431)
            ·
              refine ⟨20556516049728883720362647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704344033152589146908431 20556516049728883720362647)
              ·
                refine ⟨30834774074593325580543971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20556516049728883720362647 30834774074593325580543971)
                ·
                  refine ⟨46252161111889988370815957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30834774074593325580543971 46252161111889988370815957)
                  ·
                    refine ⟨1084035026059921602440999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46252161111889988370815957 1084035026059921602440999)
                    ·
                      rfl

theorem cell22_3166726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3166726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166726 prefixEnd_3166726 := by exact prefixLift 3166726
  have htrace : WordTrace (prefixWord ++ tailWord_3166726) baseStart_3166726 baseEnd_3166726 := by
    simpa [prefixWord, tailWord_3166726, baseEnd_3166726] using wordTrace_append hprefix tailTrace_3166726
  have hstable : (prefixWord ++ tailWord_3166726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166726).length < 2 ^ (prefixWord ++ tailWord_3166726).sum := by decide
  have hdescent : baseEnd_3166726 < baseStart_3166726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3166735 : Nat := 118140960795 + 3166735 * 2 ^ 59
def prefixEnd_3166735 : Nat := 4983230072969 + 3 ^ 40 * 3166735 * 2
def baseEnd_3166735 : Nat := 1084038106943848578965971

theorem tailTrace_3166735 : CollatzResearch.WordTrace tailWord_3166735 prefixEnd_3166735 1084038106943848578965971 := by
  unfold tailWord_3166735
  simp only [CollatzResearch.WordTrace]
  refine ⟨115500314182467405125013659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77000209454978270083342439 115500314182467405125013659)
  ·
    refine ⟨173250471273701107687520489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115500314182467405125013659 173250471273701107687520489)
    ·
      refine ⟨129937853455275830765640367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173250471273701107687520489 129937853455275830765640367)
      ·
        refine ⟨194906780182913746148460551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129937853455275830765640367 194906780182913746148460551)
        ·
          refine ⟨292360170274370619222690827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194906780182913746148460551 292360170274370619222690827)
          ·
            refine ⟨438540255411555928834036241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292360170274370619222690827 438540255411555928834036241)
            ·
              refine ⟨328905191558666946625527181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438540255411555928834036241 328905191558666946625527181)
              ·
                refine ⟨123339446834500104984572693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328905191558666946625527181 123339446834500104984572693)
                ·
                  refine ⟨5781536570367192421151845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123339446834500104984572693 5781536570367192421151845)
                  ·
                    refine ⟨1084038106943848578965971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5781536570367192421151845 1084038106943848578965971)
                    ·
                      rfl

theorem cell22_3166735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3166735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166735 prefixEnd_3166735 := by exact prefixLift 3166735
  have htrace : WordTrace (prefixWord ++ tailWord_3166735) baseStart_3166735 baseEnd_3166735 := by
    simpa [prefixWord, tailWord_3166735, baseEnd_3166735] using wordTrace_append hprefix tailTrace_3166735
  have hstable : (prefixWord ++ tailWord_3166735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166735).length < 2 ^ (prefixWord ++ tailWord_3166735).sum := by decide
  have hdescent : baseEnd_3166735 < baseStart_3166735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166816 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_3166816 : Nat := 118140960795 + 3166816 * 2 ^ 59
def prefixEnd_3166816 : Nat := 4983230072969 + 3 ^ 40 * 3166816 * 2
def baseEnd_3166816 : Nat := 1084065834899191367690723

theorem tailTrace_3166816 : CollatzResearch.WordTrace tailWord_3166816 prefixEnd_3166816 1084065834899191367690723 := by
  unfold tailWord_3166816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57751634247586977979356151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77002178996782637305808201 57751634247586977979356151)
  ·
    refine ⟨86627451371380466969034227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57751634247586977979356151 86627451371380466969034227)
    ·
      refine ⟨129941177057070700453551341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86627451371380466969034227 129941177057070700453551341)
      ·
        refine ⟨48727941396401512670081753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129941177057070700453551341 48727941396401512670081753)
        ·
          refine ⟨36545956047301134502561315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48727941396401512670081753 36545956047301134502561315)
          ·
            refine ⟨54818934070951701753841973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36545956047301134502561315 54818934070951701753841973)
            ·
              refine ⟨5139275069151722039422685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54818934070951701753841973 5139275069151722039422685)
              ·
                refine ⟨1927228150931895764783507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5139275069151722039422685 1927228150931895764783507)
                ·
                  refine ⟨2890842226397843647175261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927228150931895764783507 2890842226397843647175261)
                  ·
                    refine ⟨1084065834899191367690723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890842226397843647175261 1084065834899191367690723)
                    ·
                      rfl

theorem cell22_3166816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_3166816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166816 prefixEnd_3166816 := by exact prefixLift 3166816
  have htrace : WordTrace (prefixWord ++ tailWord_3166816) baseStart_3166816 baseEnd_3166816 := by
    simpa [prefixWord, tailWord_3166816, baseEnd_3166816] using wordTrace_append hprefix tailTrace_3166816
  have hstable : (prefixWord ++ tailWord_3166816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166816).length < 2 ^ (prefixWord ++ tailWord_3166816).sum := by decide
  have hdescent : baseEnd_3166816 < baseStart_3166816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166889 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_3166889 : Nat := 118140960795 + 3166889 * 2 ^ 59
def prefixEnd_3166889 : Nat := 4983230072969 + 3 ^ 40 * 3166889 * 2
def baseEnd_3166889 : Nat := 1084090824291043510615499

theorem tailTrace_3166889 : CollatzResearch.WordTrace tailWord_3166889 prefixEnd_3166889 1084090824291043510615499 := by
  unfold tailWord_3166889
  simp only [CollatzResearch.WordTrace]
  refine ⟨115505931023909489426119721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77003954015939659617413147 115505931023909489426119721)
  ·
    refine ⟨86629448267932117069589791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115505931023909489426119721 86629448267932117069589791)
    ·
      refine ⟨129944172401898175604384687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86629448267932117069589791 129944172401898175604384687)
      ·
        refine ⟨194916258602847263406577031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129944172401898175604384687 194916258602847263406577031)
        ·
          refine ⟨292374387904270895109865547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194916258602847263406577031 292374387904270895109865547)
          ·
            refine ⟨438561581856406342664798321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292374387904270895109865547 438561581856406342664798321)
            ·
              refine ⟨328921186392304756998598741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438561581856406342664798321 328921186392304756998598741)
              ·
                refine ⟨3854545153034821371077329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 328921186392304756998598741 3854545153034821371077329)
                ·
                  refine ⟨2890908864776116028307997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854545153034821371077329 2890908864776116028307997)
                  ·
                    refine ⟨1084090824291043510615499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890908864776116028307997 1084090824291043510615499)
                    ·
                      rfl

theorem cell22_3166889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_3166889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166889 prefixEnd_3166889 := by exact prefixLift 3166889
  have htrace : WordTrace (prefixWord ++ tailWord_3166889) baseStart_3166889 baseEnd_3166889 := by
    simpa [prefixWord, tailWord_3166889, baseEnd_3166889] using wordTrace_append hprefix tailTrace_3166889
  have hstable : (prefixWord ++ tailWord_3166889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166889).length < 2 ^ (prefixWord ++ tailWord_3166889).sum := by decide
  have hdescent : baseEnd_3166889 < baseStart_3166889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166925 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3166925 : Nat := 118140960795 + 3166925 * 2 ^ 59
def prefixEnd_3166925 : Nat := 4983230072969 + 3 ^ 40 * 3166925 * 2
def baseEnd_3166925 : Nat := 361367715942250472238463

theorem tailTrace_3166925 : CollatzResearch.WordTrace tailWord_3166925 prefixEnd_3166925 361367715942250472238463 := by
  unfold tailWord_3166925
  simp only [CollatzResearch.WordTrace]
  refine ⟨115507244051779067574430229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77004829367852711716286819 115507244051779067574430229)
  ·
    refine ⟨5414402064927143792551417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115507244051779067574430229 5414402064927143792551417)
    ·
      refine ⟨4060801548695357844413563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414402064927143792551417 4060801548695357844413563)
      ·
        refine ⟨6091202323043036766620345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060801548695357844413563 6091202323043036766620345)
        ·
          refine ⟨4568401742282277574965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6091202323043036766620345 4568401742282277574965259)
          ·
            refine ⟨6852602613423416362447889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568401742282277574965259 6852602613423416362447889)
            ·
              refine ⟨5139451960067562271835917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852602613423416362447889 5139451960067562271835917)
              ·
                refine ⟨1927294485025335851938469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5139451960067562271835917 1927294485025335851938469)
                ·
                  refine ⟨361367715942250472238463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927294485025335851938469 361367715942250472238463)
                  ·
                    rfl

theorem cell22_3166925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3166925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166925 prefixEnd_3166925 := by exact prefixLift 3166925
  have htrace : WordTrace (prefixWord ++ tailWord_3166925) baseStart_3166925 baseEnd_3166925 := by
    simpa [prefixWord, tailWord_3166925, baseEnd_3166925] using wordTrace_append hprefix tailTrace_3166925
  have hstable : (prefixWord ++ tailWord_3166925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166925).length < 2 ^ (prefixWord ++ tailWord_3166925).sum := by decide
  have hdescent : baseEnd_3166925 < baseStart_3166925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166940 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3166940 : Nat := 118140960795 + 3166940 * 2 ^ 59
def prefixEnd_3166940 : Nat := 4983230072969 + 3 ^ 40 * 3166940 * 2
def baseEnd_3166940 : Nat := 1084108282633296377590343

theorem tailTrace_3166940 : CollatzResearch.WordTrace tailWord_3166940 prefixEnd_3166940 1084108282633296377590343 := by
  unfold tailWord_3166940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57753895573362362568113137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77005194097816483424150849 57753895573362362568113137)
  ·
    refine ⟨43315421680021771926084853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57753895573362362568113137 43315421680021771926084853)
    ·
      refine ⟨4060820782502041118070455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43315421680021771926084853 4060820782502041118070455)
      ·
        refine ⟨6091231173753061677105683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060820782502041118070455 6091231173753061677105683)
        ·
          refine ⟨9136846760629592515658525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091231173753061677105683 9136846760629592515658525)
          ·
            refine ⟨3426317535236097193371947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9136846760629592515658525 3426317535236097193371947)
            ·
              refine ⟨5139476302854145790057921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426317535236097193371947 5139476302854145790057921)
              ·
                refine ⟨3854607227140609342543441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139476302854145790057921 3854607227140609342543441)
                ·
                  refine ⟨2890955420355457006907581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854607227140609342543441 2890955420355457006907581)
                  ·
                    refine ⟨1084108282633296377590343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890955420355457006907581 1084108282633296377590343)
                    ·
                      rfl

theorem cell22_3166940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3166940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3166940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3166940 prefixEnd_3166940 := by exact prefixLift 3166940
  have htrace : WordTrace (prefixWord ++ tailWord_3166940) baseStart_3166940 baseEnd_3166940 := by
    simpa [prefixWord, tailWord_3166940, baseEnd_3166940] using wordTrace_append hprefix tailTrace_3166940
  have hstable : (prefixWord ++ tailWord_3166940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166940).length < 2 ^ (prefixWord ++ tailWord_3166940).sum := by decide
  have hdescent : baseEnd_3166940 < baseStart_3166940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167028 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3167028 : Nat := 118140960795 + 3167028 * 2 ^ 59
def prefixEnd_3167028 : Nat := 4983230072969 + 3 ^ 40 * 3167028 * 2
def baseEnd_3167028 : Nat := 1084138406831693481390073

theorem tailTrace_3167028 : CollatzResearch.WordTrace tailWord_3167028 prefixEnd_3167028 1084138406831693481390073 := by
  unfold tailWord_3167028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57755500385202958082714869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77007333846937277443619825 57755500385202958082714869)
  ·
    refine ⟨5414578161112777320254519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57755500385202958082714869 5414578161112777320254519)
    ·
      refine ⟨8121867241669165980381779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5414578161112777320254519 8121867241669165980381779)
      ·
        refine ⟨12182800862503748970572669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8121867241669165980381779 12182800862503748970572669)
        ·
          refine ⟨4568550323438905863964751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12182800862503748970572669 4568550323438905863964751)
          ·
            refine ⟨6852825485158358795947127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568550323438905863964751 6852825485158358795947127)
            ·
              refine ⟨10279238227737538193920691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852825485158358795947127 10279238227737538193920691)
              ·
                refine ⟨15418857341606307290881037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279238227737538193920691 15418857341606307290881037)
                ·
                  refine ⟨5782071503102365234080389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15418857341606307290881037 5782071503102365234080389)
                  ·
                    refine ⟨1084138406831693481390073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782071503102365234080389 1084138406831693481390073)
                    ·
                      rfl

theorem cell22_3167028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3167028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167028 prefixEnd_3167028 := by exact prefixLift 3167028
  have htrace : WordTrace (prefixWord ++ tailWord_3167028) baseStart_3167028 baseEnd_3167028 := by
    simpa [prefixWord, tailWord_3167028, baseEnd_3167028] using wordTrace_append hprefix tailTrace_3167028
  have hstable : (prefixWord ++ tailWord_3167028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167028).length < 2 ^ (prefixWord ++ tailWord_3167028).sum := by decide
  have hdescent : baseEnd_3167028 < baseStart_3167028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167058 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3167058 : Nat := 118140960795 + 3167058 * 2 ^ 59
def prefixEnd_3167058 : Nat := 4983230072969 + 3 ^ 40 * 3167058 * 2
def baseEnd_3167058 : Nat := 1084148676444783403139981

theorem tailTrace_3167058 : CollatzResearch.WordTrace tailWord_3167058 prefixEnd_3167058 1084148676444783403139981 := by
  unfold tailWord_3167058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878023740074307822255457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77008063306864820859347885 28878023740074307822255457)
  ·
    refine ⟨21658517805055730866691593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28878023740074307822255457 21658517805055730866691593)
    ·
      refine ⟨16243888353791798150018695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21658517805055730866691593 16243888353791798150018695)
      ·
        refine ⟨24365832530687697225028043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16243888353791798150018695 24365832530687697225028043)
        ·
          refine ⟨36548748796031545837542065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24365832530687697225028043 36548748796031545837542065)
          ·
            refine ⟨27411561597023659378156549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36548748796031545837542065 27411561597023659378156549)
            ·
              refine ⟨5139667799441936133404353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27411561597023659378156549 5139667799441936133404353)
              ·
                refine ⟨3854750849581452100053265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139667799441936133404353 3854750849581452100053265)
                ·
                  refine ⟨2891063137186089075039949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854750849581452100053265 2891063137186089075039949)
                  ·
                    refine ⟨1084148676444783403139981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891063137186089075039949 1084148676444783403139981)
                    ·
                      rfl

theorem cell22_3167058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3167058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167058 prefixEnd_3167058 := by exact prefixLift 3167058
  have htrace : WordTrace (prefixWord ++ tailWord_3167058) baseStart_3167058 baseEnd_3167058 := by
    simpa [prefixWord, tailWord_3167058, baseEnd_3167058] using wordTrace_append hprefix tailTrace_3167058
  have hstable : (prefixWord ++ tailWord_3167058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167058).length < 2 ^ (prefixWord ++ tailWord_3167058).sum := by decide
  have hdescent : baseEnd_3167058 < baseStart_3167058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167084 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_3167084 : Nat := 118140960795 + 3167084 * 2 ^ 59
def prefixEnd_3167084 : Nat := 4983230072969 + 3 ^ 40 * 3167084 * 2
def baseEnd_3167084 : Nat := 1084157576776128001989901

theorem tailTrace_3167084 : CollatzResearch.WordTrace tailWord_3167084 prefixEnd_3167084 1084157576776128001989901 := by
  unfold tailWord_3167084
  simp only [CollatzResearch.WordTrace]
  refine ⟨57756521629101518864734153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77008695505468691819645537 57756521629101518864734153)
  ·
    refine ⟨43317391221826139148550615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57756521629101518864734153 43317391221826139148550615)
    ·
      refine ⟨64976086832739208722825923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43317391221826139148550615 64976086832739208722825923)
      ·
        refine ⟨97464130249108813084238885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64976086832739208722825923 97464130249108813084238885)
        ·
          refine ⟨18274524421707902453294791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97464130249108813084238885 18274524421707902453294791)
          ·
            refine ⟨27411786632561853679942187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18274524421707902453294791 27411786632561853679942187)
            ·
              refine ⟨41117679948842780519913281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27411786632561853679942187 41117679948842780519913281)
              ·
                refine ⟨30838259961632085389934961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41117679948842780519913281 30838259961632085389934961)
                ·
                  refine ⟨23128694971224064042451221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30838259961632085389934961 23128694971224064042451221)
                  ·
                    refine ⟨1084157576776128001989901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23128694971224064042451221 1084157576776128001989901)
                    ·
                      rfl

theorem cell22_3167084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_3167084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167084 prefixEnd_3167084 := by exact prefixLift 3167084
  have htrace : WordTrace (prefixWord ++ tailWord_3167084) baseStart_3167084 baseEnd_3167084 := by
    simpa [prefixWord, tailWord_3167084, baseEnd_3167084] using wordTrace_append hprefix tailTrace_3167084
  have hstable : (prefixWord ++ tailWord_3167084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167084).length < 2 ^ (prefixWord ++ tailWord_3167084).sum := by decide
  have hdescent : baseEnd_3167084 < baseStart_3167084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167103 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 1, 3]
def baseStart_3167103 : Nat := 118140960795 + 3167103 * 2 ^ 59
def prefixEnd_3167103 : Nat := 4983230072969 + 3 ^ 40 * 3167103 * 2
def baseEnd_3167103 : Nat := 1084164080864418285764843

theorem tailTrace_3167103 : CollatzResearch.WordTrace tailWord_3167103 prefixEnd_3167103 1084164080864418285764843 := by
  unfold tailWord_3167103
  simp only [CollatzResearch.WordTrace]
  refine ⟨115513736245134203974409963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77009157496756135982939975 115513736245134203974409963)
  ·
    refine ⟨173270604367701305961614945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115513736245134203974409963 173270604367701305961614945)
    ·
      refine ⟨129952953275775979471211209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173270604367701305961614945 129952953275775979471211209)
      ·
        refine ⟨97464714956831984603408407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129952953275775979471211209 97464714956831984603408407)
        ·
          refine ⟨146197072435247976905112611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97464714956831984603408407 146197072435247976905112611)
          ·
            refine ⟨219295608652871965357668917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146197072435247976905112611 219295608652871965357668917)
            ·
              refine ⟨20558963311206746752281461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219295608652871965357668917 20558963311206746752281461)
              ·
                refine ⟨1927402810425632508026387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20558963311206746752281461 1927402810425632508026387)
                ·
                  refine ⟨2891104215638448762039581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927402810425632508026387 2891104215638448762039581)
                  ·
                    refine ⟨1084164080864418285764843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891104215638448762039581 1084164080864418285764843)
                    ·
                      rfl

theorem cell22_3167103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_3167103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167103 prefixEnd_3167103 := by exact prefixLift 3167103
  have htrace : WordTrace (prefixWord ++ tailWord_3167103) baseStart_3167103 baseEnd_3167103 := by
    simpa [prefixWord, tailWord_3167103, baseEnd_3167103] using wordTrace_append hprefix tailTrace_3167103
  have hstable : (prefixWord ++ tailWord_3167103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167103).length < 2 ^ (prefixWord ++ tailWord_3167103).sum := by decide
  have hdescent : baseEnd_3167103 < baseStart_3167103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167116 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3167116 : Nat := 118140960795 + 3167116 * 2 ^ 59
def prefixEnd_3167116 : Nat := 4983230072969 + 3 ^ 40 * 3167116 * 2
def baseEnd_3167116 : Nat := 361389510343363528396601

theorem tailTrace_3167116 : CollatzResearch.WordTrace tailWord_3167116 prefixEnd_3167116 361389510343363528396601 := by
  unfold tailWord_3167116
  simp only [CollatzResearch.WordTrace]
  refine ⟨57757105197043553597316601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77009473596058071463088801 57757105197043553597316601)
  ·
    refine ⟨43317828897782665197987451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57757105197043553597316601 43317828897782665197987451)
    ·
      refine ⟨64976743346673997796981177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43317828897782665197987451 64976743346673997796981177)
      ·
        refine ⟨48732557510005498347735883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64976743346673997796981177 48732557510005498347735883)
        ·
          refine ⟨73098836265008247521603825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48732557510005498347735883 73098836265008247521603825)
          ·
            refine ⟨54824127198756185641202869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73098836265008247521603825 54824127198756185641202869)
            ·
              refine ⟨5139761924883392403862769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54824127198756185641202869 5139761924883392403862769)
              ·
                refine ⟨3854821443662544302897077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139761924883392403862769 3854821443662544302897077)
                ·
                  refine ⟨361389510343363528396601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854821443662544302897077 361389510343363528396601)
                  ·
                    rfl

theorem cell22_3167116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3167116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167116 prefixEnd_3167116 := by exact prefixLift 3167116
  have htrace : WordTrace (prefixWord ++ tailWord_3167116) baseStart_3167116 baseEnd_3167116 := by
    simpa [prefixWord, tailWord_3167116, baseEnd_3167116] using wordTrace_append hprefix tailTrace_3167116
  have hstable : (prefixWord ++ tailWord_3167116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167116).length < 2 ^ (prefixWord ++ tailWord_3167116).sum := by decide
  have hdescent : baseEnd_3167116 < baseStart_3167116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167133 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3167133 : Nat := 118140960795 + 3167133 * 2 ^ 59
def prefixEnd_3167133 : Nat := 4983230072969 + 3 ^ 40 * 3167133 * 2
def baseEnd_3167133 : Nat := 361391450159169402504917

theorem tailTrace_3167133 : CollatzResearch.WordTrace tailWord_3167133 prefixEnd_3167133 361391450159169402504917 := by
  unfold tailWord_3167133
  simp only [CollatzResearch.WordTrace]
  refine ⟨115514830435025519098002053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77009886956683679398668035 115514830435025519098002053)
  ·
    refine ⟨21659030706567284830875385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115514830435025519098002053 21659030706567284830875385)
    ·
      refine ⟨16244273029925463623156539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21659030706567284830875385 16244273029925463623156539)
      ·
        refine ⟨24366409544888195434734809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16244273029925463623156539 24366409544888195434734809)
        ·
          refine ⟨18274807158666146576051107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24366409544888195434734809 18274807158666146576051107)
          ·
            refine ⟨27412210737999219864076661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18274807158666146576051107 27412210737999219864076661)
            ·
              refine ⟨2569894756687426862257187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27412210737999219864076661 2569894756687426862257187)
              ·
                refine ⟨3854842135031140293385781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569894756687426862257187 3854842135031140293385781)
                ·
                  refine ⟨361391450159169402504917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854842135031140293385781 361391450159169402504917)
                  ·
                    rfl

theorem cell22_3167133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3167133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167133 prefixEnd_3167133 := by exact prefixLift 3167133
  have htrace : WordTrace (prefixWord ++ tailWord_3167133) baseStart_3167133 baseEnd_3167133 := by
    simpa [prefixWord, tailWord_3167133, baseEnd_3167133] using wordTrace_append hprefix tailTrace_3167133
  have hstable : (prefixWord ++ tailWord_3167133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167133).length < 2 ^ (prefixWord ++ tailWord_3167133).sum := by decide
  have hdescent : baseEnd_3167133 < baseStart_3167133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167255 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 3, 3]
def baseStart_3167255 : Nat := 118140960795 + 3167255 * 2 ^ 59
def prefixEnd_3167255 : Nat := 4983230072969 + 3 ^ 40 * 3167255 * 2
def baseEnd_3167255 : Nat := 1084216113570740555964377

theorem tailTrace_3167255 : CollatzResearch.WordTrace tailWord_3167255 prefixEnd_3167255 1084216113570740555964377 := by
  unfold tailWord_3167255
  simp only [CollatzResearch.WordTrace]
  refine ⟨115519280140583533933943219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77012853427055689289295479 115519280140583533933943219)
  ·
    refine ⟨173278920210875300900914829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115519280140583533933943219 173278920210875300900914829)
    ·
      refine ⟨64979595079078237837843061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173278920210875300900914829 64979595079078237837843061)
      ·
        refine ⟨6091837038663584797297787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64979595079078237837843061 6091837038663584797297787)
        ·
          refine ⟨9137755557995377195946681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091837038663584797297787 9137755557995377195946681)
          ·
            refine ⟨6853316668496532896960011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9137755557995377195946681 6853316668496532896960011)
            ·
              refine ⟨10279975002744799345440017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853316668496532896960011 10279975002744799345440017)
              ·
                refine ⟨7709981252058599509080013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10279975002744799345440017 7709981252058599509080013)
                ·
                  refine ⟨2891242969521974815905005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7709981252058599509080013 2891242969521974815905005)
                  ·
                    refine ⟨1084216113570740555964377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891242969521974815905005 1084216113570740555964377)
                    ·
                      rfl

theorem cell22_3167255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_3167255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167255 prefixEnd_3167255 := by exact prefixLift 3167255
  have htrace : WordTrace (prefixWord ++ tailWord_3167255) baseStart_3167255 baseEnd_3167255 := by
    simpa [prefixWord, tailWord_3167255, baseEnd_3167255] using wordTrace_append hprefix tailTrace_3167255
  have hstable : (prefixWord ++ tailWord_3167255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167255).length < 2 ^ (prefixWord ++ tailWord_3167255).sum := by decide
  have hdescent : baseEnd_3167255 < baseStart_3167255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167328 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_3167328 : Nat := 118140960795 + 3167328 * 2 ^ 59
def prefixEnd_3167328 : Nat := 4983230072969 + 3 ^ 40 * 3167328 * 2
def baseEnd_3167328 : Nat := 1084241102962592698889153

theorem tailTrace_3167328 : CollatzResearch.WordTrace tailWord_3167328 prefixEnd_3167328 1084241102962592698889153 := by
  unfold tailWord_3167328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57760971334659533700675319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77014628446212711600900425 57760971334659533700675319)
  ·
    refine ⟨86641457001989300551012979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57760971334659533700675319 86641457001989300551012979)
    ·
      refine ⟨129962185502983950826519469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86641457001989300551012979 129962185502983950826519469)
      ·
        refine ⟨48735819563618981559944801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129962185502983950826519469 48735819563618981559944801)
        ·
          refine ⟨36551864672714236169958601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48735819563618981559944801 36551864672714236169958601)
          ·
            refine ⟨27413898504535677127468951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36551864672714236169958601 27413898504535677127468951)
            ·
              refine ⟨41120847756803515691203427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27413898504535677127468951 41120847756803515691203427)
              ·
                refine ⟨61681271635205273536805141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41120847756803515691203427 61681271635205273536805141)
                ·
                  refine ⟨2891309607900247197037741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61681271635205273536805141 2891309607900247197037741)
                  ·
                    refine ⟨1084241102962592698889153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891309607900247197037741 1084241102962592698889153)
                    ·
                      rfl

theorem cell22_3167328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_3167328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167328 prefixEnd_3167328 := by exact prefixLift 3167328
  have htrace : WordTrace (prefixWord ++ tailWord_3167328) baseStart_3167328 baseEnd_3167328 := by
    simpa [prefixWord, tailWord_3167328, baseEnd_3167328] using wordTrace_append hprefix tailTrace_3167328
  have hstable : (prefixWord ++ tailWord_3167328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167328).length < 2 ^ (prefixWord ++ tailWord_3167328).sum := by decide
  have hdescent : baseEnd_3167328 < baseStart_3167328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167343 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_3167343 : Nat := 118140960795 + 3167343 * 2 ^ 59
def prefixEnd_3167343 : Nat := 4983230072969 + 3 ^ 40 * 3167343 * 2
def baseEnd_3167343 : Nat := 1084246237769137659764107

theorem tailTrace_3167343 : CollatzResearch.WordTrace tailWord_3167343 prefixEnd_3167343 1084246237769137659764107 := by
  unfold tailWord_3167343
  simp only [CollatzResearch.WordTrace]
  refine ⟨115522489764264724963146683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77014993176176483308764455 115522489764264724963146683)
  ·
    refine ⟨173283734646397087444720025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115522489764264724963146683 173283734646397087444720025)
    ·
      refine ⟨129962800984797815583540019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173283734646397087444720025 129962800984797815583540019)
      ·
        refine ⟨194944201477196723375310029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129962800984797815583540019 194944201477196723375310029)
        ·
          refine ⟨73104075553948771265741261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194944201477196723375310029 73104075553948771265741261)
          ·
            refine ⟨27414028332730789224652973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73104075553948771265741261 27414028332730789224652973)
            ·
              refine ⟨10280260624774045959244865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27414028332730789224652973 10280260624774045959244865)
              ·
                refine ⟨7710195468580534469433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10280260624774045959244865 7710195468580534469433649)
                ·
                  refine ⟨5782646601435400852075237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710195468580534469433649 5782646601435400852075237)
                  ·
                    refine ⟨1084246237769137659764107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5782646601435400852075237 1084246237769137659764107)
                    ·
                      rfl

theorem cell22_3167343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_3167343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167343 prefixEnd_3167343 := by exact prefixLift 3167343
  have htrace : WordTrace (prefixWord ++ tailWord_3167343) baseStart_3167343 baseEnd_3167343 := by
    simpa [prefixWord, tailWord_3167343, baseEnd_3167343] using wordTrace_append hprefix tailTrace_3167343
  have hstable : (prefixWord ++ tailWord_3167343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167343).length < 2 ^ (prefixWord ++ tailWord_3167343).sum := by decide
  have hdescent : baseEnd_3167343 < baseStart_3167343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167420 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_3167420 : Nat := 118140960795 + 3167420 * 2 ^ 59
def prefixEnd_3167420 : Nat := 4983230072969 + 3 ^ 40 * 3167420 * 2
def baseEnd_3167420 : Nat := 361424198814245041862957

theorem tailTrace_3167420 : CollatzResearch.WordTrace tailWord_3167420 prefixEnd_3167420 361424198814245041862957 := by
  unfold tailWord_3167420
  simp only [CollatzResearch.WordTrace]
  refine ⟨57762649092492883556849857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77016865456657178075799809 57762649092492883556849857)
  ·
    refine ⟨43321986819369662667637393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57762649092492883556849857 43321986819369662667637393)
    ·
      refine ⟨32491490114527247000728045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43321986819369662667637393 32491490114527247000728045)
      ·
        refine ⟨12184308792947717625273017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32491490114527247000728045 12184308792947717625273017)
        ·
          refine ⟨9138231594710788218954763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12184308792947717625273017 9138231594710788218954763)
          ·
            refine ⟨13707347392066182328432145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138231594710788218954763 13707347392066182328432145)
            ·
              refine ⟨10280510544049636746324109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13707347392066182328432145 10280510544049636746324109)
              ·
                refine ⟨3855191454018613779871541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10280510544049636746324109 3855191454018613779871541)
                ·
                  refine ⟨361424198814245041862957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3855191454018613779871541 361424198814245041862957)
                  ·
                    rfl

theorem cell22_3167420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_3167420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167420 prefixEnd_3167420 := by exact prefixLift 3167420
  have htrace : WordTrace (prefixWord ++ tailWord_3167420) baseStart_3167420 baseEnd_3167420 := by
    simpa [prefixWord, tailWord_3167420, baseEnd_3167420] using wordTrace_append hprefix tailTrace_3167420
  have hstable : (prefixWord ++ tailWord_3167420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167420).length < 2 ^ (prefixWord ++ tailWord_3167420).sum := by decide
  have hdescent : baseEnd_3167420 < baseStart_3167420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167493 : List Nat := [1, 3, 1, 1, 2, 1, 5, 8]
def baseStart_3167493 : Nat := 118140960795 + 3167493 * 2 ^ 59
def prefixEnd_3167493 : Nat := 4983230072969 + 3 ^ 40 * 3167493 * 2
def baseEnd_3167493 : Nat := 120477509537176363168183

theorem tailTrace_3167493 : CollatzResearch.WordTrace tailWord_3167493 prefixEnd_3167493 120477509537176363168183 := by
  unfold tailWord_3167493
  simp only [CollatzResearch.WordTrace]
  refine ⟨115527960713721300581107133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77018640475814200387404755 115527960713721300581107133)
  ·
    refine ⟨43322985267645487717915175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115527960713721300581107133 43322985267645487717915175)
    ·
      refine ⟨64984477901468231576872763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43322985267645487717915175 64984477901468231576872763)
      ·
        refine ⟨97476716852202347365309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64984477901468231576872763 97476716852202347365309145)
        ·
          refine ⟨73107537639151760523981859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97476716852202347365309145 73107537639151760523981859)
          ·
            refine ⟨109661306458727640785972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73107537639151760523981859 109661306458727640785972789)
            ·
              refine ⟨10280747480505716323684949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109661306458727640785972789 10280747480505716323684949)
              ·
                refine ⟨120477509537176363168183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10280747480505716323684949 120477509537176363168183)
                ·
                  rfl

theorem cell22_3167493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 8].length) (baseStart_3167493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167493 prefixEnd_3167493 := by exact prefixLift 3167493
  have htrace : WordTrace (prefixWord ++ tailWord_3167493) baseStart_3167493 baseEnd_3167493 := by
    simpa [prefixWord, tailWord_3167493, baseEnd_3167493] using wordTrace_append hprefix tailTrace_3167493
  have hstable : (prefixWord ++ tailWord_3167493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167493).length < 2 ^ (prefixWord ++ tailWord_3167493).sum := by decide
  have hdescent : baseEnd_3167493 < baseStart_3167493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167570 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3167570 : Nat := 118140960795 + 3167570 * 2 ^ 59
def prefixEnd_3167570 : Nat := 4983230072969 + 3 ^ 40 * 3167570 * 2
def baseEnd_3167570 : Nat := 1084323944508184734338411

theorem tailTrace_3167570 : CollatzResearch.WordTrace tailWord_3167570 prefixEnd_3167570 1084323944508184734338411 := by
  unfold tailWord_3167570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882692283610585682915041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77020512756294895154440109 28882692283610585682915041)
  ·
    refine ⟨21662019212707939262186281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28882692283610585682915041 21662019212707939262186281)
    ·
      refine ⟨16246514409530954446639711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21662019212707939262186281 16246514409530954446639711)
      ·
        refine ⟨24369771614296431669959567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16246514409530954446639711 24369771614296431669959567)
        ·
          refine ⟨36554657421444647504939351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24369771614296431669959567 36554657421444647504939351)
          ·
            refine ⟨54831986132166971257409027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36554657421444647504939351 54831986132166971257409027)
            ·
              refine ⟨82247979198250456886113541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54831986132166971257409027 82247979198250456886113541)
              ·
                refine ⟨15421496099671960666146289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82247979198250456886113541 15421496099671960666146289)
                ·
                  refine ⟨11566122074753970499609717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15421496099671960666146289 11566122074753970499609717)
                  ·
                    refine ⟨1084323944508184734338411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11566122074753970499609717 1084323944508184734338411)
                    ·
                      rfl

theorem cell22_3167570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3167570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3167570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3167570 prefixEnd_3167570 := by exact prefixLift 3167570
  have htrace : WordTrace (prefixWord ++ tailWord_3167570) baseStart_3167570 baseEnd_3167570 := by
    simpa [prefixWord, tailWord_3167570, baseEnd_3167570] using wordTrace_append hprefix tailTrace_3167570
  have hstable : (prefixWord ++ tailWord_3167570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167570).length < 2 ^ (prefixWord ++ tailWord_3167570).sum := by decide
  have hdescent : baseEnd_3167570 < baseStart_3167570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
