import V185TrunkScan22Chunk158

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1419289 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_1419289 : Nat := 118140960795 + 1419289 * 2 ^ 59
def prefixEnd_1419289 : Nat := 4983230072969 + 3 ^ 40 * 1419289 * 2
def baseEnd_1419289 : Nat := 485851629759468505973543

theorem tailTrace_1419289 : CollatzResearch.WordTrace tailWord_1419289 prefixEnd_1419289 485851629759468505973543 := by
  unfold tailWord_1419289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51765722555165823108236921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34510481703443882072157947 51765722555165823108236921)
  ·
    refine ⟨38824291916374367331177691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51765722555165823108236921 38824291916374367331177691)
    ·
      refine ⟨58236437874561550996766537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38824291916374367331177691 58236437874561550996766537)
      ·
        refine ⟨43677328405921163247574903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58236437874561550996766537 43677328405921163247574903)
        ·
          refine ⟨65515992608881744871362355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43677328405921163247574903 65515992608881744871362355)
          ·
            refine ⟨98273988913322617307043533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65515992608881744871362355 98273988913322617307043533)
            ·
              refine ⟨36852745842495981490141325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98273988913322617307043533 36852745842495981490141325)
              ·
                refine ⟨13819779690935993058802997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36852745842495981490141325 13819779690935993058802997)
                ·
                  refine ⟨1295604346025249349262781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13819779690935993058802997 1295604346025249349262781)
                  ·
                    refine ⟨485851629759468505973543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295604346025249349262781 485851629759468505973543)
                    ·
                      rfl

theorem cell22_1419289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_1419289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419289 prefixEnd_1419289 := by exact prefixLift 1419289
  have htrace : WordTrace (prefixWord ++ tailWord_1419289) baseStart_1419289 baseEnd_1419289 := by
    simpa [prefixWord, tailWord_1419289, baseEnd_1419289] using wordTrace_append hprefix tailTrace_1419289
  have hstable : (prefixWord ++ tailWord_1419289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419289).length < 2 ^ (prefixWord ++ tailWord_1419289).sum := by decide
  have hdescent : baseEnd_1419289 < baseStart_1419289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419319 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 5]
def baseStart_1419319 : Nat := 118140960795 + 1419319 * 2 ^ 59
def prefixEnd_1419319 : Nat := 4983230072969 + 3 ^ 40 * 1419319 * 2
def baseEnd_1419319 : Nat := 161953966457519475907817

theorem tailTrace_1419319 : CollatzResearch.WordTrace tailWord_1419319 prefixEnd_1419319 161953966457519475907817 := by
  unfold tailWord_1419319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51766816745057138231829011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34511211163371425487886007 51766816745057138231829011)
  ·
    refine ⟨77650225117585707347743517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51766816745057138231829011 77650225117585707347743517)
    ·
      refine ⟨29118834419094640255403819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77650225117585707347743517 29118834419094640255403819)
      ·
        refine ⟨43678251628641960383105729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29118834419094640255403819 43678251628641960383105729)
        ·
          refine ⟨32758688721481470287329297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43678251628641960383105729 32758688721481470287329297)
          ·
            refine ⟨24569016541111102715496973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32758688721481470287329297 24569016541111102715496973)
            ·
              refine ⟨9213381202916663518311365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24569016541111102715496973 9213381202916663518311365)
              ·
                refine ⟨1727508975546874409683381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9213381202916663518311365 1727508975546874409683381)
                ·
                  refine ⟨161953966457519475907817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727508975546874409683381 161953966457519475907817)
                  ·
                    rfl

theorem cell22_1419319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].length) (baseStart_1419319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419319 prefixEnd_1419319 := by exact prefixLift 1419319
  have htrace : WordTrace (prefixWord ++ tailWord_1419319) baseStart_1419319 baseEnd_1419319 := by
    simpa [prefixWord, tailWord_1419319, baseEnd_1419319] using wordTrace_append hprefix tailTrace_1419319
  have hstable : (prefixWord ++ tailWord_1419319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419319).length < 2 ^ (prefixWord ++ tailWord_1419319).sum := by decide
  have hdescent : baseEnd_1419319 < baseStart_1419319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419357 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1419357 : Nat := 118140960795 + 1419357 * 2 ^ 59
def prefixEnd_1419357 : Nat := 4983230072969 + 3 ^ 40 * 1419357 * 2
def baseEnd_1419357 : Nat := 485874907549138995273335

theorem tailTrace_1419357 : CollatzResearch.WordTrace tailWord_1419357 prefixEnd_1419357 485874907549138995273335 := by
  unfold tailWord_1419357
  simp only [CollatzResearch.WordTrace]
  refine ⟨51768202718919470721712325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34512135145946313814474883 51768202718919470721712325)
  ·
    refine ⟨9706538009797400760321061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51768202718919470721712325 9706538009797400760321061)
    ·
      refine ⟨1819975876837012642560199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9706538009797400760321061 1819975876837012642560199)
      ·
        refine ⟨2729963815255518963840299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819975876837012642560199 2729963815255518963840299)
        ·
          refine ⟨4094945722883278445760449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729963815255518963840299 4094945722883278445760449)
          ·
            refine ⟨3071209292162458834320337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4094945722883278445760449 3071209292162458834320337)
            ·
              refine ⟨2303406969121844125740253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071209292162458834320337 2303406969121844125740253)
              ·
                refine ⟨863777613420691547152595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303406969121844125740253 863777613420691547152595)
                ·
                  refine ⟨1295666420131037320728893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863777613420691547152595 1295666420131037320728893)
                  ·
                    refine ⟨485874907549138995273335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295666420131037320728893 485874907549138995273335)
                    ·
                      rfl

theorem cell22_1419357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1419357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419357 prefixEnd_1419357 := by exact prefixLift 1419357
  have htrace : WordTrace (prefixWord ++ tailWord_1419357) baseStart_1419357 baseEnd_1419357 := by
    simpa [prefixWord, tailWord_1419357, baseEnd_1419357] using wordTrace_append hprefix tailTrace_1419357
  have hstable : (prefixWord ++ tailWord_1419357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419357).length < 2 ^ (prefixWord ++ tailWord_1419357).sum := by decide
  have hdescent : baseEnd_1419357 < baseStart_1419357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419370 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_1419370 : Nat := 118140960795 + 1419370 * 2 ^ 59
def prefixEnd_1419370 : Nat := 4983230072969 + 3 ^ 40 * 1419370 * 2
def baseEnd_1419370 : Nat := 161959785904937098232765

theorem tailTrace_1419370 : CollatzResearch.WordTrace tailWord_1419370 prefixEnd_1419370 161959785904937098232765 := by
  unfold tailWord_1419370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12942169216968093485483891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34512451245248249294623709 12942169216968093485483891)
  ·
    refine ⟨19413253825452140228225837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12942169216968093485483891 19413253825452140228225837)
    ·
      refine ⟨7279970184544552585584689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19413253825452140228225837 7279970184544552585584689)
      ·
        refine ⟨5459977638408414439188517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7279970184544552585584689 5459977638408414439188517)
        ·
          refine ⟨1023745807201577707347847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5459977638408414439188517 1023745807201577707347847)
          ·
            refine ⟨1535618710802366561021771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023745807201577707347847 1535618710802366561021771)
            ·
              refine ⟨2303428066203549841532657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535618710802366561021771 2303428066203549841532657)
              ·
                refine ⟨1727571049652662381149493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303428066203549841532657 1727571049652662381149493)
                ·
                  refine ⟨161959785904937098232765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727571049652662381149493 161959785904937098232765)
                  ·
                    rfl

theorem cell22_1419370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_1419370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419370 prefixEnd_1419370 := by exact prefixLift 1419370
  have htrace : WordTrace (prefixWord ++ tailWord_1419370) baseStart_1419370 baseEnd_1419370 := by
    simpa [prefixWord, tailWord_1419370, baseEnd_1419370] using wordTrace_append hprefix tailTrace_1419370
  have hstable : (prefixWord ++ tailWord_1419370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419370).length < 2 ^ (prefixWord ++ tailWord_1419370).sum := by decide
  have hdescent : baseEnd_1419370 < baseStart_1419370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419415 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 4]
def baseStart_1419415 : Nat := 118140960795 + 1419415 * 2 ^ 59
def prefixEnd_1419415 : Nat := 4983230072969 + 3 ^ 40 * 1419415 * 2
def baseEnd_1419415 : Nat := 161964920711482059107719

theorem tailTrace_1419415 : CollatzResearch.WordTrace tailWord_1419415 prefixEnd_1419415 161964920711482059107719 := by
  unfold tailWord_1419415
  simp only [CollatzResearch.WordTrace]
  refine ⟨51770318152709346627323699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34513545435139564418215799 51770318152709346627323699)
  ·
    refine ⟨77655477229064019940985549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51770318152709346627323699 77655477229064019940985549)
    ·
      refine ⟨29120803960899007477869581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77655477229064019940985549 29120803960899007477869581)
      ·
        refine ⟨10920301485337127804201093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29120803960899007477869581 10920301485337127804201093)
        ·
          refine ⟨2047556528500711463287705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10920301485337127804201093 2047556528500711463287705)
          ·
            refine ⟨1535667396375533597465779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047556528500711463287705 1535667396375533597465779)
            ·
              refine ⟨2303501094563300396198669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535667396375533597465779 2303501094563300396198669)
              ·
                refine ⟨863812910461237648574501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303501094563300396198669 863812910461237648574501)
                ·
                  refine ⟨161964920711482059107719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863812910461237648574501 161964920711482059107719)
                  ·
                    rfl

theorem cell22_1419415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 4].length) (baseStart_1419415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419415 prefixEnd_1419415 := by exact prefixLift 1419415
  have htrace : WordTrace (prefixWord ++ tailWord_1419415) baseStart_1419415 baseEnd_1419415 := by
    simpa [prefixWord, tailWord_1419415, baseEnd_1419415] using wordTrace_append hprefix tailTrace_1419415
  have hstable : (prefixWord ++ tailWord_1419415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419415).length < 2 ^ (prefixWord ++ tailWord_1419415).sum := by decide
  have hdescent : baseEnd_1419415 < baseStart_1419415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419426 : List Nat := [3, 3, 1, 3, 1, 1, 10]
def baseStart_1419426 : Nat := 118140960795 + 1419426 * 2 ^ 59
def prefixEnd_1419426 : Nat := 4983230072969 + 3 ^ 40 * 1419426 * 2
def baseEnd_1419426 : Nat := 17996241765157252418449

theorem tailTrace_1419426 : CollatzResearch.WordTrace tailWord_1419426 prefixEnd_1419426 17996241765157252418449 := by
  unfold tailWord_1419426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12942679838917373876493533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34513812903779663670649421 12942679838917373876493533)
  ·
    refine ⟨4853504939594015203685075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12942679838917373876493533 4853504939594015203685075)
    ·
      refine ⟨7280257409391022805527613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853504939594015203685075 7280257409391022805527613)
      ·
        refine ⟨2730096528521633552072855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7280257409391022805527613 2730096528521633552072855)
        ·
          refine ⟨4095144792782450328109283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730096528521633552072855 4095144792782450328109283)
          ·
            refine ⟨6142717189173675492163925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095144792782450328109283 6142717189173675492163925)
            ·
              refine ⟨17996241765157252418449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6142717189173675492163925 17996241765157252418449)
              ·
                rfl

theorem cell22_1419426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 10].length) (baseStart_1419426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419426 prefixEnd_1419426 := by exact prefixLift 1419426
  have htrace : WordTrace (prefixWord ++ tailWord_1419426) baseStart_1419426 baseEnd_1419426 := by
    simpa [prefixWord, tailWord_1419426, baseEnd_1419426] using wordTrace_append hprefix tailTrace_1419426
  have hstable : (prefixWord ++ tailWord_1419426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419426).length < 2 ^ (prefixWord ++ tailWord_1419426).sum := by decide
  have hdescent : baseEnd_1419426 < baseStart_1419426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419428 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1419428 : Nat := 118140960795 + 1419428 * 2 ^ 59
def prefixEnd_1419428 : Nat := 4983230072969 + 3 ^ 40 * 1419428 * 2
def baseEnd_1419428 : Nat := 485899212300118476748117

theorem tailTrace_1419428 : CollatzResearch.WordTrace tailWord_1419428 prefixEnd_1419428 485899212300118476748117 := by
  unfold tailWord_1419428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25885396150831124923773469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34513861534441499898364625 25885396150831124923773469)
  ·
    refine ⟨9707023556561671846415051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25885396150831124923773469 9707023556561671846415051)
    ·
      refine ⟨14560535334842507769622577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707023556561671846415051 14560535334842507769622577)
      ·
        refine ⟨10920401501131880827216933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14560535334842507769622577 10920401501131880827216933)
        ·
          refine ⟨2047575281462227655103175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10920401501131880827216933 2047575281462227655103175)
          ·
            refine ⟨3071362922193341482654763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047575281462227655103175 3071362922193341482654763)
            ·
              refine ⟨4607044383290012223982145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071362922193341482654763 4607044383290012223982145)
              ·
                refine ⟨3455283287467509167986609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4607044383290012223982145 3455283287467509167986609)
                ·
                  refine ⟨2591462465600631875989957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3455283287467509167986609 2591462465600631875989957)
                  ·
                    refine ⟨485899212300118476748117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591462465600631875989957 485899212300118476748117)
                    ·
                      rfl

theorem cell22_1419428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1419428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419428 prefixEnd_1419428 := by exact prefixLift 1419428
  have htrace : WordTrace (prefixWord ++ tailWord_1419428) baseStart_1419428 baseEnd_1419428 := by
    simpa [prefixWord, tailWord_1419428, baseEnd_1419428] using wordTrace_append hprefix tailTrace_1419428
  have hstable : (prefixWord ++ tailWord_1419428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419428).length < 2 ^ (prefixWord ++ tailWord_1419428).sum := by decide
  have hdescent : baseEnd_1419428 < baseStart_1419428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419439 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_1419439 : Nat := 118140960795 + 1419439 * 2 ^ 59
def prefixEnd_1419439 : Nat := 4983230072969 + 3 ^ 40 * 1419439 * 2
def baseEnd_1419439 : Nat := 485902977824918114723083

theorem tailTrace_1419439 : CollatzResearch.WordTrace tailWord_1419439 prefixEnd_1419439 485902977824918114723083 := by
  unfold tailWord_1419439
  simp only [CollatzResearch.WordTrace]
  refine ⟨51771193504622398726197371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34514129003081599150798247 51771193504622398726197371)
  ·
    refine ⟨77656790256933598089296057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51771193504622398726197371 77656790256933598089296057)
    ·
      refine ⟨58242592692700198566972043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77656790256933598089296057 58242592692700198566972043)
      ·
        refine ⟨87363889039050297850458065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58242592692700198566972043 87363889039050297850458065)
        ·
          refine ⟨65522916779287723387843549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87363889039050297850458065 65522916779287723387843549)
          ·
            refine ⟨24571093792232896270441331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65522916779287723387843549 24571093792232896270441331)
            ·
              refine ⟨36856640688349344405661997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571093792232896270441331 36856640688349344405661997)
              ·
                refine ⟨13821240258131004152123249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36856640688349344405661997 13821240258131004152123249)
                ·
                  refine ⟨10365930193598253114092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13821240258131004152123249 10365930193598253114092437)
                  ·
                    refine ⟨485902977824918114723083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10365930193598253114092437 485902977824918114723083)
                    ·
                      rfl

theorem cell22_1419439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_1419439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419439 prefixEnd_1419439 := by exact prefixLift 1419439
  have htrace : WordTrace (prefixWord ++ tailWord_1419439) baseStart_1419439 baseEnd_1419439 := by
    simpa [prefixWord, tailWord_1419439, baseEnd_1419439] using wordTrace_append hprefix tailTrace_1419439
  have hstable : (prefixWord ++ tailWord_1419439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419439).length < 2 ^ (prefixWord ++ tailWord_1419439).sum := by decide
  have hdescent : baseEnd_1419439 < baseStart_1419439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419516 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1419516 : Nat := 118140960795 + 1419516 * 2 ^ 59
def prefixEnd_1419516 : Nat := 4983230072969 + 3 ^ 40 * 1419516 * 2
def baseEnd_1419516 : Nat := 161976445499505193515949

theorem tailTrace_1419516 : CollatzResearch.WordTrace tailWord_1419516 prefixEnd_1419516 161976445499505193515949 := by
  unfold tailWord_1419516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25887000962671720438375201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34516001283562293917833601 25887000962671720438375201)
  ·
    refine ⟨19415250722003790328781401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25887000962671720438375201 19415250722003790328781401)
    ·
      refine ⟨14561438041502842746586051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19415250722003790328781401 14561438041502842746586051)
      ·
        refine ⟨21842157062254264119879077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14561438041502842746586051 21842157062254264119879077)
        ·
          refine ⟨4095404449172674522477327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21842157062254264119879077 4095404449172674522477327)
          ·
            refine ⟨6143106673759011783715991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095404449172674522477327 6143106673759011783715991)
            ·
              refine ⟨9214660010638517675573987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143106673759011783715991 9214660010638517675573987)
              ·
                refine ⟨13821990015957776513360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214660010638517675573987 13821990015957776513360981)
                ·
                  refine ⟨161976445499505193515949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13821990015957776513360981 161976445499505193515949)
                  ·
                    rfl

theorem cell22_1419516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1419516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419516 prefixEnd_1419516 := by exact prefixLift 1419516
  have htrace : WordTrace (prefixWord ++ tailWord_1419516) baseStart_1419516 baseEnd_1419516 := by
    simpa [prefixWord, tailWord_1419516, baseEnd_1419516] using wordTrace_append hprefix tailTrace_1419516
  have hstable : (prefixWord ++ tailWord_1419516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419516).length < 2 ^ (prefixWord ++ tailWord_1419516).sum := by decide
  have hdescent : baseEnd_1419516 < baseStart_1419516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419518 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1419518 : Nat := 118140960795 + 1419518 * 2 ^ 59
def prefixEnd_1419518 : Nat := 4983230072969 + 3 ^ 40 * 1419518 * 2
def baseEnd_1419518 : Nat := 485930021139388241997841

theorem tailTrace_1419518 : CollatzResearch.WordTrace tailWord_1419518 prefixEnd_1419518 485930021139388241997841 := by
  unfold tailWord_1419518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471759358917024402290401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34516049914224130145548805 6471759358917024402290401)
  ·
    refine ⟨4853819519187768301717801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6471759358917024402290401 4853819519187768301717801)
    ·
      refine ⟨3640364639390826226288351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853819519187768301717801 3640364639390826226288351)
      ·
        refine ⟨5460546959086239339432527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640364639390826226288351 5460546959086239339432527)
        ·
          refine ⟨8190820438629359009148791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460546959086239339432527 8190820438629359009148791)
          ·
            refine ⟨12286230657944038513723187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190820438629359009148791 12286230657944038513723187)
            ·
              refine ⟨18429345986916057770584781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286230657944038513723187 18429345986916057770584781)
              ·
                refine ⟨6911004745093521663969293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18429345986916057770584781 6911004745093521663969293)
                ·
                  refine ⟨2591626779410070623988485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6911004745093521663969293 2591626779410070623988485)
                  ·
                    refine ⟨485930021139388241997841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591626779410070623988485 485930021139388241997841)
                    ·
                      rfl

theorem cell22_1419518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1419518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419518 prefixEnd_1419518 := by exact prefixLift 1419518
  have htrace : WordTrace (prefixWord ++ tailWord_1419518) baseStart_1419518 baseEnd_1419518 := by
    simpa [prefixWord, tailWord_1419518, baseEnd_1419518] using wordTrace_append hprefix tailTrace_1419518
  have hstable : (prefixWord ++ tailWord_1419518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419518).length < 2 ^ (prefixWord ++ tailWord_1419518).sum := by decide
  have hdescent : baseEnd_1419518 < baseStart_1419518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419531 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_1419531 : Nat := 118140960795 + 1419531 * 2 ^ 59
def prefixEnd_1419531 : Nat := 4983230072969 + 3 ^ 40 * 1419531 * 2
def baseEnd_1419531 : Nat := 485934471305060541422801

theorem tailTrace_1419531 : CollatzResearch.WordTrace tailWord_1419531 prefixEnd_1419531 485934471305060541422801 := by
  unfold tailWord_1419531
  simp only [CollatzResearch.WordTrace]
  refine ⟨51774549020289098438546447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34516366013526065625697631 51774549020289098438546447)
  ·
    refine ⟨77661823530433647657819671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51774549020289098438546447 77661823530433647657819671)
    ·
      refine ⟨116492735295650471486729507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77661823530433647657819671 116492735295650471486729507)
      ·
        refine ⟨174739102943475707230094261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116492735295650471486729507 174739102943475707230094261)
        ·
          refine ⟨16381790900950847552821337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174739102943475707230094261 16381790900950847552821337)
          ·
            refine ⟨12286343175713135664616003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16381790900950847552821337 12286343175713135664616003)
            ·
              refine ⟨18429514763569703496924005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286343175713135664616003 18429514763569703496924005)
              ·
                refine ⟨3455534018169319405673251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18429514763569703496924005 3455534018169319405673251)
                ·
                  refine ⟨5183301027253979108509877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455534018169319405673251 5183301027253979108509877)
                  ·
                    refine ⟨485934471305060541422801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5183301027253979108509877 485934471305060541422801)
                    ·
                      rfl

theorem cell22_1419531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_1419531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419531 prefixEnd_1419531 := by exact prefixLift 1419531
  have htrace : WordTrace (prefixWord ++ tailWord_1419531) baseStart_1419531 baseEnd_1419531 := by
    simpa [prefixWord, tailWord_1419531, baseEnd_1419531] using wordTrace_append hprefix tailTrace_1419531
  have hstable : (prefixWord ++ tailWord_1419531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419531).length < 2 ^ (prefixWord ++ tailWord_1419531).sum := by decide
  have hdescent : baseEnd_1419531 < baseStart_1419531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419550 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1419550 : Nat := 118140960795 + 1419550 * 2 ^ 59
def prefixEnd_1419550 : Nat := 4983230072969 + 3 ^ 40 * 1419550 * 2
def baseEnd_1419550 : Nat := 161980325131116941732581

theorem tailTrace_1419550 : CollatzResearch.WordTrace tailWord_1419550 prefixEnd_1419550 161980325131116941732581 := by
  unfold tailWord_1419550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471905250902533085436013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34516828004813509788992069 6471905250902533085436013)
  ·
    refine ⟨2426964469088449907038505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6471905250902533085436013 2426964469088449907038505)
    ·
      refine ⟨1820223351816337430278879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2426964469088449907038505 1820223351816337430278879)
      ·
        refine ⟨2730335027724506145418319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820223351816337430278879 2730335027724506145418319)
        ·
          refine ⟨4095502541586759218127479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730335027724506145418319 4095502541586759218127479)
          ·
            refine ⟨6143253812380138827191219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095502541586759218127479 6143253812380138827191219)
            ·
              refine ⟨9214880718570208240786829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143253812380138827191219 9214880718570208240786829)
              ·
                refine ⟨3455580269463828090295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9214880718570208240786829 3455580269463828090295061)
                ·
                  refine ⟨161980325131116941732581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3455580269463828090295061 161980325131116941732581)
                  ·
                    rfl

theorem cell22_1419550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1419550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419550 prefixEnd_1419550 := by exact prefixLift 1419550
  have htrace : WordTrace (prefixWord ++ tailWord_1419550) baseStart_1419550 baseEnd_1419550 := by
    simpa [prefixWord, tailWord_1419550, baseEnd_1419550] using wordTrace_append hprefix tailTrace_1419550
  have hstable : (prefixWord ++ tailWord_1419550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419550).length < 2 ^ (prefixWord ++ tailWord_1419550).sum := by decide
  have hdescent : baseEnd_1419550 < baseStart_1419550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419578 : List Nat := [3, 1, 1, 1, 4, 2, 4, 6]
def baseStart_1419578 : Nat := 118140960795 + 1419578 * 2 ^ 59
def prefixEnd_1419578 : Nat := 4983230072969 + 3 ^ 40 * 1419578 * 2
def baseEnd_1419578 : Nat := 53994506707285342833073

theorem tailTrace_1419578 : CollatzResearch.WordTrace tailWord_1419578 prefixEnd_1419578 53994506707285342833073 := by
  unfold tailWord_1419578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944065812779706366376847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34517508834079216977004925 12944065812779706366376847)
  ·
    refine ⟨19416098719169559549565271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944065812779706366376847 19416098719169559549565271)
    ·
      refine ⟨29124148078754339324347907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19416098719169559549565271 29124148078754339324347907)
      ·
        refine ⟨43686222118131508986521861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29124148078754339324347907 43686222118131508986521861)
        ·
          refine ⟨8191166647149657934972849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43686222118131508986521861 8191166647149657934972849)
          ·
            refine ⟨6143374985362243451229637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8191166647149657934972849 6143374985362243451229637)
            ·
              refine ⟨1151882809755420647105557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6143374985362243451229637 1151882809755420647105557)
              ·
                refine ⟨53994506707285342833073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1151882809755420647105557 53994506707285342833073)
                ·
                  rfl

theorem cell22_1419578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_1419578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419578 prefixEnd_1419578 := by exact prefixLift 1419578
  have htrace : WordTrace (prefixWord ++ tailWord_1419578) baseStart_1419578 baseEnd_1419578 := by
    simpa [prefixWord, tailWord_1419578, baseEnd_1419578] using wordTrace_append hprefix tailTrace_1419578
  have hstable : (prefixWord ++ tailWord_1419578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419578).length < 2 ^ (prefixWord ++ tailWord_1419578).sum := by decide
  have hdescent : baseEnd_1419578 < baseStart_1419578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419683 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_1419683 : Nat := 118140960795 + 1419683 * 2 ^ 59
def prefixEnd_1419683 : Nat := 4983230072969 + 3 ^ 40 * 1419683 * 2
def baseEnd_1419683 : Nat := 485986504011382811622335

theorem tailTrace_1419683 : CollatzResearch.WordTrace tailWord_1419683 prefixEnd_1419683 485986504011382811622335 := by
  unfold tailWord_1419683
  simp only [CollatzResearch.WordTrace]
  refine ⟨51780092915738428398079703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34520061943825618932053135 51780092915738428398079703)
  ·
    refine ⟨77670139373607642597119555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51780092915738428398079703 77670139373607642597119555)
    ·
      refine ⟨116505209060411463895679333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77670139373607642597119555 116505209060411463895679333)
      ·
        refine ⟨21844726698827149480439875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116505209060411463895679333 21844726698827149480439875)
        ·
          refine ⟨32767090048240724220659813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21844726698827149480439875 32767090048240724220659813)
          ·
            refine ⟨6143829384045135791373715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32767090048240724220659813 6143829384045135791373715)
            ·
              refine ⟨9215744076067703687060573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143829384045135791373715 9215744076067703687060573)
              ·
                refine ⟨3455904028525388882647715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9215744076067703687060573 3455904028525388882647715)
                ·
                  refine ⟨5183856042788083323971573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455904028525388882647715 5183856042788083323971573)
                  ·
                    refine ⟨485986504011382811622335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5183856042788083323971573 485986504011382811622335)
                    ·
                      rfl

theorem cell22_1419683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_1419683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419683 prefixEnd_1419683 := by exact prefixLift 1419683
  have htrace : WordTrace (prefixWord ++ tailWord_1419683) baseStart_1419683 baseEnd_1419683 := by
    simpa [prefixWord, tailWord_1419683, baseEnd_1419683] using wordTrace_append hprefix tailTrace_1419683
  have hstable : (prefixWord ++ tailWord_1419683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419683).length < 2 ^ (prefixWord ++ tailWord_1419683).sum := by decide
  have hdescent : baseEnd_1419683 < baseStart_1419683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419698 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1419698 : Nat := 118140960795 + 1419698 * 2 ^ 59
def prefixEnd_1419698 : Nat := 4983230072969 + 3 ^ 40 * 1419698 * 2
def baseEnd_1419698 : Nat := 485991638817927772497289

theorem tailTrace_1419698 : CollatzResearch.WordTrace tailWord_1419698 prefixEnd_1419698 485991638817927772497289 := by
  unfold tailWord_1419698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945160002671021489968937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34520426673789390639917165 12945160002671021489968937)
  ·
    refine ⟨9708870002003266117476703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12945160002671021489968937 9708870002003266117476703)
    ·
      refine ⟨14563305003004899176215055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9708870002003266117476703 14563305003004899176215055)
      ·
        refine ⟨21844957504507348764322583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563305003004899176215055 21844957504507348764322583)
        ·
          refine ⟨32767436256761023146483875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21844957504507348764322583 32767436256761023146483875)
          ·
            refine ⟨49151154385141534719725813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32767436256761023146483875 49151154385141534719725813)
            ·
              refine ⟨4607920723607018879974295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49151154385141534719725813 4607920723607018879974295)
              ·
                refine ⟨6911881085410528319961443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607920723607018879974295 6911881085410528319961443)
                ·
                  refine ⟨10367821628115792479942165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911881085410528319961443 10367821628115792479942165)
                  ·
                    refine ⟨485991638817927772497289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10367821628115792479942165 485991638817927772497289)
                    ·
                      rfl

theorem cell22_1419698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1419698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419698 prefixEnd_1419698 := by exact prefixLift 1419698
  have htrace : WordTrace (prefixWord ++ tailWord_1419698) baseStart_1419698 baseEnd_1419698 := by
    simpa [prefixWord, tailWord_1419698, baseEnd_1419698] using wordTrace_append hprefix tailTrace_1419698
  have hstable : (prefixWord ++ tailWord_1419698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419698).length < 2 ^ (prefixWord ++ tailWord_1419698).sum := by decide
  have hdescent : baseEnd_1419698 < baseStart_1419698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419745 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1419745 : Nat := 118140960795 + 1419745 * 2 ^ 59
def prefixEnd_1419745 : Nat := 4983230072969 + 3 ^ 40 * 1419745 * 2
def baseEnd_1419745 : Nat := 486007727878435316572145

theorem tailTrace_1419745 : CollatzResearch.WordTrace tailWord_1419745 prefixEnd_1419745 486007727878435316572145 := by
  unfold tailWord_1419745
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782354241513812986836689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34521569494342541991224459 51782354241513812986836689)
  ·
    refine ⟨38836765681135359740127517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51782354241513812986836689 38836765681135359740127517)
    ·
      refine ⟨14563787130425759902547819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38836765681135359740127517 14563787130425759902547819)
      ·
        refine ⟨21845680695638639853821729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563787130425759902547819 21845680695638639853821729)
        ·
          refine ⟨16384260521728979890366297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21845680695638639853821729 16384260521728979890366297)
          ·
            refine ⟨12288195391296734917774723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16384260521728979890366297 12288195391296734917774723)
            ·
              refine ⟨18432293086945102376662085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12288195391296734917774723 18432293086945102376662085)
              ·
                refine ⟨3456054953802206695624141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18432293086945102376662085 3456054953802206695624141)
                ·
                  refine ⟨1296020607675827510859053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3456054953802206695624141 1296020607675827510859053)
                  ·
                    refine ⟨486007727878435316572145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296020607675827510859053 486007727878435316572145)
                    ·
                      rfl

theorem cell22_1419745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1419745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419745 prefixEnd_1419745 := by exact prefixLift 1419745
  have htrace : WordTrace (prefixWord ++ tailWord_1419745) baseStart_1419745 baseEnd_1419745 := by
    simpa [prefixWord, tailWord_1419745, baseEnd_1419745] using wordTrace_append hprefix tailTrace_1419745
  have hstable : (prefixWord ++ tailWord_1419745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419745).length < 2 ^ (prefixWord ++ tailWord_1419745).sum := by decide
  have hdescent : baseEnd_1419745 < baseStart_1419745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419747 : List Nat := [1, 1, 1, 6, 3, 2, 2, 6]
def baseStart_1419747 : Nat := 118140960795 + 1419747 * 2 ^ 59
def prefixEnd_1419747 : Nat := 4983230072969 + 3 ^ 40 * 1419747 * 2
def baseEnd_1419747 : Nat := 54000934724367553113571

theorem tailTrace_1419747 : CollatzResearch.WordTrace tailWord_1419747 prefixEnd_1419747 54000934724367553113571 := by
  unfold tailWord_1419747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782427187506567328409495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34521618125004378218939663 51782427187506567328409495)
  ·
    refine ⟨77673640781259850992614243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51782427187506567328409495 77673640781259850992614243)
    ·
      refine ⟨116510461171889776488921365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77673640781259850992614243 116510461171889776488921365)
      ·
        refine ⟨5461427867432333272918189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116510461171889776488921365 5461427867432333272918189)
        ·
          refine ⟨2048035450287124977344321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5461427867432333272918189 2048035450287124977344321)
          ·
            refine ⟨1536026587715343733008241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048035450287124977344321 1536026587715343733008241)
            ·
              refine ⟨1152019940786507799756181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536026587715343733008241 1152019940786507799756181)
              ·
                refine ⟨54000934724367553113571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1152019940786507799756181 54000934724367553113571)
                ·
                  rfl

theorem cell22_1419747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 6].length) (baseStart_1419747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419747 prefixEnd_1419747 := by exact prefixLift 1419747
  have htrace : WordTrace (prefixWord ++ tailWord_1419747) baseStart_1419747 baseEnd_1419747 := by
    simpa [prefixWord, tailWord_1419747, baseEnd_1419747] using wordTrace_append hprefix tailTrace_1419747
  have hstable : (prefixWord ++ tailWord_1419747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419747).length < 2 ^ (prefixWord ++ tailWord_1419747).sum := by decide
  have hdescent : baseEnd_1419747 < baseStart_1419747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419779 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 1, 3]
def baseStart_1419779 : Nat := 118140960795 + 1419779 * 2 ^ 59
def prefixEnd_1419779 : Nat := 4983230072969 + 3 ^ 40 * 1419779 * 2
def baseEnd_1419779 : Nat := 486019366773270561222041

theorem tailTrace_1419779 : CollatzResearch.WordTrace tailWord_1419779 prefixEnd_1419779 486019366773270561222041 := by
  unfold tailWord_1419779
  simp only [CollatzResearch.WordTrace]
  refine ⟨51783594323390636793574391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34522396215593757862382927 51783594323390636793574391)
  ·
    refine ⟨77675391485085955190361587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51783594323390636793574391 77675391485085955190361587)
    ·
      refine ⟨116513087227628932785542381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77675391485085955190361587 116513087227628932785542381)
      ·
        refine ⟨43692407710360849794578393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116513087227628932785542381 43692407710360849794578393)
        ·
          refine ⟨32769305782770637345933795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43692407710360849794578393 32769305782770637345933795)
          ·
            refine ⟨49153958674155956018900693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32769305782770637345933795 49153958674155956018900693)
            ·
              refine ⟨1152045906425530219192985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49153958674155956018900693 1152045906425530219192985)
              ·
                refine ⟨864034429819147664394739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152045906425530219192985 864034429819147664394739)
                ·
                  refine ⟨1296051644728721496592109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864034429819147664394739 1296051644728721496592109)
                  ·
                    refine ⟨486019366773270561222041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296051644728721496592109 486019366773270561222041)
                    ·
                      rfl

theorem cell22_1419779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 3].length) (baseStart_1419779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419779 prefixEnd_1419779 := by exact prefixLift 1419779
  have htrace : WordTrace (prefixWord ++ tailWord_1419779) baseStart_1419779 baseEnd_1419779 := by
    simpa [prefixWord, tailWord_1419779, baseEnd_1419779] using wordTrace_append hprefix tailTrace_1419779
  have hstable : (prefixWord ++ tailWord_1419779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419779).length < 2 ^ (prefixWord ++ tailWord_1419779).sum := by decide
  have hdescent : baseEnd_1419779 < baseStart_1419779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419852 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1419852 : Nat := 118140960795 + 1419852 * 2 ^ 59
def prefixEnd_1419852 : Nat := 4983230072969 + 3 ^ 40 * 1419852 * 2
def baseEnd_1419852 : Nat := 486044356165122704146817

theorem tailTrace_1419852 : CollatzResearch.WordTrace tailWord_1419852 prefixEnd_1419852 486044356165122704146817 := by
  unfold tailWord_1419852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25893128426063085130490905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34524171234750780173987873 25893128426063085130490905)
  ·
    refine ⟨19419846319547313847868179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25893128426063085130490905 19419846319547313847868179)
    ·
      refine ⟨29129769479320970771802269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19419846319547313847868179 29129769479320970771802269)
      ·
        refine ⟨10923663554745364039425851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29129769479320970771802269 10923663554745364039425851)
        ·
          refine ⟨16385495332118046059138777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923663554745364039425851 16385495332118046059138777)
          ·
            refine ⟨12289121499088534544354083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385495332118046059138777 12289121499088534544354083)
            ·
              refine ⟨18433682248632801816531125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12289121499088534544354083 18433682248632801816531125)
              ·
                refine ⟨1728157710809325170299793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18433682248632801816531125 1728157710809325170299793)
                ·
                  refine ⟨1296118283106993877724845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728157710809325170299793 1296118283106993877724845)
                  ·
                    refine ⟨486044356165122704146817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296118283106993877724845 486044356165122704146817)
                    ·
                      rfl

theorem cell22_1419852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1419852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419852 prefixEnd_1419852 := by exact prefixLift 1419852
  have htrace : WordTrace (prefixWord ++ tailWord_1419852) baseStart_1419852 baseEnd_1419852 := by
    simpa [prefixWord, tailWord_1419852, baseEnd_1419852] using wordTrace_append hprefix tailTrace_1419852
  have hstable : (prefixWord ++ tailWord_1419852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419852).length < 2 ^ (prefixWord ++ tailWord_1419852).sum := by decide
  have hdescent : baseEnd_1419852 < baseStart_1419852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419886 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1419886 : Nat := 118140960795 + 1419886 * 2 ^ 59
def prefixEnd_1419886 : Nat := 4983230072969 + 3 ^ 40 * 1419886 * 2
def baseEnd_1419886 : Nat := 486055995059957948796713

theorem tailTrace_1419886 : CollatzResearch.WordTrace tailWord_1419886 prefixEnd_1419886 486055995059957948796713 := by
  unfold tailWord_1419886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473437116750374258464939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34524997956001996045146341 6473437116750374258464939)
  ·
    refine ⟨9710155675125561387697409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6473437116750374258464939 9710155675125561387697409)
    ·
      refine ⟨7282616756344171040773057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9710155675125561387697409 7282616756344171040773057)
      ·
        refine ⟨5461962567258128280579793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7282616756344171040773057 5461962567258128280579793)
        ·
          refine ⟨4096471925443596210434845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461962567258128280579793 4096471925443596210434845)
          ·
            refine ⟨1536176972041348578913067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4096471925443596210434845 1536176972041348578913067)
            ·
              refine ⟨2304265458062022868369601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536176972041348578913067 2304265458062022868369601)
              ·
                refine ⟨1728199093546517151277201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2304265458062022868369601 1728199093546517151277201)
                ·
                  refine ⟨1296149320159887863457901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728199093546517151277201 1296149320159887863457901)
                  ·
                    refine ⟨486055995059957948796713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296149320159887863457901 486055995059957948796713)
                    ·
                      rfl

theorem cell22_1419886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1419886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419886 prefixEnd_1419886 := by exact prefixLift 1419886
  have htrace : WordTrace (prefixWord ++ tailWord_1419886) baseStart_1419886 baseEnd_1419886 := by
    simpa [prefixWord, tailWord_1419886, baseEnd_1419886] using wordTrace_append hprefix tailTrace_1419886
  have hstable : (prefixWord ++ tailWord_1419886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419886).length < 2 ^ (prefixWord ++ tailWord_1419886).sum := by decide
  have hdescent : baseEnd_1419886 < baseStart_1419886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419897 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_1419897 : Nat := 118140960795 + 1419897 * 2 ^ 59
def prefixEnd_1419897 : Nat := 4983230072969 + 3 ^ 40 * 1419897 * 2
def baseEnd_1419897 : Nat := 486059760584757586771679

theorem tailTrace_1419897 : CollatzResearch.WordTrace tailWord_1419897 prefixEnd_1419897 486059760584757586771679 := by
  unfold tailWord_1419897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787898136963142946369945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34525265424642095297579963 51787898136963142946369945)
  ·
    refine ⟨38840923602722357209777459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51787898136963142946369945 38840923602722357209777459)
    ·
      refine ⟨58261385404083535814666189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38840923602722357209777459 58261385404083535814666189)
      ·
        refine ⟨21848019526531325930499821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58261385404083535814666189 21848019526531325930499821)
        ·
          refine ⟨8193007322449247223937433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21848019526531325930499821 8193007322449247223937433)
          ·
            refine ⟨6144755491836935417953075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8193007322449247223937433 6144755491836935417953075)
            ·
              refine ⟨9217133237755403126929613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144755491836935417953075 9217133237755403126929613)
              ·
                refine ⟨3456424964158276172598605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9217133237755403126929613 3456424964158276172598605)
                ·
                  refine ⟨1296159361559353564724477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3456424964158276172598605 1296159361559353564724477)
                  ·
                    refine ⟨486059760584757586771679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296159361559353564724477 486059760584757586771679)
                    ·
                      rfl

theorem cell22_1419897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_1419897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419897 prefixEnd_1419897 := by exact prefixLift 1419897
  have htrace : WordTrace (prefixWord ++ tailWord_1419897) baseStart_1419897 baseEnd_1419897 := by
    simpa [prefixWord, tailWord_1419897, baseEnd_1419897] using wordTrace_append hprefix tailTrace_1419897
  have hstable : (prefixWord ++ tailWord_1419897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419897).length < 2 ^ (prefixWord ++ tailWord_1419897).sum := by decide
  have hdescent : baseEnd_1419897 < baseStart_1419897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420004 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1420004 : Nat := 118140960795 + 1420004 * 2 ^ 59
def prefixEnd_1420004 : Nat := 4983230072969 + 3 ^ 40 * 1420004 * 2
def baseEnd_1420004 : Nat := 486096388871444974346351

theorem tailTrace_1420004 : CollatzResearch.WordTrace tailWord_1420004 prefixEnd_1420004 486096388871444974346351 := by
  unfold tailWord_1420004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895900373787750110257533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34527867165050333480343377 25895900373787750110257533)
  ·
    refine ⟨9710962640170406291346575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25895900373787750110257533 9710962640170406291346575)
    ·
      refine ⟨14566443960255609437019863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9710962640170406291346575 14566443960255609437019863)
      ·
        refine ⟨21849665940383414155529795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566443960255609437019863 21849665940383414155529795)
        ·
          refine ⟨32774498910575121233294693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21849665940383414155529795 32774498910575121233294693)
          ·
            refine ⟨6145218545732835231242755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32774498910575121233294693 6145218545732835231242755)
            ·
              refine ⟨9217827818599252846864133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145218545732835231242755 9217827818599252846864133)
              ·
                refine ⟨1728342715987359908787025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9217827818599252846864133 1728342715987359908787025)
                ·
                  refine ⟨1296257036990519931590269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728342715987359908787025 1296257036990519931590269)
                  ·
                    refine ⟨486096388871444974346351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296257036990519931590269 486096388871444974346351)
                    ·
                      rfl

theorem cell22_1420004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1420004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420004 prefixEnd_1420004 := by exact prefixLift 1420004
  have htrace : WordTrace (prefixWord ++ tailWord_1420004) baseStart_1420004 baseEnd_1420004 := by
    simpa [prefixWord, tailWord_1420004, baseEnd_1420004] using wordTrace_append hprefix tailTrace_1420004
  have hstable : (prefixWord ++ tailWord_1420004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420004).length < 2 ^ (prefixWord ++ tailWord_1420004).sum := by decide
  have hdescent : baseEnd_1420004 < baseStart_1420004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420066 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1420066 : Nat := 118140960795 + 1420066 * 2 ^ 59
def prefixEnd_1420066 : Nat := 4983230072969 + 3 ^ 40 * 1420066 * 2
def baseEnd_1420066 : Nat := 486117612738497479296161

theorem tailTrace_1420066 : CollatzResearch.WordTrace tailWord_1420066 prefixEnd_1420066 486117612738497479296161 := by
  unfold tailWord_1420066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948515518337721202318013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34529374715567256539514701 12948515518337721202318013)
  ·
    refine ⟨4855693319376645450869255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12948515518337721202318013 4855693319376645450869255)
    ·
      refine ⟨7283539979064968176303883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855693319376645450869255 7283539979064968176303883)
      ·
        refine ⟨10925309968597452264455825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283539979064968176303883 10925309968597452264455825)
        ·
          refine ⟨8193982476448089198341869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10925309968597452264455825 8193982476448089198341869)
          ·
            refine ⟨3072743428668033449378201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8193982476448089198341869 3072743428668033449378201)
            ·
              refine ⟨2304557571501025087033651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072743428668033449378201 2304557571501025087033651)
              ·
                refine ⟨3456836357251537630550477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304557571501025087033651 3456836357251537630550477)
                ·
                  refine ⟨1296313633969326611456429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3456836357251537630550477 1296313633969326611456429)
                  ·
                    refine ⟨486117612738497479296161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296313633969326611456429 486117612738497479296161)
                    ·
                      rfl

theorem cell22_1420066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1420066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420066 prefixEnd_1420066 := by exact prefixLift 1420066
  have htrace : WordTrace (prefixWord ++ tailWord_1420066) baseStart_1420066 baseEnd_1420066 := by
    simpa [prefixWord, tailWord_1420066, baseEnd_1420066] using wordTrace_append hprefix tailTrace_1420066
  have hstable : (prefixWord ++ tailWord_1420066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420066).length < 2 ^ (prefixWord ++ tailWord_1420066).sum := by decide
  have hdescent : baseEnd_1420066 < baseStart_1420066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420130 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1420130 : Nat := 118140960795 + 1420130 * 2 ^ 59
def prefixEnd_1420130 : Nat := 4983230072969 + 3 ^ 40 * 1420130 * 2
def baseEnd_1420130 : Nat := 162046507082140881898655

theorem tailTrace_1420130 : CollatzResearch.WordTrace tailWord_1420130 prefixEnd_1420130 162046507082140881898655 := by
  unfold tailWord_1420130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949099086279755934900461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34530930896746015826401229 12949099086279755934900461)
  ·
    refine ⟨4855912157354908475587673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12949099086279755934900461 4855912157354908475587673)
    ·
      refine ⟨3641934118016181356690755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4855912157354908475587673 3641934118016181356690755)
      ·
        refine ⟨5462901177024272035036133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641934118016181356690755 5462901177024272035036133)
        ·
          refine ⟨1024293970692051006569275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5462901177024272035036133 1024293970692051006569275)
          ·
            refine ⟨1536440956038076509853913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024293970692051006569275 1536440956038076509853913)
            ·
              refine ⟨1152330717028557382390435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536440956038076509853913 1152330717028557382390435)
              ·
                refine ⟨1728496075542836073585653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152330717028557382390435 1728496075542836073585653)
                ·
                  refine ⟨162046507082140881898655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728496075542836073585653 162046507082140881898655)
                  ·
                    rfl

theorem cell22_1420130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1420130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420130 prefixEnd_1420130 := by exact prefixLift 1420130
  have htrace : WordTrace (prefixWord ++ tailWord_1420130) baseStart_1420130 baseEnd_1420130 := by
    simpa [prefixWord, tailWord_1420130, baseEnd_1420130] using wordTrace_append hprefix tailTrace_1420130
  have hstable : (prefixWord ++ tailWord_1420130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420130).length < 2 ^ (prefixWord ++ tailWord_1420130).sum := by decide
  have hdescent : baseEnd_1420130 < baseStart_1420130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420186 : List Nat := [3, 1, 1, 4, 3, 2, 1, 7]
def baseStart_1420186 : Nat := 118140960795 + 1420186 * 2 ^ 59
def prefixEnd_1420186 : Nat := 4983230072969 + 3 ^ 40 * 1420186 * 2
def baseEnd_1420186 : Nat := 54017632354539685143977

theorem tailTrace_1420186 : CollatzResearch.WordTrace tailWord_1420186 prefixEnd_1420186 54017632354539685143977 := by
  unfold tailWord_1420186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949609708229036325910103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34532292555277430202426941 12949609708229036325910103)
  ·
    refine ⟨19424414562343554488865155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12949609708229036325910103 19424414562343554488865155)
    ·
      refine ⟨29136621843515331733297733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19424414562343554488865155 29136621843515331733297733)
      ·
        refine ⟨5463116595659124699993325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29136621843515331733297733 5463116595659124699993325)
        ·
          refine ⟨2048668723372171762497497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5463116595659124699993325 2048668723372171762497497)
          ·
            refine ⟨1536501542529128821873123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048668723372171762497497 1536501542529128821873123)
            ·
              refine ⟨2304752313793693232809685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536501542529128821873123 2304752313793693232809685)
              ·
                refine ⟨54017632354539685143977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2304752313793693232809685 54017632354539685143977)
                ·
                  rfl

theorem cell22_1420186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_1420186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420186 prefixEnd_1420186 := by exact prefixLift 1420186
  have htrace : WordTrace (prefixWord ++ tailWord_1420186) baseStart_1420186 baseEnd_1420186 := by
    simpa [prefixWord, tailWord_1420186, baseEnd_1420186] using wordTrace_append hprefix tailTrace_1420186
  have hstable : (prefixWord ++ tailWord_1420186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420186).length < 2 ^ (prefixWord ++ tailWord_1420186).sum := by decide
  have hdescent : baseEnd_1420186 < baseStart_1420186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420197 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 11]
def baseStart_1420197 : Nat := 118140960795 + 1420197 * 2 ^ 59
def prefixEnd_1420197 : Nat := 4983230072969 + 3 ^ 40 * 1420197 * 2
def baseEnd_1420197 : Nat := 162054152238552268090253

theorem tailTrace_1420197 : CollatzResearch.WordTrace tailWord_1420197 prefixEnd_1420197 162054152238552268090253 := by
  unfold tailWord_1420197
  simp only [CollatzResearch.WordTrace]
  refine ⟨51798840035876294182290845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34532560023917529454860563 51798840035876294182290845)
  ·
    refine ⟨19424565013453610318359067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51798840035876294182290845 19424565013453610318359067)
    ·
      refine ⟨29136847520180415477538601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19424565013453610318359067 29136847520180415477538601)
      ·
        refine ⟨21852635640135311608153951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29136847520180415477538601 21852635640135311608153951)
        ·
          refine ⟨32778953460202967412230927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21852635640135311608153951 32778953460202967412230927)
          ·
            refine ⟨49168430190304451118346391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32778953460202967412230927 49168430190304451118346391)
            ·
              refine ⟨73752645285456676677519587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49168430190304451118346391 73752645285456676677519587)
              ·
                refine ⟨110628967928185015016279381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73752645285456676677519587 110628967928185015016279381)
                ·
                  refine ⟨162054152238552268090253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 110628967928185015016279381 162054152238552268090253)
                  ·
                    rfl

theorem cell22_1420197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_1420197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420197 prefixEnd_1420197 := by exact prefixLift 1420197
  have htrace : WordTrace (prefixWord ++ tailWord_1420197) baseStart_1420197 baseEnd_1420197 := by
    simpa [prefixWord, tailWord_1420197, baseEnd_1420197] using wordTrace_append hprefix tailTrace_1420197
  have hstable : (prefixWord ++ tailWord_1420197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420197).length < 2 ^ (prefixWord ++ tailWord_1420197).sum := by decide
  have hdescent : baseEnd_1420197 < baseStart_1420197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420205 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1420205 : Nat := 118140960795 + 1420205 * 2 ^ 59
def prefixEnd_1420205 : Nat := 4983230072969 + 3 ^ 40 * 1420205 * 2
def baseEnd_1420205 : Nat := 486165195279147450070735

theorem tailTrace_1420205 : CollatzResearch.WordTrace tailWord_1420205 prefixEnd_1420205 486165195279147450070735 := by
  unfold tailWord_1420205
  simp only [CollatzResearch.WordTrace]
  refine ⟨51799131819847311548582069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34532754546564874365721379 51799131819847311548582069)
  ·
    refine ⟨4856168608110685457679569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51799131819847311548582069 4856168608110685457679569)
    ·
      refine ⟨3642126456083014093259677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4856168608110685457679569 3642126456083014093259677)
      ·
        refine ⟨1365797421031130284972379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3642126456083014093259677 1365797421031130284972379)
        ·
          refine ⟨2048696131546695427458569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365797421031130284972379 2048696131546695427458569)
          ·
            refine ⟨1536522098660021570593927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048696131546695427458569 1536522098660021570593927)
            ·
              refine ⟨2304783147990032355890891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536522098660021570593927 2304783147990032355890891)
              ·
                refine ⟨3457174721985048533836337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304783147990032355890891 3457174721985048533836337)
                ·
                  refine ⟨2592881041488786400377253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457174721985048533836337 2592881041488786400377253)
                  ·
                    refine ⟨486165195279147450070735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2592881041488786400377253 486165195279147450070735)
                    ·
                      rfl

theorem cell22_1420205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1420205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420205 prefixEnd_1420205 := by exact prefixLift 1420205
  have htrace : WordTrace (prefixWord ++ tailWord_1420205) baseStart_1420205 baseEnd_1420205 := by
    simpa [prefixWord, tailWord_1420205, baseEnd_1420205] using wordTrace_append hprefix tailTrace_1420205
  have hstable : (prefixWord ++ tailWord_1420205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420205).length < 2 ^ (prefixWord ++ tailWord_1420205).sum := by decide
  have hdescent : baseEnd_1420205 < baseStart_1420205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420218 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_1420218 : Nat := 118140960795 + 1420218 * 2 ^ 59
def prefixEnd_1420218 : Nat := 4983230072969 + 3 ^ 40 * 1420218 * 2
def baseEnd_1420218 : Nat := 486169645444819749495695

theorem tailTrace_1420218 : CollatzResearch.WordTrace tailWord_1420218 prefixEnd_1420218 486169645444819749495695 := by
  unfold tailWord_1420218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949901492200053692201327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34533070645866809845870205 12949901492200053692201327)
  ·
    refine ⟨19424852238300080538301991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12949901492200053692201327 19424852238300080538301991)
    ·
      refine ⟨29137278357450120807452987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19424852238300080538301991 29137278357450120807452987)
      ·
        refine ⟨43705917536175181211179481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29137278357450120807452987 43705917536175181211179481)
        ·
          refine ⟨32779438152131385908384611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43705917536175181211179481 32779438152131385908384611)
          ·
            refine ⟨49169157228197078862576917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32779438152131385908384611 49169157228197078862576917)
            ·
              refine ⟨2304804245071738071683293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49169157228197078862576917 2304804245071738071683293)
              ·
                refine ⟨864301591901901776881235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304804245071738071683293 864301591901901776881235)
                ·
                  refine ⟨1296452387852852665321853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864301591901901776881235 1296452387852852665321853)
                  ·
                    refine ⟨486169645444819749495695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296452387852852665321853 486169645444819749495695)
                    ·
                      rfl

theorem cell22_1420218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_1420218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420218 prefixEnd_1420218 := by exact prefixLift 1420218
  have htrace : WordTrace (prefixWord ++ tailWord_1420218) baseStart_1420218 baseEnd_1420218 := by
    simpa [prefixWord, tailWord_1420218, baseEnd_1420218] using wordTrace_append hprefix tailTrace_1420218
  have hstable : (prefixWord ++ tailWord_1420218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420218).length < 2 ^ (prefixWord ++ tailWord_1420218).sum := by decide
  have hdescent : baseEnd_1420218 < baseStart_1420218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420259 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 6]
def baseStart_1420259 : Nat := 118140960795 + 1420259 * 2 ^ 59
def prefixEnd_1420259 : Nat := 4983230072969 + 3 ^ 40 * 1420259 * 2
def baseEnd_1420259 : Nat := 162061226860903103073523

theorem tailTrace_1420259 : CollatzResearch.WordTrace tailWord_1420259 prefixEnd_1420259 162061226860903103073523 := by
  unfold tailWord_1420259
  simp only [CollatzResearch.WordTrace]
  refine ⟨51801101361651678771047831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34534067574434452514031887 51801101361651678771047831)
  ·
    refine ⟨77701652042477518156571747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51801101361651678771047831 77701652042477518156571747)
    ·
      refine ⟨116552478063716277234857621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77701652042477518156571747 116552478063716277234857621)
      ·
        refine ⟨5463397409236700495383951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116552478063716277234857621 5463397409236700495383951)
        ·
          refine ⟨8195096113855050743075927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5463397409236700495383951 8195096113855050743075927)
          ·
            refine ⟨12292644170782576114613891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8195096113855050743075927 12292644170782576114613891)
            ·
              refine ⟨18438966256173864171920837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12292644170782576114613891 18438966256173864171920837)
              ·
                refine ⟨3457306173032599532235157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18438966256173864171920837 3457306173032599532235157)
                ·
                  refine ⟨162061226860903103073523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3457306173032599532235157 162061226860903103073523)
                  ·
                    rfl

theorem cell22_1420259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_1420259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420259 prefixEnd_1420259 := by exact prefixLift 1420259
  have htrace : WordTrace (prefixWord ++ tailWord_1420259) baseStart_1420259 baseEnd_1420259 := by
    simpa [prefixWord, tailWord_1420259, baseEnd_1420259] using wordTrace_append hprefix tailTrace_1420259
  have hstable : (prefixWord ++ tailWord_1420259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420259).length < 2 ^ (prefixWord ++ tailWord_1420259).sum := by decide
  have hdescent : baseEnd_1420259 < baseStart_1420259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420278 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1420278 : Nat := 118140960795 + 1420278 * 2 ^ 59
def prefixEnd_1420278 : Nat := 4983230072969 + 3 ^ 40 * 1420278 * 2
def baseEnd_1420278 : Nat := 486190184670999592995511

theorem tailTrace_1420278 : CollatzResearch.WordTrace tailWord_1420278 prefixEnd_1420278 486190184670999592995511 := by
  unfold tailWord_1420278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237612146786427813499343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34534529565721896677326325 3237612146786427813499343)
  ·
    refine ⟨4856418220179641720249015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3237612146786427813499343 4856418220179641720249015)
    ·
      refine ⟨7284627330269462580373523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856418220179641720249015 7284627330269462580373523)
      ·
        refine ⟨10926940995404193870560285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284627330269462580373523 10926940995404193870560285)
        ·
          refine ⟨4097602873276572701460107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10926940995404193870560285 4097602873276572701460107)
          ·
            refine ⟨6146404309914859052190161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097602873276572701460107 6146404309914859052190161)
            ·
              refine ⟨4609803232436144289142621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6146404309914859052190161 4609803232436144289142621)
              ·
                refine ⟨1728676212163554108428483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4609803232436144289142621 1728676212163554108428483)
                ·
                  refine ⟨2593014318245331162642725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728676212163554108428483 2593014318245331162642725)
                  ·
                    refine ⟨486190184670999592995511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593014318245331162642725 486190184670999592995511)
                    ·
                      rfl

theorem cell22_1420278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1420278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420278 prefixEnd_1420278 := by exact prefixLift 1420278
  have htrace : WordTrace (prefixWord ++ tailWord_1420278) baseStart_1420278 baseEnd_1420278 := by
    simpa [prefixWord, tailWord_1420278, baseEnd_1420278] using wordTrace_append hprefix tailTrace_1420278
  have hstable : (prefixWord ++ tailWord_1420278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420278).length < 2 ^ (prefixWord ++ tailWord_1420278).sum := by decide
  have hdescent : baseEnd_1420278 < baseStart_1420278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420293 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 4]
def baseStart_1420293 : Nat := 118140960795 + 1420293 * 2 ^ 59
def prefixEnd_1420293 : Nat := 4983230072969 + 3 ^ 40 * 1420293 * 2
def baseEnd_1420293 : Nat := 162065106492514851290155

theorem tailTrace_1420293 : CollatzResearch.WordTrace tailWord_1420293 prefixEnd_1420293 162065106492514851290155 := by
  unfold tailWord_1420293
  simp only [CollatzResearch.WordTrace]
  refine ⟨51802341443528502577785533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34534894295685668385190355 51802341443528502577785533)
  ·
    refine ⟨19425878041323188466669575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51802341443528502577785533 19425878041323188466669575)
    ·
      refine ⟨29138817061984782700004363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19425878041323188466669575 29138817061984782700004363)
      ·
        refine ⟨43708225592977174050006545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29138817061984782700004363 43708225592977174050006545)
        ·
          refine ⟨32781169194732880537504909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43708225592977174050006545 32781169194732880537504909)
          ·
            refine ⟨12292938448024830201564341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32781169194732880537504909 12292938448024830201564341)
            ·
              refine ⟨1152462979502327831396657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12292938448024830201564341 1152462979502327831396657)
              ·
                refine ⟨864347234626745873547493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152462979502327831396657 864347234626745873547493)
                ·
                  refine ⟨162065106492514851290155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864347234626745873547493 162065106492514851290155)
                  ·
                    rfl

theorem cell22_1420293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_1420293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420293 prefixEnd_1420293 := by exact prefixLift 1420293
  have htrace : WordTrace (prefixWord ++ tailWord_1420293) baseStart_1420293 baseEnd_1420293 := by
    simpa [prefixWord, tailWord_1420293, baseEnd_1420293] using wordTrace_append hprefix tailTrace_1420293
  have hstable : (prefixWord ++ tailWord_1420293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420293).length < 2 ^ (prefixWord ++ tailWord_1420293).sum := by decide
  have hdescent : baseEnd_1420293 < baseStart_1420293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420366 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1420366 : Nat := 118140960795 + 1420366 * 2 ^ 59
def prefixEnd_1420366 : Nat := 4983230072969 + 3 ^ 40 * 1420366 * 2
def baseEnd_1420366 : Nat := 162073436289798898931747

theorem tailTrace_1420366 : CollatzResearch.WordTrace tailWord_1420366 prefixEnd_1420366 162073436289798898931747 := by
  unfold tailWord_1420366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475625496533004505649119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34536669314842690696795301 6475625496533004505649119)
  ·
    refine ⟨9713438244799506758473679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475625496533004505649119 9713438244799506758473679)
    ·
      refine ⟨14570157367199260137710519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713438244799506758473679 14570157367199260137710519)
      ·
        refine ⟨21855236050798890206565779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570157367199260137710519 21855236050798890206565779)
        ·
          refine ⟨32782854076198335309848669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21855236050798890206565779 32782854076198335309848669)
          ·
            refine ⟨12293570278574375741193251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32782854076198335309848669 12293570278574375741193251)
            ·
              refine ⟨18440355417861563611789877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12293570278574375741193251 18440355417861563611789877)
              ·
                refine ⟨1728783320424521588605301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18440355417861563611789877 1728783320424521588605301)
                ·
                  refine ⟨162073436289798898931747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728783320424521588605301 162073436289798898931747)
                  ·
                    rfl

theorem cell22_1420366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1420366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420366 prefixEnd_1420366 := by exact prefixLift 1420366
  have htrace : WordTrace (prefixWord ++ tailWord_1420366) baseStart_1420366 baseEnd_1420366 := by
    simpa [prefixWord, tailWord_1420366, baseEnd_1420366] using wordTrace_append hprefix tailTrace_1420366
  have hstable : (prefixWord ++ tailWord_1420366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420366).length < 2 ^ (prefixWord ++ tailWord_1420366).sum := by decide
  have hdescent : baseEnd_1420366 < baseStart_1420366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420374 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1420374 : Nat := 118140960795 + 1420374 * 2 ^ 59
def prefixEnd_1420374 : Nat := 4983230072969 + 3 ^ 40 * 1420374 * 2
def baseEnd_1420374 : Nat := 486223047432887342595217

theorem tailTrace_1420374 : CollatzResearch.WordTrace tailWord_1420374 prefixEnd_1420374 486223047432887342595217 := by
  unfold tailWord_1420374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237830984764690838217761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34536863837490035607656117 3237830984764690838217761)
  ·
    refine ⟨2428373238573518128663321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3237830984764690838217761 2428373238573518128663321)
    ·
      refine ⟨1821279928930138596497491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2428373238573518128663321 1821279928930138596497491)
      ·
        refine ⟨2731919893395207894746237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821279928930138596497491 2731919893395207894746237)
        ·
          refine ⟨1024469960023202960529839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2731919893395207894746237 1024469960023202960529839)
          ·
            refine ⟨1536704940034804440794759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024469960023202960529839 1536704940034804440794759)
            ·
              refine ⟨2305057410052206661192139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536704940034804440794759 2305057410052206661192139)
              ·
                refine ⟨3457586115078309991788209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305057410052206661192139 3457586115078309991788209)
                ·
                  refine ⟨2593189586308732493841157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457586115078309991788209 2593189586308732493841157)
                  ·
                    refine ⟨486223047432887342595217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593189586308732493841157 486223047432887342595217)
                    ·
                      rfl

theorem cell22_1420374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1420374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420374 prefixEnd_1420374 := by exact prefixLift 1420374
  have htrace : WordTrace (prefixWord ++ tailWord_1420374) baseStart_1420374 baseEnd_1420374 := by
    simpa [prefixWord, tailWord_1420374, baseEnd_1420374] using wordTrace_append hprefix tailTrace_1420374
  have hstable : (prefixWord ++ tailWord_1420374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420374).length < 2 ^ (prefixWord ++ tailWord_1420374).sum := by decide
  have hdescent : baseEnd_1420374 < baseStart_1420374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420430 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1420430 : Nat := 118140960795 + 1420430 * 2 ^ 59
def prefixEnd_1420430 : Nat := 4983230072969 + 3 ^ 40 * 1420430 * 2
def baseEnd_1420430 : Nat := 486242217377321863195045

theorem tailTrace_1420430 : CollatzResearch.WordTrace tailWord_1420430 prefixEnd_1420430 486242217377321863195045 := by
  unfold tailWord_1420430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475917280504021871940343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34538225496021449983681829 6475917280504021871940343)
  ·
    refine ⟨9713875920756032807910515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475917280504021871940343 9713875920756032807910515)
    ·
      refine ⟨14570813881134049211865773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713875920756032807910515 14570813881134049211865773)
      ·
        refine ⟨5464055205425268454449665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14570813881134049211865773 5464055205425268454449665)
        ·
          refine ⟨4098041404068951340837249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5464055205425268454449665 4098041404068951340837249)
          ·
            refine ⟨3073531053051713505627937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098041404068951340837249 3073531053051713505627937)
            ·
              refine ⟨2305148289788785129220953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073531053051713505627937 2305148289788785129220953)
              ·
                refine ⟨1728861217341588846915715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305148289788785129220953 1728861217341588846915715)
                ·
                  refine ⟨2593291826012383270373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728861217341588846915715 2593291826012383270373573)
                  ·
                    refine ⟨486242217377321863195045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593291826012383270373573 486242217377321863195045)
                    ·
                      rfl

theorem cell22_1420430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1420430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420430 prefixEnd_1420430 := by exact prefixLift 1420430
  have htrace : WordTrace (prefixWord ++ tailWord_1420430) baseStart_1420430 baseEnd_1420430 := by
    simpa [prefixWord, tailWord_1420430, baseEnd_1420430] using wordTrace_append hprefix tailTrace_1420430
  have hstable : (prefixWord ++ tailWord_1420430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420430).length < 2 ^ (prefixWord ++ tailWord_1420430).sum := by decide
  have hdescent : baseEnd_1420430 < baseStart_1420430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420488 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1420488 : Nat := 118140960795 + 1420488 * 2 ^ 59
def prefixEnd_1420488 : Nat := 4983230072969 + 3 ^ 40 * 1420488 * 2
def baseEnd_1420488 : Nat := 486262071962629045244867

theorem tailTrace_1420488 : CollatzResearch.WordTrace tailWord_1420488 prefixEnd_1420488 486262071962629045244867 := by
  unfold tailWord_1420488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25904726838911025440567059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34539635785214700587422745 25904726838911025440567059)
  ·
    refine ⟨38857090258366538160850589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25904726838911025440567059 38857090258366538160850589)
    ·
      refine ⟨14571408846887451810318971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38857090258366538160850589 14571408846887451810318971)
      ·
        refine ⟨21857113270331177715478457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14571408846887451810318971 21857113270331177715478457)
        ·
          refine ⟨16392834952748383286608843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21857113270331177715478457 16392834952748383286608843)
          ·
            refine ⟨24589252429122574929913265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16392834952748383286608843 24589252429122574929913265)
            ·
              refine ⟨18441939321841931197434949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24589252429122574929913265 18441939321841931197434949)
              ·
                refine ⟨3457863622845362099519053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18441939321841931197434949 3457863622845362099519053)
                ·
                  refine ⟨1296698858567010787319645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3457863622845362099519053 1296698858567010787319645)
                  ·
                    refine ⟨486262071962629045244867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296698858567010787319645 486262071962629045244867)
                    ·
                      rfl

theorem cell22_1420488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1420488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420488 prefixEnd_1420488 := by exact prefixLift 1420488
  have htrace : WordTrace (prefixWord ++ tailWord_1420488) baseStart_1420488 baseEnd_1420488 := by
    simpa [prefixWord, tailWord_1420488, baseEnd_1420488] using wordTrace_append hprefix tailTrace_1420488
  have hstable : (prefixWord ++ tailWord_1420488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420488).length < 2 ^ (prefixWord ++ tailWord_1420488).sum := by decide
  have hdescent : baseEnd_1420488 < baseStart_1420488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420505 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_1420505 : Nat := 118140960795 + 1420505 * 2 ^ 59
def prefixEnd_1420505 : Nat := 4983230072969 + 3 ^ 40 * 1420505 * 2
def baseEnd_1420505 : Nat := 486267891410046667569815

theorem tailTrace_1420505 : CollatzResearch.WordTrace tailWord_1420505 prefixEnd_1420505 486267891410046667569815 := by
  unfold tailWord_1420505
  simp only [CollatzResearch.WordTrace]
  refine ⟨51810073718760462784502969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34540049145840308523001979 51810073718760462784502969)
  ·
    refine ⟨38857555289070347088377227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51810073718760462784502969 38857555289070347088377227)
    ·
      refine ⟨58286332933605520632565841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38857555289070347088377227 58286332933605520632565841)
      ·
        refine ⟨43714749700204140474424381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58286332933605520632565841 43714749700204140474424381)
        ·
          refine ⟨16393031137576552677909143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43714749700204140474424381 16393031137576552677909143)
          ·
            refine ⟨24589546706364829016863715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393031137576552677909143 24589546706364829016863715)
            ·
              refine ⟨36884320059547243525295573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24589546706364829016863715 36884320059547243525295573)
              ·
                refine ⟨864476251395638520124115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36884320059547243525295573 864476251395638520124115)
                ·
                  refine ⟨1296714377093457780186173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864476251395638520124115 1296714377093457780186173)
                  ·
                    refine ⟨486267891410046667569815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296714377093457780186173 486267891410046667569815)
                    ·
                      rfl

theorem cell22_1420505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_1420505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420505 prefixEnd_1420505 := by exact prefixLift 1420505
  have htrace : WordTrace (prefixWord ++ tailWord_1420505) baseStart_1420505 baseEnd_1420505 := by
    simpa [prefixWord, tailWord_1420505, baseEnd_1420505] using wordTrace_append hprefix tailTrace_1420505
  have hstable : (prefixWord ++ tailWord_1420505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420505).length < 2 ^ (prefixWord ++ tailWord_1420505).sum := by decide
  have hdescent : baseEnd_1420505 < baseStart_1420505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420522 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1420522 : Nat := 118140960795 + 1420522 * 2 ^ 59
def prefixEnd_1420522 : Nat := 4983230072969 + 3 ^ 40 * 1420522 * 2
def baseEnd_1420522 : Nat := 486273710857464289894763

theorem tailTrace_1420522 : CollatzResearch.WordTrace tailWord_1420522 prefixEnd_1420522 486273710857464289894763 := by
  unfold tailWord_1420522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952673439924718671967955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34540462506465916458581213 12952673439924718671967955)
  ·
    refine ⟨19429010159887078007951933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952673439924718671967955 19429010159887078007951933)
    ·
      refine ⟨7285878809957654252981975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19429010159887078007951933 7285878809957654252981975)
      ·
        refine ⟨10928818214936481379472963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285878809957654252981975 10928818214936481379472963)
        ·
          refine ⟨16393227322404722069209445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928818214936481379472963 16393227322404722069209445)
          ·
            refine ⟨3073730122950885387976771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16393227322404722069209445 3073730122950885387976771)
            ·
              refine ⟨4610595184426328081965157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073730122950885387976771 4610595184426328081965157)
              ·
                refine ⟨864486597079936515368467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4610595184426328081965157 864486597079936515368467)
                ·
                  refine ⟨1296729895619904773052701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864486597079936515368467 1296729895619904773052701)
                  ·
                    refine ⟨486273710857464289894763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296729895619904773052701 486273710857464289894763)
                    ·
                      rfl

theorem cell22_1420522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1420522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420522 prefixEnd_1420522 := by exact prefixLift 1420522
  have htrace : WordTrace (prefixWord ++ tailWord_1420522) baseStart_1420522 baseEnd_1420522 := by
    simpa [prefixWord, tailWord_1420522, baseEnd_1420522] using wordTrace_append hprefix tailTrace_1420522
  have hstable : (prefixWord ++ tailWord_1420522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420522).length < 2 ^ (prefixWord ++ tailWord_1420522).sum := by decide
  have hdescent : baseEnd_1420522 < baseStart_1420522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420580 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1420580 : Nat := 118140960795 + 1420580 * 2 ^ 59
def prefixEnd_1420580 : Nat := 4983230072969 + 3 ^ 40 * 1420580 * 2
def baseEnd_1420580 : Nat := 162097855147590490648195

theorem tailTrace_1420580 : CollatzResearch.WordTrace tailWord_1420580 prefixEnd_1420580 162097855147590490648195 := by
  unfold tailWord_1420580
  simp only [CollatzResearch.WordTrace]
  refine ⟨25906404596744375296741597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34541872795659167062322129 25906404596744375296741597)
  ·
    refine ⟨9714901723779140736278099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25906404596744375296741597 9714901723779140736278099)
    ·
      refine ⟨14572352585668711104417149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9714901723779140736278099 14572352585668711104417149)
      ·
        refine ⟨5464632219625766664156431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14572352585668711104417149 5464632219625766664156431)
        ·
          refine ⟨8196948329438649996234647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464632219625766664156431 8196948329438649996234647)
          ·
            refine ⟨12295422494157974994351971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196948329438649996234647 12295422494157974994351971)
            ·
              refine ⟨18443133741236962491527957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12295422494157974994351971 18443133741236962491527957)
              ·
                refine ⟨864521894120482616790373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18443133741236962491527957 864521894120482616790373)
                ·
                  refine ⟨162097855147590490648195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864521894120482616790373 162097855147590490648195)
                  ·
                    rfl

theorem cell22_1420580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1420580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420580 prefixEnd_1420580 := by exact prefixLift 1420580
  have htrace : WordTrace (prefixWord ++ tailWord_1420580) baseStart_1420580 baseEnd_1420580 := by
    simpa [prefixWord, tailWord_1420580, baseEnd_1420580] using wordTrace_append hprefix tailTrace_1420580
  have hstable : (prefixWord ++ tailWord_1420580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420580).length < 2 ^ (prefixWord ++ tailWord_1420580).sum := by decide
  have hdescent : baseEnd_1420580 < baseStart_1420580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420591 : List Nat := [1, 1, 2, 1, 2, 1, 3, 11]
def baseStart_1420591 : Nat := 118140960795 + 1420591 * 2 ^ 59
def prefixEnd_1420591 : Nat := 4983230072969 + 3 ^ 40 * 1420591 * 2
def baseEnd_1420591 : Nat := 54033036774174567768839

theorem tailTrace_1420591 : CollatzResearch.WordTrace tailWord_1420591 prefixEnd_1420591 54033036774174567768839 := by
  unfold tailWord_1420591
  simp only [CollatzResearch.WordTrace]
  refine ⟨51813210396448899472133627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34542140264299266314755751 51813210396448899472133627)
  ·
    refine ⟨77719815594673349208200441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51813210396448899472133627 77719815594673349208200441)
    ·
      refine ⟨58289861696005011906150331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77719815594673349208200441 58289861696005011906150331)
      ·
        refine ⟨87434792544007517859225497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58289861696005011906150331 87434792544007517859225497)
        ·
          refine ⟨65576094408005638394419123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87434792544007517859225497 65576094408005638394419123)
          ·
            refine ⟨98364141612008457591628685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65576094408005638394419123 98364141612008457591628685)
            ·
              refine ⟨36886553104503171596860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98364141612008457591628685 36886553104503171596860757)
              ·
                refine ⟨54033036774174567768839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36886553104503171596860757 54033036774174567768839)
                ·
                  rfl

theorem cell22_1420591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 11].length) (baseStart_1420591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420591 prefixEnd_1420591 := by exact prefixLift 1420591
  have htrace : WordTrace (prefixWord ++ tailWord_1420591) baseStart_1420591 baseEnd_1420591 := by
    simpa [prefixWord, tailWord_1420591, baseEnd_1420591] using wordTrace_append hprefix tailTrace_1420591
  have hstable : (prefixWord ++ tailWord_1420591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420591).length < 2 ^ (prefixWord ++ tailWord_1420591).sum := by decide
  have hdescent : baseEnd_1420591 < baseStart_1420591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420593 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1420593 : Nat := 118140960795 + 1420593 * 2 ^ 59
def prefixEnd_1420593 : Nat := 4983230072969 + 3 ^ 40 * 1420593 * 2
def baseEnd_1420593 : Nat := 486298015608443771369545

theorem tailTrace_1420593 : CollatzResearch.WordTrace tailWord_1420593 prefixEnd_1420593 486298015608443771369545 := by
  unfold tailWord_1420593
  simp only [CollatzResearch.WordTrace]
  refine ⟨51813283342441653813706433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34542188894961102542470955 51813283342441653813706433)
  ·
    refine ⟨38859962506831240360279825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51813283342441653813706433 38859962506831240360279825)
    ·
      refine ⟨29144971880123430270209869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38859962506831240360279825 29144971880123430270209869)
      ·
        refine ⟨10929364455046286351328701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29144971880123430270209869 10929364455046286351328701)
        ·
          refine ⟨4098511670642357381748263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10929364455046286351328701 4098511670642357381748263)
          ·
            refine ⟨6147767505963536072622395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098511670642357381748263 6147767505963536072622395)
            ·
              refine ⟨9221651258945304108933593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147767505963536072622395 9221651258945304108933593)
              ·
                refine ⟨6916238444208978081700195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221651258945304108933593 6916238444208978081700195)
                ·
                  refine ⟨10374357666313467122550293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916238444208978081700195 10374357666313467122550293)
                  ·
                    refine ⟨486298015608443771369545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10374357666313467122550293 486298015608443771369545)
                    ·
                      rfl

theorem cell22_1420593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1420593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420593 prefixEnd_1420593 := by exact prefixLift 1420593
  have htrace : WordTrace (prefixWord ++ tailWord_1420593) baseStart_1420593 baseEnd_1420593 := by
    simpa [prefixWord, tailWord_1420593, baseEnd_1420593] using wordTrace_append hprefix tailTrace_1420593
  have hstable : (prefixWord ++ tailWord_1420593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420593).length < 2 ^ (prefixWord ++ tailWord_1420593).sum := by decide
  have hdescent : baseEnd_1420593 < baseStart_1420593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420595 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 5]
def baseStart_1420595 : Nat := 118140960795 + 1420595 * 2 ^ 59
def prefixEnd_1420595 : Nat := 4983230072969 + 3 ^ 40 * 1420595 * 2
def baseEnd_1420595 : Nat := 486298700249316432819539

theorem tailTrace_1420595 : CollatzResearch.WordTrace tailWord_1420595 prefixEnd_1420595 486298700249316432819539 := by
  unfold tailWord_1420595
  simp only [CollatzResearch.WordTrace]
  refine ⟨51813356288434408155279239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34542237525622938770186159 51813356288434408155279239)
  ·
    refine ⟨77720034432651612232918859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51813356288434408155279239 77720034432651612232918859)
    ·
      refine ⟨116580051648977418349378289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77720034432651612232918859 116580051648977418349378289)
      ·
        refine ⟨87435038736733063762033717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116580051648977418349378289 87435038736733063762033717)
        ·
          refine ⟨8197034881568724727690661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87435038736733063762033717 8197034881568724727690661)
          ·
            refine ⟨1536944040294135886441999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8197034881568724727690661 1536944040294135886441999)
            ·
              refine ⟨2305416060441203829662999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536944040294135886441999 2305416060441203829662999)
              ·
                refine ⟨3458124090661805744494499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305416060441203829662999 3458124090661805744494499)
                ·
                  refine ⟨5187186135992708616741749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458124090661805744494499 5187186135992708616741749)
                  ·
                    refine ⟨486298700249316432819539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5187186135992708616741749 486298700249316432819539)
                    ·
                      rfl

theorem cell22_1420595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].length) (baseStart_1420595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420595 prefixEnd_1420595 := by exact prefixLift 1420595
  have htrace : WordTrace (prefixWord ++ tailWord_1420595) baseStart_1420595 baseEnd_1420595 := by
    simpa [prefixWord, tailWord_1420595, baseEnd_1420595] using wordTrace_append hprefix tailTrace_1420595
  have hstable : (prefixWord ++ tailWord_1420595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420595).length < 2 ^ (prefixWord ++ tailWord_1420595).sum := by decide
  have hdescent : baseEnd_1420595 < baseStart_1420595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420612 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1420612 : Nat := 118140960795 + 1420612 * 2 ^ 59
def prefixEnd_1420612 : Nat := 4983230072969 + 3 ^ 40 * 1420612 * 2
def baseEnd_1420612 : Nat := 486304519696734055144487

theorem tailTrace_1420612 : CollatzResearch.WordTrace tailWord_1420612 prefixEnd_1420612 486304519696734055144487 := by
  unfold tailWord_1420612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25906988164686410029324045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34542650886248546705765393 25906988164686410029324045)
  ·
    refine ⟨9715120561757403760996517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25906988164686410029324045 9715120561757403760996517)
    ·
      refine ⟨1821585105329513205186847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9715120561757403760996517 1821585105329513205186847)
      ·
        refine ⟨2732377657994269807780271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821585105329513205186847 2732377657994269807780271)
        ·
          refine ⟨4098566486991404711670407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732377657994269807780271 4098566486991404711670407)
          ·
            refine ⟨6147849730487107067505611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098566486991404711670407 6147849730487107067505611)
            ·
              refine ⟨9221774595730660601258417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147849730487107067505611 9221774595730660601258417)
              ·
                refine ⟨6916330946797995450943813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221774595730660601258417 6916330946797995450943813)
                ·
                  refine ⟨1296812052524624147051965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6916330946797995450943813 1296812052524624147051965)
                  ·
                    refine ⟨486304519696734055144487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296812052524624147051965 486304519696734055144487)
                    ·
                      rfl

theorem cell22_1420612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1420612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420612 prefixEnd_1420612 := by exact prefixLift 1420612
  have htrace : WordTrace (prefixWord ++ tailWord_1420612) baseStart_1420612 baseEnd_1420612 := by
    simpa [prefixWord, tailWord_1420612, baseEnd_1420612] using wordTrace_append hprefix tailTrace_1420612
  have hstable : (prefixWord ++ tailWord_1420612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420612).length < 2 ^ (prefixWord ++ tailWord_1420612).sum := by decide
  have hdescent : baseEnd_1420612 < baseStart_1420612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420717 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1420717 : Nat := 118140960795 + 1420717 * 2 ^ 59
def prefixEnd_1420717 : Nat := 4983230072969 + 3 ^ 40 * 1420717 * 2
def baseEnd_1420717 : Nat := 486340463342548781269165

theorem tailTrace_1420717 : CollatzResearch.WordTrace tailWord_1420717 prefixEnd_1420717 486340463342548781269165 := by
  unfold tailWord_1420717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51817805993992422991220405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34545203995994948660813603 51817805993992422991220405)
  ·
    refine ⟨4857919311936789655426913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51817805993992422991220405 4857919311936789655426913)
    ·
      refine ⟨3643439483952592241570185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4857919311936789655426913 3643439483952592241570185)
      ·
        refine ⟨2732579612964444181177639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643439483952592241570185 2732579612964444181177639)
        ·
          refine ⟨4098869419446666271766459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732579612964444181177639 4098869419446666271766459)
          ·
            refine ⟨6148304129169999407649689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098869419446666271766459 6148304129169999407649689)
            ·
              refine ⟨4611228096877499555737267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6148304129169999407649689 4611228096877499555737267)
              ·
                refine ⟨6916842145316249333605901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611228096877499555737267 6916842145316249333605901)
                ·
                  refine ⟨2593815804493593500102213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6916842145316249333605901 2593815804493593500102213)
                  ·
                    refine ⟨486340463342548781269165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593815804493593500102213 486340463342548781269165)
                    ·
                      rfl

theorem cell22_1420717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1420717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420717 prefixEnd_1420717 := by exact prefixLift 1420717
  have htrace : WordTrace (prefixWord ++ tailWord_1420717) baseStart_1420717 baseEnd_1420717 := by
    simpa [prefixWord, tailWord_1420717, baseEnd_1420717] using wordTrace_append hprefix tailTrace_1420717
  have hstable : (prefixWord ++ tailWord_1420717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420717).length < 2 ^ (prefixWord ++ tailWord_1420717).sum := by decide
  have hdescent : baseEnd_1420717 < baseStart_1420717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420743 : List Nat := [1, 1, 4, 1, 1, 3, 11]
def baseStart_1420743 : Nat := 118140960795 + 1420743 * 2 ^ 59
def prefixEnd_1420743 : Nat := 4983230072969 + 3 ^ 40 * 1420743 * 2
def baseEnd_1420743 : Nat := 18012939395329384448855

theorem tailTrace_1420743 : CollatzResearch.WordTrace tailWord_1420743 prefixEnd_1420743 18012939395329384448855 := by
  unfold tailWord_1420743
  simp only [CollatzResearch.WordTrace]
  refine ⟨51818754291898229431666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34545836194598819621111255 51818754291898229431666883)
  ·
    refine ⟨77728131437847344147500325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51818754291898229431666883 77728131437847344147500325)
    ·
      refine ⟨14574024644596377027656311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77728131437847344147500325 14574024644596377027656311)
      ·
        refine ⟨21861036966894565541484467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574024644596377027656311 21861036966894565541484467)
        ·
          refine ⟨32791555450341848312226701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861036966894565541484467 32791555450341848312226701)
          ·
            refine ⟨12296833293878193117085013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32791555450341848312226701 12296833293878193117085013)
            ·
              refine ⟨18012939395329384448855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12296833293878193117085013 18012939395329384448855)
              ·
                rfl

theorem cell22_1420743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 11].length) (baseStart_1420743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420743 prefixEnd_1420743 := by exact prefixLift 1420743
  have htrace : WordTrace (prefixWord ++ tailWord_1420743) baseStart_1420743 baseEnd_1420743 := by
    simpa [prefixWord, tailWord_1420743, baseEnd_1420743] using wordTrace_append hprefix tailTrace_1420743
  have hstable : (prefixWord ++ tailWord_1420743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420743).length < 2 ^ (prefixWord ++ tailWord_1420743).sum := by decide
  have hdescent : baseEnd_1420743 < baseStart_1420743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420747 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 2, 3]
def baseStart_1420747 : Nat := 118140960795 + 1420747 * 2 ^ 59
def prefixEnd_1420747 : Nat := 4983230072969 + 3 ^ 40 * 1420747 * 2
def baseEnd_1420747 : Nat := 486350732955638703019073

theorem tailTrace_1420747 : CollatzResearch.WordTrace tailWord_1420747 prefixEnd_1420747 486350732955638703019073 := by
  unfold tailWord_1420747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51818900183883738114812495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34545933455922492076541663 51818900183883738114812495)
  ·
    refine ⟨77728350275825607172218743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51818900183883738114812495 77728350275825607172218743)
    ·
      refine ⟨116592525413738410758328115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77728350275825607172218743 116592525413738410758328115)
      ·
        refine ⟨174888788120607616137492173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116592525413738410758328115 174888788120607616137492173)
        ·
          refine ⟨65583295545227856051559565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174888788120607616137492173 65583295545227856051559565)
          ·
            refine ⟨24593735829460446019334837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65583295545227856051559565 24593735829460446019334837)
            ·
              refine ⟨2305662734011916814312641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24593735829460446019334837 2305662734011916814312641)
              ·
                refine ⟨1729247050508937610734481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305662734011916814312641 1729247050508937610734481)
                ·
                  refine ⟨1296935287881703208050861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729247050508937610734481 1296935287881703208050861)
                  ·
                    refine ⟨486350732955638703019073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296935287881703208050861 486350732955638703019073)
                    ·
                      rfl

theorem cell22_1420747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].length) (baseStart_1420747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420747 prefixEnd_1420747 := by exact prefixLift 1420747
  have htrace : WordTrace (prefixWord ++ tailWord_1420747) baseStart_1420747 baseEnd_1420747 := by
    simpa [prefixWord, tailWord_1420747, baseEnd_1420747] using wordTrace_append hprefix tailTrace_1420747
  have hstable : (prefixWord ++ tailWord_1420747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420747).length < 2 ^ (prefixWord ++ tailWord_1420747).sum := by decide
  have hdescent : baseEnd_1420747 < baseStart_1420747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420805 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 5]
def baseStart_1420805 : Nat := 118140960795 + 1420805 * 2 ^ 59
def prefixEnd_1420805 : Nat := 4983230072969 + 3 ^ 40 * 1420805 * 2
def baseEnd_1420805 : Nat := 162123529180315295022965

theorem tailTrace_1420805 : CollatzResearch.WordTrace tailWord_1420805 prefixEnd_1420805 162123529180315295022965 := by
  unfold tailWord_1420805
  simp only [CollatzResearch.WordTrace]
  refine ⟨51821015617673614020423869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34547343745115742680282579 51821015617673614020423869)
  ·
    refine ⟨19432880856627605257658951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51821015617673614020423869 19432880856627605257658951)
    ·
      refine ⟨29149321284941407886488427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19432880856627605257658951 29149321284941407886488427)
      ·
        refine ⟨43723981927412111829732641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149321284941407886488427 43723981927412111829732641)
        ·
          refine ⟨32792986445559083872299481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43723981927412111829732641 32792986445559083872299481)
          ·
            refine ⟨24594739834169312904224611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32792986445559083872299481 24594739834169312904224611)
            ·
              refine ⟨36892109751253969356336917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24594739834169312904224611 36892109751253969356336917)
              ·
                refine ⟨1729317644590029813578293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36892109751253969356336917 1729317644590029813578293)
                ·
                  refine ⟨162123529180315295022965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729317644590029813578293 162123529180315295022965)
                  ·
                    rfl

theorem cell22_1420805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_1420805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420805 prefixEnd_1420805 := by exact prefixLift 1420805
  have htrace : WordTrace (prefixWord ++ tailWord_1420805) baseStart_1420805 baseEnd_1420805 := by
    simpa [prefixWord, tailWord_1420805, baseEnd_1420805] using wordTrace_append hprefix tailTrace_1420805
  have hstable : (prefixWord ++ tailWord_1420805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420805).length < 2 ^ (prefixWord ++ tailWord_1420805).sum := by decide
  have hdescent : baseEnd_1420805 < baseStart_1420805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420860 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1420860 : Nat := 118140960795 + 1420860 * 2 ^ 59
def prefixEnd_1420860 : Nat := 4983230072969 + 3 ^ 40 * 1420860 * 2
def baseEnd_1420860 : Nat := 486389415164944074943727

theorem tailTrace_1420860 : CollatzResearch.WordTrace tailWord_1420860 prefixEnd_1420860 486389415164944074943727 := by
  unfold tailWord_1420860
  simp only [CollatzResearch.WordTrace]
  refine ⟨25911510816237179206838017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34548681088316238942450689 25911510816237179206838017)
  ·
    refine ⟨19433633112177884405128513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25911510816237179206838017 19433633112177884405128513)
    ·
      refine ⟨14575224834133413303846385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19433633112177884405128513 14575224834133413303846385)
      ·
        refine ⟨10931418625600059977884789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14575224834133413303846385 10931418625600059977884789)
        ·
          refine ⟨1024820496150005622926699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10931418625600059977884789 1024820496150005622926699)
          ·
            refine ⟨1537230744225008434390049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024820496150005622926699 1537230744225008434390049)
            ·
              refine ⟨1152923058168756325792537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537230744225008434390049 1152923058168756325792537)
              ·
                refine ⟨864692293626567244344403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152923058168756325792537 864692293626567244344403)
                ·
                  refine ⟨1297038440439850866516605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864692293626567244344403 1297038440439850866516605)
                  ·
                    refine ⟨486389415164944074943727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297038440439850866516605 486389415164944074943727)
                    ·
                      rfl

theorem cell22_1420860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1420860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420860 prefixEnd_1420860 := by exact prefixLift 1420860
  have htrace : WordTrace (prefixWord ++ tailWord_1420860) baseStart_1420860 baseEnd_1420860 := by
    simpa [prefixWord, tailWord_1420860, baseEnd_1420860] using wordTrace_append hprefix tailTrace_1420860
  have hstable : (prefixWord ++ tailWord_1420860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420860).length < 2 ^ (prefixWord ++ tailWord_1420860).sum := by decide
  have hdescent : baseEnd_1420860 < baseStart_1420860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420880 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_1420880 : Nat := 118140960795 + 1420880 * 2 ^ 59
def prefixEnd_1420880 : Nat := 4983230072969 + 3 ^ 40 * 1420880 * 2
def baseEnd_1420880 : Nat := 486396261573670689443665

theorem tailTrace_1420880 : CollatzResearch.WordTrace tailWord_1420880 prefixEnd_1420880 486396261573670689443665 := by
  unfold tailWord_1420880
  simp only [CollatzResearch.WordTrace]
  refine ⟨25911875546200950914702047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34549167394934601219602729 25911875546200950914702047)
  ·
    refine ⟨38867813319301426372053071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25911875546200950914702047 38867813319301426372053071)
    ·
      refine ⟨58301719978952139558079607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38867813319301426372053071 58301719978952139558079607)
      ·
        refine ⟨87452579968428209337119411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58301719978952139558079607 87452579968428209337119411)
        ·
          refine ⟨131178869952642314005679117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87452579968428209337119411 131178869952642314005679117)
          ·
            refine ⟨49192076232240867752129669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131178869952642314005679117 49192076232240867752129669)
            ·
              refine ⟨9223514293545162703524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49192076232240867752129669 9223514293545162703524313)
              ·
                refine ⟨6917635720158872027643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9223514293545162703524313 6917635720158872027643235)
                ·
                  refine ⟨10376453580238308041464853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917635720158872027643235 10376453580238308041464853)
                  ·
                    refine ⟨486396261573670689443665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10376453580238308041464853 486396261573670689443665)
                    ·
                      rfl

theorem cell22_1420880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_1420880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420880 prefixEnd_1420880 := by exact prefixLift 1420880
  have htrace : WordTrace (prefixWord ++ tailWord_1420880) baseStart_1420880 baseEnd_1420880 := by
    simpa [prefixWord, tailWord_1420880, baseEnd_1420880] using wordTrace_append hprefix tailTrace_1420880
  have hstable : (prefixWord ++ tailWord_1420880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420880).length < 2 ^ (prefixWord ++ tailWord_1420880).sum := by decide
  have hdescent : baseEnd_1420880 < baseStart_1420880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420882 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1420882 : Nat := 118140960795 + 1420882 * 2 ^ 59
def prefixEnd_1420882 : Nat := 4983230072969 + 3 ^ 40 * 1420882 * 2
def baseEnd_1420882 : Nat := 486396946214543350893659

theorem tailTrace_1420882 : CollatzResearch.WordTrace tailWord_1420882 prefixEnd_1420882 486396946214543350893659 := by
  unfold tailWord_1420882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955956009598664042744225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34549216025596437447317933 12955956009598664042744225)
  ·
    refine ⟨9716967007198998032058169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12955956009598664042744225 9716967007198998032058169)
    ·
      refine ⟨7287725255399248524043627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9716967007198998032058169 7287725255399248524043627)
      ·
        refine ⟨10931587883098872786065441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7287725255399248524043627 10931587883098872786065441)
        ·
          refine ⟨8198690912324154589549081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10931587883098872786065441 8198690912324154589549081)
          ·
            refine ⟨6149018184243115942161811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8198690912324154589549081 6149018184243115942161811)
            ·
              refine ⟨9223527276364673913242717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149018184243115942161811 9223527276364673913242717)
              ·
                refine ⟨3458822728636752717466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9223527276364673913242717 3458822728636752717466019)
                ·
                  refine ⟨5188234092955129076199029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458822728636752717466019 5188234092955129076199029)
                  ·
                    refine ⟨486396946214543350893659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5188234092955129076199029 486396946214543350893659)
                    ·
                      rfl

theorem cell22_1420882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1420882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420882 prefixEnd_1420882 := by exact prefixLift 1420882
  have htrace : WordTrace (prefixWord ++ tailWord_1420882) baseStart_1420882 baseEnd_1420882 := by
    simpa [prefixWord, tailWord_1420882, baseEnd_1420882] using wordTrace_append hprefix tailTrace_1420882
  have hstable : (prefixWord ++ tailWord_1420882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420882).length < 2 ^ (prefixWord ++ tailWord_1420882).sum := by decide
  have hdescent : baseEnd_1420882 < baseStart_1420882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420946 : List Nat := [3, 2, 3, 1, 3, 2, 2, 6]
def baseStart_1420946 : Nat := 118140960795 + 1420946 * 2 ^ 59
def prefixEnd_1420946 : Nat := 4983230072969 + 3 ^ 40 * 1420946 * 2
def baseEnd_1420946 : Nat := 54046539413607613032607

theorem tailTrace_1420946 : CollatzResearch.WordTrace tailWord_1420946 prefixEnd_1420946 54046539413607613032607 := by
  unfold tailWord_1420946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956539577540698775326673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34550772206775196734204461 12956539577540698775326673)
  ·
    refine ⟨9717404683155524081495005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12956539577540698775326673 9717404683155524081495005)
    ·
      refine ⟨3644026756183321530560627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9717404683155524081495005 3644026756183321530560627)
      ·
        refine ⟨5466040134274982295840941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644026756183321530560627 5466040134274982295840941)
        ·
          refine ⟨2049765050353118360940353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5466040134274982295840941 2049765050353118360940353)
          ·
            refine ⟨1537323787764838770705265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2049765050353118360940353 1537323787764838770705265)
            ·
              refine ⟨1152992840823629078028949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537323787764838770705265 1152992840823629078028949)
              ·
                refine ⟨54046539413607613032607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1152992840823629078028949 54046539413607613032607)
                ·
                  rfl

theorem cell22_1420946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_1420946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1420946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1420946 prefixEnd_1420946 := by exact prefixLift 1420946
  have htrace : WordTrace (prefixWord ++ tailWord_1420946) baseStart_1420946 baseEnd_1420946 := by
    simpa [prefixWord, tailWord_1420946, baseEnd_1420946] using wordTrace_append hprefix tailTrace_1420946
  have hstable : (prefixWord ++ tailWord_1420946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420946).length < 2 ^ (prefixWord ++ tailWord_1420946).sum := by decide
  have hdescent : baseEnd_1420946 < baseStart_1420946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421017 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_1421017 : Nat := 118140960795 + 1421017 * 2 ^ 59
def prefixEnd_1421017 : Nat := 4983230072969 + 3 ^ 40 * 1421017 * 2
def baseEnd_1421017 : Nat := 486443159473447998768245

theorem tailTrace_1421017 : CollatzResearch.WordTrace tailWord_1421017 prefixEnd_1421017 486443159473447998768245 := by
  unfold tailWord_1421017
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828747892905574227141305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34552498595270382818094203 51828747892905574227141305)
  ·
    refine ⟨38871560919679180670355979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51828747892905574227141305 38871560919679180670355979)
    ·
      refine ⟨58307341379518771005533969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38871560919679180670355979 58307341379518771005533969)
      ·
        refine ⟨43730506034639078254150477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58307341379518771005533969 43730506034639078254150477)
        ·
          refine ⟨16398939762989654345306429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43730506034639078254150477 16398939762989654345306429)
          ·
            refine ⟨6149602411121120379489911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16398939762989654345306429 6149602411121120379489911)
            ·
              refine ⟨9224403616681680569234867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149602411121120379489911 9224403616681680569234867)
              ·
                refine ⟨13836605425022520853852301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9224403616681680569234867 13836605425022520853852301)
                ·
                  refine ⟨5188727034383445320194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13836605425022520853852301 5188727034383445320194613)
                  ·
                    refine ⟨486443159473447998768245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5188727034383445320194613 486443159473447998768245)
                    ·
                      rfl

theorem cell22_1421017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_1421017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421017 prefixEnd_1421017 := by exact prefixLift 1421017
  have htrace : WordTrace (prefixWord ++ tailWord_1421017) baseStart_1421017 baseEnd_1421017 := by
    simpa [prefixWord, tailWord_1421017, baseEnd_1421017] using wordTrace_append hprefix tailTrace_1421017
  have hstable : (prefixWord ++ tailWord_1421017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421017).length < 2 ^ (prefixWord ++ tailWord_1421017).sum := by decide
  have hdescent : baseEnd_1421017 < baseStart_1421017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421034 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1421034 : Nat := 118140960795 + 1421034 * 2 ^ 59
def prefixEnd_1421034 : Nat := 4983230072969 + 3 ^ 40 * 1421034 * 2
def baseEnd_1421034 : Nat := 486448978920865621093193

theorem tailTrace_1421034 : CollatzResearch.WordTrace tailWord_1421034 prefixEnd_1421034 486448978920865621093193 := by
  unfold tailWord_1421034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957341983460996532627539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34552911955895990753673437 12957341983460996532627539)
  ·
    refine ⟨19436012975191494798941309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12957341983460996532627539 19436012975191494798941309)
    ·
      refine ⟨7288504865696810549602991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19436012975191494798941309 7288504865696810549602991)
      ·
        refine ⟨10932757298545215824404487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288504865696810549602991 10932757298545215824404487)
        ·
          refine ⟨16399135947817823736606731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932757298545215824404487 16399135947817823736606731)
          ·
            refine ⟨24598703921726735604910097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16399135947817823736606731 24598703921726735604910097)
            ·
              refine ⟨18449027941295051703682573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24598703921726735604910097 18449027941295051703682573)
              ·
                refine ⟨6918385477985644388880965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18449027941295051703682573 6918385477985644388880965)
                ·
                  refine ⟨1297197277122308322915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6918385477985644388880965 1297197277122308322915181)
                  ·
                    refine ⟨486448978920865621093193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297197277122308322915181 486448978920865621093193)
                    ·
                      rfl

theorem cell22_1421034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1421034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421034 prefixEnd_1421034 := by exact prefixLift 1421034
  have htrace : WordTrace (prefixWord ++ tailWord_1421034) baseStart_1421034 baseEnd_1421034 := by
    simpa [prefixWord, tailWord_1421034, baseEnd_1421034] using wordTrace_append hprefix tailTrace_1421034
  have hstable : (prefixWord ++ tailWord_1421034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421034).length < 2 ^ (prefixWord ++ tailWord_1421034).sum := by decide
  have hdescent : baseEnd_1421034 < baseStart_1421034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421036 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_1421036 : Nat := 118140960795 + 1421036 * 2 ^ 59
def prefixEnd_1421036 : Nat := 4983230072969 + 3 ^ 40 * 1421036 * 2
def baseEnd_1421036 : Nat := 162149887853912760847729

theorem tailTrace_1421036 : CollatzResearch.WordTrace tailWord_1421036 prefixEnd_1421036 162149887853912760847729 := by
  unfold tailWord_1421036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25914720439918370236041481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34552960586557826981388641 25914720439918370236041481)
  ·
    refine ⟨19436040329938777677031111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25914720439918370236041481 19436040329938777677031111)
    ·
      refine ⟨29154060494908166515546667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19436040329938777677031111 29154060494908166515546667)
      ·
        refine ⟨43731090742362249773320001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29154060494908166515546667 43731090742362249773320001)
        ·
          refine ⟨32798318056771687329990001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43731090742362249773320001 32798318056771687329990001)
          ·
            refine ⟨24598738542578765497492501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32798318056771687329990001 24598738542578765497492501)
            ·
              refine ⟨1153065869183379632694961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24598738542578765497492501 1153065869183379632694961)
              ·
                refine ⟨864799401887534724521221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153065869183379632694961 864799401887534724521221)
                ·
                  refine ⟨162149887853912760847729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864799401887534724521221 162149887853912760847729)
                  ·
                    rfl

theorem cell22_1421036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_1421036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421036 prefixEnd_1421036 := by exact prefixLift 1421036
  have htrace : WordTrace (prefixWord ++ tailWord_1421036) baseStart_1421036 baseEnd_1421036 := by
    simpa [prefixWord, tailWord_1421036, baseEnd_1421036] using wordTrace_append hprefix tailTrace_1421036
  have hstable : (prefixWord ++ tailWord_1421036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421036).length < 2 ^ (prefixWord ++ tailWord_1421036).sum := by decide
  have hdescent : baseEnd_1421036 < baseStart_1421036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421047 : List Nat := [1, 1, 3, 1, 1, 1, 7, 7]
def baseStart_1421047 : Nat := 118140960795 + 1421047 * 2 ^ 59
def prefixEnd_1421047 : Nat := 4983230072969 + 3 ^ 40 * 1421047 * 2
def baseEnd_1421047 : Nat := 54050381009615324502017

theorem tailTrace_1421047 : CollatzResearch.WordTrace tailWord_1421047 prefixEnd_1421047 54050381009615324502017 := by
  unfold tailWord_1421047
  simp only [CollatzResearch.WordTrace]
  refine ⟨51829842082796889350733395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34553228055197926233822263 51829842082796889350733395)
  ·
    refine ⟨77744763124195334026100093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51829842082796889350733395 77744763124195334026100093)
    ·
      refine ⟨29154286171573250259787535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77744763124195334026100093 29154286171573250259787535)
      ·
        refine ⟨43731429257359875389681303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29154286171573250259787535 43731429257359875389681303)
        ·
          refine ⟨65597143886039813084521955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43731429257359875389681303 65597143886039813084521955)
          ·
            refine ⟨98395715829059719626782933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65597143886039813084521955 98395715829059719626782933)
            ·
              refine ⟨2306149589743587178752725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98395715829059719626782933 2306149589743587178752725)
              ·
                refine ⟨54050381009615324502017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2306149589743587178752725 54050381009615324502017)
                ·
                  rfl

theorem cell22_1421047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 7].length) (baseStart_1421047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421047 prefixEnd_1421047 := by exact prefixLift 1421047
  have htrace : WordTrace (prefixWord ++ tailWord_1421047) baseStart_1421047 baseEnd_1421047 := by
    simpa [prefixWord, tailWord_1421047, baseEnd_1421047] using wordTrace_append hprefix tailTrace_1421047
  have hstable : (prefixWord ++ tailWord_1421047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421047).length < 2 ^ (prefixWord ++ tailWord_1421047).sum := by decide
  have hdescent : baseEnd_1421047 < baseStart_1421047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421064 : List Nat := [2, 1, 3, 2, 2, 1, 5, 6]
def baseStart_1421064 : Nat := 118140960795 + 1421064 * 2 ^ 59
def prefixEnd_1421064 : Nat := 4983230072969 + 3 ^ 40 * 1421064 * 2
def baseEnd_1421064 : Nat := 54051027614883949204789

theorem tailTrace_1421064 : CollatzResearch.WordTrace tailWord_1421064 prefixEnd_1421064 54051027614883949204789 := by
  unfold tailWord_1421064
  simp only [CollatzResearch.WordTrace]
  refine ⟨25915231061867650627051123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34553641415823534169401497 25915231061867650627051123)
  ·
    refine ⟨38872846592801475940576685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25915231061867650627051123 38872846592801475940576685)
    ·
      refine ⟨14577317472300553477716257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38872846592801475940576685 14577317472300553477716257)
      ·
        refine ⟨10932988104225415108287193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14577317472300553477716257 10932988104225415108287193)
        ·
          refine ⟨8199741078169061331215395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10932988104225415108287193 8199741078169061331215395)
          ·
            refine ⟨12299611617253591996823093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199741078169061331215395 12299611617253591996823093)
            ·
              refine ⟨1153088589117524249702165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12299611617253591996823093 1153088589117524249702165)
              ·
                refine ⟨54051027614883949204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1153088589117524249702165 54051027614883949204789)
                ·
                  rfl

theorem cell22_1421064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_1421064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421064 prefixEnd_1421064 := by exact prefixLift 1421064
  have htrace : WordTrace (prefixWord ++ tailWord_1421064) baseStart_1421064 baseEnd_1421064 := by
    simpa [prefixWord, tailWord_1421064, baseEnd_1421064] using wordTrace_append hprefix tailTrace_1421064
  have hstable : (prefixWord ++ tailWord_1421064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421064).length < 2 ^ (prefixWord ++ tailWord_1421064).sum := by decide
  have hdescent : baseEnd_1421064 < baseStart_1421064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421066 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_1421066 : Nat := 118140960795 + 1421066 * 2 ^ 59
def prefixEnd_1421066 : Nat := 4983230072969 + 3 ^ 40 * 1421066 * 2
def baseEnd_1421066 : Nat := 486459933174828204293095

theorem tailTrace_1421066 : CollatzResearch.WordTrace tailWord_1421066 prefixEnd_1421066 486459933174828204293095 := by
  unfold tailWord_1421066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957633767432013898918763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34553690046485370397116701 12957633767432013898918763)
  ·
    refine ⟨19436450651148020848378145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12957633767432013898918763 19436450651148020848378145)
    ·
      refine ⟨14577337988361015636283609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19436450651148020848378145 14577337988361015636283609)
      ·
        refine ⟨10933003491270761727212707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14577337988361015636283609 10933003491270761727212707)
        ·
          refine ⟨16399505236906142590819061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933003491270761727212707 16399505236906142590819061)
          ·
            refine ⟨1537453615959950867889287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16399505236906142590819061 1537453615959950867889287)
            ·
              refine ⟨2306180423939926301833931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537453615959950867889287 2306180423939926301833931)
              ·
                refine ⟨3459270635909889452750897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306180423939926301833931 3459270635909889452750897)
                ·
                  refine ⟨2594452976932417089563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459270635909889452750897 2594452976932417089563173)
                  ·
                    refine ⟨486459933174828204293095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594452976932417089563173 486459933174828204293095)
                    ·
                      rfl

theorem cell22_1421066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_1421066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421066 prefixEnd_1421066 := by exact prefixLift 1421066
  have htrace : WordTrace (prefixWord ++ tailWord_1421066) baseStart_1421066 baseEnd_1421066 := by
    simpa [prefixWord, tailWord_1421066, baseEnd_1421066] using wordTrace_append hprefix tailTrace_1421066
  have hstable : (prefixWord ++ tailWord_1421066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421066).length < 2 ^ (prefixWord ++ tailWord_1421066).sum := by decide
  have hdescent : baseEnd_1421066 < baseStart_1421066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421096 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1421096 : Nat := 118140960795 + 1421096 * 2 ^ 59
def prefixEnd_1421096 : Nat := 4983230072969 + 3 ^ 40 * 1421096 * 2
def baseEnd_1421096 : Nat := 486470202787918126043003

theorem tailTrace_1421096 : CollatzResearch.WordTrace tailWord_1421096 prefixEnd_1421096 486470202787918126043003 := by
  unfold tailWord_1421096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25915814629809685359633571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34554419506412913812844761 25915814629809685359633571)
  ·
    refine ⟨38873721944714528039450357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25915814629809685359633571 38873721944714528039450357)
    ·
      refine ⟨3644411432316987003698471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38873721944714528039450357 3644411432316987003698471)
      ·
        refine ⟨5466617148475480505547707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644411432316987003698471 5466617148475480505547707)
        ·
          refine ⟨8199925722713220758321561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466617148475480505547707 8199925722713220758321561)
          ·
            refine ⟨6149944292034915568741171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8199925722713220758321561 6149944292034915568741171)
            ·
              refine ⟨9224916438052373353111757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149944292034915568741171 9224916438052373353111757)
              ·
                refine ⟨3459343664269640007416909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9224916438052373353111757 3459343664269640007416909)
                ·
                  refine ⟨1297253874101115002781341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3459343664269640007416909 1297253874101115002781341)
                  ·
                    refine ⟨486470202787918126043003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297253874101115002781341 486470202787918126043003)
                    ·
                      rfl

theorem cell22_1421096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1421096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421096 prefixEnd_1421096 := by exact prefixLift 1421096
  have htrace : WordTrace (prefixWord ++ tailWord_1421096) baseStart_1421096 baseEnd_1421096 := by
    simpa [prefixWord, tailWord_1421096, baseEnd_1421096] using wordTrace_append hprefix tailTrace_1421096
  have hstable : (prefixWord ++ tailWord_1421096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421096).length < 2 ^ (prefixWord ++ tailWord_1421096).sum := by decide
  have hdescent : baseEnd_1421096 < baseStart_1421096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421169 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1421169 : Nat := 118140960795 + 1421169 * 2 ^ 59
def prefixEnd_1421169 : Nat := 4983230072969 + 3 ^ 40 * 1421169 * 2
def baseEnd_1421169 : Nat := 486495192179770268967779

theorem tailTrace_1421169 : CollatzResearch.WordTrace tailWord_1421169 prefixEnd_1421169 486495192179770268967779 := by
  unfold tailWord_1421169
  simp only [CollatzResearch.WordTrace]
  refine ⟨51834291788354904186674561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34556194525569936124449707 51834291788354904186674561)
  ·
    refine ⟨38875718841266178140005921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51834291788354904186674561 38875718841266178140005921)
    ·
      refine ⟨29156789130949633605004441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38875718841266178140005921 29156789130949633605004441)
      ·
        refine ⟨21867591848212225203753331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29156789130949633605004441 21867591848212225203753331)
        ·
          refine ⟨32801387772318337805629997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21867591848212225203753331 32801387772318337805629997)
          ·
            refine ⟨12300520414619376677111249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32801387772318337805629997 12300520414619376677111249)
            ·
              refine ⟨9225390310964532507833437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300520414619376677111249 9225390310964532507833437)
              ·
                refine ⟨3459521366611699690437539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9225390310964532507833437 3459521366611699690437539)
                ·
                  refine ⟨5189282049917549535656309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459521366611699690437539 5189282049917549535656309)
                  ·
                    refine ⟨486495192179770268967779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189282049917549535656309 486495192179770268967779)
                    ·
                      rfl

theorem cell22_1421169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1421169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421169 prefixEnd_1421169 := by exact prefixLift 1421169
  have htrace : WordTrace (prefixWord ++ tailWord_1421169) baseStart_1421169 baseEnd_1421169 := by
    simpa [prefixWord, tailWord_1421169, baseEnd_1421169] using wordTrace_append hprefix tailTrace_1421169
  have hstable : (prefixWord ++ tailWord_1421169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421169).length < 2 ^ (prefixWord ++ tailWord_1421169).sum := by decide
  have hdescent : baseEnd_1421169 < baseStart_1421169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421231 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 3, 3]
def baseStart_1421231 : Nat := 118140960795 + 1421231 * 2 ^ 59
def prefixEnd_1421231 : Nat := 4983230072969 + 3 ^ 40 * 1421231 * 2
def baseEnd_1421231 : Nat := 486516416046822773917589

theorem tailTrace_1421231 : CollatzResearch.WordTrace tailWord_1421231 prefixEnd_1421231 486516416046822773917589 := by
  unfold tailWord_1421231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51836553114130288775431547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34557702076086859183621031 51836553114130288775431547)
  ·
    refine ⟨77754829671195433163147321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51836553114130288775431547 77754829671195433163147321)
    ·
      refine ⟨58316122253396574872360491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77754829671195433163147321 58316122253396574872360491)
      ·
        refine ⟨87474183380094862308540737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58316122253396574872360491 87474183380094862308540737)
        ·
          refine ⟨65605637535071146731405553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87474183380094862308540737 65605637535071146731405553)
          ·
            refine ⟨49204228151303360048554165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65605637535071146731405553 49204228151303360048554165)
            ·
              refine ⟨4612896389184690004551953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49204228151303360048554165 4612896389184690004551953)
              ·
                refine ⟨3459672291888517503413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612896389184690004551953 3459672291888517503413965)
                ·
                  refine ⟨1297377109458194063780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3459672291888517503413965 1297377109458194063780237)
                  ·
                    refine ⟨486516416046822773917589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297377109458194063780237 486516416046822773917589)
                    ·
                      rfl

theorem cell22_1421231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_1421231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421231 prefixEnd_1421231 := by exact prefixLift 1421231
  have htrace : WordTrace (prefixWord ++ tailWord_1421231) baseStart_1421231 baseEnd_1421231 := by
    simpa [prefixWord, tailWord_1421231, baseEnd_1421231] using wordTrace_append hprefix tailTrace_1421231
  have hstable : (prefixWord ++ tailWord_1421231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421231).length < 2 ^ (prefixWord ++ tailWord_1421231).sum := by decide
  have hdescent : baseEnd_1421231 < baseStart_1421231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421259 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_1421259 : Nat := 118140960795 + 1421259 * 2 ^ 59
def prefixEnd_1421259 : Nat := 4983230072969 + 3 ^ 40 * 1421259 * 2
def baseEnd_1421259 : Nat := 486526001019040034217503

theorem tailTrace_1421259 : CollatzResearch.WordTrace tailWord_1421259 prefixEnd_1421259 486526001019040034217503 := by
  unfold tailWord_1421259
  simp only [CollatzResearch.WordTrace]
  refine ⟨51837574358028849557450831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34558382905352566371633887 51837574358028849557450831)
  ·
    refine ⟨77756361537043274336176247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51837574358028849557450831 77756361537043274336176247)
    ·
      refine ⟨116634542305564911504264371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77756361537043274336176247 116634542305564911504264371)
      ·
        refine ⟨174951813458347367256396557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116634542305564911504264371 174951813458347367256396557)
        ·
          refine ⟨65606930046880262721148709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174951813458347367256396557 65606930046880262721148709)
          ·
            refine ⟨12301299383790049260215383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65606930046880262721148709 12301299383790049260215383)
            ·
              refine ⟨18451949075685073890323075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301299383790049260215383 18451949075685073890323075)
              ·
                refine ⟨27677923613527610835484613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18451949075685073890323075 27677923613527610835484613)
                ·
                  refine ⟨5189610677536427031653365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27677923613527610835484613 5189610677536427031653365)
                  ·
                    refine ⟨486526001019040034217503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189610677536427031653365 486526001019040034217503)
                    ·
                      rfl

theorem cell22_1421259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_1421259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421259 prefixEnd_1421259 := by exact prefixLift 1421259
  have htrace : WordTrace (prefixWord ++ tailWord_1421259) baseStart_1421259 baseEnd_1421259 := by
    simpa [prefixWord, tailWord_1421259, baseEnd_1421259] using wordTrace_append hprefix tailTrace_1421259
  have hstable : (prefixWord ++ tailWord_1421259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421259).length < 2 ^ (prefixWord ++ tailWord_1421259).sum := by decide
  have hdescent : baseEnd_1421259 < baseStart_1421259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421336 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1421336 : Nat := 118140960795 + 1421336 * 2 ^ 59
def prefixEnd_1421336 : Nat := 4983230072969 + 3 ^ 40 * 1421336 * 2
def baseEnd_1421336 : Nat := 486552359692637500042267

theorem tailTrace_1421336 : CollatzResearch.WordTrace tailWord_1421336 prefixEnd_1421336 486552359692637500042267 := by
  unfold tailWord_1421336
  simp only [CollatzResearch.WordTrace]
  refine ⟨25920191389374945854001931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34560255185833261138669241 25920191389374945854001931)
  ·
    refine ⟨38880287084062418781002897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25920191389374945854001931 38880287084062418781002897)
    ·
      refine ⟨29160215313046814085752173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38880287084062418781002897 29160215313046814085752173)
      ·
        refine ⟨10935080742392555282157065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29160215313046814085752173 10935080742392555282157065)
        ·
          refine ⟨8201310556794416461617799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935080742392555282157065 8201310556794416461617799)
          ·
            refine ⟨12301965835191624692426699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201310556794416461617799 12301965835191624692426699)
            ·
              refine ⟨18452948752787437038640049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301965835191624692426699 18452948752787437038640049)
              ·
                refine ⟨13839711564590577778980037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18452948752787437038640049 13839711564590577778980037)
                ·
                  refine ⟨2594945918360733333558757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13839711564590577778980037 2594945918360733333558757)
                  ·
                    refine ⟨486552359692637500042267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594945918360733333558757 486552359692637500042267)
                    ·
                      rfl

theorem cell22_1421336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1421336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421336 prefixEnd_1421336 := by exact prefixLift 1421336
  have htrace : WordTrace (prefixWord ++ tailWord_1421336) baseStart_1421336 baseEnd_1421336 := by
    simpa [prefixWord, tailWord_1421336, baseEnd_1421336] using wordTrace_append hprefix tailTrace_1421336
  have hstable : (prefixWord ++ tailWord_1421336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421336).length < 2 ^ (prefixWord ++ tailWord_1421336).sum := by decide
  have hdescent : baseEnd_1421336 < baseStart_1421336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421374 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1421374 : Nat := 118140960795 + 1421374 * 2 ^ 59
def prefixEnd_1421374 : Nat := 4983230072969 + 3 ^ 40 * 1421374 * 2
def baseEnd_1421374 : Nat := 162188455956406022530717

theorem tailTrace_1421374 : CollatzResearch.WordTrace tailWord_1421374 prefixEnd_1421374 162188455956406022530717 := by
  unfold tailWord_1421374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480221094076528024735897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34561179168408149465258117 6480221094076528024735897)
  ·
    refine ⟨4860165820557396018551923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6480221094076528024735897 4860165820557396018551923)
    ·
      refine ⟨7290248730836094027827885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860165820557396018551923 7290248730836094027827885)
      ·
        refine ⟨2733843274063535260435457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7290248730836094027827885 2733843274063535260435457)
        ·
          refine ⟨2050382455547651445326593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733843274063535260435457 2050382455547651445326593)
          ·
            refine ⟨1537786841660738583994945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050382455547651445326593 1537786841660738583994945)
            ·
              refine ⟨1153340131245553937996209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537786841660738583994945 1153340131245553937996209)
              ·
                refine ⟨865005098434165453497157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153340131245553937996209 865005098434165453497157)
                ·
                  refine ⟨162188455956406022530717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865005098434165453497157 162188455956406022530717)
                  ·
                    rfl

theorem cell22_1421374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1421374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421374 prefixEnd_1421374 := by exact prefixLift 1421374
  have htrace : WordTrace (prefixWord ++ tailWord_1421374) baseStart_1421374 baseEnd_1421374 := by
    simpa [prefixWord, tailWord_1421374, baseEnd_1421374] using wordTrace_append hprefix tailTrace_1421374
  have hstable : (prefixWord ++ tailWord_1421374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421374).length < 2 ^ (prefixWord ++ tailWord_1421374).sum := by decide
  have hdescent : baseEnd_1421374 < baseStart_1421374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421383 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1421383 : Nat := 118140960795 + 1421383 * 2 ^ 59
def prefixEnd_1421383 : Nat := 4983230072969 + 3 ^ 40 * 1421383 * 2
def baseEnd_1421383 : Nat := 486568448753145044117123

theorem tailTrace_1421383 : CollatzResearch.WordTrace tailWord_1421383 prefixEnd_1421383 486568448753145044117123 := by
  unfold tailWord_1421383
  simp only [CollatzResearch.WordTrace]
  refine ⟨51842097009579618734964803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34561398006386412489976535 51842097009579618734964803)
  ·
    refine ⟨77763145514369428102447205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51842097009579618734964803 77763145514369428102447205)
    ·
      refine ⟨14580589783944267769208851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77763145514369428102447205 14580589783944267769208851)
      ·
        refine ⟨21870884675916401653813277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14580589783944267769208851 21870884675916401653813277)
        ·
          refine ⟨8201581753468650620179979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21870884675916401653813277 8201581753468650620179979)
          ·
            refine ⟨12302372630202975930269969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201581753468650620179979 12302372630202975930269969)
            ·
              refine ⟨9226779472652231947702477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302372630202975930269969 9226779472652231947702477)
              ·
                refine ⟨3460042302244586980388429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9226779472652231947702477 3460042302244586980388429)
                ·
                  refine ⟨1297515863341720117645661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3460042302244586980388429 1297515863341720117645661)
                  ·
                    refine ⟨486568448753145044117123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297515863341720117645661 486568448753145044117123)
                    ·
                      rfl

theorem cell22_1421383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1421383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421383 prefixEnd_1421383 := by exact prefixLift 1421383
  have htrace : WordTrace (prefixWord ++ tailWord_1421383) baseStart_1421383 baseEnd_1421383 := by
    simpa [prefixWord, tailWord_1421383, baseEnd_1421383] using wordTrace_append hprefix tailTrace_1421383
  have hstable : (prefixWord ++ tailWord_1421383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421383).length < 2 ^ (prefixWord ++ tailWord_1421383).sum := by decide
  have hdescent : baseEnd_1421383 < baseStart_1421383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421396 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1421396 : Nat := 118140960795 + 1421396 * 2 ^ 59
def prefixEnd_1421396 : Nat := 4983230072969 + 3 ^ 40 * 1421396 * 2
def baseEnd_1421396 : Nat := 162190966306272447847361

theorem tailTrace_1421396 : CollatzResearch.WordTrace tailWord_1421396 prefixEnd_1421396 162190966306272447847361 := by
  unfold tailWord_1421396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921285579266260977594021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34561714105688347970125361 25921285579266260977594021)
  ·
    refine ⟨4860241046112423933298879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25921285579266260977594021 4860241046112423933298879)
    ·
      refine ⟨7290361569168635899948319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860241046112423933298879 7290361569168635899948319)
      ·
        refine ⟨10935542353752953849922479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290361569168635899948319 10935542353752953849922479)
        ·
          refine ⟨16403313530629430774883719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10935542353752953849922479 16403313530629430774883719)
          ·
            refine ⟨24604970295944146162325579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16403313530629430774883719 24604970295944146162325579)
            ·
              refine ⟨36907455443916219243488369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24604970295944146162325579 36907455443916219243488369)
              ·
                refine ⟨27680591582937164432616277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36907455443916219243488369 27680591582937164432616277)
                ·
                  refine ⟨162190966306272447847361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27680591582937164432616277 162190966306272447847361)
                  ·
                    rfl

theorem cell22_1421396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1421396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421396 prefixEnd_1421396 := by exact prefixLift 1421396
  have htrace : WordTrace (prefixWord ++ tailWord_1421396) baseStart_1421396 baseEnd_1421396 := by
    simpa [prefixWord, tailWord_1421396, baseEnd_1421396] using wordTrace_append hprefix tailTrace_1421396
  have hstable : (prefixWord ++ tailWord_1421396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421396).length < 2 ^ (prefixWord ++ tailWord_1421396).sum := by decide
  have hdescent : baseEnd_1421396 < baseStart_1421396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421430 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1421430 : Nat := 118140960795 + 1421430 * 2 ^ 59
def prefixEnd_1421430 : Nat := 4983230072969 + 3 ^ 40 * 1421430 * 2
def baseEnd_1421430 : Nat := 162194845937884196063993

theorem tailTrace_1421430 : CollatzResearch.WordTrace tailWord_1421430 prefixEnd_1421430 162194845937884196063993 := by
  unfold tailWord_1421430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240238202525584110120359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34562540826939563841283829 3240238202525584110120359)
  ·
    refine ⟨4860357303788376165180539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3240238202525584110120359 4860357303788376165180539)
    ·
      refine ⟨7290535955682564247770809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860357303788376165180539 7290535955682564247770809)
      ·
        refine ⟨5467901966761923185828107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7290535955682564247770809 5467901966761923185828107)
        ·
          refine ⟨8201852950142884778742161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467901966761923185828107 8201852950142884778742161)
          ·
            refine ⟨6151389712607163584056621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8201852950142884778742161 6151389712607163584056621)
            ·
              refine ⟨2306771142227686344021233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6151389712607163584056621 2306771142227686344021233)
              ·
                refine ⟨1730078356670764758015925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306771142227686344021233 1730078356670764758015925)
                ·
                  refine ⟨162194845937884196063993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1730078356670764758015925 162194845937884196063993)
                  ·
                    rfl

theorem cell22_1421430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1421430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421430 prefixEnd_1421430 := by exact prefixLift 1421430
  have htrace : WordTrace (prefixWord ++ tailWord_1421430) baseStart_1421430 baseEnd_1421430 := by
    simpa [prefixWord, tailWord_1421430, baseEnd_1421430] using wordTrace_append hprefix tailTrace_1421430
  have hstable : (prefixWord ++ tailWord_1421430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421430).length < 2 ^ (prefixWord ++ tailWord_1421430).sum := by decide
  have hdescent : baseEnd_1421430 < baseStart_1421430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421458 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1421458 : Nat := 118140960795 + 1421458 * 2 ^ 59
def prefixEnd_1421458 : Nat := 4983230072969 + 3 ^ 40 * 1421458 * 2
def baseEnd_1421458 : Nat := 162198040928623282830631

theorem tailTrace_1421458 : CollatzResearch.WordTrace tailWord_1421458 prefixEnd_1421458 162198040928623282830631 := by
  unfold tailWord_1421458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12961208121076976635986257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34563221656205271029296685 12961208121076976635986257)
  ·
    refine ⟨9720906090807732476989693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12961208121076976635986257 9720906090807732476989693)
    ·
      refine ⟨3645339784052899678871135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9720906090807732476989693 3645339784052899678871135)
      ·
        refine ⟨5468009676079349518306703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645339784052899678871135 5468009676079349518306703)
        ·
          refine ⟨8202014514119024277460055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468009676079349518306703 8202014514119024277460055)
          ·
            refine ⟨12303021771178536416190083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202014514119024277460055 12303021771178536416190083)
            ·
              refine ⟨18454532656767804624285125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12303021771178536416190083 18454532656767804624285125)
              ·
                refine ⟨3460224873143963367053461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18454532656767804624285125 3460224873143963367053461)
                ·
                  refine ⟨162198040928623282830631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3460224873143963367053461 162198040928623282830631)
                  ·
                    rfl

theorem cell22_1421458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1421458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421458 prefixEnd_1421458 := by exact prefixLift 1421458
  have htrace : WordTrace (prefixWord ++ tailWord_1421458) baseStart_1421458 baseEnd_1421458 := by
    simpa [prefixWord, tailWord_1421458, baseEnd_1421458] using wordTrace_append hprefix tailTrace_1421458
  have hstable : (prefixWord ++ tailWord_1421458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421458).length < 2 ^ (prefixWord ++ tailWord_1421458).sum := by decide
  have hdescent : baseEnd_1421458 < baseStart_1421458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421490 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1421490 : Nat := 118140960795 + 1421490 * 2 ^ 59
def prefixEnd_1421490 : Nat := 4983230072969 + 3 ^ 40 * 1421490 * 2
def baseEnd_1421490 : Nat := 486605077039832431691795

theorem tailTrace_1421490 : CollatzResearch.WordTrace tailWord_1421490 prefixEnd_1421490 486605077039832431691795 := by
  unfold tailWord_1421490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12961499905047994002277481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34563999746794650672739949 12961499905047994002277481)
  ·
    refine ⟨9721124928785995501708111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12961499905047994002277481 9721124928785995501708111)
    ·
      refine ⟨14581687393178993252562167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721124928785995501708111 14581687393178993252562167)
      ·
        refine ⟨21872531089768489878843251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581687393178993252562167 21872531089768489878843251)
        ·
          refine ⟨32808796634652734818264877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872531089768489878843251 32808796634652734818264877)
          ·
            refine ⟨12303298737994775556849329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32808796634652734818264877 12303298737994775556849329)
            ·
              refine ⟨9227474053496081667636997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12303298737994775556849329 9227474053496081667636997)
              ·
                refine ⟨1730151385030515312681937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9227474053496081667636997 1730151385030515312681937)
                ·
                  refine ⟨1297613538772886484511453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730151385030515312681937 1297613538772886484511453)
                  ·
                    refine ⟨486605077039832431691795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297613538772886484511453 486605077039832431691795)
                    ·
                      rfl

theorem cell22_1421490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1421490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421490 prefixEnd_1421490 := by exact prefixLift 1421490
  have htrace : WordTrace (prefixWord ++ tailWord_1421490) baseStart_1421490 baseEnd_1421490 := by
    simpa [prefixWord, tailWord_1421490, baseEnd_1421490] using wordTrace_append hprefix tailTrace_1421490
  have hstable : (prefixWord ++ tailWord_1421490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421490).length < 2 ^ (prefixWord ++ tailWord_1421490).sum := by decide
  have hdescent : baseEnd_1421490 < baseStart_1421490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421676 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1421676 : Nat := 118140960795 + 1421676 * 2 ^ 59
def prefixEnd_1421676 : Nat := 4983230072969 + 3 ^ 40 * 1421676 * 2
def baseEnd_1421676 : Nat := 486668748640989946541225

theorem tailTrace_1421676 : CollatzResearch.WordTrace tailWord_1421676 prefixEnd_1421676 486668748640989946541225 := by
  unfold tailWord_1421676
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926391798759064887690441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34568522398345419850253921 25926391798759064887690441)
  ·
    refine ⟨19444793849069298665767831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25926391798759064887690441 19444793849069298665767831)
    ·
      refine ⟨29167190773603947998651747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19444793849069298665767831 29167190773603947998651747)
      ·
        refine ⟨43750786160405921997977621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29167190773603947998651747 43750786160405921997977621)
        ·
          refine ⟨2050818101269027593655201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43750786160405921997977621 2050818101269027593655201)
          ·
            refine ⟨1538113575951770695241401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050818101269027593655201 1538113575951770695241401)
            ·
              refine ⟨1153585181963828021431051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538113575951770695241401 1153585181963828021431051)
              ·
                refine ⟨1730377772945742032146577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153585181963828021431051 1730377772945742032146577)
                ·
                  refine ⟨1297783329709306524109933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730377772945742032146577 1297783329709306524109933)
                  ·
                    refine ⟨486668748640989946541225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297783329709306524109933 486668748640989946541225)
                    ·
                      rfl

theorem cell22_1421676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1421676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421676 prefixEnd_1421676 := by exact prefixLift 1421676
  have htrace : WordTrace (prefixWord ++ tailWord_1421676) baseStart_1421676 baseEnd_1421676 := by
    simpa [prefixWord, tailWord_1421676, baseEnd_1421676] using wordTrace_append hprefix tailTrace_1421676
  have hstable : (prefixWord ++ tailWord_1421676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421676).length < 2 ^ (prefixWord ++ tailWord_1421676).sum := by decide
  have hdescent : baseEnd_1421676 < baseStart_1421676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421704 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_1421704 : Nat := 118140960795 + 1421704 * 2 ^ 59
def prefixEnd_1421704 : Nat := 4983230072969 + 3 ^ 40 * 1421704 * 2
def baseEnd_1421704 : Nat := 486678333613207206841139

theorem tailTrace_1421704 : CollatzResearch.WordTrace tailWord_1421704 prefixEnd_1421704 486678333613207206841139 := by
  unfold tailWord_1421704
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926902420708345278700083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34569203227611127038266777 25926902420708345278700083)
  ·
    refine ⟨38890353631062517918050125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25926902420708345278700083 38890353631062517918050125)
    ·
      refine ⟨14583882611648444219268797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38890353631062517918050125 14583882611648444219268797)
      ·
        refine ⟨5468955979368166582225799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14583882611648444219268797 5468955979368166582225799)
        ·
          refine ⟨8203433969052249873338699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468955979368166582225799 8203433969052249873338699)
          ·
            refine ⟨12305150953578374810008049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203433969052249873338699 12305150953578374810008049)
            ·
              refine ⟨9228863215183781107506037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12305150953578374810008049 9228863215183781107506037)
              ·
                refine ⟨865205926423479478828691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9228863215183781107506037 865205926423479478828691)
                ·
                  refine ⟨1297808889635219218243037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865205926423479478828691 1297808889635219218243037)
                  ·
                    refine ⟨486678333613207206841139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297808889635219218243037 486678333613207206841139)
                    ·
                      rfl

theorem cell22_1421704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_1421704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421704 prefixEnd_1421704 := by exact prefixLift 1421704
  have htrace : WordTrace (prefixWord ++ tailWord_1421704) baseStart_1421704 baseEnd_1421704 := by
    simpa [prefixWord, tailWord_1421704, baseEnd_1421704] using wordTrace_append hprefix tailTrace_1421704
  have hstable : (prefixWord ++ tailWord_1421704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421704).length < 2 ^ (prefixWord ++ tailWord_1421704).sum := by decide
  have hdescent : baseEnd_1421704 < baseStart_1421704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421738 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1421738 : Nat := 118140960795 + 1421738 * 2 ^ 59
def prefixEnd_1421738 : Nat := 4983230072969 + 3 ^ 40 * 1421738 * 2
def baseEnd_1421738 : Nat := 486689972508042451491035

theorem tailTrace_1421738 : CollatzResearch.WordTrace tailWord_1421738 prefixEnd_1421738 486689972508042451491035 := by
  unfold tailWord_1421738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963761230823378591034467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34570029948862342909425245 12963761230823378591034467)
  ·
    refine ⟨19445641846235067886551701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12963761230823378591034467 19445641846235067886551701)
    ·
      refine ⟨911514461542268807182111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19445641846235067886551701 911514461542268807182111)
      ·
        refine ⟨1367271692313403210773167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911514461542268807182111 1367271692313403210773167)
        ·
          refine ⟨2050907538470104816159751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367271692313403210773167 2050907538470104816159751)
          ·
            refine ⟨3076361307705157224239627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050907538470104816159751 3076361307705157224239627)
            ·
              refine ⟨4614541961557735836359441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076361307705157224239627 4614541961557735836359441)
              ·
                refine ⟨3460906471168301877269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614541961557735836359441 3460906471168301877269581)
                ·
                  refine ⟨1297839926688113203976093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3460906471168301877269581 1297839926688113203976093)
                  ·
                    refine ⟨486689972508042451491035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297839926688113203976093 486689972508042451491035)
                    ·
                      rfl

theorem cell22_1421738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1421738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421738 prefixEnd_1421738 := by exact prefixLift 1421738
  have htrace : WordTrace (prefixWord ++ tailWord_1421738) baseStart_1421738 baseEnd_1421738 := by
    simpa [prefixWord, tailWord_1421738, baseEnd_1421738] using wordTrace_append hprefix tailTrace_1421738
  have hstable : (prefixWord ++ tailWord_1421738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421738).length < 2 ^ (prefixWord ++ tailWord_1421738).sum := by decide
  have hdescent : baseEnd_1421738 < baseStart_1421738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421745 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 8]
def baseStart_1421745 : Nat := 118140960795 + 1421745 * 2 ^ 59
def prefixEnd_1421745 : Nat := 4983230072969 + 3 ^ 40 * 1421745 * 2
def baseEnd_1421745 : Nat := 162230789583698922188671

theorem tailTrace_1421745 : CollatzResearch.WordTrace tailWord_1421745 prefixEnd_1421745 162230789583698922188671 := by
  unfold tailWord_1421745
  simp only [CollatzResearch.WordTrace]
  refine ⟨51855300234268154559642689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34570200156178769706428459 51855300234268154559642689)
  ·
    refine ⟨38891475175701115919732017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51855300234268154559642689 38891475175701115919732017)
    ·
      refine ⟨29168606381775836939799013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38891475175701115919732017 29168606381775836939799013)
      ·
        refine ⟨5469113696582969426212315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29168606381775836939799013 5469113696582969426212315)
        ·
          refine ⟨8203670544874454139318473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5469113696582969426212315 8203670544874454139318473)
          ·
            refine ⟨6152752908655840604488855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8203670544874454139318473 6152752908655840604488855)
            ·
              refine ⟨9229129362983760906733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152752908655840604488855 9229129362983760906733283)
              ·
                refine ⟨13843694044475641360099925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9229129362983760906733283 13843694044475641360099925)
                ·
                  refine ⟨162230789583698922188671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13843694044475641360099925 162230789583698922188671)
                  ·
                    rfl

theorem cell22_1421745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_1421745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421745 prefixEnd_1421745 := by exact prefixLift 1421745
  have htrace : WordTrace (prefixWord ++ tailWord_1421745) baseStart_1421745 baseEnd_1421745 := by
    simpa [prefixWord, tailWord_1421745, baseEnd_1421745] using wordTrace_append hprefix tailTrace_1421745
  have hstable : (prefixWord ++ tailWord_1421745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421745).length < 2 ^ (prefixWord ++ tailWord_1421745).sum := by decide
  have hdescent : baseEnd_1421745 < baseStart_1421745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421775 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_1421775 : Nat := 118140960795 + 1421775 * 2 ^ 59
def prefixEnd_1421775 : Nat := 4983230072969 + 3 ^ 40 * 1421775 * 2
def baseEnd_1421775 : Nat := 486702638364186688315921

theorem tailTrace_1421775 : CollatzResearch.WordTrace tailWord_1421775 prefixEnd_1421775 486702638364186688315921 := by
  unfold tailWord_1421775
  simp only [CollatzResearch.WordTrace]
  refine ⟨51856394424159469683234779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34570929616106313122156519 51856394424159469683234779)
  ·
    refine ⟨77784591636239204524852169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51856394424159469683234779 77784591636239204524852169)
    ·
      refine ⟨58338443727179403393639127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77784591636239204524852169 58338443727179403393639127)
      ·
        refine ⟨87507665590769105090458691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58338443727179403393639127 87507665590769105090458691)
        ·
          refine ⟨131261498386153657635688037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87507665590769105090458691 131261498386153657635688037)
          ·
            refine ⟨24611530947403810806691507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131261498386153657635688037 24611530947403810806691507)
            ·
              refine ⟨36917296421105716210037261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24611530947403810806691507 36917296421105716210037261)
              ·
                refine ⟨13843986157914643578763973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36917296421105716210037261 13843986157914643578763973)
                ·
                  refine ⟨2595747404608995671018245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13843986157914643578763973 2595747404608995671018245)
                  ·
                    refine ⟨486702638364186688315921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595747404608995671018245 486702638364186688315921)
                    ·
                      rfl

theorem cell22_1421775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_1421775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421775 prefixEnd_1421775 := by exact prefixLift 1421775
  have htrace : WordTrace (prefixWord ++ tailWord_1421775) baseStart_1421775 baseEnd_1421775 := by
    simpa [prefixWord, tailWord_1421775, baseEnd_1421775] using wordTrace_append hprefix tailTrace_1421775
  have hstable : (prefixWord ++ tailWord_1421775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421775).length < 2 ^ (prefixWord ++ tailWord_1421775).sum := by decide
  have hdescent : baseEnd_1421775 < baseStart_1421775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421813 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 4]
def baseStart_1421813 : Nat := 118140960795 + 1421813 * 2 ^ 59
def prefixEnd_1421813 : Nat := 4983230072969 + 3 ^ 40 * 1421813 * 2
def baseEnd_1421813 : Nat := 162238548846922418621935

theorem tailTrace_1421813 : CollatzResearch.WordTrace tailWord_1421813 prefixEnd_1421813 162238548846922418621935 := by
  unfold tailWord_1421813
  simp only [CollatzResearch.WordTrace]
  refine ⟨51857780398021802173118093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34571853598681201448745395 51857780398021802173118093)
  ·
    refine ⟨19446667649258175814919285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51857780398021802173118093 19446667649258175814919285)
    ·
      refine ⟨1823125092117953982648683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19446667649258175814919285 1823125092117953982648683)
      ·
        refine ⟨2734687638176930973973025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823125092117953982648683 2734687638176930973973025)
        ·
          refine ⟨2051015728632698230479769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2734687638176930973973025 2051015728632698230479769)
          ·
            refine ⟨1538261796474523672859827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051015728632698230479769 1538261796474523672859827)
            ·
              refine ⟨2307392694711785509289741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538261796474523672859827 2307392694711785509289741)
              ·
                refine ⟨865272260516919565983653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2307392694711785509289741 865272260516919565983653)
                ·
                  refine ⟨162238548846922418621935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865272260516919565983653 162238548846922418621935)
                  ·
                    rfl

theorem cell22_1421813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_1421813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421813 prefixEnd_1421813 := by exact prefixLift 1421813
  have htrace : WordTrace (prefixWord ++ tailWord_1421813) baseStart_1421813 baseEnd_1421813 := by
    simpa [prefixWord, tailWord_1421813, baseEnd_1421813] using wordTrace_append hprefix tailTrace_1421813
  have hstable : (prefixWord ++ tailWord_1421813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421813).length < 2 ^ (prefixWord ++ tailWord_1421813).sum := by decide
  have hdescent : baseEnd_1421813 < baseStart_1421813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421820 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1421820 : Nat := 118140960795 + 1421820 * 2 ^ 59
def prefixEnd_1421820 : Nat := 4983230072969 + 3 ^ 40 * 1421820 * 2
def baseEnd_1421820 : Nat := 486718042783821570940783

theorem tailTrace_1421820 : CollatzResearch.WordTrace tailWord_1421820 prefixEnd_1421820 486718042783821570940783 := by
  unfold tailWord_1421820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25929017854498221184311457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34572023805997628245748609 25929017854498221184311457)
  ·
    refine ⟨19446763390873665888233593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25929017854498221184311457 19446763390873665888233593)
    ·
      refine ⟨14585072543155249416175195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19446763390873665888233593 14585072543155249416175195)
      ·
        refine ⟨21877608814732874124262793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14585072543155249416175195 21877608814732874124262793)
        ·
          refine ⟨16408206611049655593197095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21877608814732874124262793 16408206611049655593197095)
          ·
            refine ⟨24612309916574483389795643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16408206611049655593197095 24612309916574483389795643)
            ·
              refine ⟨36918464874861725084693465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24612309916574483389795643 36918464874861725084693465)
              ·
                refine ⟨27688848656146293813520099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36918464874861725084693465 27688848656146293813520099)
                ·
                  refine ⟨41533272984219440720280149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27688848656146293813520099 41533272984219440720280149)
                  ·
                    refine ⟨486718042783821570940783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41533272984219440720280149 486718042783821570940783)
                    ·
                      rfl

theorem cell22_1421820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1421820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421820 prefixEnd_1421820 := by exact prefixLift 1421820
  have htrace : WordTrace (prefixWord ++ tailWord_1421820) baseStart_1421820 baseEnd_1421820 := by
    simpa [prefixWord, tailWord_1421820, baseEnd_1421820] using wordTrace_append hprefix tailTrace_1421820
  have hstable : (prefixWord ++ tailWord_1421820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421820).length < 2 ^ (prefixWord ++ tailWord_1421820).sum := by decide
  have hdescent : baseEnd_1421820 < baseStart_1421820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421826 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1421826 : Nat := 118140960795 + 1421826 * 2 ^ 59
def prefixEnd_1421826 : Nat := 4983230072969 + 3 ^ 40 * 1421826 * 2
def baseEnd_1421826 : Nat := 486720096706439555290765

theorem tailTrace_1421826 : CollatzResearch.WordTrace tailWord_1421826 prefixEnd_1421826 486720096706439555290765 := by
  unfold tailWord_1421826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964563636743676348335333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34572169697983136928894221 12964563636743676348335333)
  ·
    refine ⟨2430855681889439315312875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12964563636743676348335333 2430855681889439315312875)
    ·
      refine ⟨3646283522834158972969313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430855681889439315312875 3646283522834158972969313)
      ·
        refine ⟨2734712642125619229726985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3646283522834158972969313 2734712642125619229726985)
        ·
          refine ⟨2051034481594214422295239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2734712642125619229726985 2051034481594214422295239)
          ·
            refine ⟨3076551722391321633442859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051034481594214422295239 3076551722391321633442859)
            ·
              refine ⟨4614827583586982450164289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076551722391321633442859 4614827583586982450164289)
              ·
                refine ⟨3461120687690236837623217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614827583586982450164289 3461120687690236837623217)
                ·
                  refine ⟨2595840515767677628217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461120687690236837623217 2595840515767677628217413)
                  ·
                    refine ⟨486720096706439555290765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595840515767677628217413 486720096706439555290765)
                    ·
                      rfl

theorem cell22_1421826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1421826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421826 prefixEnd_1421826 := by exact prefixLift 1421826
  have htrace : WordTrace (prefixWord ++ tailWord_1421826) baseStart_1421826 baseEnd_1421826 := by
    simpa [prefixWord, tailWord_1421826, baseEnd_1421826] using wordTrace_append hprefix tailTrace_1421826
  have hstable : (prefixWord ++ tailWord_1421826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421826).length < 2 ^ (prefixWord ++ tailWord_1421826).sum := by decide
  have hdescent : baseEnd_1421826 < baseStart_1421826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421912 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1421912 : Nat := 118140960795 + 1421912 * 2 ^ 59
def prefixEnd_1421912 : Nat := 4983230072969 + 3 ^ 40 * 1421912 * 2
def baseEnd_1421912 : Nat := 486749536263963997640501

theorem tailTrace_1421912 : CollatzResearch.WordTrace tailWord_1421912 prefixEnd_1421912 486749536263963997640501 := by
  unfold tailWord_1421912
  simp only [CollatzResearch.WordTrace]
  refine ⟨25930695612331571040485995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34574260816442094720647993 25930695612331571040485995)
  ·
    refine ⟨38896043418497356560728993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25930695612331571040485995 38896043418497356560728993)
    ·
      refine ⟨29172032563873017420546745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38896043418497356560728993 29172032563873017420546745)
      ·
        refine ⟨21879024422904763065410059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29172032563873017420546745 21879024422904763065410059)
        ·
          refine ⟨32818536634357144598115089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21879024422904763065410059 32818536634357144598115089)
          ·
            refine ⟨24613902475767858448586317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32818536634357144598115089 24613902475767858448586317)
            ·
              refine ⟨9230213428412946918219869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24613902475767858448586317 9230213428412946918219869)
              ·
                refine ⟨3461330035654855094332451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9230213428412946918219869 3461330035654855094332451)
                ·
                  refine ⟨5191995053482282641498677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461330035654855094332451 5191995053482282641498677)
                  ·
                    refine ⟨486749536263963997640501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5191995053482282641498677 486749536263963997640501)
                    ·
                      rfl

theorem cell22_1421912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1421912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421912 prefixEnd_1421912 := by exact prefixLift 1421912
  have htrace : WordTrace (prefixWord ++ tailWord_1421912) baseStart_1421912 baseEnd_1421912 := by
    simpa [prefixWord, tailWord_1421912, baseEnd_1421912] using wordTrace_append hprefix tailTrace_1421912
  have hstable : (prefixWord ++ tailWord_1421912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421912).length < 2 ^ (prefixWord ++ tailWord_1421912).sum := by decide
  have hdescent : baseEnd_1421912 < baseStart_1421912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421933 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_1421933 : Nat := 118140960795 + 1421933 * 2 ^ 59
def prefixEnd_1421933 : Nat := 4983230072969 + 3 ^ 40 * 1421933 * 2
def baseEnd_1421933 : Nat := 486756724993126942865437

theorem tailTrace_1421933 : CollatzResearch.WordTrace tailWord_1421933 prefixEnd_1421933 486756724993126942865437 := by
  unfold tailWord_1421933
  simp only [CollatzResearch.WordTrace]
  refine ⟨51862157157587062667486453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34574771438391375111657635 51862157157587062667486453)
  ·
    refine ⟨4862077233523787125076855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51862157157587062667486453 4862077233523787125076855)
    ·
      refine ⟨7293115850285680687615283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862077233523787125076855 7293115850285680687615283)
      ·
        refine ⟨10939673775428521031422925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293115850285680687615283 10939673775428521031422925)
        ·
          refine ⟨4102377665785695386783597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10939673775428521031422925 4102377665785695386783597)
          ·
            refine ⟨1538391624669635770043849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4102377665785695386783597 1538391624669635770043849)
            ·
              refine ⟨1153793718502226827532887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538391624669635770043849 1153793718502226827532887)
              ·
                refine ⟨1730690577753340241299331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153793718502226827532887 1730690577753340241299331)
                ·
                  refine ⟨2596035866630010361948997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730690577753340241299331 2596035866630010361948997)
                  ·
                    refine ⟨486756724993126942865437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596035866630010361948997 486756724993126942865437)
                    ·
                      rfl

theorem cell22_1421933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_1421933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1421933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1421933 prefixEnd_1421933 := by exact prefixLift 1421933
  have htrace : WordTrace (prefixWord ++ tailWord_1421933) baseStart_1421933 baseEnd_1421933 := by
    simpa [prefixWord, tailWord_1421933, baseEnd_1421933] using wordTrace_append hprefix tailTrace_1421933
  have hstable : (prefixWord ++ tailWord_1421933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421933).length < 2 ^ (prefixWord ++ tailWord_1421933).sum := by decide
  have hdescent : baseEnd_1421933 < baseStart_1421933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422132 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1422132 : Nat := 118140960795 + 1422132 * 2 ^ 59
def prefixEnd_1422132 : Nat := 4983230072969 + 3 ^ 40 * 1422132 * 2
def baseEnd_1422132 : Nat := 486824846759956757139827

theorem tailTrace_1422132 : CollatzResearch.WordTrace tailWord_1422132 prefixEnd_1422132 486824846759956757139827 := by
  unfold tailWord_1422132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25934707641933059826990325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34579610189244079769320433 25934707641933059826990325)
  ·
    refine ⟨2431378841431224358780343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25934707641933059826990325 2431378841431224358780343)
    ·
      refine ⟨3647068262146836538170515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431378841431224358780343 3647068262146836538170515)
      ·
        refine ⟨5470602393220254807255773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647068262146836538170515 5470602393220254807255773)
        ·
          refine ⟨2051475897457595552720915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5470602393220254807255773 2051475897457595552720915)
          ·
            refine ⟨3077213846186393329081373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051475897457595552720915 3077213846186393329081373)
            ·
              refine ⟨1153955192319897498405515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3077213846186393329081373 1153955192319897498405515)
              ·
                refine ⟨1730932788479846247608273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153955192319897498405515 1730932788479846247608273)
                ·
                  refine ⟨1298199591359884685706205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730932788479846247608273 1298199591359884685706205)
                  ·
                    refine ⟨486824846759956757139827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298199591359884685706205 486824846759956757139827)
                    ·
                      rfl

theorem cell22_1422132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1422132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422132 prefixEnd_1422132 := by exact prefixLift 1422132
  have htrace : WordTrace (prefixWord ++ tailWord_1422132) baseStart_1422132 baseEnd_1422132 := by
    simpa [prefixWord, tailWord_1422132, baseEnd_1422132] using wordTrace_append hprefix tailTrace_1422132
  have hstable : (prefixWord ++ tailWord_1422132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422132).length < 2 ^ (prefixWord ++ tailWord_1422132).sum := by decide
  have hdescent : baseEnd_1422132 < baseStart_1422132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422145 : List Nat := [1, 2, 5, 3, 1, 2, 2, 6]
def baseStart_1422145 : Nat := 118140960795 + 1422145 * 2 ^ 59
def prefixEnd_1422145 : Nat := 4983230072969 + 3 ^ 40 * 1422145 * 2
def baseEnd_1422145 : Nat := 54092144102847672951643

theorem tailTrace_1422145 : CollatzResearch.WordTrace tailWord_1422145 prefixEnd_1422145 54092144102847672951643 := by
  unfold tailWord_1422145
  simp only [CollatzResearch.WordTrace]
  refine ⟨51869889432819022874203889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34579926288546015249469259 51869889432819022874203889)
  ·
    refine ⟨38902417074614267155652917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51869889432819022874203889 38902417074614267155652917)
    ·
      refine ⟨3647101600745087545842461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38902417074614267155652917 3647101600745087545842461)
      ·
        refine ⟨1367663100279407829690923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3647101600745087545842461 1367663100279407829690923)
        ·
          refine ⟨2051494650419111744536385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367663100279407829690923 2051494650419111744536385)
          ·
            refine ⟨1538620987814333808402289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051494650419111744536385 1538620987814333808402289)
            ·
              refine ⟨1153965740860750356301717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538620987814333808402289 1153965740860750356301717)
              ·
                refine ⟨54092144102847672951643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1153965740860750356301717 54092144102847672951643)
                ·
                  rfl

theorem cell22_1422145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 6].length) (baseStart_1422145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422145 prefixEnd_1422145 := by exact prefixLift 1422145
  have htrace : WordTrace (prefixWord ++ tailWord_1422145) baseStart_1422145 baseEnd_1422145 := by
    simpa [prefixWord, tailWord_1422145, baseEnd_1422145] using wordTrace_append hprefix tailTrace_1422145
  have hstable : (prefixWord ++ tailWord_1422145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422145).length < 2 ^ (prefixWord ++ tailWord_1422145).sum := by decide
  have hdescent : baseEnd_1422145 < baseStart_1422145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422154 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1422154 : Nat := 118140960795 + 1422154 * 2 ^ 59
def prefixEnd_1422154 : Nat := 4983230072969 + 3 ^ 40 * 1422154 * 2
def baseEnd_1422154 : Nat := 486832377809556033089759

theorem tailTrace_1422154 : CollatzResearch.WordTrace tailWord_1422154 prefixEnd_1422154 486832377809556033089759 := by
  unfold tailWord_1422154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967554422446604352820379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34580145126524278274187677 12967554422446604352820379)
  ·
    refine ⟨19451331633669906529230569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967554422446604352820379 19451331633669906529230569)
    ·
      refine ⟨14588498725252429896922927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19451331633669906529230569 14588498725252429896922927)
      ·
        refine ⟨21882748087878644845384391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588498725252429896922927 21882748087878644845384391)
        ·
          refine ⟨32824122131817967268076587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882748087878644845384391 32824122131817967268076587)
          ·
            refine ⟨49236183197726950902114881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32824122131817967268076587 49236183197726950902114881)
            ·
              refine ⟨36927137398295213176586161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49236183197726950902114881 36927137398295213176586161)
              ·
                refine ⟨27695353048721409882439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36927137398295213176586161 27695353048721409882439621)
                ·
                  refine ⟨5192878696635264352957429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27695353048721409882439621 5192878696635264352957429)
                  ·
                    refine ⟨486832377809556033089759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5192878696635264352957429 486832377809556033089759)
                    ·
                      rfl

theorem cell22_1422154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1422154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422154 prefixEnd_1422154 := by exact prefixLift 1422154
  have htrace : WordTrace (prefixWord ++ tailWord_1422154) baseStart_1422154 baseEnd_1422154 := by
    simpa [prefixWord, tailWord_1422154, baseEnd_1422154] using wordTrace_append hprefix tailTrace_1422154
  have hstable : (prefixWord ++ tailWord_1422154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422154).length < 2 ^ (prefixWord ++ tailWord_1422154).sum := by decide
  have hdescent : baseEnd_1422154 < baseStart_1422154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422199 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1422199 : Nat := 118140960795 + 1422199 * 2 ^ 59
def prefixEnd_1422199 : Nat := 4983230072969 + 3 ^ 40 * 1422199 * 2
def baseEnd_1422199 : Nat := 486847782229190915714621

theorem tailTrace_1422199 : CollatzResearch.WordTrace tailWord_1422199 prefixEnd_1422199 486847782229190915714621 := by
  unfold tailWord_1422199
  simp only [CollatzResearch.WordTrace]
  refine ⟨51871858974623390096669651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34581239316415593397779767 51871858974623390096669651)
  ·
    refine ⟨77807788461935085145004477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51871858974623390096669651 77807788461935085145004477)
    ·
      refine ⟨29177920673225656929376679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77807788461935085145004477 29177920673225656929376679)
      ·
        refine ⟨43766881009838485394065019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29177920673225656929376679 43766881009838485394065019)
        ·
          refine ⟨65650321514757728091097529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43766881009838485394065019 65650321514757728091097529)
          ·
            refine ⟨49237741136068296068323147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65650321514757728091097529 49237741136068296068323147)
            ·
              refine ⟨73856611704102444102484721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49237741136068296068323147 73856611704102444102484721)
              ·
                refine ⟨55392458778076833076863541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73856611704102444102484721 55392458778076833076863541)
                ·
                  refine ⟨5193043010444703100955957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55392458778076833076863541 5193043010444703100955957)
                  ·
                    refine ⟨486847782229190915714621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5193043010444703100955957 486847782229190915714621)
                    ·
                      rfl

theorem cell22_1422199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1422199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422199 prefixEnd_1422199 := by exact prefixLift 1422199
  have htrace : WordTrace (prefixWord ++ tailWord_1422199) baseStart_1422199 baseEnd_1422199 := by
    simpa [prefixWord, tailWord_1422199, baseEnd_1422199] using wordTrace_append hprefix tailTrace_1422199
  have hstable : (prefixWord ++ tailWord_1422199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422199).length < 2 ^ (prefixWord ++ tailWord_1422199).sum := by decide
  have hdescent : baseEnd_1422199 < baseStart_1422199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422216 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1422216 : Nat := 118140960795 + 1422216 * 2 ^ 59
def prefixEnd_1422216 : Nat := 4983230072969 + 3 ^ 40 * 1422216 * 2
def baseEnd_1422216 : Nat := 486853601676608538039569

theorem tailTrace_1422216 : CollatzResearch.WordTrace tailWord_1422216 prefixEnd_1422216 486853601676608538039569 := by
  unfold tailWord_1422216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25936239507780901000019251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34581652677041201333359001 25936239507780901000019251)
  ·
    refine ⟨38904359261671351500028877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25936239507780901000019251 38904359261671351500028877)
    ·
      refine ⟨14589134723126756812510829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38904359261671351500028877 14589134723126756812510829)
      ·
        refine ⟨5470925521172533804691561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14589134723126756812510829 5470925521172533804691561)
        ·
          refine ⟨4103194140879400353518671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5470925521172533804691561 4103194140879400353518671)
          ·
            refine ⟨6154791211319100530278007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103194140879400353518671 6154791211319100530278007)
            ·
              refine ⟨9232186816978650795417011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154791211319100530278007 9232186816978650795417011)
              ·
                refine ⟨13848280225467976193125517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9232186816978650795417011 13848280225467976193125517)
                ·
                  refine ⟨5193105084550491072422069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13848280225467976193125517 5193105084550491072422069)
                  ·
                    refine ⟨486853601676608538039569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5193105084550491072422069 486853601676608538039569)
                    ·
                      rfl

theorem cell22_1422216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1422216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422216 prefixEnd_1422216 := by exact prefixLift 1422216
  have htrace : WordTrace (prefixWord ++ tailWord_1422216) baseStart_1422216 baseEnd_1422216 := by
    simpa [prefixWord, tailWord_1422216, baseEnd_1422216] using wordTrace_append hprefix tailTrace_1422216
  have hstable : (prefixWord ++ tailWord_1422216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422216).length < 2 ^ (prefixWord ++ tailWord_1422216).sum := by decide
  have hdescent : baseEnd_1422216 < baseStart_1422216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422229 : List Nat := [1, 3, 2, 1, 1, 14]
def baseStart_1422229 : Nat := 118140960795 + 1422229 * 2 ^ 59
def prefixEnd_1422229 : Nat := 4983230072969 + 3 ^ 40 * 1422229 * 2
def baseEnd_1422229 : Nat := 6010593232620751079809

theorem tailTrace_1422229 : CollatzResearch.WordTrace tailWord_1422229 prefixEnd_1422229 6010593232620751079809 := by
  unfold tailWord_1422229
  simp only [CollatzResearch.WordTrace]
  refine ⟨51872953164514705220261741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34581968776343136813507827 51872953164514705220261741)
  ·
    refine ⟨19452357436693014457598153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51872953164514705220261741 19452357436693014457598153)
    ·
      refine ⟨14589268077519760843198615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19452357436693014457598153 14589268077519760843198615)
      ·
        refine ⟨21883902116279641264797923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14589268077519760843198615 21883902116279641264797923)
        ·
          refine ⟨32825853174419461897196885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21883902116279641264797923 32825853174419461897196885)
          ·
            refine ⟨6010593232620751079809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 32825853174419461897196885 6010593232620751079809)
            ·
              rfl

theorem cell22_1422229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 14].length) (baseStart_1422229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422229 prefixEnd_1422229 := by exact prefixLift 1422229
  have htrace : WordTrace (prefixWord ++ tailWord_1422229) baseStart_1422229 baseEnd_1422229 := by
    simpa [prefixWord, tailWord_1422229, baseEnd_1422229] using wordTrace_append hprefix tailTrace_1422229
  have hstable : (prefixWord ++ tailWord_1422229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422229).length < 2 ^ (prefixWord ++ tailWord_1422229).sum := by decide
  have hdescent : baseEnd_1422229 < baseStart_1422229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422231 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1422231 : Nat := 118140960795 + 1422231 * 2 ^ 59
def prefixEnd_1422231 : Nat := 4983230072969 + 3 ^ 40 * 1422231 * 2
def baseEnd_1422231 : Nat := 486858736483153498914523

theorem tailTrace_1422231 : CollatzResearch.WordTrace tailWord_1422231 prefixEnd_1422231 486858736483153498914523 := by
  unfold tailWord_1422231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51873026110507459561834547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34582017407004973041223031 51873026110507459561834547)
  ·
    refine ⟨77809539165761189342751821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51873026110507459561834547 77809539165761189342751821)
    ·
      refine ⟨29178577187160446003531933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77809539165761189342751821 29178577187160446003531933)
      ·
        refine ⟨10941966445185167251324475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29178577187160446003531933 10941966445185167251324475)
        ·
          refine ⟨16412949667777750876986713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941966445185167251324475 16412949667777750876986713)
          ·
            refine ⟨12309712250833313157740035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16412949667777750876986713 12309712250833313157740035)
            ·
              refine ⟨18464568376249969736610053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12309712250833313157740035 18464568376249969736610053)
              ·
                refine ⟨3462106570546869325614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18464568376249969736610053 3462106570546869325614385)
                ·
                  refine ⟨2596579927910151994210789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462106570546869325614385 2596579927910151994210789)
                  ·
                    refine ⟨486858736483153498914523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596579927910151994210789 486858736483153498914523)
                    ·
                      rfl

theorem cell22_1422231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1422231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422231 prefixEnd_1422231 := by exact prefixLift 1422231
  have htrace : WordTrace (prefixWord ++ tailWord_1422231) baseStart_1422231 baseEnd_1422231 := by
    simpa [prefixWord, tailWord_1422231, baseEnd_1422231] using wordTrace_append hprefix tailTrace_1422231
  have hstable : (prefixWord ++ tailWord_1422231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422231).length < 2 ^ (prefixWord ++ tailWord_1422231).sum := by decide
  have hdescent : baseEnd_1422231 < baseStart_1422231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422353 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 4]
def baseStart_1422353 : Nat := 118140960795 + 1422353 * 2 ^ 59
def prefixEnd_1422353 : Nat := 4983230072969 + 3 ^ 40 * 1422353 * 2
def baseEnd_1422353 : Nat := 162300166525461949121383

theorem tailTrace_1422353 : CollatzResearch.WordTrace tailWord_1422353 prefixEnd_1422353 162300166525461949121383 := by
  unfold tailWord_1422353
  simp only [CollatzResearch.WordTrace]
  refine ⟨51877475816065474397775713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34584983877376982931850475 51877475816065474397775713)
  ·
    refine ⟨38908106862049105798331785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51877475816065474397775713 38908106862049105798331785)
    ·
      refine ⟨29181080146536829348748839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38908106862049105798331785 29181080146536829348748839)
      ·
        refine ⟨43771620219805244023123259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29181080146536829348748839 43771620219805244023123259)
        ·
          refine ⟨65657430329707866034684889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43771620219805244023123259 65657430329707866034684889)
          ·
            refine ⟨49243072747280899526013667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65657430329707866034684889 49243072747280899526013667)
            ·
              refine ⟨73864609120921349289020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49243072747280899526013667 73864609120921349289020501)
              ·
                refine ⟨865600888135797061980709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73864609120921349289020501 865600888135797061980709)
                ·
                  refine ⟨162300166525461949121383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865600888135797061980709 162300166525461949121383)
                  ·
                    rfl

theorem cell22_1422353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_1422353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422353 prefixEnd_1422353 := by exact prefixLift 1422353
  have htrace : WordTrace (prefixWord ++ tailWord_1422353) baseStart_1422353 baseEnd_1422353 := by
    simpa [prefixWord, tailWord_1422353, baseEnd_1422353] using wordTrace_append hprefix tailTrace_1422353
  have hstable : (prefixWord ++ tailWord_1422353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422353).length < 2 ^ (prefixWord ++ tailWord_1422353).sum := by decide
  have hdescent : baseEnd_1422353 < baseStart_1422353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422372 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1422372 : Nat := 118140960795 + 1422372 * 2 ^ 59
def prefixEnd_1422372 : Nat := 4983230072969 + 3 ^ 40 * 1422372 * 2
def baseEnd_1422372 : Nat := 486907003664676131139091

theorem tailTrace_1422372 : CollatzResearch.WordTrace tailWord_1422372 prefixEnd_1422372 486907003664676131139091 := by
  unfold tailWord_1422372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25939084401498320321358685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34585445868664427095144913 25939084401498320321358685)
  ·
    refine ⟨9727156650561870120509507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25939084401498320321358685 9727156650561870120509507)
    ·
      refine ⟨14590734975842805180764261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9727156650561870120509507 14590734975842805180764261)
      ·
        refine ⟨2735762807970525971393299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14590734975842805180764261 2735762807970525971393299)
        ·
          refine ⟨4103644211955788957089949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735762807970525971393299 4103644211955788957089949)
          ·
            refine ⟨1538866579483420858908731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4103644211955788957089949 1538866579483420858908731)
            ·
              refine ⟨2308299869225131288363097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538866579483420858908731 2308299869225131288363097)
              ·
                refine ⟨1731224901918848466272323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308299869225131288363097 1731224901918848466272323)
                ·
                  refine ⟨2596837352878272699408485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731224901918848466272323 2596837352878272699408485)
                  ·
                    refine ⟨486907003664676131139091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596837352878272699408485 486907003664676131139091)
                    ·
                      rfl

theorem cell22_1422372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1422372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422372 prefixEnd_1422372 := by exact prefixLift 1422372
  have htrace : WordTrace (prefixWord ++ tailWord_1422372) baseStart_1422372 baseEnd_1422372 := by
    simpa [prefixWord, tailWord_1422372, baseEnd_1422372] using wordTrace_append hprefix tailTrace_1422372
  have hstable : (prefixWord ++ tailWord_1422372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422372).length < 2 ^ (prefixWord ++ tailWord_1422372).sum := by decide
  have hdescent : baseEnd_1422372 < baseStart_1422372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422398 : List Nat := [4, 2, 1, 3, 1, 11]
def baseStart_1422398 : Nat := 118140960795 + 1422398 * 2 ^ 59
def prefixEnd_1422398 : Nat := 4983230072969 + 3 ^ 40 * 1422398 * 2
def baseEnd_1422398 : Nat := 6011307456740996666531

theorem tailTrace_1422398 : CollatzResearch.WordTrace tailWord_1422398 prefixEnd_1422398 6011307456740996666531 := by
  unfold tailWord_1422398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484889637612805885395481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34586078067268298055442565 6484889637612805885395481)
  ·
    refine ⟨4863667228209604414046611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484889637612805885395481 4863667228209604414046611)
    ·
      refine ⟨7295500842314406621069917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863667228209604414046611 7295500842314406621069917)
      ·
        refine ⟨2735812815867902482901219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7295500842314406621069917 2735812815867902482901219)
        ·
          refine ⟨4103719223801853724351829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735812815867902482901219 4103719223801853724351829)
          ·
            refine ⟨6011307456740996666531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4103719223801853724351829 6011307456740996666531)
            ·
              rfl

theorem cell22_1422398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 11].length) (baseStart_1422398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422398 prefixEnd_1422398 := by exact prefixLift 1422398
  have htrace : WordTrace (prefixWord ++ tailWord_1422398) baseStart_1422398 baseEnd_1422398 := by
    simpa [prefixWord, tailWord_1422398, baseEnd_1422398] using wordTrace_append hprefix tailTrace_1422398
  have hstable : (prefixWord ++ tailWord_1422398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422398).length < 2 ^ (prefixWord ++ tailWord_1422398).sum := by decide
  have hdescent : baseEnd_1422398 < baseStart_1422398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422428 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1422428 : Nat := 118140960795 + 1422428 * 2 ^ 59
def prefixEnd_1422428 : Nat := 4983230072969 + 3 ^ 40 * 1422428 * 2
def baseEnd_1422428 : Nat := 486926173609110651738919

theorem tailTrace_1422428 : CollatzResearch.WordTrace tailWord_1422428 prefixEnd_1422428 486926173609110651738919 := by
  unfold tailWord_1422428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25940105645396881103377969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34586807527195841471170625 25940105645396881103377969)
  ·
    refine ⟨19455079234047660827533477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25940105645396881103377969 19455079234047660827533477)
    ·
      refine ⟨3647827356383936405162527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19455079234047660827533477 3647827356383936405162527)
      ·
        refine ⟨5471741034575904607743791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647827356383936405162527 5471741034575904607743791)
        ·
          refine ⟨8207611551863856911615687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5471741034575904607743791 8207611551863856911615687)
          ·
            refine ⟨12311417327795785367423531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8207611551863856911615687 12311417327795785367423531)
            ·
              refine ⟨18467125991693678051135297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12311417327795785367423531 18467125991693678051135297)
              ·
                refine ⟨13850344493770258538351473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18467125991693678051135297 13850344493770258538351473)
                ·
                  refine ⟨10387758370327693903763605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13850344493770258538351473 10387758370327693903763605)
                  ·
                    refine ⟨486926173609110651738919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10387758370327693903763605 486926173609110651738919)
                    ·
                      rfl

theorem cell22_1422428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1422428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422428 prefixEnd_1422428 := by exact prefixLift 1422428
  have htrace : WordTrace (prefixWord ++ tailWord_1422428) baseStart_1422428 baseEnd_1422428 := by
    simpa [prefixWord, tailWord_1422428, baseEnd_1422428] using wordTrace_append hprefix tailTrace_1422428
  have hstable : (prefixWord ++ tailWord_1422428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422428).length < 2 ^ (prefixWord ++ tailWord_1422428).sum := by decide
  have hdescent : baseEnd_1422428 < baseStart_1422428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422447 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 1, 3]
def baseStart_1422447 : Nat := 118140960795 + 1422447 * 2 ^ 59
def prefixEnd_1422447 : Nat := 4983230072969 + 3 ^ 40 * 1422447 * 2
def baseEnd_1422447 : Nat := 486932677697400935513861

theorem tailTrace_1422447 : CollatzResearch.WordTrace tailWord_1422447 prefixEnd_1422447 486932677697400935513861 := by
  unfold tailWord_1422447
  simp only [CollatzResearch.WordTrace]
  refine ⟨51880904277724928451697595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34587269518483285634465063 51880904277724928451697595)
  ·
    refine ⟨77821356416587392677546393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51880904277724928451697595 77821356416587392677546393)
    ·
      refine ⟨58366017312440544508159795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77821356416587392677546393 58366017312440544508159795)
      ·
        refine ⟨87549025968660816762239693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58366017312440544508159795 87549025968660816762239693)
        ·
          refine ⟨32830884738247806285839885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87549025968660816762239693 32830884738247806285839885)
          ·
            refine ⟨12311581776842927357189957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32830884738247806285839885 12311581776842927357189957)
            ·
              refine ⟨2308421583158048879473117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12311581776842927357189957 2308421583158048879473117)
              ·
                refine ⟨865658093684268329802419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308421583158048879473117 865658093684268329802419)
                ·
                  refine ⟨1298487140526402494703629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865658093684268329802419 1298487140526402494703629)
                  ·
                    refine ⟨486932677697400935513861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298487140526402494703629 486932677697400935513861)
                    ·
                      rfl

theorem cell22_1422447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_1422447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422447 prefixEnd_1422447 := by exact prefixLift 1422447
  have htrace : WordTrace (prefixWord ++ tailWord_1422447) baseStart_1422447 baseEnd_1422447 := by
    simpa [prefixWord, tailWord_1422447, baseEnd_1422447] using wordTrace_append hprefix tailTrace_1422447
  have hstable : (prefixWord ++ tailWord_1422447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422447).length < 2 ^ (prefixWord ++ tailWord_1422447).sum := by decide
  have hdescent : baseEnd_1422447 < baseStart_1422447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422498 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1422498 : Nat := 118140960795 + 1422498 * 2 ^ 59
def prefixEnd_1422498 : Nat := 4983230072969 + 3 ^ 40 * 1422498 * 2
def baseEnd_1422498 : Nat := 486950136039653802488705

theorem tailTrace_1422498 : CollatzResearch.WordTrace tailWord_1422498 prefixEnd_1422498 486950136039653802488705 := by
  unfold tailWord_1422498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970691100135041040451037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34588509600360109441202765 12970691100135041040451037)
  ·
    refine ⟨4864009162550640390169139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12970691100135041040451037 4864009162550640390169139)
    ·
      refine ⟨7296013743825960585253709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864009162550640390169139 7296013743825960585253709)
      ·
        refine ⟨2736005153934735219470141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7296013743825960585253709 2736005153934735219470141)
        ·
          refine ⟨1026001932725525707301303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2736005153934735219470141 1026001932725525707301303)
          ·
            refine ⟨1539002899088288560951955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026001932725525707301303 1539002899088288560951955)
            ·
              refine ⟨2308504348632432841427933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539002899088288560951955 2308504348632432841427933)
              ·
                refine ⟨865689130737162315535475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308504348632432841427933 865689130737162315535475)
                ·
                  refine ⟨1298533696105743473303213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865689130737162315535475 1298533696105743473303213)
                  ·
                    refine ⟨486950136039653802488705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298533696105743473303213 486950136039653802488705)
                    ·
                      rfl

theorem cell22_1422498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1422498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422498 prefixEnd_1422498 := by exact prefixLift 1422498
  have htrace : WordTrace (prefixWord ++ tailWord_1422498) baseStart_1422498 baseEnd_1422498 := by
    simpa [prefixWord, tailWord_1422498, baseEnd_1422498] using wordTrace_append hprefix tailTrace_1422498
  have hstable : (prefixWord ++ tailWord_1422498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422498).length < 2 ^ (prefixWord ++ tailWord_1422498).sum := by decide
  have hdescent : baseEnd_1422498 < baseStart_1422498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422552 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1422552 : Nat := 118140960795 + 1422552 * 2 ^ 59
def prefixEnd_1422552 : Nat := 4983230072969 + 3 ^ 40 * 1422552 * 2
def baseEnd_1422552 : Nat := 486968621343215661638539

theorem tailTrace_1422552 : CollatzResearch.WordTrace tailWord_1422552 prefixEnd_1422552 486968621343215661638539 := by
  unfold tailWord_1422552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25942366971172265692134955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34589822628229687589513273 25942366971172265692134955)
  ·
    refine ⟨38913550456758398538202433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25942366971172265692134955 38913550456758398538202433)
    ·
      refine ⟨29185162842568798903651825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38913550456758398538202433 29185162842568798903651825)
      ·
        refine ⟨21888872131926599177738869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29185162842568798903651825 21888872131926599177738869)
        ·
          refine ⟨2052081762368118672913019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21888872131926599177738869 2052081762368118672913019)
          ·
            refine ⟨3078122643552178009369529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052081762368118672913019 3078122643552178009369529)
            ·
              refine ⟨2308591982664133507027147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078122643552178009369529 2308591982664133507027147)
              ·
                refine ⟨3462887973996200260540721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308591982664133507027147 3462887973996200260540721)
                ·
                  refine ⟨2597165980497150195405541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462887973996200260540721 2597165980497150195405541)
                  ·
                    refine ⟨486968621343215661638539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597165980497150195405541 486968621343215661638539)
                    ·
                      rfl

theorem cell22_1422552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1422552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422552 prefixEnd_1422552 := by exact prefixLift 1422552
  have htrace : WordTrace (prefixWord ++ tailWord_1422552) baseStart_1422552 baseEnd_1422552 := by
    simpa [prefixWord, tailWord_1422552, baseEnd_1422552] using wordTrace_append hprefix tailTrace_1422552
  have hstable : (prefixWord ++ tailWord_1422552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422552).length < 2 ^ (prefixWord ++ tailWord_1422552).sum := by decide
  have hdescent : baseEnd_1422552 < baseStart_1422552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422582 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_1422582 : Nat := 118140960795 + 1422582 * 2 ^ 59
def prefixEnd_1422582 : Nat := 4983230072969 + 3 ^ 40 * 1422582 * 2
def baseEnd_1422582 : Nat := 486978890956305583388447

theorem tailTrace_1422582 : CollatzResearch.WordTrace tailWord_1422582 prefixEnd_1422582 486978890956305583388447 := by
  unfold tailWord_1422582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242864258264740406741375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34590552088157231005241333 3242864258264740406741375)
  ·
    refine ⟨4864296387397110610112063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242864258264740406741375 4864296387397110610112063)
    ·
      refine ⟨7296444581095665915168095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864296387397110610112063 7296444581095665915168095)
      ·
        refine ⟨10944666871643498872752143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7296444581095665915168095 10944666871643498872752143)
        ·
          refine ⟨16417000307465248309128215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944666871643498872752143 16417000307465248309128215)
          ·
            refine ⟨24625500461197872463692323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16417000307465248309128215 24625500461197872463692323)
            ·
              refine ⟨36938250691796808695538485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24625500461197872463692323 36938250691796808695538485)
              ·
                refine ⟨3462961002355950815206733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36938250691796808695538485 3462961002355950815206733)
                ·
                  refine ⟨1298610375883481555702525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3462961002355950815206733 1298610375883481555702525)
                  ·
                    refine ⟨486978890956305583388447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298610375883481555702525 486978890956305583388447)
                    ·
                      rfl

theorem cell22_1422582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_1422582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422582 prefixEnd_1422582 := by exact prefixLift 1422582
  have htrace : WordTrace (prefixWord ++ tailWord_1422582) baseStart_1422582 baseEnd_1422582 := by
    simpa [prefixWord, tailWord_1422582, baseEnd_1422582] using wordTrace_append hprefix tailTrace_1422582
  have hstable : (prefixWord ++ tailWord_1422582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422582).length < 2 ^ (prefixWord ++ tailWord_1422582).sum := by decide
  have hdescent : baseEnd_1422582 < baseStart_1422582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422595 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 5]
def baseStart_1422595 : Nat := 118140960795 + 1422595 * 2 ^ 59
def prefixEnd_1422595 : Nat := 4983230072969 + 3 ^ 40 * 1422595 * 2
def baseEnd_1422595 : Nat := 162327780373992627604469

theorem tailTrace_1422595 : CollatzResearch.WordTrace tailWord_1422595 prefixEnd_1422595 162327780373992627604469 := by
  unfold tailWord_1422595
  simp only [CollatzResearch.WordTrace]
  refine ⟨51886302281188749728085239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34590868187459166485390159 51886302281188749728085239)
  ·
    refine ⟨77829453421783124592127859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51886302281188749728085239 77829453421783124592127859)
    ·
      refine ⟨116744180132674686888191789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77829453421783124592127859 116744180132674686888191789)
      ·
        refine ⟨43779067549753007583071921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116744180132674686888191789 43779067549753007583071921)
        ·
          refine ⟨32834300662314755687303941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43779067549753007583071921 32834300662314755687303941)
          ·
            refine ⟨6156431374184016691369489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32834300662314755687303941 6156431374184016691369489)
            ·
              refine ⟨4617323530638012518527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156431374184016691369489 4617323530638012518527117)
              ·
                refine ⟨1731496323989254694447669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4617323530638012518527117 1731496323989254694447669)
                ·
                  refine ⟨162327780373992627604469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1731496323989254694447669 162327780373992627604469)
                  ·
                    rfl

theorem cell22_1422595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].length) (baseStart_1422595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422595 prefixEnd_1422595 := by exact prefixLift 1422595
  have htrace : WordTrace (prefixWord ++ tailWord_1422595) baseStart_1422595 baseEnd_1422595 := by
    simpa [prefixWord, tailWord_1422595, baseEnd_1422595] using wordTrace_append hprefix tailTrace_1422595
  have hstable : (prefixWord ++ tailWord_1422595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422595).length < 2 ^ (prefixWord ++ tailWord_1422595).sum := by decide
  have hdescent : baseEnd_1422595 < baseStart_1422595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422640 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_1422640 : Nat := 118140960795 + 1422640 * 2 ^ 59
def prefixEnd_1422640 : Nat := 4983230072969 + 3 ^ 40 * 1422640 * 2
def baseEnd_1422640 : Nat := 162332915180537588479423

theorem tailTrace_1422640 : CollatzResearch.WordTrace tailWord_1422640 prefixEnd_1422640 162332915180537588479423 := by
  unfold tailWord_1422640
  simp only [CollatzResearch.WordTrace]
  refine ⟨25943971783012861206736687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34591962377350481608982249 25943971783012861206736687)
  ·
    refine ⟨38915957674519291810105031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25943971783012861206736687 38915957674519291810105031)
    ·
      refine ⟨58373936511778937715157547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38915957674519291810105031 58373936511778937715157547)
      ·
        refine ⟨87560904767668406572736321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58373936511778937715157547 87560904767668406572736321)
        ·
          refine ⟨65670678575751304929552241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87560904767668406572736321 65670678575751304929552241)
          ·
            refine ⟨49253008931813478697164181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65670678575751304929552241 49253008931813478697164181)
            ·
              refine ⟨2308734793678756813929571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49253008931813478697164181 2308734793678756813929571)
              ·
                refine ⟨3463102190518135220894357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308734793678756813929571 3463102190518135220894357)
                ·
                  refine ⟨162332915180537588479423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3463102190518135220894357 162332915180537588479423)
                  ·
                    rfl

theorem cell22_1422640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_1422640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422640 prefixEnd_1422640 := by exact prefixLift 1422640
  have htrace : WordTrace (prefixWord ++ tailWord_1422640) baseStart_1422640 baseEnd_1422640 := by
    simpa [prefixWord, tailWord_1422640, baseEnd_1422640] using wordTrace_append hprefix tailTrace_1422640
  have hstable : (prefixWord ++ tailWord_1422640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422640).length < 2 ^ (prefixWord ++ tailWord_1422640).sum := by decide
  have hdescent : baseEnd_1422640 < baseStart_1422640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422657 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 6]
def baseStart_1422657 : Nat := 118140960795 + 1422657 * 2 ^ 59
def prefixEnd_1422657 : Nat := 4983230072969 + 3 ^ 40 * 1422657 * 2
def baseEnd_1422657 : Nat := 162334854996343462587739

theorem tailTrace_1422657 : CollatzResearch.WordTrace tailWord_1422657 prefixEnd_1422657 162334854996343462587739 := by
  unfold tailWord_1422657
  simp only [CollatzResearch.WordTrace]
  refine ⟨51888563606964134316842225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34592375737976089544561483 51888563606964134316842225)
  ·
    refine ⟨38916422705223100737631669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51888563606964134316842225 38916422705223100737631669)
    ·
      refine ⟨3648414628614665694152969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38916422705223100737631669 3648414628614665694152969)
      ·
        refine ⟨2736310971460999270614727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648414628614665694152969 2736310971460999270614727)
        ·
          refine ⟨4104466457191498905922091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736310971460999270614727 4104466457191498905922091)
          ·
            refine ⟨6156699685787248358883137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104466457191498905922091 6156699685787248358883137)
            ·
              refine ⟨4617524764340436269162353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156699685787248358883137 4617524764340436269162353)
              ·
                refine ⟨3463143573255327201871765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617524764340436269162353 3463143573255327201871765)
                ·
                  refine ⟨162334854996343462587739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3463143573255327201871765 162334854996343462587739)
                  ·
                    rfl

theorem cell22_1422657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_1422657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422657 prefixEnd_1422657 := by exact prefixLift 1422657
  have htrace : WordTrace (prefixWord ++ tailWord_1422657) baseStart_1422657 baseEnd_1422657 := by
    simpa [prefixWord, tailWord_1422657, baseEnd_1422657] using wordTrace_append hprefix tailTrace_1422657
  have hstable : (prefixWord ++ tailWord_1422657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422657).length < 2 ^ (prefixWord ++ tailWord_1422657).sum := by decide
  have hdescent : baseEnd_1422657 < baseStart_1422657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422670 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1422670 : Nat := 118140960795 + 1422670 * 2 ^ 59
def prefixEnd_1422670 : Nat := 4983230072969 + 3 ^ 40 * 1422670 * 2
def baseEnd_1422670 : Nat := 487009015154702687188177

theorem tailTrace_1422670 : CollatzResearch.WordTrace tailWord_1422670 prefixEnd_1422670 487009015154702687188177 := by
  unfold tailWord_1422670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486129719489629692133183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34592691837278025024710309 6486129719489629692133183)
  ·
    refine ⟨9729194579234444538199775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486129719489629692133183 9729194579234444538199775)
    ·
      refine ⟨14593791868851666807299663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729194579234444538199775 14593791868851666807299663)
      ·
        refine ⟨21890687803277500210949495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14593791868851666807299663 21890687803277500210949495)
        ·
          refine ⟨32836031704916250316424243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890687803277500210949495 32836031704916250316424243)
          ·
            refine ⟨49254047557374375474636365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32836031704916250316424243 49254047557374375474636365)
            ·
              refine ⟨18470267834015390802988637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49254047557374375474636365 18470267834015390802988637)
              ·
                refine ⟨6926350437755771551120739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18470267834015390802988637 6926350437755771551120739)
                ·
                  refine ⟨10389525656633657326681109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926350437755771551120739 10389525656633657326681109)
                  ·
                    refine ⟨487009015154702687188177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10389525656633657326681109 487009015154702687188177)
                    ·
                      rfl

theorem cell22_1422670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1422670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422670 prefixEnd_1422670 := by exact prefixLift 1422670
  have htrace : WordTrace (prefixWord ++ tailWord_1422670) baseStart_1422670 baseEnd_1422670 := by
    simpa [prefixWord, tailWord_1422670, baseEnd_1422670] using wordTrace_append hprefix tailTrace_1422670
  have hstable : (prefixWord ++ tailWord_1422670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422670).length < 2 ^ (prefixWord ++ tailWord_1422670).sum := by decide
  have hdescent : baseEnd_1422670 < baseStart_1422670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422717 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1422717 : Nat := 118140960795 + 1422717 * 2 ^ 59
def prefixEnd_1422717 : Nat := 4983230072969 + 3 ^ 40 * 1422717 * 2
def baseEnd_1422717 : Nat := 487025104215210231263033

theorem tailTrace_1422717 : CollatzResearch.WordTrace tailWord_1422717 prefixEnd_1422717 487025104215210231263033 := by
  unfold tailWord_1422717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51890751986746764564026405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34593834657831176376017603 51890751986746764564026405)
  ·
    refine ⟨9729515997515018355754951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51890751986746764564026405 9729515997515018355754951)
    ·
      refine ⟨14594273996272527533632427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729515997515018355754951 14594273996272527533632427)
      ·
        refine ⟨21891410994408791300448641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594273996272527533632427 21891410994408791300448641)
        ·
          refine ⟨16418558245806593475336481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21891410994408791300448641 16418558245806593475336481)
          ·
            refine ⟨12313918684354945106502361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16418558245806593475336481 12313918684354945106502361)
            ·
              refine ⟨9235439013266208829876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12313918684354945106502361 9235439013266208829876771)
              ·
                refine ⟨13853158519899313244815157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9235439013266208829876771 13853158519899313244815157)
                ·
                  refine ⟨1298733611240560616701421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13853158519899313244815157 1298733611240560616701421)
                  ·
                    refine ⟨487025104215210231263033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298733611240560616701421 487025104215210231263033)
                    ·
                      rfl

theorem cell22_1422717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1422717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422717 prefixEnd_1422717 := by exact prefixLift 1422717
  have htrace : WordTrace (prefixWord ++ tailWord_1422717) baseStart_1422717 baseEnd_1422717 := by
    simpa [prefixWord, tailWord_1422717, baseEnd_1422717] using wordTrace_append hprefix tailTrace_1422717
  have hstable : (prefixWord ++ tailWord_1422717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422717).length < 2 ^ (prefixWord ++ tailWord_1422717).sum := by decide
  have hdescent : baseEnd_1422717 < baseStart_1422717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422751 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 1, 3]
def baseStart_1422751 : Nat := 118140960795 + 1422751 * 2 ^ 59
def prefixEnd_1422751 : Nat := 4983230072969 + 3 ^ 40 * 1422751 * 2
def baseEnd_1422751 : Nat := 487036743110045475912929

theorem tailTrace_1422751 : CollatzResearch.WordTrace tailWord_1422751 prefixEnd_1422751 487036743110045475912929 := by
  unfold tailWord_1422751
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891992068623588370764107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34594661379082392247176071 51891992068623588370764107)
  ·
    refine ⟨77837988102935382556146161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51891992068623588370764107 77837988102935382556146161)
    ·
      refine ⟨58378491077201536917109621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77837988102935382556146161 58378491077201536917109621)
      ·
        refine ⟨5472983538487644085979027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58378491077201536917109621 5472983538487644085979027)
        ·
          refine ⟨8209475307731466128968541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472983538487644085979027 8209475307731466128968541)
          ·
            refine ⟨3078553240399299798363203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8209475307731466128968541 3078553240399299798363203)
            ·
              refine ⟨4617829860598949697544805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078553240399299798363203 4617829860598949697544805)
              ·
                refine ⟨865843098862303068289651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4617829860598949697544805 865843098862303068289651)
                ·
                  refine ⟨1298764648293454602434477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865843098862303068289651 1298764648293454602434477)
                  ·
                    refine ⟨487036743110045475912929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298764648293454602434477 487036743110045475912929)
                    ·
                      rfl

theorem cell22_1422751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_1422751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422751 prefixEnd_1422751 := by exact prefixLift 1422751
  have htrace : WordTrace (prefixWord ++ tailWord_1422751) baseStart_1422751 baseEnd_1422751 := by
    simpa [prefixWord, tailWord_1422751, baseEnd_1422751] using wordTrace_append hprefix tailTrace_1422751
  have hstable : (prefixWord ++ tailWord_1422751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422751).length < 2 ^ (prefixWord ++ tailWord_1422751).sum := by decide
  have hdescent : baseEnd_1422751 < baseStart_1422751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422794 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1422794 : Nat := 118140960795 + 1422794 * 2 ^ 59
def prefixEnd_1422794 : Nat := 4983230072969 + 3 ^ 40 * 1422794 * 2
def baseEnd_1422794 : Nat := 487051462888807697087797

theorem tailTrace_1422794 : CollatzResearch.WordTrace tailWord_1422794 prefixEnd_1422794 487051462888807697087797 := by
  unfold tailWord_1422794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973390101866951678644859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34595706938311871143052957 12973390101866951678644859)
  ·
    refine ⟨19460085152800427517967289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12973390101866951678644859 19460085152800427517967289)
    ·
      refine ⟨14595063864600320638475467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19460085152800427517967289 14595063864600320638475467)
      ·
        refine ⟨21892595796900480957713201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14595063864600320638475467 21892595796900480957713201)
        ·
          refine ⟨16419446847675360718284901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21892595796900480957713201 16419446847675360718284901)
          ·
            refine ⟨3078646283939130134678419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16419446847675360718284901 3078646283939130134678419)
            ·
              refine ⟨4617969425908695202017629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078646283939130134678419 4617969425908695202017629)
              ·
                refine ⟨1731738534715760700756611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4617969425908695202017629 1731738534715760700756611)
                ·
                  refine ⟨2597607802073641051134917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731738534715760700756611 2597607802073641051134917)
                  ·
                    refine ⟨487051462888807697087797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597607802073641051134917 487051462888807697087797)
                    ·
                      rfl

theorem cell22_1422794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1422794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422794 prefixEnd_1422794 := by exact prefixLift 1422794
  have htrace : WordTrace (prefixWord ++ tailWord_1422794) baseStart_1422794 baseEnd_1422794 := by
    simpa [prefixWord, tailWord_1422794, baseEnd_1422794] using wordTrace_append hprefix tailTrace_1422794
  have hstable : (prefixWord ++ tailWord_1422794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422794).length < 2 ^ (prefixWord ++ tailWord_1422794).sum := by decide
  have hdescent : baseEnd_1422794 < baseStart_1422794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422809 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 4]
def baseStart_1422809 : Nat := 118140960795 + 1422809 * 2 ^ 59
def prefixEnd_1422809 : Nat := 4983230072969 + 3 ^ 40 * 1422809 * 2
def baseEnd_1422809 : Nat := 162352199231784219320917

theorem tailTrace_1422809 : CollatzResearch.WordTrace tailWord_1422809 prefixEnd_1422809 162352199231784219320917 := by
  unfold tailWord_1422809
  simp only [CollatzResearch.WordTrace]
  refine ⟨51894107502413464276375481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34596071668275642850916987 51894107502413464276375481)
  ·
    refine ⟨38920580626810098207281611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51894107502413464276375481 38920580626810098207281611)
    ·
      refine ⟨58380870940215147310922417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38920580626810098207281611 58380870940215147310922417)
      ·
        refine ⟨43785653205161360483191813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58380870940215147310922417 43785653205161360483191813)
        ·
          refine ⟨8209809975967755090598465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43785653205161360483191813 8209809975967755090598465)
          ·
            refine ⟨6157357481975816317948849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209809975967755090598465 6157357481975816317948849)
            ·
              refine ⟨4618018111481862238461637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157357481975816317948849 4618018111481862238461637)
              ·
                refine ⟨865878395902849169711557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4618018111481862238461637 865878395902849169711557)
                ·
                  refine ⟨162352199231784219320917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865878395902849169711557 162352199231784219320917)
                  ·
                    rfl

theorem cell22_1422809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_1422809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422809 prefixEnd_1422809 := by exact prefixLift 1422809
  have htrace : WordTrace (prefixWord ++ tailWord_1422809) baseStart_1422809 baseEnd_1422809 := by
    simpa [prefixWord, tailWord_1422809, baseEnd_1422809] using wordTrace_append hprefix tailTrace_1422809
  have hstable : (prefixWord ++ tailWord_1422809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422809).length < 2 ^ (prefixWord ++ tailWord_1422809).sum := by decide
  have hdescent : baseEnd_1422809 < baseStart_1422809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422897 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1422897 : Nat := 118140960795 + 1422897 * 2 ^ 59
def prefixEnd_1422897 : Nat := 4983230072969 + 3 ^ 40 * 1422897 * 2
def baseEnd_1422897 : Nat := 487086721893749761762481

theorem tailTrace_1422897 : CollatzResearch.WordTrace tailWord_1422897 prefixEnd_1422897 487086721893749761762481 := by
  unfold tailWord_1422897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51897317126094655305578945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34598211417396436870385963 51897317126094655305578945)
  ·
    refine ⟨38922987844570991479184209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51897317126094655305578945 38922987844570991479184209)
    ·
      refine ⟨29192240883428243609388157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38922987844570991479184209 29192240883428243609388157)
      ·
        refine ⟨10947090331285591353520559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29192240883428243609388157 10947090331285591353520559)
        ·
          refine ⟨16420635496928387030280839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947090331285591353520559 16420635496928387030280839)
          ·
            refine ⟨24630953245392580545421259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16420635496928387030280839 24630953245392580545421259)
            ·
              refine ⟨36946429868088870818131889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24630953245392580545421259 36946429868088870818131889)
              ·
                refine ⟨27709822401066653113598917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36946429868088870818131889 27709822401066653113598917)
                ·
                  refine ⟨5195591700199997458799797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27709822401066653113598917 5195591700199997458799797)
                  ·
                    refine ⟨487086721893749761762481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5195591700199997458799797 487086721893749761762481)
                    ·
                      rfl

theorem cell22_1422897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1422897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422897 prefixEnd_1422897 := by exact prefixLift 1422897
  have htrace : WordTrace (prefixWord ++ tailWord_1422897) baseStart_1422897 baseEnd_1422897 := by
    simpa [prefixWord, tailWord_1422897, baseEnd_1422897] using wordTrace_append hprefix tailTrace_1422897
  have hstable : (prefixWord ++ tailWord_1422897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422897).length < 2 ^ (prefixWord ++ tailWord_1422897).sum := by decide
  have hdescent : baseEnd_1422897 < baseStart_1422897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422927 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 6]
def baseStart_1422927 : Nat := 118140960795 + 1422927 * 2 ^ 59
def prefixEnd_1422927 : Nat := 4983230072969 + 3 ^ 40 * 1422927 * 2
def baseEnd_1422927 : Nat := 162365663835613227837463

theorem tailTrace_1422927 : CollatzResearch.WordTrace tailWord_1422927 prefixEnd_1422927 162365663835613227837463 := by
  unfold tailWord_1422927
  simp only [CollatzResearch.WordTrace]
  refine ⟨51898411315985970429171035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34598940877323980286114023 51898411315985970429171035)
  ·
    refine ⟨77847616973978955643756553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51898411315985970429171035 77847616973978955643756553)
    ·
      refine ⟨58385712730484216732817415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77847616973978955643756553 58385712730484216732817415)
      ·
        refine ⟨87578569095726325099226123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58385712730484216732817415 87578569095726325099226123)
        ·
          refine ⟨131367853643589487648839185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87578569095726325099226123 131367853643589487648839185)
          ·
            refine ⟨98525890232692115736629389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131367853643589487648839185 98525890232692115736629389)
            ·
              refine ⟨36947208837259543401236021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98525890232692115736629389 36947208837259543401236021)
              ·
                refine ⟨3463800828493082193865877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36947208837259543401236021 3463800828493082193865877)
                ·
                  refine ⟨162365663835613227837463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3463800828493082193865877 162365663835613227837463)
                  ·
                    rfl

theorem cell22_1422927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_1422927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422927 prefixEnd_1422927 := by exact prefixLift 1422927
  have htrace : WordTrace (prefixWord ++ tailWord_1422927) baseStart_1422927 baseEnd_1422927 := by
    simpa [prefixWord, tailWord_1422927, baseEnd_1422927] using wordTrace_append hprefix tailTrace_1422927
  have hstable : (prefixWord ++ tailWord_1422927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422927).length < 2 ^ (prefixWord ++ tailWord_1422927).sum := by decide
  have hdescent : baseEnd_1422927 < baseStart_1422927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422959 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 4, 3]
def baseStart_1422959 : Nat := 118140960795 + 1422959 * 2 ^ 59
def prefixEnd_1422959 : Nat := 4983230072969 + 3 ^ 40 * 1422959 * 2
def baseEnd_1422959 : Nat := 487107945760802266712291

theorem tailTrace_1422959 : CollatzResearch.WordTrace tailWord_1422959 prefixEnd_1422959 487107945760802266712291 := by
  unfold tailWord_1422959
  simp only [CollatzResearch.WordTrace]
  refine ⟨51899578451870039894335931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34599718967913359929557287 51899578451870039894335931)
  ·
    refine ⟨77849367677805059841503897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51899578451870039894335931 77849367677805059841503897)
    ·
      refine ⟨58387025758353794881127923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77849367677805059841503897 58387025758353794881127923)
      ·
        refine ⟨87580538637530692321691885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58387025758353794881127923 87580538637530692321691885)
        ·
          refine ⟨32842701989074009620634457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87580538637530692321691885 32842701989074009620634457)
          ·
            refine ⟨24632026491805507215475843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32842701989074009620634457 24632026491805507215475843)
            ·
              refine ⟨36948039737708260823213765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24632026491805507215475843 36948039737708260823213765)
              ·
                refine ⟨6927757450820298904352581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36948039737708260823213765 6927757450820298904352581)
                ·
                  refine ⟨1298954522028806044566109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6927757450820298904352581 1298954522028806044566109)
                  ·
                    refine ⟨487107945760802266712291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298954522028806044566109 487107945760802266712291)
                    ·
                      rfl

theorem cell22_1422959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_1422959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1422959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1422959 prefixEnd_1422959 := by exact prefixLift 1422959
  have htrace : WordTrace (prefixWord ++ tailWord_1422959) baseStart_1422959 baseEnd_1422959 := by
    simpa [prefixWord, tailWord_1422959, baseEnd_1422959] using wordTrace_append hprefix tailTrace_1422959
  have hstable : (prefixWord ++ tailWord_1422959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422959).length < 2 ^ (prefixWord ++ tailWord_1422959).sum := by decide
  have hdescent : baseEnd_1422959 < baseStart_1422959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423006 : List Nat := [4, 3, 1, 1, 1, 3, 1, 8]
def baseStart_1423006 : Nat := 118140960795 + 1423006 * 2 ^ 59
def prefixEnd_1423006 : Nat := 4983230072969 + 3 ^ 40 * 1423006 * 2
def baseEnd_1423006 : Nat := 54124892757923312309683

theorem tailTrace_1423006 : CollatzResearch.WordTrace tailWord_1423006 prefixEnd_1423006 54124892757923312309683 := by
  unfold tailWord_1423006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6487661585337470865162109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34600861788466511280864581 6487661585337470865162109)
  ·
    refine ⟨2432873094501551574435791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6487661585337470865162109 2432873094501551574435791)
    ·
      refine ⟨3649309641752327361653687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432873094501551574435791 3649309641752327361653687)
      ·
        refine ⟨5473964462628491042480531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649309641752327361653687 5473964462628491042480531)
        ·
          refine ⟨8210946693942736563720797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473964462628491042480531 8210946693942736563720797)
          ·
            refine ⟨3079105010228526211395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8210946693942736563720797 3079105010228526211395299)
            ·
              refine ⟨4618657515342789317092949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079105010228526211395299 4618657515342789317092949)
              ·
                refine ⟨54124892757923312309683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4618657515342789317092949 54124892757923312309683)
                ·
                  rfl

theorem cell22_1423006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_1423006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423006 prefixEnd_1423006 := by exact prefixLift 1423006
  have htrace : WordTrace (prefixWord ++ tailWord_1423006) baseStart_1423006 baseEnd_1423006 := by
    simpa [prefixWord, tailWord_1423006, baseEnd_1423006] using wordTrace_append hprefix tailTrace_1423006
  have hstable : (prefixWord ++ tailWord_1423006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423006).length < 2 ^ (prefixWord ++ tailWord_1423006).sum := by decide
  have hdescent : baseEnd_1423006 < baseStart_1423006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423034 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1423034 : Nat := 118140960795 + 1423034 * 2 ^ 59
def prefixEnd_1423034 : Nat := 4983230072969 + 3 ^ 40 * 1423034 * 2
def baseEnd_1423034 : Nat := 162377873264509023695687

theorem tailTrace_1423034 : CollatzResearch.WordTrace tailWord_1423034 prefixEnd_1423034 162377873264509023695687 := by
  unfold tailWord_1423034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975578481649581925829039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34601542617732218468877437 12975578481649581925829039)
  ·
    refine ⟨19463367722474372888743559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975578481649581925829039 19463367722474372888743559)
    ·
      refine ⟨29195051583711559333115339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19463367722474372888743559 29195051583711559333115339)
      ·
        refine ⟨43792577375567338999673009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29195051583711559333115339 43792577375567338999673009)
        ·
          refine ⟨32844433031675504249754757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43792577375567338999673009 32844433031675504249754757)
          ·
            refine ⟨6158331193439157046829017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32844433031675504249754757 6158331193439157046829017)
            ·
              refine ⟨4618748395079367785121763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158331193439157046829017 4618748395079367785121763)
              ·
                refine ⟨6928122592619051677682645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618748395079367785121763 6928122592619051677682645)
                ·
                  refine ⟨162377873264509023695687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6928122592619051677682645 162377873264509023695687)
                  ·
                    rfl

theorem cell22_1423034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1423034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423034 prefixEnd_1423034 := by exact prefixLift 1423034
  have htrace : WordTrace (prefixWord ++ tailWord_1423034) baseStart_1423034 baseEnd_1423034 := by
    simpa [prefixWord, tailWord_1423034, baseEnd_1423034] using wordTrace_append hprefix tailTrace_1423034
  have hstable : (prefixWord ++ tailWord_1423034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423034).length < 2 ^ (prefixWord ++ tailWord_1423034).sum := by decide
  have hdescent : baseEnd_1423034 < baseStart_1423034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423038 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1423038 : Nat := 118140960795 + 1423038 * 2 ^ 59
def prefixEnd_1423038 : Nat := 4983230072969 + 3 ^ 40 * 1423038 * 2
def baseEnd_1423038 : Nat := 487134989075272393987049

theorem tailTrace_1423038 : CollatzResearch.WordTrace tailWord_1423038 prefixEnd_1423038 487134989075272393987049 := by
  unfold tailWord_1423038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6487807477322979548307721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34601639879055890924307845 6487807477322979548307721)
  ·
    refine ⟨4865855607992234661230791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6487807477322979548307721 4865855607992234661230791)
    ·
      refine ⟨7298783411988351991846187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865855607992234661230791 7298783411988351991846187)
      ·
        refine ⟨10948175117982527987769281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298783411988351991846187 10948175117982527987769281)
        ·
          refine ⟨8211131338486895990826961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10948175117982527987769281 8211131338486895990826961)
          ·
            refine ⟨6158348503865171993120221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211131338486895990826961 6158348503865171993120221)
            ·
              refine ⟨2309380688949439497420083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6158348503865171993120221 2309380688949439497420083)
              ·
                refine ⟨3464071033424159246130125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309380688949439497420083 3464071033424159246130125)
                ·
                  refine ⟨1299026637534059717298797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3464071033424159246130125 1299026637534059717298797)
                  ·
                    refine ⟨487134989075272393987049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299026637534059717298797 487134989075272393987049)
                    ·
                      rfl

theorem cell22_1423038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1423038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423038 prefixEnd_1423038 := by exact prefixLift 1423038
  have htrace : WordTrace (prefixWord ++ tailWord_1423038) baseStart_1423038 baseEnd_1423038 := by
    simpa [prefixWord, tailWord_1423038, baseEnd_1423038] using wordTrace_append hprefix tailTrace_1423038
  have hstable : (prefixWord ++ tailWord_1423038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423038).length < 2 ^ (prefixWord ++ tailWord_1423038).sum := by decide
  have hdescent : baseEnd_1423038 < baseStart_1423038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423186 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1423186 : Nat := 118140960795 + 1423186 * 2 ^ 59
def prefixEnd_1423186 : Nat := 4983230072969 + 3 ^ 40 * 1423186 * 2
def baseEnd_1423186 : Nat := 162395217499949780428865

theorem tailTrace_1423186 : CollatzResearch.WordTrace tailWord_1423186 prefixEnd_1423186 162395217499949780428865 := by
  unfold tailWord_1423186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976964455511914415712353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34605238548031771775232941 12976964455511914415712353)
  ·
    refine ⟨9732723341633935811784265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12976964455511914415712353 9732723341633935811784265)
    ·
      refine ⟨7299542506225451858838199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9732723341633935811784265 7299542506225451858838199)
      ·
        refine ⟨10949313759338177788257299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7299542506225451858838199 10949313759338177788257299)
        ·
          refine ⟨16423970639007266682385949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949313759338177788257299 16423970639007266682385949)
          ·
            refine ⟨6158988989627725005894731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16423970639007266682385949 6158988989627725005894731)
            ·
              refine ⟨9238483484441587508842097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158988989627725005894731 9238483484441587508842097)
              ·
                refine ⟨6928862613331190631631573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9238483484441587508842097 6928862613331190631631573)
                ·
                  refine ⟨162395217499949780428865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6928862613331190631631573 162395217499949780428865)
                  ·
                    rfl

theorem cell22_1423186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1423186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423186 prefixEnd_1423186 := by exact prefixLift 1423186
  have htrace : WordTrace (prefixWord ++ tailWord_1423186) baseStart_1423186 baseEnd_1423186 := by
    simpa [prefixWord, tailWord_1423186, baseEnd_1423186] using wordTrace_append hprefix tailTrace_1423186
  have hstable : (prefixWord ++ tailWord_1423186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423186).length < 2 ^ (prefixWord ++ tailWord_1423186).sum := by decide
  have hdescent : baseEnd_1423186 < baseStart_1423186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423207 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1423207 : Nat := 118140960795 + 1423207 * 2 ^ 59
def prefixEnd_1423207 : Nat := 4983230072969 + 3 ^ 40 * 1423207 * 2
def baseEnd_1423207 : Nat := 487192841229012286511531

theorem tailTrace_1423207 : CollatzResearch.WordTrace tailWord_1423207 prefixEnd_1423207 487192841229012286511531 := by
  unfold tailWord_1423207
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908623754971578249363875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34605749169981052166242583 51908623754971578249363875)
  ·
    refine ⟨77862935632457367374045813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51908623754971578249363875 77862935632457367374045813)
    ·
      refine ⟨7299650215542878191316795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77862935632457367374045813 7299650215542878191316795)
      ·
        refine ⟨10949475323314317286975193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7299650215542878191316795 10949475323314317286975193)
        ·
          refine ⟨8212106492485737965231395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10949475323314317286975193 8212106492485737965231395)
          ·
            refine ⟨12318159738728606947847093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212106492485737965231395 12318159738728606947847093)
            ·
              refine ⟨1154827475505806901360665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12318159738728606947847093 1154827475505806901360665)
              ·
                refine ⟨866120606629355176020499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154827475505806901360665 866120606629355176020499)
                ·
                  refine ⟨1299180909944032764030749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866120606629355176020499 1299180909944032764030749)
                  ·
                    refine ⟨487192841229012286511531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299180909944032764030749 487192841229012286511531)
                    ·
                      rfl

theorem cell22_1423207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1423207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423207 prefixEnd_1423207 := by exact prefixLift 1423207
  have htrace : WordTrace (prefixWord ++ tailWord_1423207) baseStart_1423207 baseEnd_1423207 := by
    simpa [prefixWord, tailWord_1423207, baseEnd_1423207] using wordTrace_append hprefix tailTrace_1423207
  have hstable : (prefixWord ++ tailWord_1423207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423207).length < 2 ^ (prefixWord ++ tailWord_1423207).sum := by decide
  have hdescent : baseEnd_1423207 < baseStart_1423207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423216 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_1423216 : Nat := 118140960795 + 1423216 * 2 ^ 59
def prefixEnd_1423216 : Nat := 4983230072969 + 3 ^ 40 * 1423216 * 2
def baseEnd_1423216 : Nat := 487195922112939263036503

theorem tailTrace_1423216 : CollatzResearch.WordTrace tailWord_1423216 prefixEnd_1423216 487195922112939263036503 := by
  unfold tailWord_1423216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954476005969486393220751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34605968007959315190961001 25954476005969486393220751)
  ·
    refine ⟨38931714008954229589831127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25954476005969486393220751 38931714008954229589831127)
    ·
      refine ⟨58397571013431344384746691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38931714008954229589831127 58397571013431344384746691)
      ·
        refine ⟨87596356520147016577120037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58397571013431344384746691 87596356520147016577120037)
        ·
          refine ⟨16424316847527565608210007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87596356520147016577120037 16424316847527565608210007)
          ·
            refine ⟨24636475271291348412315011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16424316847527565608210007 24636475271291348412315011)
            ·
              refine ⟨36954712906937022618472517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24636475271291348412315011 36954712906937022618472517)
              ·
                refine ⟨6929008670050691740963597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36954712906937022618472517 6929008670050691740963597)
                ·
                  refine ⟨2598378251269009402861349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6929008670050691740963597 2598378251269009402861349)
                  ·
                    refine ⟨487195922112939263036503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598378251269009402861349 487195922112939263036503)
                    ·
                      rfl

theorem cell22_1423216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_1423216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423216 prefixEnd_1423216 := by exact prefixLift 1423216
  have htrace : WordTrace (prefixWord ++ tailWord_1423216) baseStart_1423216 baseEnd_1423216 := by
    simpa [prefixWord, tailWord_1423216, baseEnd_1423216] using wordTrace_append hprefix tailTrace_1423216
  have hstable : (prefixWord ++ tailWord_1423216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423216).length < 2 ^ (prefixWord ++ tailWord_1423216).sum := by decide
  have hdescent : baseEnd_1423216 < baseStart_1423216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423254 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1423254 : Nat := 118140960795 + 1423254 * 2 ^ 59
def prefixEnd_1423254 : Nat := 4983230072969 + 3 ^ 40 * 1423254 * 2
def baseEnd_1423254 : Nat := 162402976763173276862129

theorem tailTrace_1423254 : CollatzResearch.WordTrace tailWord_1423254 prefixEnd_1423254 162402976763173276862129 := by
  unfold tailWord_1423254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244396124112581579770301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34606891990534203517549877 3244396124112581579770301)
  ·
    refine ⟨1216648546542218092413863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3244396124112581579770301 1216648546542218092413863)
    ·
      refine ⟨1824972819813327138620795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216648546542218092413863 1824972819813327138620795)
      ·
        refine ⟨2737459229719990707931193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824972819813327138620795 2737459229719990707931193)
        ·
          refine ⟨2053094422289993030948395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737459229719990707931193 2053094422289993030948395)
          ·
            refine ⟨3079641633434989546422593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053094422289993030948395 3079641633434989546422593)
            ·
              refine ⟨2309731225076242159816945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079641633434989546422593 2309731225076242159816945)
              ·
                refine ⟨1732298418807181619862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309731225076242159816945 1732298418807181619862709)
                ·
                  refine ⟨162402976763173276862129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1732298418807181619862709 162402976763173276862129)
                  ·
                    rfl

theorem cell22_1423254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1423254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423254 prefixEnd_1423254 := by exact prefixLift 1423254
  have htrace : WordTrace (prefixWord ++ tailWord_1423254) baseStart_1423254 baseEnd_1423254 := by
    simpa [prefixWord, tailWord_1423254, baseEnd_1423254] using wordTrace_append hprefix tailTrace_1423254
  have hstable : (prefixWord ++ tailWord_1423254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423254).length < 2 ^ (prefixWord ++ tailWord_1423254).sum := by decide
  have hdescent : baseEnd_1423254 < baseStart_1423254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423314 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1423314 : Nat := 118140960795 + 1423314 * 2 ^ 59
def prefixEnd_1423314 : Nat := 4983230072969 + 3 ^ 40 * 1423314 * 2
def baseEnd_1423314 : Nat := 487229469515699674086203

theorem tailTrace_1423314 : CollatzResearch.WordTrace tailWord_1423314 prefixEnd_1423314 487229469515699674086203 := by
  unfold tailWord_1423314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12978131591395983880877249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34608350910389290349005997 12978131591395983880877249)
  ·
    refine ⟨9733598693546987910657937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12978131591395983880877249 9733598693546987910657937)
    ·
      refine ⟨7300199020160240932993453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9733598693546987910657937 7300199020160240932993453)
      ·
        refine ⟨2737574632560090349872545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7300199020160240932993453 2737574632560090349872545)
        ·
          refine ⟨2053180974420067762404409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737574632560090349872545 2053180974420067762404409)
          ·
            refine ⟨1539885730815050821803307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053180974420067762404409 1539885730815050821803307)
            ·
              refine ⟨2309828596222576232704961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539885730815050821803307 2309828596222576232704961)
              ·
                refine ⟨1732371447166932174528721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309828596222576232704961 1732371447166932174528721)
                ·
                  refine ⟨1299278585375199130896541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1732371447166932174528721 1299278585375199130896541)
                  ·
                    refine ⟨487229469515699674086203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299278585375199130896541 487229469515699674086203)
                    ·
                      rfl

theorem cell22_1423314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1423314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423314 prefixEnd_1423314 := by exact prefixLift 1423314
  have htrace : WordTrace (prefixWord ++ tailWord_1423314) baseStart_1423314 baseEnd_1423314 := by
    simpa [prefixWord, tailWord_1423314, baseEnd_1423314] using wordTrace_append hprefix tailTrace_1423314
  have hstable : (prefixWord ++ tailWord_1423314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423314).length < 2 ^ (prefixWord ++ tailWord_1423314).sum := by decide
  have hdescent : baseEnd_1423314 < baseStart_1423314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423351 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1423351 : Nat := 118140960795 + 1423351 * 2 ^ 59
def prefixEnd_1423351 : Nat := 4983230072969 + 3 ^ 40 * 1423351 * 2
def baseEnd_1423351 : Nat := 487242135371843910911089

theorem tailTrace_1423351 : CollatzResearch.WordTrace tailWord_1423351 prefixEnd_1423351 487242135371843910911089 := by
  unfold tailWord_1423351
  simp only [CollatzResearch.WordTrace]
  refine ⟨51913875866449890842605907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34609250577633260561737271 51913875866449890842605907)
  ·
    refine ⟨77870813799674836263908861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51913875866449890842605907 77870813799674836263908861)
    ·
      refine ⟨29201555174878063598965823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77870813799674836263908861 29201555174878063598965823)
      ·
        refine ⟨43802332762317095398448735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201555174878063598965823 43802332762317095398448735)
        ·
          refine ⟨65703499143475643097673103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43802332762317095398448735 65703499143475643097673103)
          ·
            refine ⟨98555248715213464646509655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65703499143475643097673103 98555248715213464646509655)
            ·
              refine ⟨147832873072820196969764483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98555248715213464646509655 147832873072820196969764483)
              ·
                refine ⟨221749309609230295454646725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147832873072820196969764483 221749309609230295454646725)
                ·
                  refine ⟨41577995551730680397746261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221749309609230295454646725 41577995551730680397746261)
                  ·
                    refine ⟨487242135371843910911089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41577995551730680397746261 487242135371843910911089)
                    ·
                      rfl

theorem cell22_1423351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1423351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423351 prefixEnd_1423351 := by exact prefixLift 1423351
  have htrace : WordTrace (prefixWord ++ tailWord_1423351) baseStart_1423351 baseEnd_1423351 := by
    simpa [prefixWord, tailWord_1423351, baseEnd_1423351] using wordTrace_append hprefix tailTrace_1423351
  have hstable : (prefixWord ++ tailWord_1423351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423351).length < 2 ^ (prefixWord ++ tailWord_1423351).sum := by decide
  have hdescent : baseEnd_1423351 < baseStart_1423351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423402 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1423402 : Nat := 118140960795 + 1423402 * 2 ^ 59
def prefixEnd_1423402 : Nat := 4983230072969 + 3 ^ 40 * 1423402 * 2
def baseEnd_1423402 : Nat := 487259593714096777885933

theorem tailTrace_1423402 : CollatzResearch.WordTrace tailWord_1423402 prefixEnd_1423402 487259593714096777885933 := by
  unfold tailWord_1423402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12978933997316281638178115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34610490659510084368474973 12978933997316281638178115)
  ·
    refine ⟨19468400995974422457267173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12978933997316281638178115 19468400995974422457267173)
    ·
      refine ⟨3650325186745204210737595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19468400995974422457267173 3650325186745204210737595)
      ·
        refine ⟨5475487780117806316106393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650325186745204210737595 5475487780117806316106393)
        ·
          refine ⟨4106615835088354737079795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5475487780117806316106393 4106615835088354737079795)
          ·
            refine ⟨6159923752632532105619693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106615835088354737079795 6159923752632532105619693)
            ·
              refine ⟨2309971407237199539607385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6159923752632532105619693 2309971407237199539607385)
              ·
                refine ⟨1732478555427899654705539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309971407237199539607385 1732478555427899654705539)
                ·
                  refine ⟨2598717833141849482058309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732478555427899654705539 2598717833141849482058309)
                  ·
                    refine ⟨487259593714096777885933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598717833141849482058309 487259593714096777885933)
                    ·
                      rfl

theorem cell22_1423402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1423402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423402 prefixEnd_1423402 := by exact prefixLift 1423402
  have htrace : WordTrace (prefixWord ++ tailWord_1423402) baseStart_1423402 baseEnd_1423402 := by
    simpa [prefixWord, tailWord_1423402, baseEnd_1423402] using wordTrace_append hprefix tailTrace_1423402
  have hstable : (prefixWord ++ tailWord_1423402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423402).length < 2 ^ (prefixWord ++ tailWord_1423402).sum := by decide
  have hdescent : baseEnd_1423402 < baseStart_1423402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423413 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1423413 : Nat := 118140960795 + 1423413 * 2 ^ 59
def prefixEnd_1423413 : Nat := 4983230072969 + 3 ^ 40 * 1423413 * 2
def baseEnd_1423413 : Nat := 487263359238896415860899

theorem tailTrace_1423413 : CollatzResearch.WordTrace tailWord_1423413 prefixEnd_1423413 487263359238896415860899 := by
  unfold tailWord_1423413
  simp only [CollatzResearch.WordTrace]
  refine ⟨51916137192225275431362893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34610758128150183620908595 51916137192225275431362893)
  ·
    refine ⟨19468551447084478286761085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51916137192225275431362893 19468551447084478286761085)
    ·
      refine ⟨7300706792656679357535407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19468551447084478286761085 7300706792656679357535407)
      ·
        refine ⟨10951060188985019036303111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7300706792656679357535407 10951060188985019036303111)
        ·
          refine ⟨16426590283477528554454667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10951060188985019036303111 16426590283477528554454667)
          ·
            refine ⟨24639885425216292831682001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426590283477528554454667 24639885425216292831682001)
            ·
              refine ⟨18479914068912219623761501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24639885425216292831682001 18479914068912219623761501)
              ·
                refine ⟨6929967775842082358910563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18479914068912219623761501 6929967775842082358910563)
                ·
                  refine ⟨10394951663763123538365845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929967775842082358910563 10394951663763123538365845)
                  ·
                    refine ⟨487263359238896415860899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10394951663763123538365845 487263359238896415860899)
                    ·
                      rfl

theorem cell22_1423413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1423413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423413 prefixEnd_1423413 := by exact prefixLift 1423413
  have htrace : WordTrace (prefixWord ++ tailWord_1423413) baseStart_1423413 baseEnd_1423413 := by
    simpa [prefixWord, tailWord_1423413, baseEnd_1423413] using wordTrace_append hprefix tailTrace_1423413
  have hstable : (prefixWord ++ tailWord_1423413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423413).length < 2 ^ (prefixWord ++ tailWord_1423413).sum := by decide
  have hdescent : baseEnd_1423413 < baseStart_1423413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423445 : List Nat := [1, 3, 2, 2, 1, 5, 1, 7]
def baseStart_1423445 : Nat := 118140960795 + 1423445 * 2 ^ 59
def prefixEnd_1423445 : Nat := 4983230072969 + 3 ^ 40 * 1423445 * 2
def baseEnd_1423445 : Nat := 54141590388095444340089

theorem tailTrace_1423445 : CollatzResearch.WordTrace tailWord_1423445 prefixEnd_1423445 54141590388095444340089 := by
  unfold tailWord_1423445
  simp only [CollatzResearch.WordTrace]
  refine ⟨51917304328109344896527789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34611536218739563264351859 51917304328109344896527789)
  ·
    refine ⟨19468989123041004336197921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51917304328109344896527789 19468989123041004336197921)
    ·
      refine ⟨14601741842280753252148441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19468989123041004336197921 14601741842280753252148441)
      ·
        refine ⟨10951306381710564939111331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14601741842280753252148441 10951306381710564939111331)
        ·
          refine ⟨16426959572565847408666997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10951306381710564939111331 16426959572565847408666997)
          ·
            refine ⟨1540027459928048194562531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16426959572565847408666997 1540027459928048194562531)
            ·
              refine ⟨2310041189892072291843797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540027459928048194562531 2310041189892072291843797)
              ·
                refine ⟨54141590388095444340089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2310041189892072291843797 54141590388095444340089)
                ·
                  rfl

theorem cell22_1423445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 7].length) (baseStart_1423445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423445 prefixEnd_1423445 := by exact prefixLift 1423445
  have htrace : WordTrace (prefixWord ++ tailWord_1423445) baseStart_1423445 baseEnd_1423445 := by
    simpa [prefixWord, tailWord_1423445, baseEnd_1423445] using wordTrace_append hprefix tailTrace_1423445
  have hstable : (prefixWord ++ tailWord_1423445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423445).length < 2 ^ (prefixWord ++ tailWord_1423445).sum := by decide
  have hdescent : baseEnd_1423445 < baseStart_1423445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423460 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1423460 : Nat := 118140960795 + 1423460 * 2 ^ 59
def prefixEnd_1423460 : Nat := 4983230072969 + 3 ^ 40 * 1423460 * 2
def baseEnd_1423460 : Nat := 487279448299403959935755

theorem tailTrace_1423460 : CollatzResearch.WordTrace tailWord_1423460 prefixEnd_1423460 487279448299403959935755 := by
  unfold tailWord_1423460
  simp only [CollatzResearch.WordTrace]
  refine ⟨25958925711527501229161917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34611900948703334972215889 25958925711527501229161917)
  ·
    refine ⟨9734597141822812960935719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25958925711527501229161917 9734597141822812960935719)
    ·
      refine ⟨14601895712734219441403579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734597141822812960935719 14601895712734219441403579)
      ·
        refine ⟨21902843569101329162105369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601895712734219441403579 21902843569101329162105369)
        ·
          refine ⟨16427132676825996871579027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21902843569101329162105369 16427132676825996871579027)
          ·
            refine ⟨24640699015238995307368541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16427132676825996871579027 24640699015238995307368541)
            ·
              refine ⟨9240262130714623240263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24640699015238995307368541 9240262130714623240263203)
              ·
                refine ⟨13860393196071934860394805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9240262130714623240263203 13860393196071934860394805)
                ·
                  refine ⟨1299411862131743893162013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13860393196071934860394805 1299411862131743893162013)
                  ·
                    refine ⟨487279448299403959935755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299411862131743893162013 487279448299403959935755)
                    ·
                      rfl

theorem cell22_1423460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1423460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423460 prefixEnd_1423460 := by exact prefixLift 1423460
  have htrace : WordTrace (prefixWord ++ tailWord_1423460) baseStart_1423460 baseEnd_1423460 := by
    simpa [prefixWord, tailWord_1423460, baseEnd_1423460] using wordTrace_append hprefix tailTrace_1423460
  have hstable : (prefixWord ++ tailWord_1423460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423460).length < 2 ^ (prefixWord ++ tailWord_1423460).sum := by decide
  have hdescent : baseEnd_1423460 < baseStart_1423460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423473 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 7]
def baseStart_1423473 : Nat := 118140960795 + 1423473 * 2 ^ 59
def prefixEnd_1423473 : Nat := 4983230072969 + 3 ^ 40 * 1423473 * 2
def baseEnd_1423473 : Nat := 162427966155025419786905

theorem tailTrace_1423473 : CollatzResearch.WordTrace tailWord_1423473 prefixEnd_1423473 162427966155025419786905 := by
  unfold tailWord_1423473
  simp only [CollatzResearch.WordTrace]
  refine ⟨51918325572007905678547073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34612217048005270452364715 51918325572007905678547073)
  ·
    refine ⟨38938744179005929258910305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51918325572007905678547073 38938744179005929258910305)
    ·
      refine ⟨29204058134254446944182729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38938744179005929258910305 29204058134254446944182729)
      ·
        refine ⟨21903043600690835208137047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29204058134254446944182729 21903043600690835208137047)
        ·
          refine ⟨32854565401036252812205571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21903043600690835208137047 32854565401036252812205571)
          ·
            refine ⟨49281848101554379218308357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32854565401036252812205571 49281848101554379218308357)
            ·
              refine ⟨9240346519041446103432817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49281848101554379218308357 9240346519041446103432817)
              ·
                refine ⟨6930259889281084577574613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9240346519041446103432817 6930259889281084577574613)
                ·
                  refine ⟨162427966155025419786905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6930259889281084577574613 162427966155025419786905)
                  ·
                    rfl

theorem cell22_1423473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_1423473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423473 prefixEnd_1423473 := by exact prefixLift 1423473
  have htrace : WordTrace (prefixWord ++ tailWord_1423473) baseStart_1423473 baseEnd_1423473 := by
    simpa [prefixWord, tailWord_1423473, baseEnd_1423473] using wordTrace_append hprefix tailTrace_1423473
  have hstable : (prefixWord ++ tailWord_1423473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423473).length < 2 ^ (prefixWord ++ tailWord_1423473).sum := by decide
  have hdescent : baseEnd_1423473 < baseStart_1423473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423552 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_1423552 : Nat := 118140960795 + 1423552 * 2 ^ 59
def prefixEnd_1423552 : Nat := 4983230072969 + 3 ^ 40 * 1423552 * 2
def baseEnd_1423552 : Nat := 162436980593182128878491

theorem tailTrace_1423552 : CollatzResearch.WordTrace tailWord_1423552 prefixEnd_1423552 162436980593182128878491 := by
  unfold tailWord_1423552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25960603469360851085336455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34614137959147801447115273 25960603469360851085336455)
  ·
    refine ⟨38940905204041276628004683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25960603469360851085336455 38940905204041276628004683)
    ·
      refine ⟨58411357806061914942007025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38940905204041276628004683 58411357806061914942007025)
      ·
        refine ⟨43808518354546436206505269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58411357806061914942007025 43808518354546436206505269)
        ·
          refine ⟨4107048595738728394359869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43808518354546436206505269 4107048595738728394359869)
          ·
            refine ⟨1540143223402023147884951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4107048595738728394359869 1540143223402023147884951)
            ·
              refine ⟨2310214835103034721827427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540143223402023147884951 2310214835103034721827427)
              ·
                refine ⟨3465322252654552082741141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310214835103034721827427 3465322252654552082741141)
                ·
                  refine ⟨162436980593182128878491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3465322252654552082741141 162436980593182128878491)
                  ·
                    rfl

theorem cell22_1423552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_1423552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423552 prefixEnd_1423552 := by exact prefixLift 1423552
  have htrace : WordTrace (prefixWord ++ tailWord_1423552) baseStart_1423552 baseEnd_1423552 := by
    simpa [prefixWord, tailWord_1423552, baseEnd_1423552] using wordTrace_append hprefix tailTrace_1423552
  have hstable : (prefixWord ++ tailWord_1423552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423552).length < 2 ^ (prefixWord ++ tailWord_1423552).sum := by decide
  have hdescent : baseEnd_1423552 < baseStart_1423552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423567 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 2, 3]
def baseStart_1423567 : Nat := 118140960795 + 1423567 * 2 ^ 59
def prefixEnd_1423567 : Nat := 4983230072969 + 3 ^ 40 * 1423567 * 2
def baseEnd_1423567 : Nat := 487316076586091347510427

theorem tailTrace_1423567 : CollatzResearch.WordTrace tailWord_1423567 prefixEnd_1423567 487316076586091347510427 := by
  unfold tailWord_1423567
  simp only [CollatzResearch.WordTrace]
  refine ⟨51921754033667359732468955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34614502689111573154979303 51921754033667359732468955)
  ·
    refine ⟨77882631050501039598703433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51921754033667359732468955 77882631050501039598703433)
    ·
      refine ⟨58411973287875779699027575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77882631050501039598703433 58411973287875779699027575)
      ·
        refine ⟨87617959931813669548541363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58411973287875779699027575 87617959931813669548541363)
        ·
          refine ⟨131426939897720504322812045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87617959931813669548541363 131426939897720504322812045)
          ·
            refine ⟨49285102461645189121054517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131426939897720504322812045 49285102461645189121054517)
            ·
              refine ⟨4620478355779236480098861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49285102461645189121054517 4620478355779236480098861)
              ·
                refine ⟨1732679383417213680037073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4620478355779236480098861 1732679383417213680037073)
                ·
                  refine ⟨1299509537562910260027805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1732679383417213680037073 1299509537562910260027805)
                  ·
                    refine ⟨487316076586091347510427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299509537562910260027805 487316076586091347510427)
                    ·
                      rfl

theorem cell22_1423567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_1423567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423567 prefixEnd_1423567 := by exact prefixLift 1423567
  have htrace : WordTrace (prefixWord ++ tailWord_1423567) baseStart_1423567 baseEnd_1423567 := by
    simpa [prefixWord, tailWord_1423567, baseEnd_1423567] using wordTrace_append hprefix tailTrace_1423567
  have hstable : (prefixWord ++ tailWord_1423567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423567).length < 2 ^ (prefixWord ++ tailWord_1423567).sum := by decide
  have hdescent : baseEnd_1423567 < baseStart_1423567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423597 : List Nat := [1, 5, 1, 2, 4, 9]
def baseStart_1423597 : Nat := 118140960795 + 1423597 * 2 ^ 59
def prefixEnd_1423597 : Nat := 4983230072969 + 3 ^ 40 * 1423597 * 2
def baseEnd_1423597 : Nat := 6016374644434336657535

theorem tailTrace_1423597 : CollatzResearch.WordTrace tailWord_1423597 prefixEnd_1423597 6016374644434336657535 := by
  unfold tailWord_1423597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51922848223558674856061045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34615232149039116570707363 51922848223558674856061045)
  ·
    refine ⟨4867767020958625767755723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51922848223558674856061045 4867767020958625767755723)
    ·
      refine ⟨7301650531437938651633585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867767020958625767755723 7301650531437938651633585)
      ·
        refine ⟨5476237898578453988725189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7301650531437938651633585 5476237898578453988725189)
        ·
          refine ⟨1026794605983460122885973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5476237898578453988725189 1026794605983460122885973)
          ·
            refine ⟨6016374644434336657535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1026794605983460122885973 6016374644434336657535)
            ·
              rfl

theorem cell22_1423597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 9].length) (baseStart_1423597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423597 prefixEnd_1423597 := by exact prefixLift 1423597
  have htrace : WordTrace (prefixWord ++ tailWord_1423597) baseStart_1423597 baseEnd_1423597 := by
    simpa [prefixWord, tailWord_1423597, baseEnd_1423597] using wordTrace_append hprefix tailTrace_1423597
  have hstable : (prefixWord ++ tailWord_1423597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423597).length < 2 ^ (prefixWord ++ tailWord_1423597).sum := by decide
  have hdescent : baseEnd_1423597 < baseStart_1423597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423610 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1423610 : Nat := 118140960795 + 1423610 * 2 ^ 59
def prefixEnd_1423610 : Nat := 4983230072969 + 3 ^ 40 * 1423610 * 2
def baseEnd_1423610 : Nat := 487330796364853568685295

theorem tailTrace_1423610 : CollatzResearch.WordTrace tailWord_1423610 prefixEnd_1423610 487330796364853568685295 := by
  unfold tailWord_1423610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980830593127894519071071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34615548248341052050856189 12980830593127894519071071)
  ·
    refine ⟨19471245889691841778606607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980830593127894519071071 19471245889691841778606607)
    ·
      refine ⟨29206868834537762667909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19471245889691841778606607 29206868834537762667909911)
      ·
        refine ⟨43810303251806644001864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29206868834537762667909911 43810303251806644001864867)
        ·
          refine ⟨65715454877709966002797301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43810303251806644001864867 65715454877709966002797301)
          ·
            refine ⟨6160823894785309312762247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65715454877709966002797301 6160823894785309312762247)
            ·
              refine ⟨9241235842177963969143371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160823894785309312762247 9241235842177963969143371)
              ·
                refine ⟨13861853763266945953715057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9241235842177963969143371 13861853763266945953715057)
                ·
                  refine ⟨10396390322450209465286293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13861853763266945953715057 10396390322450209465286293)
                  ·
                    refine ⟨487330796364853568685295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10396390322450209465286293 487330796364853568685295)
                    ·
                      rfl

theorem cell22_1423610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1423610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423610 prefixEnd_1423610 := by exact prefixLift 1423610
  have htrace : WordTrace (prefixWord ++ tailWord_1423610) baseStart_1423610 baseEnd_1423610 := by
    simpa [prefixWord, tailWord_1423610, baseEnd_1423610] using wordTrace_append hprefix tailTrace_1423610
  have hstable : (prefixWord ++ tailWord_1423610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423610).length < 2 ^ (prefixWord ++ tailWord_1423610).sum := by decide
  have hdescent : baseEnd_1423610 < baseStart_1423610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423640 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1423640 : Nat := 118140960795 + 1423640 * 2 ^ 59
def prefixEnd_1423640 : Nat := 4983230072969 + 3 ^ 40 * 1423640 * 2
def baseEnd_1423640 : Nat := 487341065977943490435203

theorem tailTrace_1423640 : CollatzResearch.WordTrace tailWord_1423640 prefixEnd_1423640 487341065977943490435203 := by
  unfold tailWord_1423640
  simp only [CollatzResearch.WordTrace]
  refine ⟨25962208281201446599938187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34616277708268595466584249 25962208281201446599938187)
  ·
    refine ⟨38943312421802169899907281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25962208281201446599938187 38943312421802169899907281)
    ·
      refine ⟨29207484316351627424930461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38943312421802169899907281 29207484316351627424930461)
      ·
        refine ⟨10952806618631860284348923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29207484316351627424930461 10952806618631860284348923)
        ·
          refine ⟨16429209927947790426523385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10952806618631860284348923 16429209927947790426523385)
          ·
            refine ⟨12321907445960842819892539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16429209927947790426523385 12321907445960842819892539)
            ·
              refine ⟨18482861168941264229838809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12321907445960842819892539 18482861168941264229838809)
              ·
                refine ⟨13862145876705948172379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18482861168941264229838809 13862145876705948172379107)
                ·
                  refine ⟨20793218815058922258568661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13862145876705948172379107 20793218815058922258568661)
                  ·
                    refine ⟨487341065977943490435203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20793218815058922258568661 487341065977943490435203)
                    ·
                      rfl

theorem cell22_1423640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1423640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423640 prefixEnd_1423640 := by exact prefixLift 1423640
  have htrace : WordTrace (prefixWord ++ tailWord_1423640) baseStart_1423640 baseEnd_1423640 := by
    simpa [prefixWord, tailWord_1423640, baseEnd_1423640] using wordTrace_append hprefix tailTrace_1423640
  have hstable : (prefixWord ++ tailWord_1423640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423640).length < 2 ^ (prefixWord ++ tailWord_1423640).sum := by decide
  have hdescent : baseEnd_1423640 < baseStart_1423640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423717 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1423717 : Nat := 118140960795 + 1423717 * 2 ^ 59
def prefixEnd_1423717 : Nat := 4983230072969 + 3 ^ 40 * 1423717 * 2
def baseEnd_1423717 : Nat := 487367424651540956259967

theorem tailTrace_1423717 : CollatzResearch.WordTrace tailWord_1423717 prefixEnd_1423717 487367424651540956259967 := by
  unfold tailWord_1423717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51927224983123935350429405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34618149988749290233619603 51927224983123935350429405)
  ·
    refine ⟨19472709368671475756411027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51927224983123935350429405 19472709368671475756411027)
    ·
      refine ⟨29209064053007213634616541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19472709368671475756411027 29209064053007213634616541)
      ·
        refine ⟨10953399019877705112981203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29209064053007213634616541 10953399019877705112981203)
        ·
          refine ⟨16430098529816557669471805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10953399019877705112981203 16430098529816557669471805)
          ·
            refine ⟨6161286948681209126051927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16430098529816557669471805 6161286948681209126051927)
            ·
              refine ⟨9241930423021813689077891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161286948681209126051927 9241930423021813689077891)
              ·
                refine ⟨13862895634532720533616837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9241930423021813689077891 13862895634532720533616837)
                ·
                  refine ⟨2599292931474885100053157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13862895634532720533616837 2599292931474885100053157)
                  ·
                    refine ⟨487367424651540956259967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599292931474885100053157 487367424651540956259967)
                    ·
                      rfl

theorem cell22_1423717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1423717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423717 prefixEnd_1423717 := by exact prefixLift 1423717
  have htrace : WordTrace (prefixWord ++ tailWord_1423717) baseStart_1423717 baseEnd_1423717 := by
    simpa [prefixWord, tailWord_1423717, baseEnd_1423717] using wordTrace_append hprefix tailTrace_1423717
  have hstable : (prefixWord ++ tailWord_1423717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423717).length < 2 ^ (prefixWord ++ tailWord_1423717).sum := by decide
  have hdescent : baseEnd_1423717 < baseStart_1423717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423719 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1423719 : Nat := 118140960795 + 1423719 * 2 ^ 59
def prefixEnd_1423719 : Nat := 4983230072969 + 3 ^ 40 * 1423719 * 2
def baseEnd_1423719 : Nat := 487368109292413617709961

theorem tailTrace_1423719 : CollatzResearch.WordTrace tailWord_1423719 prefixEnd_1423719 487368109292413617709961 := by
  unfold tailWord_1423719
  simp only [CollatzResearch.WordTrace]
  refine ⟨51927297929116689692002211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34618198619411126461334807 51927297929116689692002211)
  ·
    refine ⟨77890946893675034538003317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51927297929116689692002211 77890946893675034538003317)
    ·
      refine ⟨7302276271282034487937811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77890946893675034538003317 7302276271282034487937811)
      ·
        refine ⟨10953414406923051731906717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302276271282034487937811 10953414406923051731906717)
        ·
          refine ⟨4107530402596144399465019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10953414406923051731906717 4107530402596144399465019)
          ·
            refine ⟨6161295603894216599197529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107530402596144399465019 6161295603894216599197529)
            ·
              refine ⟨4620971702920662449398147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161295603894216599197529 4620971702920662449398147)
              ·
                refine ⟨6931457554380993674097221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620971702920662449398147 6931457554380993674097221)
                ·
                  refine ⟨1299648291446436313893229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6931457554380993674097221 1299648291446436313893229)
                  ·
                    refine ⟨487368109292413617709961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299648291446436313893229 487368109292413617709961)
                    ·
                      rfl

theorem cell22_1423719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1423719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423719 prefixEnd_1423719 := by exact prefixLift 1423719
  have htrace : WordTrace (prefixWord ++ tailWord_1423719) baseStart_1423719 baseEnd_1423719 := by
    simpa [prefixWord, tailWord_1423719, baseEnd_1423719] using wordTrace_append hprefix tailTrace_1423719
  have hstable : (prefixWord ++ tailWord_1423719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423719).length < 2 ^ (prefixWord ++ tailWord_1423719).sum := by decide
  have hdescent : baseEnd_1423719 < baseStart_1423719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423766 : List Nat := [5, 3, 1, 2, 11]
def baseStart_1423766 : Nat := 118140960795 + 1423766 * 2 ^ 59
def prefixEnd_1423766 : Nat := 4983230072969 + 3 ^ 40 * 1423766 * 2
def baseEnd_1423766 : Nat := 2005696289518194081419

theorem tailTrace_1423766 : CollatzResearch.WordTrace tailWord_1423766 prefixEnd_1423766 2005696289518194081419 := by
  unfold tailWord_1423766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245563259996651044935197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34619341439964277812642101 3245563259996651044935197)
  ·
    refine ⟨1217086222498744141850699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3245563259996651044935197 1217086222498744141850699)
    ·
      refine ⟨1825629333748116212776049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217086222498744141850699 1825629333748116212776049)
      ·
        refine ⟨1369222000311087159582037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825629333748116212776049 1369222000311087159582037)
        ·
          refine ⟨2005696289518194081419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1369222000311087159582037 2005696289518194081419)
          ·
            rfl

theorem cell22_1423766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 11].length) (baseStart_1423766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423766 prefixEnd_1423766 := by exact prefixLift 1423766
  have htrace : WordTrace (prefixWord ++ tailWord_1423766) baseStart_1423766 baseEnd_1423766 := by
    simpa [prefixWord, tailWord_1423766, baseEnd_1423766] using wordTrace_append hprefix tailTrace_1423766
  have hstable : (prefixWord ++ tailWord_1423766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423766).length < 2 ^ (prefixWord ++ tailWord_1423766).sum := by decide
  have hdescent : baseEnd_1423766 < baseStart_1423766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423781 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_1423781 : Nat := 118140960795 + 1423781 * 2 ^ 59
def prefixEnd_1423781 : Nat := 4983230072969 + 3 ^ 40 * 1423781 * 2
def baseEnd_1423781 : Nat := 487389333159466122659771

theorem tailTrace_1423781 : CollatzResearch.WordTrace tailWord_1423781 prefixEnd_1423781 487389333159466122659771 := by
  unfold tailWord_1423781
  simp only [CollatzResearch.WordTrace]
  refine ⟨51929559254892074280759197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34619706169928049520506131 51929559254892074280759197)
  ·
    refine ⟨19473584720584527855284699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51929559254892074280759197 19473584720584527855284699)
    ·
      refine ⟨29210377080876791782927049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19473584720584527855284699 29210377080876791782927049)
      ·
        refine ⟨21907782810657593837195287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29210377080876791782927049 21907782810657593837195287)
        ·
          refine ⟨32861674215986390755792931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907782810657593837195287 32861674215986390755792931)
          ·
            refine ⟨49292511323979586133689397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32861674215986390755792931 49292511323979586133689397)
            ·
              refine ⟨4621172936623086200033381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49292511323979586133689397 4621172936623086200033381)
              ·
                refine ⟨866469925616828662506259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4621172936623086200033381 866469925616828662506259)
                ·
                  refine ⟨1299704888425242993759389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866469925616828662506259 1299704888425242993759389)
                  ·
                    refine ⟨487389333159466122659771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299704888425242993759389 487389333159466122659771)
                    ·
                      rfl

theorem cell22_1423781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_1423781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423781 prefixEnd_1423781 := by exact prefixLift 1423781
  have htrace : WordTrace (prefixWord ++ tailWord_1423781) baseStart_1423781 baseEnd_1423781 := by
    simpa [prefixWord, tailWord_1423781, baseEnd_1423781] using wordTrace_append hprefix tailTrace_1423781
  have hstable : (prefixWord ++ tailWord_1423781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423781).length < 2 ^ (prefixWord ++ tailWord_1423781).sum := by decide
  have hdescent : baseEnd_1423781 < baseStart_1423781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423822 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1423822 : Nat := 118140960795 + 1423822 * 2 ^ 59
def prefixEnd_1423822 : Nat := 4983230072969 + 3 ^ 40 * 1423822 * 2
def baseEnd_1423822 : Nat := 162467789432451894128215

theorem tailTrace_1423822 : CollatzResearch.WordTrace tailWord_1423822 prefixEnd_1423822 162467789432451894128215 := by
  unfold tailWord_1423822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491381830967942285375215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34620703098495692188667813 6491381830967942285375215)
  ·
    refine ⟨9737072746451913428062823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491381830967942285375215 9737072746451913428062823)
    ·
      refine ⟨14605609119677870142094235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737072746451913428062823 14605609119677870142094235)
      ·
        refine ⟨21908413679516805213141353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14605609119677870142094235 21908413679516805213141353)
        ·
          refine ⟨16431310259637603909856015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21908413679516805213141353 16431310259637603909856015)
          ·
            refine ⟨24646965389456405864784023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431310259637603909856015 24646965389456405864784023)
            ·
              refine ⟨36970448084184608797176035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24646965389456405864784023 36970448084184608797176035)
              ·
                refine ⟨55455672126276913195764053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36970448084184608797176035 55455672126276913195764053)
                ·
                  refine ⟨162467789432451894128215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55455672126276913195764053 162467789432451894128215)
                  ·
                    rfl

theorem cell22_1423822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1423822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423822 prefixEnd_1423822 := by exact prefixLift 1423822
  have htrace : WordTrace (prefixWord ++ tailWord_1423822) baseStart_1423822 baseEnd_1423822 := by
    simpa [prefixWord, tailWord_1423822, baseEnd_1423822] using wordTrace_append hprefix tailTrace_1423822
  have hstable : (prefixWord ++ tailWord_1423822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423822).length < 2 ^ (prefixWord ++ tailWord_1423822).sum := by decide
  have hdescent : baseEnd_1423822 < baseStart_1423822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423839 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 6]
def baseStart_1423839 : Nat := 118140960795 + 1423839 * 2 ^ 59
def prefixEnd_1423839 : Nat := 4983230072969 + 3 ^ 40 * 1423839 * 2
def baseEnd_1423839 : Nat := 162469729248257768236531

theorem tailTrace_1423839 : CollatzResearch.WordTrace tailWord_1423839 prefixEnd_1423839 162469729248257768236531 := by
  unfold tailWord_1423839
  simp only [CollatzResearch.WordTrace]
  refine ⟨51931674688681950186370571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34621116459121300124247047 51931674688681950186370571)
  ·
    refine ⟨77897512033022925279555857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51931674688681950186370571 77897512033022925279555857)
    ·
      refine ⟨58423134024767193959666893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77897512033022925279555857 58423134024767193959666893)
      ·
        refine ⟨21908675259287697734875085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58423134024767193959666893 21908675259287697734875085)
        ·
          refine ⟨8215753222232886650578157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21908675259287697734875085 8215753222232886650578157)
          ·
            refine ⟨3080907458337332493966809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8215753222232886650578157 3080907458337332493966809)
            ·
              refine ⟨2310680593752999370475107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080907458337332493966809 2310680593752999370475107)
              ·
                refine ⟨3466020890629499055712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310680593752999370475107 3466020890629499055712661)
                ·
                  refine ⟨162469729248257768236531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3466020890629499055712661 162469729248257768236531)
                  ·
                    rfl

theorem cell22_1423839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_1423839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423839 prefixEnd_1423839 := by exact prefixLift 1423839
  have htrace : WordTrace (prefixWord ++ tailWord_1423839) baseStart_1423839 baseEnd_1423839 := by
    simpa [prefixWord, tailWord_1423839, baseEnd_1423839] using wordTrace_append hprefix tailTrace_1423839
  have hstable : (prefixWord ++ tailWord_1423839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423839).length < 2 ^ (prefixWord ++ tailWord_1423839).sum := by decide
  have hdescent : baseEnd_1423839 < baseStart_1423839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423852 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1423852 : Nat := 118140960795 + 1423852 * 2 ^ 59
def prefixEnd_1423852 : Nat := 4983230072969 + 3 ^ 40 * 1423852 * 2
def baseEnd_1423852 : Nat := 487413637910445604134553

theorem tailTrace_1423852 : CollatzResearch.WordTrace tailWord_1423852 prefixEnd_1423852 487413637910445604134553 := by
  unfold tailWord_1423852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25966074418817426703296905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34621432558423235604395873 25966074418817426703296905)
  ·
    refine ⟨19474555814113070027472679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25966074418817426703296905 19474555814113070027472679)
    ·
      refine ⟨29211833721169605041209019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19474555814113070027472679 29211833721169605041209019)
      ·
        refine ⟨43817750581754407561813529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29211833721169605041209019 43817750581754407561813529)
        ·
          refine ⟨32863312936315805671360147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43817750581754407561813529 32863312936315805671360147)
          ·
            refine ⟨49294969404473708507040221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32863312936315805671360147 49294969404473708507040221)
            ·
              refine ⟨18485613526677640690140083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49294969404473708507040221 18485613526677640690140083)
              ·
                refine ⟨27728420290016461035210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18485613526677640690140083 27728420290016461035210125)
                ·
                  refine ⟨10398157608756172888203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27728420290016461035210125 10398157608756172888203797)
                  ·
                    refine ⟨487413637910445604134553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10398157608756172888203797 487413637910445604134553)
                    ·
                      rfl

theorem cell22_1423852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1423852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423852 prefixEnd_1423852 := by exact prefixLift 1423852
  have htrace : WordTrace (prefixWord ++ tailWord_1423852) baseStart_1423852 baseEnd_1423852 := by
    simpa [prefixWord, tailWord_1423852, baseEnd_1423852] using wordTrace_append hprefix tailTrace_1423852
  have hstable : (prefixWord ++ tailWord_1423852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423852).length < 2 ^ (prefixWord ++ tailWord_1423852).sum := by decide
  have hdescent : baseEnd_1423852 < baseStart_1423852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423858 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1423858 : Nat := 118140960795 + 1423858 * 2 ^ 59
def prefixEnd_1423858 : Nat := 4983230072969 + 3 ^ 40 * 1423858 * 2
def baseEnd_1423858 : Nat := 487415691833063588484535

theorem tailTrace_1423858 : CollatzResearch.WordTrace tailWord_1423858 prefixEnd_1423858 487415691833063588484535 := by
  unfold tailWord_1423858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983091918903279107828057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34621578450408744287541485 12983091918903279107828057)
  ·
    refine ⟨9737318939177459330871043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12983091918903279107828057 9737318939177459330871043)
    ·
      refine ⟨14605978408766188996306565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737318939177459330871043 14605978408766188996306565)
      ·
        refine ⟨2738620951643660436807481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14605978408766188996306565 2738620951643660436807481)
        ·
          refine ⟨2053965713732745327605611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738620951643660436807481 2053965713732745327605611)
          ·
            refine ⟨3080948570599117991408417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053965713732745327605611 3080948570599117991408417)
            ·
              refine ⟨2310711427949338493556313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080948570599117991408417 2310711427949338493556313)
              ·
                refine ⟨1733033570962003870167235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310711427949338493556313 1733033570962003870167235)
                ·
                  refine ⟨2599550356443005805250853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733033570962003870167235 2599550356443005805250853)
                  ·
                    refine ⟨487415691833063588484535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599550356443005805250853 487415691833063588484535)
                    ·
                      rfl

theorem cell22_1423858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1423858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423858 prefixEnd_1423858 := by exact prefixLift 1423858
  have htrace : WordTrace (prefixWord ++ tailWord_1423858) baseStart_1423858 baseEnd_1423858 := by
    simpa [prefixWord, tailWord_1423858, baseEnd_1423858] using wordTrace_append hprefix tailTrace_1423858
  have hstable : (prefixWord ++ tailWord_1423858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423858).length < 2 ^ (prefixWord ++ tailWord_1423858).sum := by decide
  have hdescent : baseEnd_1423858 < baseStart_1423858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423869 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1423869 : Nat := 118140960795 + 1423869 * 2 ^ 59
def prefixEnd_1423869 : Nat := 4983230072969 + 3 ^ 40 * 1423869 * 2
def baseEnd_1423869 : Nat := 487419457357863226459501

theorem tailTrace_1423869 : CollatzResearch.WordTrace tailWord_1423869 prefixEnd_1423869 487419457357863226459501 := by
  unfold tailWord_1423869
  simp only [CollatzResearch.WordTrace]
  refine ⟨51932768878573265309962661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34621845919048843539975107 51932768878573265309962661)
  ·
    refine ⟨9737394164732487245617999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51932768878573265309962661 9737394164732487245617999)
    ·
      refine ⟨14606091247098730868426999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737394164732487245617999 14606091247098730868426999)
      ·
        refine ⟨21909136870648096302640499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606091247098730868426999 21909136870648096302640499)
        ·
          refine ⟨32863705305972144453960749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21909136870648096302640499 32863705305972144453960749)
          ·
            refine ⟨12323889489739554170235281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32863705305972144453960749 12323889489739554170235281)
            ·
              refine ⟨9242917117304665627676461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12323889489739554170235281 9242917117304665627676461)
              ·
                refine ⟨3466093918989249610378673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9242917117304665627676461 3466093918989249610378673)
                ·
                  refine ⟨2599570439241937207784005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466093918989249610378673 2599570439241937207784005)
                  ·
                    refine ⟨487419457357863226459501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599570439241937207784005 487419457357863226459501)
                    ·
                      rfl

theorem cell22_1423869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1423869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423869 prefixEnd_1423869 := by exact prefixLift 1423869
  have htrace : WordTrace (prefixWord ++ tailWord_1423869) baseStart_1423869 baseEnd_1423869 := by
    simpa [prefixWord, tailWord_1423869, baseEnd_1423869] using wordTrace_append hprefix tailTrace_1423869
  have hstable : (prefixWord ++ tailWord_1423869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423869).length < 2 ^ (prefixWord ++ tailWord_1423869).sum := by decide
  have hdescent : baseEnd_1423869 < baseStart_1423869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423873 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 4]
def baseStart_1423873 : Nat := 118140960795 + 1423873 * 2 ^ 59
def prefixEnd_1423873 : Nat := 4983230072969 + 3 ^ 40 * 1423873 * 2
def baseEnd_1423873 : Nat := 162473608879869516453163

theorem tailTrace_1423873 : CollatzResearch.WordTrace tailWord_1423873 prefixEnd_1423873 162473608879869516453163 := by
  unfold tailWord_1423873
  simp only [CollatzResearch.WordTrace]
  refine ⟨51932914770558773993108273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34621943180372515995405515 51932914770558773993108273)
  ·
    refine ⟨38949686077919080494831205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51932914770558773993108273 38949686077919080494831205)
    ·
      refine ⟨7303066139609827592780851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38949686077919080494831205 7303066139609827592780851)
      ·
        refine ⟨10954599209414741389171277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303066139609827592780851 10954599209414741389171277)
        ·
          refine ⟨4107974703530528020939229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954599209414741389171277 4107974703530528020939229)
          ·
            refine ⟨1540490513823948007852211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4107974703530528020939229 1540490513823948007852211)
            ·
              refine ⟨2310735770735922011778317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540490513823948007852211 2310735770735922011778317)
              ·
                refine ⟨866525914025970754416869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310735770735922011778317 866525914025970754416869)
                ·
                  refine ⟨162473608879869516453163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866525914025970754416869 162473608879869516453163)
                  ·
                    rfl

theorem cell22_1423873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_1423873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423873 prefixEnd_1423873 := by exact prefixLift 1423873
  have htrace : WordTrace (prefixWord ++ tailWord_1423873) baseStart_1423873 baseEnd_1423873 := by
    simpa [prefixWord, tailWord_1423873, baseEnd_1423873] using wordTrace_append hprefix tailTrace_1423873
  have hstable : (prefixWord ++ tailWord_1423873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423873).length < 2 ^ (prefixWord ++ tailWord_1423873).sum := by decide
  have hdescent : baseEnd_1423873 < baseStart_1423873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423884 : List Nat := [2, 2, 1, 2, 4, 3, 8]
def baseStart_1423884 : Nat := 118140960795 + 1423884 * 2 ^ 59
def prefixEnd_1423884 : Nat := 4983230072969 + 3 ^ 40 * 1423884 * 2
def baseEnd_1423884 : Nat := 18052762672755858790165

theorem tailTrace_1423884 : CollatzResearch.WordTrace tailWord_1423884 prefixEnd_1423884 18052762672755858790165 := by
  unfold tailWord_1423884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25966657986759461435879353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34622210649012615247839137 25966657986759461435879353)
  ·
    refine ⟨19474993490069596076909515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25966657986759461435879353 19474993490069596076909515)
    ·
      refine ⟨29212490235104394115364273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19474993490069596076909515 29212490235104394115364273)
      ·
        refine ⟨21909367676328295586523205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29212490235104394115364273 21909367676328295586523205)
        ·
          refine ⟨4108006439311555422473101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21909367676328295586523205 4108006439311555422473101)
          ·
            refine ⟨1540502414741833283427413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4108006439311555422473101 1540502414741833283427413)
            ·
              refine ⟨18052762672755858790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1540502414741833283427413 18052762672755858790165)
              ·
                rfl

theorem cell22_1423884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 8].length) (baseStart_1423884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423884 prefixEnd_1423884 := by exact prefixLift 1423884
  have htrace : WordTrace (prefixWord ++ tailWord_1423884) baseStart_1423884 baseEnd_1423884 := by
    simpa [prefixWord, tailWord_1423884, baseEnd_1423884] using wordTrace_append hprefix tailTrace_1423884
  have hstable : (prefixWord ++ tailWord_1423884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423884).length < 2 ^ (prefixWord ++ tailWord_1423884).sum := by decide
  have hdescent : baseEnd_1423884 < baseStart_1423884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423886 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1423886 : Nat := 118140960795 + 1423886 * 2 ^ 59
def prefixEnd_1423886 : Nat := 4983230072969 + 3 ^ 40 * 1423886 * 2
def baseEnd_1423886 : Nat := 487425276805280848784449

theorem tailTrace_1423886 : CollatzResearch.WordTrace tailWord_1423886 prefixEnd_1423886 487425276805280848784449 := by
  unfold tailWord_1423886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491673614938959651666439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34622259279674451475554341 6491673614938959651666439)
  ·
    refine ⟨9737510422408439477499659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491673614938959651666439 9737510422408439477499659)
    ·
      refine ⟨14606265633612659216249489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737510422408439477499659 14606265633612659216249489)
      ·
        refine ⟨10954699225209494412187117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14606265633612659216249489 10954699225209494412187117)
        ·
          refine ⟨4108012209453560404570169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954699225209494412187117 4108012209453560404570169)
          ·
            refine ⟨3081009157090170303427627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108012209453560404570169 3081009157090170303427627)
            ·
              refine ⟨4621513735635255455141441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081009157090170303427627 4621513735635255455141441)
              ·
                refine ⟨3466135301726441591356081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621513735635255455141441 3466135301726441591356081)
                ·
                  refine ⟨2599601476294831193517061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466135301726441591356081 2599601476294831193517061)
                  ·
                    refine ⟨487425276805280848784449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599601476294831193517061 487425276805280848784449)
                    ·
                      rfl

theorem cell22_1423886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1423886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423886 prefixEnd_1423886 := by exact prefixLift 1423886
  have htrace : WordTrace (prefixWord ++ tailWord_1423886) baseStart_1423886 baseEnd_1423886 := by
    simpa [prefixWord, tailWord_1423886, baseEnd_1423886] using wordTrace_append hprefix tailTrace_1423886
  have hstable : (prefixWord ++ tailWord_1423886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423886).length < 2 ^ (prefixWord ++ tailWord_1423886).sum := by decide
  have hdescent : baseEnd_1423886 < baseStart_1423886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423897 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_1423897 : Nat := 118140960795 + 1423897 * 2 ^ 59
def prefixEnd_1423897 : Nat := 4983230072969 + 3 ^ 40 * 1423897 * 2
def baseEnd_1423897 : Nat := 487429042330080486759415

theorem tailTrace_1423897 : CollatzResearch.WordTrace tailWord_1423897 prefixEnd_1423897 487429042330080486759415 := by
  unfold tailWord_1423897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51933790122471826091981945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34622526748314550727987963 51933790122471826091981945)
  ·
    refine ⟨38950342591853869568986459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51933790122471826091981945 38950342591853869568986459)
    ·
      refine ⟨58425513887780804353479689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38950342591853869568986459 58425513887780804353479689)
      ·
        refine ⟨43819135415835603265109767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58425513887780804353479689 43819135415835603265109767)
        ·
          refine ⟨65728703123753404897664651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43819135415835603265109767 65728703123753404897664651)
          ·
            refine ⟨98593054685630107346496977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65728703123753404897664651 98593054685630107346496977)
            ·
              refine ⟨73944791014222580509872733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98593054685630107346496977 73944791014222580509872733)
              ·
                refine ⟨27729296630333467691202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73944791014222580509872733 27729296630333467691202275)
                ·
                  refine ⟨41593944945500201536803413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27729296630333467691202275 41593944945500201536803413)
                  ·
                    refine ⟨487429042330080486759415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41593944945500201536803413 487429042330080486759415)
                    ·
                      rfl

theorem cell22_1423897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_1423897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423897 prefixEnd_1423897 := by exact prefixLift 1423897
  have htrace : WordTrace (prefixWord ++ tailWord_1423897) baseStart_1423897 baseEnd_1423897 := by
    simpa [prefixWord, tailWord_1423897, baseEnd_1423897] using wordTrace_append hprefix tailTrace_1423897
  have hstable : (prefixWord ++ tailWord_1423897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423897).length < 2 ^ (prefixWord ++ tailWord_1423897).sum := by decide
  have hdescent : baseEnd_1423897 < baseStart_1423897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423946 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1423946 : Nat := 118140960795 + 1423946 * 2 ^ 59
def prefixEnd_1423946 : Nat := 4983230072969 + 3 ^ 40 * 1423946 * 2
def baseEnd_1423946 : Nat := 162481938677153564094755

theorem tailTrace_1423946 : CollatzResearch.WordTrace tailWord_1423946 prefixEnd_1423946 162481938677153564094755 := by
  unfold tailWord_1423946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983894324823576865128923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34623718199529538307010461 12983894324823576865128923)
  ·
    refine ⟨19475841487235365297693385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983894324823576865128923 19475841487235365297693385)
    ·
      refine ⟨14606881115426523973270039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19475841487235365297693385 14606881115426523973270039)
      ·
        refine ⟨21910321673139785959905059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606881115426523973270039 21910321673139785959905059)
        ·
          refine ⟨32865482509709678939857589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21910321673139785959905059 32865482509709678939857589)
          ·
            refine ⟨3081138985285282400611649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32865482509709678939857589 3081138985285282400611649)
            ·
              refine ⟨2310854238963961800458737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081138985285282400611649 2310854238963961800458737)
              ·
                refine ⟨1733140679222971350344053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310854238963961800458737 1733140679222971350344053)
                ·
                  refine ⟨162481938677153564094755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733140679222971350344053 162481938677153564094755)
                  ·
                    rfl

theorem cell22_1423946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1423946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423946 prefixEnd_1423946 := by exact prefixLift 1423946
  have htrace : WordTrace (prefixWord ++ tailWord_1423946) baseStart_1423946 baseEnd_1423946 := by
    simpa [prefixWord, tailWord_1423946, baseEnd_1423946] using wordTrace_append hprefix tailTrace_1423946
  have hstable : (prefixWord ++ tailWord_1423946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423946).length < 2 ^ (prefixWord ++ tailWord_1423946).sum := by decide
  have hdescent : baseEnd_1423946 < baseStart_1423946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423950 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1423950 : Nat := 118140960795 + 1423950 * 2 ^ 59
def prefixEnd_1423950 : Nat := 4983230072969 + 3 ^ 40 * 1423950 * 2
def baseEnd_1423950 : Nat := 487447185313206015184253

theorem tailTrace_1423950 : CollatzResearch.WordTrace tailWord_1423950 prefixEnd_1423950 487447185313206015184253 := by
  unfold tailWord_1423950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491965398909977017957663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34623815460853210762440869 6491965398909977017957663)
  ·
    refine ⟨9737948098364965526936495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491965398909977017957663 9737948098364965526936495)
    ·
      refine ⟨14606922147547448290404743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737948098364965526936495 14606922147547448290404743)
      ·
        refine ⟨21910383221321172435607115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606922147547448290404743 21910383221321172435607115)
        ·
          refine ⟨32865574831981758653410673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21910383221321172435607115 32865574831981758653410673)
          ·
            refine ⟨24649181123986318990058005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32865574831981758653410673 24649181123986318990058005)
            ·
              refine ⟨1155430365186858702658969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24649181123986318990058005 1155430365186858702658969)
              ·
                refine ⟨866572773890144026994227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155430365186858702658969 866572773890144026994227)
                ·
                  refine ⟨1299859160835216040491341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866572773890144026994227 1299859160835216040491341)
                  ·
                    refine ⟨487447185313206015184253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299859160835216040491341 487447185313206015184253)
                    ·
                      rfl

theorem cell22_1423950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1423950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423950 prefixEnd_1423950 := by exact prefixLift 1423950
  have htrace : WordTrace (prefixWord ++ tailWord_1423950) baseStart_1423950 baseEnd_1423950 := by
    simpa [prefixWord, tailWord_1423950, baseEnd_1423950] using wordTrace_append hprefix tailTrace_1423950
  have hstable : (prefixWord ++ tailWord_1423950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423950).length < 2 ^ (prefixWord ++ tailWord_1423950).sum := by decide
  have hdescent : baseEnd_1423950 < baseStart_1423950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423959 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1423959 : Nat := 118140960795 + 1423959 * 2 ^ 59
def prefixEnd_1423959 : Nat := 4983230072969 + 3 ^ 40 * 1423959 * 2
def baseEnd_1423959 : Nat := 487450266197132991709225

theorem tailTrace_1423959 : CollatzResearch.WordTrace tailWord_1423959 prefixEnd_1423959 487450266197132991709225 := by
  unfold tailWord_1423959
  simp only [CollatzResearch.WordTrace]
  refine ⟨51936051448247210680738931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34624034298831473787159287 51936051448247210680738931)
  ·
    refine ⟨77904077172370816021108397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51936051448247210680738931 77904077172370816021108397)
    ·
      refine ⟨29214028939639056007915649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77904077172370816021108397 29214028939639056007915649)
      ·
        refine ⟨21910521704729292005936737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29214028939639056007915649 21910521704729292005936737)
        ·
          refine ⟨16432891278546969004452553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21910521704729292005936737 16432891278546969004452553)
          ·
            refine ⟨12324668458910226753339415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16432891278546969004452553 12324668458910226753339415)
            ·
              refine ⟨18487002688365340130009123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324668458910226753339415 18487002688365340130009123)
              ·
                refine ⟨27730504032548010195013685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18487002688365340130009123 27730504032548010195013685)
                ·
                  refine ⟨2599734753051375955782533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27730504032548010195013685 2599734753051375955782533)
                  ·
                    refine ⟨487450266197132991709225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599734753051375955782533 487450266197132991709225)
                    ·
                      rfl

theorem cell22_1423959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1423959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423959 prefixEnd_1423959 := by exact prefixLift 1423959
  have htrace : WordTrace (prefixWord ++ tailWord_1423959) baseStart_1423959 baseEnd_1423959 := by
    simpa [prefixWord, tailWord_1423959, baseEnd_1423959] using wordTrace_append hprefix tailTrace_1423959
  have hstable : (prefixWord ++ tailWord_1423959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423959).length < 2 ^ (prefixWord ++ tailWord_1423959).sum := by decide
  have hdescent : baseEnd_1423959 < baseStart_1423959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423991 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 4]
def baseStart_1423991 : Nat := 118140960795 + 1423991 * 2 ^ 59
def prefixEnd_1423991 : Nat := 4983230072969 + 3 ^ 40 * 1423991 * 2
def baseEnd_1423991 : Nat := 162487073483698524969709

theorem tailTrace_1423991 : CollatzResearch.WordTrace tailWord_1423991 prefixEnd_1423991 162487073483698524969709 := by
  unfold tailWord_1423991
  simp only [CollatzResearch.WordTrace]
  refine ⟨51937218584131280145903827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34624812389420853430602551 51937218584131280145903827)
  ·
    refine ⟨77905827876196920218855741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51937218584131280145903827 77905827876196920218855741)
    ·
      refine ⟨29214685453573845082070903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77905827876196920218855741 29214685453573845082070903)
      ·
        refine ⟨43822028180360767623106355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29214685453573845082070903 43822028180360767623106355)
        ·
          refine ⟨65733042270541151434659533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43822028180360767623106355 65733042270541151434659533)
          ·
            refine ⟨24649890851452931787997325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65733042270541151434659533 24649890851452931787997325)
            ·
              refine ⟨9243709069294849420498997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24649890851452931787997325 9243709069294849420498997)
              ·
                refine ⟨866597725246392133171781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9243709069294849420498997 866597725246392133171781)
                ·
                  refine ⟨162487073483698524969709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866597725246392133171781 162487073483698524969709)
                  ·
                    rfl

theorem cell22_1423991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 4].length) (baseStart_1423991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423991 prefixEnd_1423991 := by exact prefixLift 1423991
  have htrace : WordTrace (prefixWord ++ tailWord_1423991) baseStart_1423991 baseEnd_1423991 := by
    simpa [prefixWord, tailWord_1423991, baseEnd_1423991] using wordTrace_append hprefix tailTrace_1423991
  have hstable : (prefixWord ++ tailWord_1423991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423991).length < 2 ^ (prefixWord ++ tailWord_1423991).sum := by decide
  have hdescent : baseEnd_1423991 < baseStart_1423991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423993 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_1423993 : Nat := 118140960795 + 1423993 * 2 ^ 59
def prefixEnd_1423993 : Nat := 4983230072969 + 3 ^ 40 * 1423993 * 2
def baseEnd_1423993 : Nat := 487461905091968236359121

theorem tailTrace_1423993 : CollatzResearch.WordTrace tailWord_1423993 prefixEnd_1423993 487461905091968236359121 := by
  unfold tailWord_1423993
  simp only [CollatzResearch.WordTrace]
  refine ⟨51937291530124034487476633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34624861020082689658317755 51937291530124034487476633)
  ·
    refine ⟨38952968647593025865607475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51937291530124034487476633 38952968647593025865607475)
    ·
      refine ⟨58429452971389538798411213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38952968647593025865607475 58429452971389538798411213)
      ·
        refine ⟨21911044864271077049404205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58429452971389538798411213 21911044864271077049404205)
        ·
          refine ⟨8216641824101653893526577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21911044864271077049404205 8216641824101653893526577)
          ·
            refine ⟨6162481368076240420144933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216641824101653893526577 6162481368076240420144933)
            ·
              refine ⟨1155465256514295078777175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6162481368076240420144933 1155465256514295078777175)
              ·
                refine ⟨1733197884771442618165763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155465256514295078777175 1733197884771442618165763)
                ·
                  refine ⟨2599796827157163927248645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733197884771442618165763 2599796827157163927248645)
                  ·
                    refine ⟨487461905091968236359121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599796827157163927248645 487461905091968236359121)
                    ·
                      rfl

theorem cell22_1423993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_1423993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1423993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1423993 prefixEnd_1423993 := by exact prefixLift 1423993
  have htrace : WordTrace (prefixWord ++ tailWord_1423993) baseStart_1423993 baseEnd_1423993 := by
    simpa [prefixWord, tailWord_1423993, baseEnd_1423993] using wordTrace_append hprefix tailTrace_1423993
  have hstable : (prefixWord ++ tailWord_1423993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423993).length < 2 ^ (prefixWord ++ tailWord_1423993).sum := by decide
  have hdescent : baseEnd_1423993 < baseStart_1423993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424081 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 5]
def baseStart_1424081 : Nat := 118140960795 + 1424081 * 2 ^ 59
def prefixEnd_1424081 : Nat := 4983230072969 + 3 ^ 40 * 1424081 * 2
def baseEnd_1424081 : Nat := 162497343096788446719617

theorem tailTrace_1424081 : CollatzResearch.WordTrace tailWord_1424081 prefixEnd_1424081 162497343096788446719617 := by
  unfold tailWord_1424081
  simp only [CollatzResearch.WordTrace]
  refine ⟨51940501153805225516680097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34627000769203483677786731 51940501153805225516680097)
  ·
    refine ⟨38955375865353919137510073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51940501153805225516680097 38955375865353919137510073)
    ·
      refine ⟨29216531899015439353132555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38955375865353919137510073 29216531899015439353132555)
      ·
        refine ⟨43824797848523159029698833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29216531899015439353132555 43824797848523159029698833)
        ·
          refine ⟨32868598386392369272274125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43824797848523159029698833 32868598386392369272274125)
          ·
            refine ⟨12325724394897138477102797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32868598386392369272274125 12325724394897138477102797)
            ·
              refine ⟨4622146648086426928913549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12325724394897138477102797 4622146648086426928913549)
              ·
                refine ⟨1733304993032410098342581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4622146648086426928913549 1733304993032410098342581)
                ·
                  refine ⟨162497343096788446719617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733304993032410098342581 162497343096788446719617)
                  ·
                    rfl

theorem cell22_1424081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_1424081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424081 prefixEnd_1424081 := by exact prefixLift 1424081
  have htrace : WordTrace (prefixWord ++ tailWord_1424081) baseStart_1424081 baseEnd_1424081 := by
    simpa [prefixWord, tailWord_1424081, baseEnd_1424081] using wordTrace_append hprefix tailTrace_1424081
  have hstable : (prefixWord ++ tailWord_1424081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424081).length < 2 ^ (prefixWord ++ tailWord_1424081).sum := by decide
  have hdescent : baseEnd_1424081 < baseStart_1424081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424160 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_1424160 : Nat := 118140960795 + 1424160 * 2 ^ 59
def prefixEnd_1424160 : Nat := 4983230072969 + 3 ^ 40 * 1424160 * 2
def baseEnd_1424160 : Nat := 162506357534945155811203

theorem tailTrace_1424160 : CollatzResearch.WordTrace tailWord_1424160 prefixEnd_1424160 162506357534945155811203 := by
  unfold tailWord_1424160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971691260259511004402967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34628921680346014672537289 25971691260259511004402967)
  ·
    refine ⟨38957536890389266506604451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25971691260259511004402967 38957536890389266506604451)
    ·
      refine ⟨58436305335583899759906677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38957536890389266506604451 58436305335583899759906677)
      ·
        refine ⟨5478403625210990602491251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58436305335583899759906677 5478403625210990602491251)
        ·
          refine ⟨8217605437816485903736877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5478403625210990602491251 8217605437816485903736877)
          ·
            refine ⟨3081602039181182213901329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8217605437816485903736877 3081602039181182213901329)
            ·
              refine ⟨2311201529385886660425997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081602039181182213901329 2311201529385886660425997)
              ·
                refine ⟨866700573519707497659749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311201529385886660425997 866700573519707497659749)
                ·
                  refine ⟨162506357534945155811203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866700573519707497659749 162506357534945155811203)
                  ·
                    rfl

theorem cell22_1424160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_1424160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424160 prefixEnd_1424160 := by exact prefixLift 1424160
  have htrace : WordTrace (prefixWord ++ tailWord_1424160) baseStart_1424160 baseEnd_1424160 := by
    simpa [prefixWord, tailWord_1424160, baseEnd_1424160] using wordTrace_append hprefix tailTrace_1424160
  have hstable : (prefixWord ++ tailWord_1424160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424160).length < 2 ^ (prefixWord ++ tailWord_1424160).sum := by decide
  have hdescent : baseEnd_1424160 < baseStart_1424160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424162 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1424162 : Nat := 118140960795 + 1424162 * 2 ^ 59
def prefixEnd_1424162 : Nat := 4983230072969 + 3 ^ 40 * 1424162 * 2
def baseEnd_1424162 : Nat := 487519757245708128883603

theorem tailTrace_1424162 : CollatzResearch.WordTrace tailWord_1424162 prefixEnd_1424162 487519757245708128883603 := by
  unfold tailWord_1424162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985863866627944087594685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34628970311007850900252493 12985863866627944087594685)
  ·
    refine ⟨4869698949985479032848007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12985863866627944087594685 4869698949985479032848007)
    ·
      refine ⟨7304548424978218549272011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869698949985479032848007 7304548424978218549272011)
      ·
        refine ⟨10956822637467327823908017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7304548424978218549272011 10956822637467327823908017)
        ·
          refine ⟨8217616978100495867931013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10956822637467327823908017 8217616978100495867931013)
          ·
            refine ⟨1540803183393842975237065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8217616978100495867931013 1540803183393842975237065)
            ·
              refine ⟨1155602387545382231427799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540803183393842975237065 1155602387545382231427799)
              ·
                refine ⟨1733403581318073347141699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155602387545382231427799 1733403581318073347141699)
                ·
                  refine ⟨2600105371977110020712549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733403581318073347141699 2600105371977110020712549)
                  ·
                    refine ⟨487519757245708128883603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600105371977110020712549 487519757245708128883603)
                    ·
                      rfl

theorem cell22_1424162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1424162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424162 prefixEnd_1424162 := by exact prefixLift 1424162
  have htrace : WordTrace (prefixWord ++ tailWord_1424162) baseStart_1424162 baseEnd_1424162 := by
    simpa [prefixWord, tailWord_1424162, baseEnd_1424162] using wordTrace_append hprefix tailTrace_1424162
  have hstable : (prefixWord ++ tailWord_1424162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424162).length < 2 ^ (prefixWord ++ tailWord_1424162).sum := by decide
  have hdescent : baseEnd_1424162 < baseStart_1424162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424205 : List Nat := [1, 6, 1, 2, 2, 1, 1, 8]
def baseStart_1424205 : Nat := 118140960795 + 1424205 * 2 ^ 59
def prefixEnd_1424205 : Nat := 4983230072969 + 3 ^ 40 * 1424205 * 2
def baseEnd_1424205 : Nat := 54170497447163372228719

theorem tailTrace_1424205 : CollatzResearch.WordTrace tailWord_1424205 prefixEnd_1424205 54170497447163372228719 := by
  unfold tailWord_1424205
  simp only [CollatzResearch.WordTrace]
  refine ⟨51945023805355994694194069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34630015870237329796129379 51945023805355994694194069)
  ·
    refine ⟨2434922990876062251290347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51945023805355994694194069 2434922990876062251290347)
    ·
      refine ⟨3652384486314093376935521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434922990876062251290347 3652384486314093376935521)
      ·
        refine ⟨2739288364735570032701641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652384486314093376935521 2739288364735570032701641)
        ·
          refine ⟨2054466273551677524526231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2739288364735570032701641 2054466273551677524526231)
          ·
            refine ⟨3081699410327516286789347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054466273551677524526231 3081699410327516286789347)
            ·
              refine ⟨4622549115491274430184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081699410327516286789347 4622549115491274430184021)
              ·
                refine ⟨54170497447163372228719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4622549115491274430184021 54170497447163372228719)
                ·
                  rfl

theorem cell22_1424205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 8].length) (baseStart_1424205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424205 prefixEnd_1424205 := by exact prefixLift 1424205
  have htrace : WordTrace (prefixWord ++ tailWord_1424205) baseStart_1424205 baseEnd_1424205 := by
    simpa [prefixWord, tailWord_1424205, baseEnd_1424205] using wordTrace_append hprefix tailTrace_1424205
  have hstable : (prefixWord ++ tailWord_1424205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424205).length < 2 ^ (prefixWord ++ tailWord_1424205).sum := by decide
  have hdescent : baseEnd_1424205 < baseStart_1424205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424430 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_1424430 : Nat := 118140960795 + 1424430 * 2 ^ 59
def prefixEnd_1424430 : Nat := 4983230072969 + 3 ^ 40 * 1424430 * 2
def baseEnd_1424430 : Nat := 162537166374214921060927

theorem tailTrace_1424430 : CollatzResearch.WordTrace tailWord_1424430 prefixEnd_1424430 162537166374214921060927 := by
  unfold tailWord_1424430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494153778692607265141843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34635486819693905414089829 6494153778692607265141843)
  ·
    refine ⟨9741230668038910897712765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6494153778692607265141843 9741230668038910897712765)
    ·
      refine ⟨3652961500514591586642287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9741230668038910897712765 3652961500514591586642287)
      ·
        refine ⟨5479442250771887379963431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652961500514591586642287 5479442250771887379963431)
        ·
          refine ⟨8219163376157831069945147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479442250771887379963431 8219163376157831069945147)
          ·
            refine ⟨12328745064236746604917721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219163376157831069945147 12328745064236746604917721)
            ·
              refine ⟨9246558798177559953688291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12328745064236746604917721 9246558798177559953688291)
              ·
                refine ⟨13869838197266339930532437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246558798177559953688291 13869838197266339930532437)
                ·
                  refine ⟨162537166374214921060927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13869838197266339930532437 162537166374214921060927)
                  ·
                    rfl

theorem cell22_1424430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_1424430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424430 prefixEnd_1424430 := by exact prefixLift 1424430
  have htrace : WordTrace (prefixWord ++ tailWord_1424430) baseStart_1424430 baseEnd_1424430 := by
    simpa [prefixWord, tailWord_1424430, baseEnd_1424430] using wordTrace_append hprefix tailTrace_1424430
  have hstable : (prefixWord ++ tailWord_1424430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424430).length < 2 ^ (prefixWord ++ tailWord_1424430).sum := by decide
  have hdescent : baseEnd_1424430 < baseStart_1424430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424445 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1424445 : Nat := 118140960795 + 1424445 * 2 ^ 59
def prefixEnd_1424445 : Nat := 4983230072969 + 3 ^ 40 * 1424445 * 2
def baseEnd_1424445 : Nat := 487616633929189724057735

theorem tailTrace_1424445 : CollatzResearch.WordTrace tailWord_1424445 prefixEnd_1424445 487616633929189724057735 := by
  unfold tailWord_1424445
  simp only [CollatzResearch.WordTrace]
  refine ⟨51953777324486515682930789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34635851549657677121953859 51953777324486515682930789)
  ·
    refine ⟨9741333248341221690549523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51953777324486515682930789 9741333248341221690549523)
    ·
      refine ⟨14611999872511832535824285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741333248341221690549523 14611999872511832535824285)
      ·
        refine ⟨5479499952191937200934107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14611999872511832535824285 5479499952191937200934107)
        ·
          refine ⟨8219249928287905801401161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479499952191937200934107 8219249928287905801401161)
          ·
            refine ⟨6164437446215929351050871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8219249928287905801401161 6164437446215929351050871)
            ·
              refine ⟨9246656169323894026576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164437446215929351050871 9246656169323894026576307)
              ·
                refine ⟨13869984253985841039864461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246656169323894026576307 13869984253985841039864461)
                ·
                  refine ⟨5201244095244690389949173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13869984253985841039864461 5201244095244690389949173)
                  ·
                    refine ⟨487616633929189724057735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5201244095244690389949173 487616633929189724057735)
                    ·
                      rfl

theorem cell22_1424445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1424445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424445 prefixEnd_1424445 := by exact prefixLift 1424445
  have htrace : WordTrace (prefixWord ++ tailWord_1424445) baseStart_1424445 baseEnd_1424445 := by
    simpa [prefixWord, tailWord_1424445, baseEnd_1424445] using wordTrace_append hprefix tailTrace_1424445
  have hstable : (prefixWord ++ tailWord_1424445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424445).length < 2 ^ (prefixWord ++ tailWord_1424445).sum := by decide
  have hdescent : baseEnd_1424445 < baseStart_1424445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424494 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1424494 : Nat := 118140960795 + 1424494 * 2 ^ 59
def prefixEnd_1424494 : Nat := 4983230072969 + 3 ^ 40 * 1424494 * 2
def baseEnd_1424494 : Nat := 487633407630569929582585

theorem tailTrace_1424494 : CollatzResearch.WordTrace tailWord_1424494 prefixEnd_1424494 487633407630569929582585 := by
  unfold tailWord_1424494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494445562663624631433067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34637043000872664700976357 6494445562663624631433067)
  ·
    refine ⟨9741668343995436947149601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6494445562663624631433067 9741668343995436947149601)
    ·
      refine ⟨7306251257996577710362201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9741668343995436947149601 7306251257996577710362201)
      ·
        refine ⟨5479688443497433282771651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7306251257996577710362201 5479688443497433282771651)
        ·
          refine ⟨8219532665246149924157477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479688443497433282771651 8219532665246149924157477)
          ·
            refine ⟨1541162374733653110779527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8219532665246149924157477 1541162374733653110779527)
            ·
              refine ⟨2311743562100479666169291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541162374733653110779527 2311743562100479666169291)
              ·
                refine ⟨3467615343150719499253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311743562100479666169291 3467615343150719499253937)
                ·
                  refine ⟨2600711507363039624440453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467615343150719499253937 2600711507363039624440453)
                  ·
                    refine ⟨487633407630569929582585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600711507363039624440453 487633407630569929582585)
                    ·
                      rfl

theorem cell22_1424494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1424494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424494 prefixEnd_1424494 := by exact prefixLift 1424494
  have htrace : WordTrace (prefixWord ++ tailWord_1424494) baseStart_1424494 baseEnd_1424494 := by
    simpa [prefixWord, tailWord_1424494, baseEnd_1424494] using wordTrace_append hprefix tailTrace_1424494
  have hstable : (prefixWord ++ tailWord_1424494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424494).length < 2 ^ (prefixWord ++ tailWord_1424494).sum := by decide
  have hdescent : baseEnd_1424494 < baseStart_1424494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424567 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 1, 4]
def baseStart_1424567 : Nat := 118140960795 + 1424567 * 2 ^ 59
def prefixEnd_1424567 : Nat := 4983230072969 + 3 ^ 40 * 1424567 * 2
def baseEnd_1424567 : Nat := 487658397022422072507361

theorem tailTrace_1424567 : CollatzResearch.WordTrace tailWord_1424567 prefixEnd_1424567 487658397022422072507361 := by
  unfold tailWord_1424567
  simp only [CollatzResearch.WordTrace]
  refine ⟨51958227030044530518871955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34638818020029687012581303 51958227030044530518871955)
  ·
    refine ⟨77937340545066795778307933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51958227030044530518871955 77937340545066795778307933)
    ·
      refine ⟨29226502704400048416865475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77937340545066795778307933 29226502704400048416865475)
      ·
        refine ⟨43839754056600072625298213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29226502704400048416865475 43839754056600072625298213)
        ·
          refine ⟨8219953885612513617243415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43839754056600072625298213 8219953885612513617243415)
          ·
            refine ⟨12329930828418770425865123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219953885612513617243415 12329930828418770425865123)
            ·
              refine ⟨18494896242628155638797685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12329930828418770425865123 18494896242628155638797685)
              ·
                refine ⟨1733896522746389591137283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18494896242628155638797685 1733896522746389591137283)
                ·
                  refine ⟨2600844784119584386705925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733896522746389591137283 2600844784119584386705925)
                  ·
                    refine ⟨487658397022422072507361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600844784119584386705925 487658397022422072507361)
                    ·
                      rfl

theorem cell22_1424567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_1424567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424567 prefixEnd_1424567 := by exact prefixLift 1424567
  have htrace : WordTrace (prefixWord ++ tailWord_1424567) baseStart_1424567 baseEnd_1424567 := by
    simpa [prefixWord, tailWord_1424567, baseEnd_1424567] using wordTrace_append hprefix tailTrace_1424567
  have hstable : (prefixWord ++ tailWord_1424567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424567).length < 2 ^ (prefixWord ++ tailWord_1424567).sum := by decide
  have hdescent : baseEnd_1424567 < baseStart_1424567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424612 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1424612 : Nat := 118140960795 + 1424612 * 2 ^ 59
def prefixEnd_1424612 : Nat := 4983230072969 + 3 ^ 40 * 1424612 * 2
def baseEnd_1424612 : Nat := 487673801442056955132223

theorem tailTrace_1424612 : CollatzResearch.WordTrace tailWord_1424612 prefixEnd_1424612 487673801442056955132223 := by
  unfold tailWord_1424612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25979934157440751602130045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34639912209921002136173393 25979934157440751602130045)
  ·
    refine ⟨9742475309040281850798767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25979934157440751602130045 9742475309040281850798767)
    ·
      refine ⟨14613712963560422776198151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9742475309040281850798767 14613712963560422776198151)
      ·
        refine ⟨21920569445340634164297227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14613712963560422776198151 21920569445340634164297227)
        ·
          refine ⟨32880854168010951246445841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21920569445340634164297227 32880854168010951246445841)
          ·
            refine ⟨24660640626008213434834381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32880854168010951246445841 24660640626008213434834381)
            ·
              refine ⟨9247740234753080038062893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24660640626008213434834381 9247740234753080038062893)
              ·
                refine ⟨3467902588032405014273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247740234753080038062893 3467902588032405014273585)
                ·
                  refine ⟨2600926941024303760705189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467902588032405014273585 2600926941024303760705189)
                  ·
                    refine ⟨487673801442056955132223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600926941024303760705189 487673801442056955132223)
                    ·
                      rfl

theorem cell22_1424612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1424612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424612 prefixEnd_1424612 := by exact prefixLift 1424612
  have htrace : WordTrace (prefixWord ++ tailWord_1424612) baseStart_1424612 baseEnd_1424612 := by
    simpa [prefixWord, tailWord_1424612, baseEnd_1424612] using wordTrace_append hprefix tailTrace_1424612
  have hstable : (prefixWord ++ tailWord_1424612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424612).length < 2 ^ (prefixWord ++ tailWord_1424612).sum := by decide
  have hdescent : baseEnd_1424612 < baseStart_1424612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424644 : List Nat := [2, 3, 2, 2, 2, 3, 1, 7]
def baseStart_1424644 : Nat := 118140960795 + 1424644 * 2 ^ 59
def prefixEnd_1424644 : Nat := 4983230072969 + 3 ^ 40 * 1424644 * 2
def baseEnd_1424644 : Nat := 54187195077335504259125

theorem tailTrace_1424644 : CollatzResearch.WordTrace tailWord_1424644 prefixEnd_1424644 54187195077335504259125 := by
  unfold tailWord_1424644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980517725382786334712493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34640690300510381779616657 25980517725382786334712493)
  ·
    refine ⟨9742694147018544875517185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25980517725382786334712493 9742694147018544875517185)
    ·
      refine ⟨7307020610263908656637889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9742694147018544875517185 7307020610263908656637889)
      ·
        refine ⟨5480265457697931492478417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7307020610263908656637889 5480265457697931492478417)
        ·
          refine ⟨4110199093273448619358813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5480265457697931492478417 4110199093273448619358813)
          ·
            refine ⟨1541324659977543232259555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4110199093273448619358813 1541324659977543232259555)
            ·
              refine ⟨2311986989966314848389333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541324659977543232259555 2311986989966314848389333)
              ·
                refine ⟨54187195077335504259125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2311986989966314848389333 54187195077335504259125)
                ·
                  rfl

theorem cell22_1424644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_1424644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424644 prefixEnd_1424644 := by exact prefixLift 1424644
  have htrace : WordTrace (prefixWord ++ tailWord_1424644) baseStart_1424644 baseEnd_1424644 := by
    simpa [prefixWord, tailWord_1424644, baseEnd_1424644] using wordTrace_append hprefix tailTrace_1424644
  have hstable : (prefixWord ++ tailWord_1424644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424644).length < 2 ^ (prefixWord ++ tailWord_1424644).sum := by decide
  have hdescent : baseEnd_1424644 < baseStart_1424644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424655 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 11]
def baseStart_1424655 : Nat := 118140960795 + 1424655 * 2 ^ 59
def prefixEnd_1424655 : Nat := 4983230072969 + 3 ^ 40 * 1424655 * 2
def baseEnd_1424655 : Nat := 162562840406939725435697

theorem tailTrace_1424655 : CollatzResearch.WordTrace tailWord_1424655 prefixEnd_1424655 162562840406939725435697 := by
  unfold tailWord_1424655
  simp only [CollatzResearch.WordTrace]
  refine ⟨51961436653725721548075419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34640957769150481032050279 51961436653725721548075419)
  ·
    refine ⟨77942154980588582322113129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51961436653725721548075419 77942154980588582322113129)
    ·
      refine ⟨58456616235441436741584847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77942154980588582322113129 58456616235441436741584847)
      ·
        refine ⟨87684924353162155112377271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58456616235441436741584847 87684924353162155112377271)
        ·
          refine ⟨131527386529743232668565907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87684924353162155112377271 131527386529743232668565907)
          ·
            refine ⟨197291079794614849002848861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131527386529743232668565907 197291079794614849002848861)
            ·
              refine ⟨73984154922980568376068323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197291079794614849002848861 73984154922980568376068323)
              ·
                refine ⟨110976232384470852564102485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73984154922980568376068323 110976232384470852564102485)
                ·
                  refine ⟨162562840406939725435697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 110976232384470852564102485 162562840406939725435697)
                  ·
                    rfl

theorem cell22_1424655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_1424655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424655 prefixEnd_1424655 := by exact prefixLift 1424655
  have htrace : WordTrace (prefixWord ++ tailWord_1424655) baseStart_1424655 baseEnd_1424655 := by
    simpa [prefixWord, tailWord_1424655, baseEnd_1424655] using wordTrace_append hprefix tailTrace_1424655
  have hstable : (prefixWord ++ tailWord_1424655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424655).length < 2 ^ (prefixWord ++ tailWord_1424655).sum := by decide
  have hdescent : baseEnd_1424655 < baseStart_1424655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424689 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 5]
def baseStart_1424689 : Nat := 118140960795 + 1424689 * 2 ^ 59
def prefixEnd_1424689 : Nat := 4983230072969 + 3 ^ 40 * 1424689 * 2
def baseEnd_1424689 : Nat := 162566720038551473652329

theorem tailTrace_1424689 : CollatzResearch.WordTrace tailWord_1424689 prefixEnd_1424689 162566720038551473652329 := by
  unfold tailWord_1424689
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962676735602545354813121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34641784490401696903208747 51962676735602545354813121)
  ·
    refine ⟨38972007551701909016109841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51962676735602545354813121 38972007551701909016109841)
    ·
      refine ⟨29229005663776431762082381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38972007551701909016109841 29229005663776431762082381)
      ·
        refine ⟨10960877123916161910780893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29229005663776431762082381 10960877123916161910780893)
        ·
          refine ⟨4110328921468560716542835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10960877123916161910780893 4110328921468560716542835)
          ·
            refine ⟨6165493382202841074814253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110328921468560716542835 6165493382202841074814253)
            ·
              refine ⟨2312060018326065403055345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6165493382202841074814253 2312060018326065403055345)
              ·
                refine ⟨1734045013744549052291509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312060018326065403055345 1734045013744549052291509)
                ·
                  refine ⟨162566720038551473652329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734045013744549052291509 162566720038551473652329)
                  ·
                    rfl

theorem cell22_1424689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_1424689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424689 prefixEnd_1424689 := by exact prefixLift 1424689
  have htrace : WordTrace (prefixWord ++ tailWord_1424689) baseStart_1424689 baseEnd_1424689 := by
    simpa [prefixWord, tailWord_1424689, baseEnd_1424689] using wordTrace_append hprefix tailTrace_1424689
  have hstable : (prefixWord ++ tailWord_1424689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424689).length < 2 ^ (prefixWord ++ tailWord_1424689).sum := by decide
  have hdescent : baseEnd_1424689 < baseStart_1424689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424751 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 4]
def baseStart_1424751 : Nat := 118140960795 + 1424751 * 2 ^ 59
def prefixEnd_1424751 : Nat := 4983230072969 + 3 ^ 40 * 1424751 * 2
def baseEnd_1424751 : Nat := 162573794660902308635599

theorem tailTrace_1424751 : CollatzResearch.WordTrace tailWord_1424751 prefixEnd_1424751 162573794660902308635599 := by
  unfold tailWord_1424751
  simp only [CollatzResearch.WordTrace]
  refine ⟨51964938061377929943570107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34643292040918619962380071 51964938061377929943570107)
  ·
    refine ⟨77947407092066894915355161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51964938061377929943570107 77947407092066894915355161)
    ·
      refine ⟨58460555319050171186516371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77947407092066894915355161 58460555319050171186516371)
      ·
        refine ⟨87690832978575256779774557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58460555319050171186516371 87690832978575256779774557)
        ·
          refine ⟨32884062366965721292415459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87690832978575256779774557 32884062366965721292415459)
          ·
            refine ⟨49326093550448581938623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32884062366965721292415459 49326093550448581938623189)
            ·
              refine ⟨1156080317588638639186481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49326093550448581938623189 1156080317588638639186481)
              ·
                refine ⟨867060238191478979389861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156080317588638639186481 867060238191478979389861)
                ·
                  refine ⟨162573794660902308635599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867060238191478979389861 162573794660902308635599)
                  ·
                    rfl

theorem cell22_1424751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 4].length) (baseStart_1424751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424751 prefixEnd_1424751 := by exact prefixLift 1424751
  have htrace : WordTrace (prefixWord ++ tailWord_1424751) baseStart_1424751 baseEnd_1424751 := by
    simpa [prefixWord, tailWord_1424751, baseEnd_1424751] using wordTrace_append hprefix tailTrace_1424751
  have hstable : (prefixWord ++ tailWord_1424751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424751).length < 2 ^ (prefixWord ++ tailWord_1424751).sum := by decide
  have hdescent : baseEnd_1424751 < baseStart_1424751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424770 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1424770 : Nat := 118140960795 + 1424770 * 2 ^ 59
def prefixEnd_1424770 : Nat := 4983230072969 + 3 ^ 40 * 1424770 * 2
def baseEnd_1424770 : Nat := 487727888070997209681739

theorem tailTrace_1424770 : CollatzResearch.WordTrace tailWord_1424770 prefixEnd_1424770 487727888070997209681739 := by
  unfold tailWord_1424770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12991407762077274047127941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34643754032206064125674509 12991407762077274047127941)
  ·
    refine ⟨2435888955389488883836489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12991407762077274047127941 2435888955389488883836489)
    ·
      refine ⟨1826916716542116662877367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2435888955389488883836489 1826916716542116662877367)
      ·
        refine ⟨2740375074813174994316051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826916716542116662877367 2740375074813174994316051)
        ·
          refine ⟨4110562612219762491474077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740375074813174994316051 4110562612219762491474077)
          ·
            refine ⟨1541460979582410934302779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4110562612219762491474077 1541460979582410934302779)
            ·
              refine ⟨2312191469373616401454169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541460979582410934302779 2312191469373616401454169)
              ·
                refine ⟨1734143602030212301090627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312191469373616401454169 1734143602030212301090627)
                ·
                  refine ⟨2601215403045318451635941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734143602030212301090627 2601215403045318451635941)
                  ·
                    refine ⟨487727888070997209681739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601215403045318451635941 487727888070997209681739)
                    ·
                      rfl

theorem cell22_1424770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1424770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424770 prefixEnd_1424770 := by exact prefixLift 1424770
  have htrace : WordTrace (prefixWord ++ tailWord_1424770) baseStart_1424770 baseEnd_1424770 := by
    simpa [prefixWord, tailWord_1424770, baseEnd_1424770] using wordTrace_append hprefix tailTrace_1424770
  have hstable : (prefixWord ++ tailWord_1424770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424770).length < 2 ^ (prefixWord ++ tailWord_1424770).sum := by decide
  have hdescent : baseEnd_1424770 < baseStart_1424770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424796 : List Nat := [2, 2, 3, 4, 2, 9]
def baseStart_1424796 : Nat := 118140960795 + 1424796 * 2 ^ 59
def prefixEnd_1424796 : Nat := 4983230072969 + 3 ^ 40 * 1424796 * 2
def baseEnd_1424796 : Nat := 6021441832127676648539

theorem tailTrace_1424796 : CollatzResearch.WordTrace tailWord_1424796 prefixEnd_1424796 6021441832127676648539 := by
  unfold tailWord_1424796
  simp only [CollatzResearch.WordTrace]
  refine ⟨25983289673107451314479121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34644386230809935085972161 25983289673107451314479121)
  ·
    refine ⟨19487467254830588485859341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25983289673107451314479121 19487467254830588485859341)
    ·
      refine ⟨7307800220561470682197253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19487467254830588485859341 7307800220561470682197253)
      ·
        refine ⟨1370212541355275752911985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7307800220561470682197253 1370212541355275752911985)
        ·
          refine ⟨1027659406016456814683989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370212541355275752911985 1027659406016456814683989)
          ·
            refine ⟨6021441832127676648539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1027659406016456814683989 6021441832127676648539)
            ·
              rfl

theorem cell22_1424796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 9].length) (baseStart_1424796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424796 prefixEnd_1424796 := by exact prefixLift 1424796
  have htrace : WordTrace (prefixWord ++ tailWord_1424796) baseStart_1424796 baseEnd_1424796 := by
    simpa [prefixWord, tailWord_1424796, baseEnd_1424796] using wordTrace_append hprefix tailTrace_1424796
  have hstable : (prefixWord ++ tailWord_1424796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424796).length < 2 ^ (prefixWord ++ tailWord_1424796).sum := by decide
  have hdescent : baseEnd_1424796 < baseStart_1424796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424824 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_1424824 : Nat := 118140960795 + 1424824 * 2 ^ 59
def prefixEnd_1424824 : Nat := 4983230072969 + 3 ^ 40 * 1424824 * 2
def baseEnd_1424824 : Nat := 162582124458186356277191

theorem tailTrace_1424824 : CollatzResearch.WordTrace tailWord_1424824 prefixEnd_1424824 162582124458186356277191 := by
  unfold tailWord_1424824
  simp only [CollatzResearch.WordTrace]
  refine ⟨25983800295056731705488763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34645067060075642273985017 25983800295056731705488763)
  ·
    refine ⟨38975700442585097558233145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25983800295056731705488763 38975700442585097558233145)
    ·
      refine ⟨29231775331938823168674859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38975700442585097558233145 29231775331938823168674859)
      ·
        refine ⟨43847662997908234753012289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29231775331938823168674859 43847662997908234753012289)
        ·
          refine ⟨32885747248431176064759217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43847662997908234753012289 32885747248431176064759217)
          ·
            refine ⟨24664310436323382048569413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32885747248431176064759217 24664310436323382048569413)
            ·
              refine ⟨4624558206810634134106765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24664310436323382048569413 4624558206810634134106765)
              ·
                refine ⟨1734209327553987800290037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4624558206810634134106765 1734209327553987800290037)
                ·
                  refine ⟨162582124458186356277191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734209327553987800290037 162582124458186356277191)
                  ·
                    rfl

theorem cell22_1424824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_1424824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424824 prefixEnd_1424824 := by exact prefixLift 1424824
  have htrace : WordTrace (prefixWord ++ tailWord_1424824) baseStart_1424824 baseEnd_1424824 := by
    simpa [prefixWord, tailWord_1424824, baseEnd_1424824] using wordTrace_append hprefix tailTrace_1424824
  have hstable : (prefixWord ++ tailWord_1424824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424824).length < 2 ^ (prefixWord ++ tailWord_1424824).sum := by decide
  have hdescent : baseEnd_1424824 < baseStart_1424824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424828 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1424828 : Nat := 118140960795 + 1424828 * 2 ^ 59
def prefixEnd_1424828 : Nat := 4983230072969 + 3 ^ 40 * 1424828 * 2
def baseEnd_1424828 : Nat := 487747742656304391731561

theorem tailTrace_1424828 : CollatzResearch.WordTrace tailWord_1424828 prefixEnd_1424828 487747742656304391731561 := by
  unfold tailWord_1424828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25983873241049486047061569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34645164321399314729415425 25983873241049486047061569)
  ·
    refine ⟨19487904930787114535296177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25983873241049486047061569 19487904930787114535296177)
    ·
      refine ⟨14615928698090335901472133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19487904930787114535296177 14615928698090335901472133)
      ·
        refine ⟨2740486630891937981526025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14615928698090335901472133 2740486630891937981526025)
        ·
          refine ⟨2055364973168953486144519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740486630891937981526025 2055364973168953486144519)
          ·
            refine ⟨3083047459753430229216779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055364973168953486144519 3083047459753430229216779)
            ·
              refine ⟨4624571189630145343825169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083047459753430229216779 4624571189630145343825169)
              ·
                refine ⟨3468428392222609007868877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624571189630145343825169 3468428392222609007868877)
                ·
                  refine ⟨1300660647083478377950829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3468428392222609007868877 1300660647083478377950829)
                  ·
                    refine ⟨487747742656304391731561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300660647083478377950829 487747742656304391731561)
                    ·
                      rfl

theorem cell22_1424828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1424828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424828 prefixEnd_1424828 := by exact prefixLift 1424828
  have htrace : WordTrace (prefixWord ++ tailWord_1424828) baseStart_1424828 baseEnd_1424828 := by
    simpa [prefixWord, tailWord_1424828, baseEnd_1424828] using wordTrace_append hprefix tailTrace_1424828
  have hstable : (prefixWord ++ tailWord_1424828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424828).length < 2 ^ (prefixWord ++ tailWord_1424828).sum := by decide
  have hdescent : baseEnd_1424828 < baseStart_1424828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424886 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1424886 : Nat := 118140960795 + 1424886 * 2 ^ 59
def prefixEnd_1424886 : Nat := 4983230072969 + 3 ^ 40 * 1424886 * 2
def baseEnd_1424886 : Nat := 162589199080537191260461

theorem tailTrace_1424886 : CollatzResearch.WordTrace tailWord_1424886 prefixEnd_1424886 162589199080537191260461 := by
  unfold tailWord_1424886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248116369743052999983407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34646574610592565333156341 3248116369743052999983407)
  ·
    refine ⟨4872174554614579499975111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248116369743052999983407 4872174554614579499975111)
    ·
      refine ⟨7308261831921869249962667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4872174554614579499975111 7308261831921869249962667)
      ·
        refine ⟨10962392747882803874944001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7308261831921869249962667 10962392747882803874944001)
        ·
          refine ⟨8221794560912102906208001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10962392747882803874944001 8221794560912102906208001)
          ·
            refine ⟨6166345920684077179656001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221794560912102906208001 6166345920684077179656001)
            ·
              refine ⟨4624759440513057884742001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6166345920684077179656001 4624759440513057884742001)
              ·
                refine ⟨3468569580384793413556501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624759440513057884742001 3468569580384793413556501)
                ·
                  refine ⟨162589199080537191260461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3468569580384793413556501 162589199080537191260461)
                  ·
                    rfl

theorem cell22_1424886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1424886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424886 prefixEnd_1424886 := by exact prefixLift 1424886
  have htrace : WordTrace (prefixWord ++ tailWord_1424886) baseStart_1424886 baseEnd_1424886 := by
    simpa [prefixWord, tailWord_1424886, baseEnd_1424886] using wordTrace_append hprefix tailTrace_1424886
  have hstable : (prefixWord ++ tailWord_1424886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424886).length < 2 ^ (prefixWord ++ tailWord_1424886).sum := by decide
  have hdescent : baseEnd_1424886 < baseStart_1424886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424903 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 4]
def baseStart_1424903 : Nat := 118140960795 + 1424903 * 2 ^ 59
def prefixEnd_1424903 : Nat := 4983230072969 + 3 ^ 40 * 1424903 * 2
def baseEnd_1424903 : Nat := 162591138896343065368777

theorem tailTrace_1424903 : CollatzResearch.WordTrace tailWord_1424903 prefixEnd_1424903 162591138896343065368777 := by
  unfold tailWord_1424903
  simp only [CollatzResearch.WordTrace]
  refine ⟨51970481956827259903103363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34646987971218173268735575 51970481956827259903103363)
  ·
    refine ⟨77955722935240889854655045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51970481956827259903103363 77955722935240889854655045)
    ·
      refine ⟨14616698050357666847747821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77955722935240889854655045 14616698050357666847747821)
      ·
        refine ⟨5481261768884125067905433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14616698050357666847747821 5481261768884125067905433)
        ·
          refine ⟨4110946326663093800929075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5481261768884125067905433 4110946326663093800929075)
          ·
            refine ⟨6166419489994640701393613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110946326663093800929075 6166419489994640701393613)
            ·
              refine ⟨2312407308747990263022605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6166419489994640701393613 2312407308747990263022605)
              ·
                refine ⟨867152740780496348633477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2312407308747990263022605 867152740780496348633477)
                ·
                  refine ⟨162591138896343065368777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867152740780496348633477 162591138896343065368777)
                  ·
                    rfl

theorem cell22_1424903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 4].length) (baseStart_1424903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424903 prefixEnd_1424903 := by exact prefixLift 1424903
  have htrace : WordTrace (prefixWord ++ tailWord_1424903) baseStart_1424903 baseEnd_1424903 := by
    simpa [prefixWord, tailWord_1424903, baseEnd_1424903] using wordTrace_append hprefix tailTrace_1424903
  have hstable : (prefixWord ++ tailWord_1424903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424903).length < 2 ^ (prefixWord ++ tailWord_1424903).sum := by decide
  have hdescent : baseEnd_1424903 < baseStart_1424903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424920 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_1424920 : Nat := 118140960795 + 1424920 * 2 ^ 59
def prefixEnd_1424920 : Nat := 4983230072969 + 3 ^ 40 * 1424920 * 2
def baseEnd_1424920 : Nat := 162593078712148939477093

theorem tailTrace_1424920 : CollatzResearch.WordTrace tailWord_1424920 prefixEnd_1424920 162593078712148939477093 := by
  unfold tailWord_1424920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985550998882835903236107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34647401331843781204314809 25985550998882835903236107)
  ·
    refine ⟨38978326498324253854854161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25985550998882835903236107 38978326498324253854854161)
    ·
      refine ⟨29233744873743190391140621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38978326498324253854854161 29233744873743190391140621)
      ·
        refine ⟨10962654327653696396677733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29233744873743190391140621 10962654327653696396677733)
        ·
          refine ⟨2055497686435068074377075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10962654327653696396677733 2055497686435068074377075)
          ·
            refine ⟨3083246529652602111565613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055497686435068074377075 3083246529652602111565613)
            ·
              refine ⟨1156217448619725791837105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3083246529652602111565613 1156217448619725791837105)
              ·
                refine ⟨867163086464794343877829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156217448619725791837105 867163086464794343877829)
                ·
                  refine ⟨162593078712148939477093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867163086464794343877829 162593078712148939477093)
                  ·
                    rfl

theorem cell22_1424920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_1424920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424920 prefixEnd_1424920 := by exact prefixLift 1424920
  have htrace : WordTrace (prefixWord ++ tailWord_1424920) baseStart_1424920 baseEnd_1424920 := by
    simpa [prefixWord, tailWord_1424920, baseEnd_1424920] using wordTrace_append hprefix tailTrace_1424920
  have hstable : (prefixWord ++ tailWord_1424920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424920).length < 2 ^ (prefixWord ++ tailWord_1424920).sum := by decide
  have hdescent : baseEnd_1424920 < baseStart_1424920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424926 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1424926 : Nat := 118140960795 + 1424926 * 2 ^ 59
def prefixEnd_1424926 : Nat := 4983230072969 + 3 ^ 40 * 1424926 * 2
def baseEnd_1424926 : Nat := 162593763353021600927087

theorem tailTrace_1424926 : CollatzResearch.WordTrace tailWord_1424926 prefixEnd_1424926 162593763353021600927087 := by
  unfold tailWord_1424926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496415104467991853898829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34647547223829289887460421 6496415104467991853898829)
  ·
    refine ⟨2436155664175496945212061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6496415104467991853898829 2436155664175496945212061)
    ·
      refine ⟨913558374065811354454523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2436155664175496945212061 913558374065811354454523)
      ·
        refine ⟨1370337561098717031681785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913558374065811354454523 1370337561098717031681785)
        ·
          refine ⟨1027753170824037773761339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370337561098717031681785 1027753170824037773761339)
          ·
            refine ⟨1541629756236056660642009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027753170824037773761339 1541629756236056660642009)
            ·
              refine ⟨1156222317177042495481507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541629756236056660642009 1156222317177042495481507)
              ·
                refine ⟨1734333475765563743222261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156222317177042495481507 1734333475765563743222261)
                ·
                  refine ⟨162593763353021600927087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734333475765563743222261 162593763353021600927087)
                  ·
                    rfl

theorem cell22_1424926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1424926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424926 prefixEnd_1424926 := by exact prefixLift 1424926
  have htrace : WordTrace (prefixWord ++ tailWord_1424926) baseStart_1424926 baseEnd_1424926 := by
    simpa [prefixWord, tailWord_1424926, baseEnd_1424926] using wordTrace_append hprefix tailTrace_1424926
  have hstable : (prefixWord ++ tailWord_1424926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424926).length < 2 ^ (prefixWord ++ tailWord_1424926).sum := by decide
  have hdescent : baseEnd_1424926 < baseStart_1424926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424931 : List Nat := [1, 1, 1, 4, 5, 1, 2, 7]
def baseStart_1424931 : Nat := 118140960795 + 1424931 * 2 ^ 59
def prefixEnd_1424931 : Nat := 4983230072969 + 3 ^ 40 * 1424931 * 2
def baseEnd_1424931 : Nat := 54198111295694050711805

theorem tailTrace_1424931 : CollatzResearch.WordTrace tailWord_1424931 prefixEnd_1424931 54198111295694050711805 := by
  unfold tailWord_1424931
  simp only [CollatzResearch.WordTrace]
  refine ⟨51971503200725820685122647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34647668800483880456748431 51971503200725820685122647)
  ·
    refine ⟨77957254801088731027683971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51971503200725820685122647 77957254801088731027683971)
    ·
      refine ⟨116935882201633096541525957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77957254801088731027683971 116935882201633096541525957)
      ·
        refine ⟨21925477912806205601536117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116935882201633096541525957 21925477912806205601536117)
        ·
          refine ⟨2055513554325581775144011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21925477912806205601536117 2055513554325581775144011)
          ·
            refine ⟨3083270331488372662716017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055513554325581775144011 3083270331488372662716017)
            ·
              refine ⟨2312452748616279497037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083270331488372662716017 2312452748616279497037013)
              ·
                refine ⟨54198111295694050711805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2312452748616279497037013 54198111295694050711805)
                ·
                  rfl

theorem cell22_1424931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 7].length) (baseStart_1424931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424931 prefixEnd_1424931 := by exact prefixLift 1424931
  have htrace : WordTrace (prefixWord ++ tailWord_1424931) baseStart_1424931 baseEnd_1424931 := by
    simpa [prefixWord, tailWord_1424931, baseEnd_1424931] using wordTrace_append hprefix tailTrace_1424931
  have hstable : (prefixWord ++ tailWord_1424931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424931).length < 2 ^ (prefixWord ++ tailWord_1424931).sum := by decide
  have hdescent : baseEnd_1424931 < baseStart_1424931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424946 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1424946 : Nat := 118140960795 + 1424946 * 2 ^ 59
def prefixEnd_1424946 : Nat := 4983230072969 + 3 ^ 40 * 1424946 * 2
def baseEnd_1424946 : Nat := 487788136467791417281199

theorem tailTrace_1424946 : CollatzResearch.WordTrace tailWord_1424946 prefixEnd_1424946 487788136467791417281199 := by
  unfold tailWord_1424946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993012573917869561729673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34648033530447652164612461 12993012573917869561729673)
  ·
    refine ⟨9744759430438402171297255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12993012573917869561729673 9744759430438402171297255)
    ·
      refine ⟨14617139145657603256945883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744759430438402171297255 14617139145657603256945883)
      ·
        refine ⟨21925708718486404885418825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617139145657603256945883 21925708718486404885418825)
        ·
          refine ⟨16444281538864803664064119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21925708718486404885418825 16444281538864803664064119)
          ·
            refine ⟨24666422308297205496096179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16444281538864803664064119 24666422308297205496096179)
            ·
              refine ⟨36999633462445808244144269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24666422308297205496096179 36999633462445808244144269)
              ·
                refine ⟨13874862548417178091554101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36999633462445808244144269 13874862548417178091554101)
                ·
                  refine ⟨1300768363914110446083197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13874862548417178091554101 1300768363914110446083197)
                  ·
                    refine ⟨487788136467791417281199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300768363914110446083197 487788136467791417281199)
                    ·
                      rfl

theorem cell22_1424946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1424946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424946 prefixEnd_1424946 := by exact prefixLift 1424946
  have htrace : WordTrace (prefixWord ++ tailWord_1424946) baseStart_1424946 baseEnd_1424946 := by
    simpa [prefixWord, tailWord_1424946, baseEnd_1424946] using wordTrace_append hprefix tailTrace_1424946
  have hstable : (prefixWord ++ tailWord_1424946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424946).length < 2 ^ (prefixWord ++ tailWord_1424946).sum := by decide
  have hdescent : baseEnd_1424946 < baseStart_1424946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424950 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1424950 : Nat := 118140960795 + 1424950 * 2 ^ 59
def prefixEnd_1424950 : Nat := 4983230072969 + 3 ^ 40 * 1424950 * 2
def baseEnd_1424950 : Nat := 487789505749536740181187

theorem tailTrace_1424950 : CollatzResearch.WordTrace tailWord_1424950 prefixEnd_1424950 487789505749536740181187 := by
  unfold tailWord_1424950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248262261728561683129019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34648130791771324620042869 3248262261728561683129019)
  ·
    refine ⟨4872393392592842524693529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248262261728561683129019 4872393392592842524693529)
    ·
      refine ⟨3654295044444631893520147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4872393392592842524693529 3654295044444631893520147)
      ·
        refine ⟨5481442566666947840280221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654295044444631893520147 5481442566666947840280221)
        ·
          refine ⟨2055540962500105440105083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5481442566666947840280221 2055540962500105440105083)
          ·
            refine ⟨3083311443750158160157625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055540962500105440105083 3083311443750158160157625)
            ·
              refine ⟨2312483582812618620118219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083311443750158160157625 2312483582812618620118219)
              ·
                refine ⟨3468725374218927930177329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312483582812618620118219 3468725374218927930177329)
                ·
                  refine ⟨2601544030664195947632997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468725374218927930177329 2601544030664195947632997)
                  ·
                    refine ⟨487789505749536740181187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601544030664195947632997 487789505749536740181187)
                    ·
                      rfl

theorem cell22_1424950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1424950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424950 prefixEnd_1424950 := by exact prefixLift 1424950
  have htrace : WordTrace (prefixWord ++ tailWord_1424950) baseStart_1424950 baseEnd_1424950 := by
    simpa [prefixWord, tailWord_1424950, baseEnd_1424950] using wordTrace_append hprefix tailTrace_1424950
  have hstable : (prefixWord ++ tailWord_1424950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424950).length < 2 ^ (prefixWord ++ tailWord_1424950).sum := by decide
  have hdescent : baseEnd_1424950 < baseStart_1424950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424976 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_1424976 : Nat := 118140960795 + 1424976 * 2 ^ 59
def prefixEnd_1424976 : Nat := 4983230072969 + 3 ^ 40 * 1424976 * 2
def baseEnd_1424976 : Nat := 162599468693627113010369

theorem tailTrace_1424976 : CollatzResearch.WordTrace tailWord_1424976 prefixEnd_1424976 162599468693627113010369 := by
  unfold tailWord_1424976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986572242781396685255391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34648762990375195580340521 25986572242781396685255391)
  ·
    refine ⟨38979858364172095027883087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25986572242781396685255391 38979858364172095027883087)
    ·
      refine ⟨58469787546258142541824631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38979858364172095027883087 58469787546258142541824631)
      ·
        refine ⟨87704681319387213812736947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58469787546258142541824631 87704681319387213812736947)
        ·
          refine ⟨131557021979080820719105421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87704681319387213812736947 131557021979080820719105421)
          ·
            refine ⟨49333883242155307769664533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131557021979080820719105421 49333883242155307769664533)
            ·
              refine ⟨2312525776976030051703025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49333883242155307769664533 2312525776976030051703025)
              ·
                refine ⟨1734394332732022538777269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312525776976030051703025 1734394332732022538777269)
                ·
                  refine ⟨162599468693627113010369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734394332732022538777269 162599468693627113010369)
                  ·
                    rfl

theorem cell22_1424976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_1424976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424976 prefixEnd_1424976 := by exact prefixLift 1424976
  have htrace : WordTrace (prefixWord ++ tailWord_1424976) baseStart_1424976 baseEnd_1424976 := by
    simpa [prefixWord, tailWord_1424976, baseEnd_1424976] using wordTrace_append hprefix tailTrace_1424976
  have hstable : (prefixWord ++ tailWord_1424976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424976).length < 2 ^ (prefixWord ++ tailWord_1424976).sum := by decide
  have hdescent : baseEnd_1424976 < baseStart_1424976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424980 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1424980 : Nat := 118140960795 + 1424980 * 2 ^ 59
def prefixEnd_1424980 : Nat := 4983230072969 + 3 ^ 40 * 1424980 * 2
def baseEnd_1424980 : Nat := 487799775362626661931095

theorem tailTrace_1424980 : CollatzResearch.WordTrace tailWord_1424980 prefixEnd_1424980 487799775362626661931095 := by
  unfold tailWord_1424980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986645188774151026828197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34648860251698868035770929 25986645188774151026828197)
  ·
    refine ⟨4872495972895153317530287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25986645188774151026828197 4872495972895153317530287)
    ·
      refine ⟨7308743959342729976295431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4872495972895153317530287 7308743959342729976295431)
      ·
        refine ⟨10963115939014094964443147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7308743959342729976295431 10963115939014094964443147)
        ·
          refine ⟨16444673908521142446664721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963115939014094964443147 16444673908521142446664721)
          ·
            refine ⟨12333505431390856834998541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16444673908521142446664721 12333505431390856834998541)
            ·
              refine ⟨4625064536771571313124453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12333505431390856834998541 4625064536771571313124453)
              ·
                refine ⟨867199600644669621210835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4625064536771571313124453 867199600644669621210835)
                ·
                  refine ⟨1300799400967004431816253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867199600644669621210835 1300799400967004431816253)
                  ·
                    refine ⟨487799775362626661931095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300799400967004431816253 487799775362626661931095)
                    ·
                      rfl

theorem cell22_1424980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1424980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424980 prefixEnd_1424980 := by exact prefixLift 1424980
  have htrace : WordTrace (prefixWord ++ tailWord_1424980) baseStart_1424980 baseEnd_1424980 := by
    simpa [prefixWord, tailWord_1424980, baseEnd_1424980] using wordTrace_append hprefix tailTrace_1424980
  have hstable : (prefixWord ++ tailWord_1424980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424980).length < 2 ^ (prefixWord ++ tailWord_1424980).sum := by decide
  have hdescent : baseEnd_1424980 < baseStart_1424980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424982 : List Nat := [5, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1424982 : Nat := 118140960795 + 1424982 * 2 ^ 59
def prefixEnd_1424982 : Nat := 4983230072969 + 3 ^ 40 * 1424982 * 2
def baseEnd_1424982 : Nat := 54200051111499924820121

theorem tailTrace_1424982 : CollatzResearch.WordTrace tailWord_1424982 prefixEnd_1424982 54200051111499924820121 := by
  unfold tailWord_1424982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248335207721316024701825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34648908882360704263486133 3248335207721316024701825)
  ·
    refine ⟨2436251405790987018526369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248335207721316024701825 2436251405790987018526369)
    ·
      refine ⟨1827188554343240263894777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436251405790987018526369 1827188554343240263894777)
      ·
        refine ⟨1370391415757430197921083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1827188554343240263894777 1370391415757430197921083)
        ·
          refine ⟨2055587123636145296881625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370391415757430197921083 2055587123636145296881625)
          ·
            refine ⟨1541690342727108972661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055587123636145296881625 1541690342727108972661219)
            ·
              refine ⟨2312535514090663458991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541690342727108972661219 2312535514090663458991829)
              ·
                refine ⟨54200051111499924820121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2312535514090663458991829 54200051111499924820121)
                ·
                  rfl

theorem cell22_1424982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1424982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1424982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1424982 prefixEnd_1424982 := by exact prefixLift 1424982
  have htrace : WordTrace (prefixWord ++ tailWord_1424982) baseStart_1424982 baseEnd_1424982 := by
    simpa [prefixWord, tailWord_1424982, baseEnd_1424982] using wordTrace_append hprefix tailTrace_1424982
  have hstable : (prefixWord ++ tailWord_1424982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424982).length < 2 ^ (prefixWord ++ tailWord_1424982).sum := by decide
  have hdescent : baseEnd_1424982 < baseStart_1424982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425038 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1425038 : Nat := 118140960795 + 1425038 * 2 ^ 59
def prefixEnd_1425038 : Nat := 4983230072969 + 3 ^ 40 * 1425038 * 2
def baseEnd_1425038 : Nat := 162606543315977947993639

theorem tailTrace_1425038 : CollatzResearch.WordTrace tailWord_1425038 prefixEnd_1425038 162606543315977947993639 := by
  unfold tailWord_1425038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496925726417272244908471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34650270540892118639511845 6496925726417272244908471)
  ·
    refine ⟨9745388589625908367362707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6496925726417272244908471 9745388589625908367362707)
    ·
      refine ⟨14618082884438862551044061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9745388589625908367362707 14618082884438862551044061)
      ·
        refine ⟨5481781081664573456641523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14618082884438862551044061 5481781081664573456641523)
        ·
          refine ⟨8222671622496860184962285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481781081664573456641523 8222671622496860184962285)
          ·
            refine ⟨3083501858436322569360857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8222671622496860184962285 3083501858436322569360857)
            ·
              refine ⟨2312626393827241927020643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083501858436322569360857 2312626393827241927020643)
              ·
                refine ⟨3468939590740862890530965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312626393827241927020643 3468939590740862890530965)
                ·
                  refine ⟨162606543315977947993639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3468939590740862890530965 162606543315977947993639)
                  ·
                    rfl

theorem cell22_1425038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1425038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425038 prefixEnd_1425038 := by exact prefixLift 1425038
  have htrace : WordTrace (prefixWord ++ tailWord_1425038) baseStart_1425038 baseEnd_1425038 := by
    simpa [prefixWord, tailWord_1425038, baseEnd_1425038] using wordTrace_append hprefix tailTrace_1425038
  have hstable : (prefixWord ++ tailWord_1425038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425038).length < 2 ^ (prefixWord ++ tailWord_1425038).sum := by decide
  have hdescent : baseEnd_1425038 < baseStart_1425038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425096 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1425096 : Nat := 118140960795 + 1425096 * 2 ^ 59
def prefixEnd_1425096 : Nat := 4983230072969 + 3 ^ 40 * 1425096 * 2
def baseEnd_1425096 : Nat := 487839484533241026030739

theorem tailTrace_1425096 : CollatzResearch.WordTrace tailWord_1425096 prefixEnd_1425096 487839484533241026030739 := by
  unfold tailWord_1425096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25988760622564026932439571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34651680830085369243252761 25988760622564026932439571)
  ·
    refine ⟨38983140933846040398659357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25988760622564026932439571 38983140933846040398659357)
    ·
      refine ⟨14618677850192265149497259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38983140933846040398659357 14618677850192265149497259)
      ·
        refine ⟨21928016775288397724245889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14618677850192265149497259 21928016775288397724245889)
        ·
          refine ⟨16446012581466298293184417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21928016775288397724245889 16446012581466298293184417)
          ·
            refine ⟨12334509436099723719888313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16446012581466298293184417 12334509436099723719888313)
            ·
              refine ⟨9250882077074792789916235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12334509436099723719888313 9250882077074792789916235)
              ·
                refine ⟨13876323115612189184874353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9250882077074792789916235 13876323115612189184874353)
                ·
                  refine ⟨10407242336709141888655765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13876323115612189184874353 10407242336709141888655765)
                  ·
                    refine ⟨487839484533241026030739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10407242336709141888655765 487839484533241026030739)
                    ·
                      rfl

theorem cell22_1425096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1425096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425096 prefixEnd_1425096 := by exact prefixLift 1425096
  have htrace : WordTrace (prefixWord ++ tailWord_1425096) baseStart_1425096 baseEnd_1425096 := by
    simpa [prefixWord, tailWord_1425096, baseEnd_1425096] using wordTrace_append hprefix tailTrace_1425096
  have hstable : (prefixWord ++ tailWord_1425096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425096).length < 2 ^ (prefixWord ++ tailWord_1425096).sum := by decide
  have hdescent : baseEnd_1425096 < baseStart_1425096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425173 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 6]
def baseStart_1425173 : Nat := 118140960795 + 1425173 * 2 ^ 59
def prefixEnd_1425173 : Nat := 4983230072969 + 3 ^ 40 * 1425173 * 2
def baseEnd_1425173 : Nat := 162621947735612830618501

theorem tailTrace_1425173 : CollatzResearch.WordTrace tailWord_1425173 prefixEnd_1425173 162621947735612830618501 := by
  unfold tailWord_1425173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51980329665849096015432173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34653553110566064010288115 51980329665849096015432173)
  ·
    refine ⟨19492623624693411005787065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51980329665849096015432173 19492623624693411005787065)
    ·
      refine ⟨14619467718520058254340299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19492623624693411005787065 14619467718520058254340299)
      ·
        refine ⟨21929201577780087381510449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14619467718520058254340299 21929201577780087381510449)
        ·
          refine ⟨16446901183335065536132837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21929201577780087381510449 16446901183335065536132837)
          ·
            refine ⟨3083793971875324788024907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16446901183335065536132837 3083793971875324788024907)
            ·
              refine ⟨4625690957812987182037361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083793971875324788024907 4625690957812987182037361)
              ·
                refine ⟨3469268218359740386528021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4625690957812987182037361 3469268218359740386528021)
                ·
                  refine ⟨162621947735612830618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3469268218359740386528021 162621947735612830618501)
                  ·
                    rfl

theorem cell22_1425173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_1425173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425173 prefixEnd_1425173 := by exact prefixLift 1425173
  have htrace : WordTrace (prefixWord ++ tailWord_1425173) baseStart_1425173 baseEnd_1425173 := by
    simpa [prefixWord, tailWord_1425173, baseEnd_1425173] using wordTrace_append hprefix tailTrace_1425173
  have hstable : (prefixWord ++ tailWord_1425173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425173).length < 2 ^ (prefixWord ++ tailWord_1425173).sum := by decide
  have hdescent : baseEnd_1425173 < baseStart_1425173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425192 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1425192 : Nat := 118140960795 + 1425192 * 2 ^ 59
def prefixEnd_1425192 : Nat := 4983230072969 + 3 ^ 40 * 1425192 * 2
def baseEnd_1425192 : Nat := 487872347295128775630445

theorem tailTrace_1425192 : CollatzResearch.WordTrace tailWord_1425192 prefixEnd_1425192 487872347295128775630445 := by
  unfold tailWord_1425192
  simp only [CollatzResearch.WordTrace]
  refine ⟨25990511326390131130186915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34654015101853508173582553 25990511326390131130186915)
  ·
    refine ⟨38985766989585196695280373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25990511326390131130186915 38985766989585196695280373)
    ·
      refine ⟨3654915655273612190182535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38985766989585196695280373 3654915655273612190182535)
      ·
        refine ⟨5482373482910418285273803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654915655273612190182535 5482373482910418285273803)
        ·
          refine ⟨8223560224365627427910705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482373482910418285273803 8223560224365627427910705)
          ·
            refine ⟨6167670168274220570933029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8223560224365627427910705 6167670168274220570933029)
            ·
              refine ⟨1156438156551416357049943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6167670168274220570933029 1156438156551416357049943)
              ·
                refine ⟨1734657234827124535574915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156438156551416357049943 1734657234827124535574915)
                ·
                  refine ⟨2601985852240686803362373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734657234827124535574915 2601985852240686803362373)
                  ·
                    refine ⟨487872347295128775630445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601985852240686803362373 487872347295128775630445)
                    ·
                      rfl

theorem cell22_1425192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1425192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425192 prefixEnd_1425192 := by exact prefixLift 1425192
  have htrace : WordTrace (prefixWord ++ tailWord_1425192) baseStart_1425192 baseEnd_1425192 := by
    simpa [prefixWord, tailWord_1425192, baseEnd_1425192] using wordTrace_append hprefix tailTrace_1425192
  have hstable : (prefixWord ++ tailWord_1425192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425192).length < 2 ^ (prefixWord ++ tailWord_1425192).sum := by decide
  have hdescent : baseEnd_1425192 < baseStart_1425192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425370 : List Nat := [3, 1, 1, 2, 5, 1, 9]
def baseStart_1425370 : Nat := 118140960795 + 1425370 * 2 ^ 59
def prefixEnd_1425370 : Nat := 4983230072969 + 3 ^ 40 * 1425370 * 2
def baseEnd_1425370 : Nat := 18071602975288727580737

theorem tailTrace_1425370 : CollatzResearch.WordTrace tailWord_1425370 prefixEnd_1425370 18071602975288727580737 := by
  unfold tailWord_1425370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12996878711533849665088391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34658343230756932440235709 12996878711533849665088391)
  ·
    refine ⟨19495318067300774497632587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12996878711533849665088391 19495318067300774497632587)
    ·
      refine ⟨29242977100951161746448881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19495318067300774497632587 29242977100951161746448881)
      ·
        refine ⟨21932232825713371309836661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29242977100951161746448881 21932232825713371309836661)
        ·
          refine ⟨2056146827410628560297187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21932232825713371309836661 2056146827410628560297187)
          ·
            refine ⟨3084220241115942840445781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056146827410628560297187 3084220241115942840445781)
            ·
              refine ⟨18071602975288727580737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3084220241115942840445781 18071602975288727580737)
              ·
                rfl

theorem cell22_1425370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 9].length) (baseStart_1425370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425370 prefixEnd_1425370 := by exact prefixLift 1425370
  have htrace : WordTrace (prefixWord ++ tailWord_1425370) baseStart_1425370 baseEnd_1425370 := by
    simpa [prefixWord, tailWord_1425370, baseEnd_1425370] using wordTrace_append hprefix tailTrace_1425370
  have hstable : (prefixWord ++ tailWord_1425370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425370).length < 2 ^ (prefixWord ++ tailWord_1425370).sum := by decide
  have hdescent : baseEnd_1425370 < baseStart_1425370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425415 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 7]
def baseStart_1425415 : Nat := 118140960795 + 1425415 * 2 ^ 59
def prefixEnd_1425415 : Nat := 4983230072969 + 3 ^ 40 * 1425415 * 2
def baseEnd_1425415 : Nat := 162649561584143509101587

theorem tailTrace_1425415 : CollatzResearch.WordTrace tailWord_1425415 prefixEnd_1425415 162649561584143509101587 := by
  unfold tailWord_1425415
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989156130972371345741699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34659437420648247563827799 51989156130972371345741699)
  ·
    refine ⟨77983734196458557018612549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51989156130972371345741699 77983734196458557018612549)
    ·
      refine ⟨14621950161835979440989853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77983734196458557018612549 14621950161835979440989853)
      ·
        refine ⟨5483231310688492290371195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14621950161835979440989853 5483231310688492290371195)
        ·
          refine ⟨8224846966032738435556793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483231310688492290371195 8224846966032738435556793)
          ·
            refine ⟨6168635224524553826667595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224846966032738435556793 6168635224524553826667595)
            ·
              refine ⟨9252952836786830740001393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168635224524553826667595 9252952836786830740001393)
              ·
                refine ⟨6939714627590123055001045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9252952836786830740001393 6939714627590123055001045)
                ·
                  refine ⟨162649561584143509101587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6939714627590123055001045 162649561584143509101587)
                  ·
                    rfl

theorem cell22_1425415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_1425415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425415 prefixEnd_1425415 := by exact prefixLift 1425415
  have htrace : WordTrace (prefixWord ++ tailWord_1425415) baseStart_1425415 baseEnd_1425415 := by
    simpa [prefixWord, tailWord_1425415, baseEnd_1425415] using wordTrace_append hprefix tailTrace_1425415
  have hstable : (prefixWord ++ tailWord_1425415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425415).length < 2 ^ (prefixWord ++ tailWord_1425415).sum := by decide
  have hdescent : baseEnd_1425415 < baseStart_1425415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425421 : List Nat := [1, 7, 1, 2, 1, 2, 8]
def baseStart_1425421 : Nat := 118140960795 + 1425421 * 2 ^ 59
def prefixEnd_1425421 : Nat := 4983230072969 + 3 ^ 40 * 1425421 * 2
def baseEnd_1425421 : Nat := 18072249580557352283509

theorem tailTrace_1425421 : CollatzResearch.WordTrace tailWord_1425421 prefixEnd_1425421 18072249580557352283509 := by
  unfold tailWord_1425421
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989374968950634370460117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34659583312633756246973411 51989374968950634370460117)
  ·
    refine ⟨1218500975834780493057659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51989374968950634370460117 1218500975834780493057659)
    ·
      refine ⟨1827751463752170739586489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218500975834780493057659 1827751463752170739586489)
      ·
        refine ⟨1370813597814128054689867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1827751463752170739586489 1370813597814128054689867)
        ·
          refine ⟨2056220396721192082034801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370813597814128054689867 2056220396721192082034801)
          ·
            refine ⟨1542165297540894061526101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056220396721192082034801 1542165297540894061526101)
            ·
              refine ⟨18072249580557352283509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1542165297540894061526101 18072249580557352283509)
              ·
                rfl

theorem cell22_1425421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 8].length) (baseStart_1425421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425421 prefixEnd_1425421 := by exact prefixLift 1425421
  have htrace : WordTrace (prefixWord ++ tailWord_1425421) baseStart_1425421 baseEnd_1425421 := by
    simpa [prefixWord, tailWord_1425421, baseEnd_1425421] using wordTrace_append hprefix tailTrace_1425421
  have hstable : (prefixWord ++ tailWord_1425421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425421).length < 2 ^ (prefixWord ++ tailWord_1425421).sum := by decide
  have hdescent : baseEnd_1425421 < baseStart_1425421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425477 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 4]
def baseStart_1425477 : Nat := 118140960795 + 1425477 * 2 ^ 59
def prefixEnd_1425477 : Nat := 4983230072969 + 3 ^ 40 * 1425477 * 2
def baseEnd_1425477 : Nat := 162656636206494344084857

theorem tailTrace_1425477 : CollatzResearch.WordTrace tailWord_1425477 prefixEnd_1425477 162656636206494344084857 := by
  unfold tailWord_1425477
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991417456747755934498685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34660944971165170622999123 51991417456747755934498685)
  ·
    refine ⟨19496781546280408475437007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51991417456747755934498685 19496781546280408475437007)
    ·
      refine ⟨29245172319420612713155511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19496781546280408475437007 29245172319420612713155511)
      ·
        refine ⟨43867758479130919069733267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29245172319420612713155511 43867758479130919069733267)
        ·
          refine ⟨65801637718696378604599901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43867758479130919069733267 65801637718696378604599901)
          ·
            refine ⟨24675614144511141976724963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65801637718696378604599901 24675614144511141976724963)
            ·
              refine ⟨37013421216766712965087445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24675614144511141976724963 37013421216766712965087445)
              ·
                refine ⟨867502059767969835119237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37013421216766712965087445 867502059767969835119237)
                ·
                  refine ⟨162656636206494344084857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867502059767969835119237 162656636206494344084857)
                  ·
                    rfl

theorem cell22_1425477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_1425477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425477 prefixEnd_1425477 := by exact prefixLift 1425477
  have htrace : WordTrace (prefixWord ++ tailWord_1425477) baseStart_1425477 baseEnd_1425477 := by
    simpa [prefixWord, tailWord_1425477, baseEnd_1425477] using wordTrace_append hprefix tailTrace_1425477
  have hstable : (prefixWord ++ tailWord_1425477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425477).length < 2 ^ (prefixWord ++ tailWord_1425477).sum := by decide
  have hdescent : baseEnd_1425477 < baseStart_1425477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425479 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 1, 4]
def baseStart_1425479 : Nat := 118140960795 + 1425479 * 2 ^ 59
def prefixEnd_1425479 : Nat := 4983230072969 + 3 ^ 40 * 1425479 * 2
def baseEnd_1425479 : Nat := 487970593260355693704565

theorem tailTrace_1425479 : CollatzResearch.WordTrace tailWord_1425479 prefixEnd_1425479 487970593260355693704565 := by
  unfold tailWord_1425479
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991490402740510276071491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34660993601827006850714327 51991490402740510276071491)
  ·
    refine ⟨77987235604110765414107237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51991490402740510276071491 77987235604110765414107237)
    ·
      refine ⟨14622606675770768515145107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77987235604110765414107237 14622606675770768515145107)
      ·
        refine ⟨21933910013656152772717661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14622606675770768515145107 21933910013656152772717661)
        ·
          refine ⟨8225216255121057289769123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21933910013656152772717661 8225216255121057289769123)
          ·
            refine ⟨12337824382681585934653685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225216255121057289769123 12337824382681585934653685)
            ·
              refine ⟨1156671035876398681373783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12337824382681585934653685 1156671035876398681373783)
              ·
                refine ⟨1735006553814598022060675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156671035876398681373783 1735006553814598022060675)
                ·
                  refine ⟨2602509830721897033091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735006553814598022060675 2602509830721897033091013)
                  ·
                    refine ⟨487970593260355693704565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602509830721897033091013 487970593260355693704565)
                    ·
                      rfl

theorem cell22_1425479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_1425479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425479 prefixEnd_1425479 := by exact prefixLift 1425479
  have htrace : WordTrace (prefixWord ++ tailWord_1425479) baseStart_1425479 baseEnd_1425479 := by
    simpa [prefixWord, tailWord_1425479, baseEnd_1425479] using wordTrace_append hprefix tailTrace_1425479
  have hstable : (prefixWord ++ tailWord_1425479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425479).length < 2 ^ (prefixWord ++ tailWord_1425479).sum := by decide
  have hdescent : baseEnd_1425479 < baseStart_1425479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425509 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_1425509 : Nat := 118140960795 + 1425509 * 2 ^ 59
def prefixEnd_1425509 : Nat := 4983230072969 + 3 ^ 40 * 1425509 * 2
def baseEnd_1425509 : Nat := 487980862873445615454473

theorem tailTrace_1425509 : CollatzResearch.WordTrace tailWord_1425509 prefixEnd_1425509 487980862873445615454473 := by
  unfold tailWord_1425509
  simp only [CollatzResearch.WordTrace]
  refine ⟨51992584592631825399663581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34661723061754550266442387 51992584592631825399663581)
  ·
    refine ⟨19497219222236934524873843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51992584592631825399663581 19497219222236934524873843)
    ·
      refine ⟨29245828833355401787310765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19497219222236934524873843 29245828833355401787310765)
      ·
        refine ⟨10967185812508275670241537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29245828833355401787310765 10967185812508275670241537)
        ·
          refine ⟨8225389359381206752681153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10967185812508275670241537 8225389359381206752681153)
          ·
            refine ⟨6169042019535905064510865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8225389359381206752681153 6169042019535905064510865)
            ·
              refine ⟨4626781514651928798383149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169042019535905064510865 4626781514651928798383149)
              ·
                refine ⟨1735043067994473299393681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4626781514651928798383149 1735043067994473299393681)
                ·
                  refine ⟨1301282300995854974545261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735043067994473299393681 1301282300995854974545261)
                  ·
                    refine ⟨487980862873445615454473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301282300995854974545261 487980862873445615454473)
                    ·
                      rfl

theorem cell22_1425509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_1425509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425509 prefixEnd_1425509 := by exact prefixLift 1425509
  have htrace : WordTrace (prefixWord ++ tailWord_1425509) baseStart_1425509 baseEnd_1425509 := by
    simpa [prefixWord, tailWord_1425509, baseEnd_1425509] using wordTrace_append hprefix tailTrace_1425509
  have hstable : (prefixWord ++ tailWord_1425509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425509).length < 2 ^ (prefixWord ++ tailWord_1425509).sum := by decide
  have hdescent : baseEnd_1425509 < baseStart_1425509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1425597 : Nat := 118140960795 + 1425597 * 2 ^ 59
def prefixEnd_1425597 : Nat := 4983230072969 + 3 ^ 40 * 1425597 * 2
def baseEnd_1425597 : Nat := 488010987071842719254203

theorem tailTrace_1425597 : CollatzResearch.WordTrace tailWord_1425597 prefixEnd_1425597 488010987071842719254203 := by
  unfold tailWord_1425597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51995794216313016428867045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34663862810875344285911363 51995794216313016428867045)
  ·
    refine ⟨9749211415558690580412571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51995794216313016428867045 9749211415558690580412571)
    ·
      refine ⟨14623817123338035870618857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9749211415558690580412571 14623817123338035870618857)
      ·
        refine ⟨10967862842503526902964143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14623817123338035870618857 10967862842503526902964143)
        ·
          refine ⟨16451794263755290354446215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10967862842503526902964143 16451794263755290354446215)
          ·
            refine ⟨24677691395632935531669323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16451794263755290354446215 24677691395632935531669323)
            ·
              refine ⟨37016537093449403297503985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24677691395632935531669323 37016537093449403297503985)
              ·
                refine ⟨27762402820087052473127989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37016537093449403297503985 27762402820087052473127989)
                ·
                  refine ⟨2602725264383161169355749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27762402820087052473127989 2602725264383161169355749)
                  ·
                    refine ⟨488010987071842719254203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602725264383161169355749 488010987071842719254203)
                    ·
                      rfl

theorem cell22_1425597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1425597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425597 prefixEnd_1425597 := by exact prefixLift 1425597
  have htrace : WordTrace (prefixWord ++ tailWord_1425597) baseStart_1425597 baseEnd_1425597 := by
    simpa [prefixWord, tailWord_1425597, baseEnd_1425597] using wordTrace_append hprefix tailTrace_1425597
  have hstable : (prefixWord ++ tailWord_1425597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425597).length < 2 ^ (prefixWord ++ tailWord_1425597).sum := by decide
  have hdescent : baseEnd_1425597 < baseStart_1425597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425693 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1425693 : Nat := 118140960795 + 1425693 * 2 ^ 59
def prefixEnd_1425693 : Nat := 4983230072969 + 3 ^ 40 * 1425693 * 2
def baseEnd_1425693 : Nat := 488043849833730468853909

theorem tailTrace_1425693 : CollatzResearch.WordTrace tailWord_1425693 prefixEnd_1425693 488043849833730468853909 := by
  unfold tailWord_1425693
  simp only [CollatzResearch.WordTrace]
  refine ⟨51999295623965224824361733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34666197082643483216241155 51999295623965224824361733)
  ·
    refine ⟨9749867929493479654567825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51999295623965224824361733 9749867929493479654567825)
    ·
      refine ⟨7312400947120109740925869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9749867929493479654567825 7312400947120109740925869)
      ·
        refine ⟨2742150355170041152847201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7312400947120109740925869 2742150355170041152847201)
        ·
          refine ⟨2056612766377530864635401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742150355170041152847201 2056612766377530864635401)
          ·
            refine ⟨1542459574783148148476551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056612766377530864635401 1542459574783148148476551)
            ·
              refine ⟨2313689362174722222714827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542459574783148148476551 2313689362174722222714827)
              ·
                refine ⟨3470534043262083334072241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313689362174722222714827 3470534043262083334072241)
                ·
                  refine ⟨2602900532446562500554181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470534043262083334072241 2602900532446562500554181)
                  ·
                    refine ⟨488043849833730468853909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602900532446562500554181 488043849833730468853909)
                    ·
                      rfl

theorem cell22_1425693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1425693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425693 prefixEnd_1425693 := by exact prefixLift 1425693
  have htrace : WordTrace (prefixWord ++ tailWord_1425693) baseStart_1425693 baseEnd_1425693 := by
    simpa [prefixWord, tailWord_1425693, baseEnd_1425693] using wordTrace_append hprefix tailTrace_1425693
  have hstable : (prefixWord ++ tailWord_1425693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425693).length < 2 ^ (prefixWord ++ tailWord_1425693).sum := by decide
  have hdescent : baseEnd_1425693 < baseStart_1425693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425747 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 8]
def baseStart_1425747 : Nat := 118140960795 + 1425747 * 2 ^ 59
def prefixEnd_1425747 : Nat := 4983230072969 + 3 ^ 40 * 1425747 * 2
def baseEnd_1425747 : Nat := 162687445045764109334581

theorem tailTrace_1425747 : CollatzResearch.WordTrace tailWord_1425747 prefixEnd_1425747 162687445045764109334581 := by
  unfold tailWord_1425747
  simp only [CollatzResearch.WordTrace]
  refine ⟨52001265165769592046827495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34667510110513061364551663 52001265165769592046827495)
  ·
    refine ⟨78001897748654388070241243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52001265165769592046827495 78001897748654388070241243)
    ·
      refine ⟨117002846622981582105361865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78001897748654388070241243 117002846622981582105361865)
      ·
        refine ⟨87752134967236186579021399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117002846622981582105361865 87752134967236186579021399)
        ·
          refine ⟨131628202450854279868532099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87752134967236186579021399 131628202450854279868532099)
          ·
            refine ⟨197442303676281419802798149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131628202450854279868532099 197442303676281419802798149)
            ·
              refine ⟨37020431939302766213024653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197442303676281419802798149 37020431939302766213024653)
              ·
                refine ⟨13882661977238537329884245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37020431939302766213024653 13882661977238537329884245)
                ·
                  refine ⟨162687445045764109334581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13882661977238537329884245 162687445045764109334581)
                  ·
                    rfl

theorem cell22_1425747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_1425747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425747 prefixEnd_1425747 := by exact prefixLift 1425747
  have htrace : WordTrace (prefixWord ++ tailWord_1425747) baseStart_1425747 baseEnd_1425747 := by
    simpa [prefixWord, tailWord_1425747, baseEnd_1425747] using wordTrace_append hprefix tailTrace_1425747
  have hstable : (prefixWord ++ tailWord_1425747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425747).length < 2 ^ (prefixWord ++ tailWord_1425747).sum := by decide
  have hdescent : baseEnd_1425747 < baseStart_1425747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425781 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 6]
def baseStart_1425781 : Nat := 118140960795 + 1425781 * 2 ^ 59
def prefixEnd_1425781 : Nat := 4983230072969 + 3 ^ 40 * 1425781 * 2
def baseEnd_1425781 : Nat := 162691324677375857551213

theorem tailTrace_1425781 : CollatzResearch.WordTrace tailWord_1425781 prefixEnd_1425781 162691324677375857551213 := by
  unfold tailWord_1425781
  simp only [CollatzResearch.WordTrace]
  refine ⟨52002505247646415853565197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34668336831764277235710131 52002505247646415853565197)
  ·
    refine ⟨19500939467867405945086949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52002505247646415853565197 19500939467867405945086949)
    ·
      refine ⟨3656426150225138614703803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19500939467867405945086949 3656426150225138614703803)
      ·
        refine ⟨5484639225337707922055705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656426150225138614703803 5484639225337707922055705)
        ·
          refine ⟨4113479419003280941541779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5484639225337707922055705 4113479419003280941541779)
          ·
            refine ⟨6170219128504921412312669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113479419003280941541779 6170219128504921412312669)
            ·
              refine ⟨2313832173189345529617251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6170219128504921412312669 2313832173189345529617251)
              ·
                refine ⟨3470748259784018294425877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313832173189345529617251 3470748259784018294425877)
                ·
                  refine ⟨162691324677375857551213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3470748259784018294425877 162691324677375857551213)
                  ·
                    rfl

theorem cell22_1425781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_1425781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425781 prefixEnd_1425781 := by exact prefixLift 1425781
  have htrace : WordTrace (prefixWord ++ tailWord_1425781) baseStart_1425781 baseEnd_1425781 := by
    simpa [prefixWord, tailWord_1425781, baseEnd_1425781] using wordTrace_append hprefix tailTrace_1425781
  have hstable : (prefixWord ++ tailWord_1425781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425781).length < 2 ^ (prefixWord ++ tailWord_1425781).sum := by decide
  have hdescent : baseEnd_1425781 < baseStart_1425781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425832 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_1425832 : Nat := 118140960795 + 1425832 * 2 ^ 59
def prefixEnd_1425832 : Nat := 4983230072969 + 3 ^ 40 * 1425832 * 2
def baseEnd_1425832 : Nat := 162697144124793479876161

theorem tailTrace_1425832 : CollatzResearch.WordTrace tailWord_1425832 prefixEnd_1425832 162697144124793479876161 := by
  unfold tailWord_1425832
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002182685230825781835875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34669576913641101042447833 26002182685230825781835875)
  ·
    refine ⟨39003274027846238672753813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26002182685230825781835875 39003274027846238672753813)
    ·
      refine ⟨1828278470055292437785335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39003274027846238672753813 1828278470055292437785335)
      ·
        refine ⟨2742417705082938656678003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828278470055292437785335 2742417705082938656678003)
        ·
          refine ⟨4113626557624407985017005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742417705082938656678003 4113626557624407985017005)
          ·
            refine ⟨1542609959109152994381377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4113626557624407985017005 1542609959109152994381377)
            ·
              refine ⟨1156957469331864745786033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542609959109152994381377 1156957469331864745786033)
              ·
                refine ⟨867718101998898559339525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156957469331864745786033 867718101998898559339525)
                ·
                  refine ⟨162697144124793479876161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867718101998898559339525 162697144124793479876161)
                  ·
                    rfl

theorem cell22_1425832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_1425832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425832 prefixEnd_1425832 := by exact prefixLift 1425832
  have htrace : WordTrace (prefixWord ++ tailWord_1425832) baseStart_1425832 baseEnd_1425832 := by
    simpa [prefixWord, tailWord_1425832, baseEnd_1425832] using wordTrace_append hprefix tailTrace_1425832
  have hstable : (prefixWord ++ tailWord_1425832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425832).length < 2 ^ (prefixWord ++ tailWord_1425832).sum := by decide
  have hdescent : baseEnd_1425832 < baseStart_1425832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425926 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1425926 : Nat := 118140960795 + 1425926 * 2 ^ 59
def prefixEnd_1425926 : Nat := 4983230072969 + 3 ^ 40 * 1425926 * 2
def baseEnd_1425926 : Nat := 488123610495395527778195

theorem tailTrace_1425926 : CollatzResearch.WordTrace tailWord_1425926 prefixEnd_1425926 488123610495395527778195 := by
  unfold tailWord_1425926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625243557253784550549801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34671862554747403745062421 1625243557253784550549801)
  ·
    refine ⟨1218932667940338412912351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625243557253784550549801 1218932667940338412912351)
    ·
      refine ⟨1828399001910507619368527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218932667940338412912351 1828399001910507619368527)
      ·
        refine ⟨2742598502865761429052791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828399001910507619368527 2742598502865761429052791)
        ·
          refine ⟨4113897754298642143579187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742598502865761429052791 4113897754298642143579187)
          ·
            refine ⟨6170846631447963215368781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113897754298642143579187 6170846631447963215368781)
            ·
              refine ⟨2314067486792986205763293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6170846631447963215368781 2314067486792986205763293)
              ·
                refine ⟨867775307547369827161235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2314067486792986205763293 867775307547369827161235)
                ·
                  refine ⟨1301662961321054740741853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867775307547369827161235 1301662961321054740741853)
                  ·
                    refine ⟨488123610495395527778195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301662961321054740741853 488123610495395527778195)
                    ·
                      rfl

theorem cell22_1425926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1425926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425926 prefixEnd_1425926 := by exact prefixLift 1425926
  have htrace : WordTrace (prefixWord ++ tailWord_1425926) baseStart_1425926 baseEnd_1425926 := by
    simpa [prefixWord, tailWord_1425926, baseEnd_1425926] using wordTrace_append hprefix tailTrace_1425926
  have hstable : (prefixWord ++ tailWord_1425926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425926).length < 2 ^ (prefixWord ++ tailWord_1425926).sum := by decide
  have hdescent : baseEnd_1425926 < baseStart_1425926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425946 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1425946 : Nat := 118140960795 + 1425946 * 2 ^ 59
def prefixEnd_1425946 : Nat := 4983230072969 + 3 ^ 40 * 1425946 * 2
def baseEnd_1425946 : Nat := 488130456904122142278133

theorem tailTrace_1425946 : CollatzResearch.WordTrace tailWord_1425946 prefixEnd_1425946 488130456904122142278133 := by
  unfold tailWord_1425946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002130823012162258330423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34672348861365766022214461 13002130823012162258330423)
  ·
    refine ⟨19503196234518243387495635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13002130823012162258330423 19503196234518243387495635)
    ·
      refine ⟨29254794351777365081243453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19503196234518243387495635 29254794351777365081243453)
      ·
        refine ⟨10970547881916511905466295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29254794351777365081243453 10970547881916511905466295)
        ·
          refine ⟨16455821822874767858199443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970547881916511905466295 16455821822874767858199443)
          ·
            refine ⟨24683732734312151787299165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16455821822874767858199443 24683732734312151787299165)
            ·
              refine ⟨9256399775367056920237187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24683732734312151787299165 9256399775367056920237187)
              ·
                refine ⟨13884599663050585380355781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256399775367056920237187 13884599663050585380355781)
                ·
                  refine ⟨2603362436821984758816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13884599663050585380355781 2603362436821984758816709)
                  ·
                    refine ⟨488130456904122142278133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2603362436821984758816709 488130456904122142278133)
                    ·
                      rfl

theorem cell22_1425946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1425946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425946 prefixEnd_1425946 := by exact prefixLift 1425946
  have htrace : WordTrace (prefixWord ++ tailWord_1425946) baseStart_1425946 baseEnd_1425946 := by
    simpa [prefixWord, tailWord_1425946, baseEnd_1425946] using wordTrace_append hprefix tailTrace_1425946
  have hstable : (prefixWord ++ tailWord_1425946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425946).length < 2 ^ (prefixWord ++ tailWord_1425946).sum := by decide
  have hdescent : baseEnd_1425946 < baseStart_1425946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425948 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1425948 : Nat := 118140960795 + 1425948 * 2 ^ 59
def prefixEnd_1425948 : Nat := 4983230072969 + 3 ^ 40 * 1425948 * 2
def baseEnd_1425948 : Nat := 488131141544994803728127

theorem tailTrace_1425948 : CollatzResearch.WordTrace tailWord_1425948 prefixEnd_1425948 488131141544994803728127 := by
  unfold tailWord_1425948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004298119020701687447249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34672397492027602249929665 26004298119020701687447249)
  ·
    refine ⟨19503223589265526265585437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26004298119020701687447249 19503223589265526265585437)
    ·
      refine ⟨7313708845974572349594539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19503223589265526265585437 7313708845974572349594539)
      ·
        refine ⟨10970563268961858524391809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313708845974572349594539 10970563268961858524391809)
        ·
          refine ⟨8227922451721393893293857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970563268961858524391809 8227922451721393893293857)
          ·
            refine ⟨6170941838791045419970393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8227922451721393893293857 6170941838791045419970393)
            ·
              refine ⟨4628206379093284064977795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170941838791045419970393 4628206379093284064977795)
              ·
                refine ⟨6942309568639926097466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628206379093284064977795 6942309568639926097466693)
                ·
                  refine ⟨1301683044119986143275005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6942309568639926097466693 1301683044119986143275005)
                  ·
                    refine ⟨488131141544994803728127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301683044119986143275005 488131141544994803728127)
                    ·
                      rfl

theorem cell22_1425948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1425948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1425948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1425948 prefixEnd_1425948 := by exact prefixLift 1425948
  have htrace : WordTrace (prefixWord ++ tailWord_1425948) baseStart_1425948 baseEnd_1425948 := by
    simpa [prefixWord, tailWord_1425948, baseEnd_1425948] using wordTrace_append hprefix tailTrace_1425948
  have hstable : (prefixWord ++ tailWord_1425948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425948).length < 2 ^ (prefixWord ++ tailWord_1425948).sum := by decide
  have hdescent : baseEnd_1425948 < baseStart_1425948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426098 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1426098 : Nat := 118140960795 + 1426098 * 2 ^ 59
def prefixEnd_1426098 : Nat := 4983230072969 + 3 ^ 40 * 1426098 * 2
def baseEnd_1426098 : Nat := 488182489610444412477667

theorem tailTrace_1426098 : CollatzResearch.WordTrace tailWord_1426098 prefixEnd_1426098 488182489610444412477667 := by
  unfold tailWord_1426098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003516796874494748213737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34676044791665319328569965 13003516796874494748213737)
  ·
    refine ⟨9752637597655871061160303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003516796874494748213737 9752637597655871061160303)
    ·
      refine ⟨14628956396483806591740455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9752637597655871061160303 14628956396483806591740455)
      ·
        refine ⟨21943434594725709887610683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14628956396483806591740455 21943434594725709887610683)
        ·
          refine ⟨32915151892088564831416025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21943434594725709887610683 32915151892088564831416025)
          ·
            refine ⟨24686363919066423623562019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32915151892088564831416025 24686363919066423623562019)
            ·
              refine ⟨37029545878599635435343029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24686363919066423623562019 37029545878599635435343029)
              ·
                refine ⟨3471519926118715822063409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37029545878599635435343029 3471519926118715822063409)
                ·
                  refine ⟨2603639944589036866547557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471519926118715822063409 2603639944589036866547557)
                  ·
                    refine ⟨488182489610444412477667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2603639944589036866547557 488182489610444412477667)
                    ·
                      rfl

theorem cell22_1426098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1426098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426098 prefixEnd_1426098 := by exact prefixLift 1426098
  have htrace : WordTrace (prefixWord ++ tailWord_1426098) baseStart_1426098 baseEnd_1426098 := by
    simpa [prefixWord, tailWord_1426098, baseEnd_1426098] using wordTrace_append hprefix tailTrace_1426098
  have hstable : (prefixWord ++ tailWord_1426098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426098).length < 2 ^ (prefixWord ++ tailWord_1426098).sum := by decide
  have hdescent : baseEnd_1426098 < baseStart_1426098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426130 : List Nat := [3, 2, 2, 2, 3, 1, 2, 7]
def baseStart_1426130 : Nat := 118140960795 + 1426130 * 2 ^ 59
def prefixEnd_1426130 : Nat := 4983230072969 + 3 ^ 40 * 1426130 * 2
def baseEnd_1426130 : Nat := 54243715984934110630841

theorem tailTrace_1426130 : CollatzResearch.WordTrace tailWord_1426130 prefixEnd_1426130 54243715984934110630841 := by
  unfold tailWord_1426130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003808580845512114504961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34676822882254698972013229 13003808580845512114504961)
  ·
    refine ⟨9752856435634134085878721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003808580845512114504961 9752856435634134085878721)
    ·
      refine ⟨7314642326725600564409041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9752856435634134085878721 7314642326725600564409041)
      ·
        refine ⟨5485981745044200423306781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314642326725600564409041 5485981745044200423306781)
        ·
          refine ⟨2057243154391575158740043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5485981745044200423306781 2057243154391575158740043)
          ·
            refine ⟨3085864731587362738110065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057243154391575158740043 3085864731587362738110065)
            ·
              refine ⟨2314398548690522053582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085864731587362738110065 2314398548690522053582549)
              ·
                refine ⟨54243715984934110630841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2314398548690522053582549 54243715984934110630841)
                ·
                  rfl

theorem cell22_1426130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_1426130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426130 prefixEnd_1426130 := by exact prefixLift 1426130
  have htrace : WordTrace (prefixWord ++ tailWord_1426130) baseStart_1426130 baseEnd_1426130 := by
    simpa [prefixWord, tailWord_1426130, baseEnd_1426130] using wordTrace_append hprefix tailTrace_1426130
  have hstable : (prefixWord ++ tailWord_1426130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426130).length < 2 ^ (prefixWord ++ tailWord_1426130).sum := by decide
  have hdescent : baseEnd_1426130 < baseStart_1426130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426173 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1426173 : Nat := 118140960795 + 1426173 * 2 ^ 59
def prefixEnd_1426173 : Nat := 4983230072969 + 3 ^ 40 * 1426173 * 2
def baseEnd_1426173 : Nat := 488208163643169216852437

theorem tailTrace_1426173 : CollatzResearch.WordTrace tailWord_1426173 prefixEnd_1426173 488208163643169216852437 := by
  unfold tailWord_1426173
  simp only [CollatzResearch.WordTrace]
  refine ⟨52016802662226266801835173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34677868441484177867890115 52016802662226266801835173)
  ·
    refine ⟨9753150499167425025344095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52016802662226266801835173 9753150499167425025344095)
    ·
      refine ⟨14629725748751137538016143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9753150499167425025344095 14629725748751137538016143)
      ·
        refine ⟨21944588623126706307024215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629725748751137538016143 21944588623126706307024215)
        ·
          refine ⟨32916882934690059460536323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21944588623126706307024215 32916882934690059460536323)
          ·
            refine ⟨49375324402035089190804485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32916882934690059460536323 49375324402035089190804485)
            ·
              refine ⟨9257873325381579223275841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49375324402035089190804485 9257873325381579223275841)
              ·
                refine ⟨6943404994036184417456881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257873325381579223275841 6943404994036184417456881)
                ·
                  refine ⟨5207553745527138313092661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943404994036184417456881 5207553745527138313092661)
                  ·
                    refine ⟨488208163643169216852437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5207553745527138313092661 488208163643169216852437)
                    ·
                      rfl

theorem cell22_1426173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1426173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426173 prefixEnd_1426173 := by exact prefixLift 1426173
  have htrace : WordTrace (prefixWord ++ tailWord_1426173) baseStart_1426173 baseEnd_1426173 := by
    simpa [prefixWord, tailWord_1426173, baseEnd_1426173] using wordTrace_append hprefix tailTrace_1426173
  have hstable : (prefixWord ++ tailWord_1426173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426173).length < 2 ^ (prefixWord ++ tailWord_1426173).sum := by decide
  have hdescent : baseEnd_1426173 < baseStart_1426173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426237 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1426237 : Nat := 118140960795 + 1426237 * 2 ^ 59
def prefixEnd_1426237 : Nat := 4983230072969 + 3 ^ 40 * 1426237 * 2
def baseEnd_1426237 : Nat := 162743357383698127750747

theorem tailTrace_1426237 : CollatzResearch.WordTrace tailWord_1426237 prefixEnd_1426237 162743357383698127750747 := by
  unfold tailWord_1426237
  simp only [CollatzResearch.WordTrace]
  refine ⟨52019136933994405732164965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34679424622662937154776643 52019136933994405732164965)
  ·
    refine ⟨9753588175123951074780931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52019136933994405732164965 9753588175123951074780931)
    ·
      refine ⟨14630382262685926612171397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9753588175123951074780931 14630382262685926612171397)
      ·
        refine ⟨2743196674253611239782137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14630382262685926612171397 2743196674253611239782137)
        ·
          refine ⟨2057397505690208429836603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743196674253611239782137 2057397505690208429836603)
          ·
            refine ⟨3086096258535312644754905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057397505690208429836603 3086096258535312644754905)
            ·
              refine ⟨2314572193901484483566179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086096258535312644754905 2314572193901484483566179)
              ·
                refine ⟨3471858290852226725349269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314572193901484483566179 3471858290852226725349269)
                ·
                  refine ⟨162743357383698127750747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3471858290852226725349269 162743357383698127750747)
                  ·
                    rfl

theorem cell22_1426237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1426237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426237 prefixEnd_1426237 := by exact prefixLift 1426237
  have htrace : WordTrace (prefixWord ++ tailWord_1426237) baseStart_1426237 baseEnd_1426237 := by
    simpa [prefixWord, tailWord_1426237, baseEnd_1426237] using wordTrace_append hprefix tailTrace_1426237
  have hstable : (prefixWord ++ tailWord_1426237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426237).length < 2 ^ (prefixWord ++ tailWord_1426237).sum := by decide
  have hdescent : baseEnd_1426237 < baseStart_1426237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426248 : List Nat := [2, 1, 3, 1, 1, 3, 2, 9]
def baseStart_1426248 : Nat := 118140960795 + 1426248 * 2 ^ 59
def prefixEnd_1426248 : Nat := 4983230072969 + 3 ^ 40 * 1426248 * 2
def baseEnd_1426248 : Nat := 54248204186210446803023

theorem tailTrace_1426248 : CollatzResearch.WordTrace tailWord_1426248 prefixEnd_1426248 54248204186210446803023 := by
  unfold tailWord_1426248
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009769068477277305407699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34679692091303036407210265 26009769068477277305407699)
  ·
    refine ⟨39014653602715915958111549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26009769068477277305407699 39014653602715915958111549)
    ·
      refine ⟨14630495101018468484291831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39014653602715915958111549 14630495101018468484291831)
      ·
        refine ⟨21945742651527702726437747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630495101018468484291831 21945742651527702726437747)
        ·
          refine ⟨32918613977291554089656621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945742651527702726437747 32918613977291554089656621)
          ·
            refine ⟨12344480241484332783621233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32918613977291554089656621 12344480241484332783621233)
            ·
              refine ⟨9258360181113249587715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12344480241484332783621233 9258360181113249587715925)
              ·
                refine ⟨54248204186210446803023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9258360181113249587715925 54248204186210446803023)
                ·
                  rfl

theorem cell22_1426248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_1426248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426248 prefixEnd_1426248 := by exact prefixLift 1426248
  have htrace : WordTrace (prefixWord ++ tailWord_1426248) baseStart_1426248 baseEnd_1426248 := by
    simpa [prefixWord, tailWord_1426248, baseEnd_1426248] using wordTrace_append hprefix tailTrace_1426248
  have hstable : (prefixWord ++ tailWord_1426248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426248).length < 2 ^ (prefixWord ++ tailWord_1426248).sum := by decide
  have hdescent : baseEnd_1426248 < baseStart_1426248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426252 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1426252 : Nat := 118140960795 + 1426252 * 2 ^ 59
def prefixEnd_1426252 : Nat := 4983230072969 + 3 ^ 40 * 1426252 * 2
def baseEnd_1426252 : Nat := 488235206957639344127195

theorem tailTrace_1426252 : CollatzResearch.WordTrace tailWord_1426252 prefixEnd_1426252 488235206957639344127195 := by
  unfold tailWord_1426252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009842014470031646980505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34679789352626708862640673 26009842014470031646980505)
  ·
    refine ⟨19507381510852523735235379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26009842014470031646980505 19507381510852523735235379)
    ·
      refine ⟨29261072266278785602853069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19507381510852523735235379 29261072266278785602853069)
      ·
        refine ⟨10972902099854544601069901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29261072266278785602853069 10972902099854544601069901)
        ·
          refine ⟨4114838287445454225401213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10972902099854544601069901 4114838287445454225401213)
          ·
            refine ⟨1543064357792045334525455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4114838287445454225401213 1543064357792045334525455)
            ·
              refine ⟨2314596536688068001788183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543064357792045334525455 2314596536688068001788183)
              ·
                refine ⟨3471894805032102002682275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314596536688068001788183 3471894805032102002682275)
                ·
                  refine ⟨5207842207548153004023413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471894805032102002682275 5207842207548153004023413)
                  ·
                    refine ⟨488235206957639344127195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5207842207548153004023413 488235206957639344127195)
                    ·
                      rfl

theorem cell22_1426252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1426252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426252 prefixEnd_1426252 := by exact prefixLift 1426252
  have htrace : WordTrace (prefixWord ++ tailWord_1426252) baseStart_1426252 baseEnd_1426252 := by
    simpa [prefixWord, tailWord_1426252, baseEnd_1426252] using wordTrace_append hprefix tailTrace_1426252
  have hstable : (prefixWord ++ tailWord_1426252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426252).length < 2 ^ (prefixWord ++ tailWord_1426252).sum := by decide
  have hdescent : baseEnd_1426252 < baseStart_1426252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426265 : List Nat := [1, 2, 1, 2, 2, 4, 4, 6]
def baseStart_1426265 : Nat := 118140960795 + 1426265 * 2 ^ 59
def prefixEnd_1426265 : Nat := 4983230072969 + 3 ^ 40 * 1426265 * 2
def baseEnd_1426265 : Nat := 54248850791479071505795

theorem tailTrace_1426265 : CollatzResearch.WordTrace tailWord_1426265 prefixEnd_1426265 54248850791479071505795 := by
  unfold tailWord_1426265
  simp only [CollatzResearch.WordTrace]
  refine ⟨52020158177892966514184249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34680105451928644342789499 52020158177892966514184249)
  ·
    refine ⟨39015118633419724885638187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52020158177892966514184249 39015118633419724885638187)
    ·
      refine ⟨58522677950129587328457281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39015118633419724885638187 58522677950129587328457281)
      ·
        refine ⟨43892008462597190496342961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58522677950129587328457281 43892008462597190496342961)
        ·
          refine ⟨32919006346947892872257221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43892008462597190496342961 32919006346947892872257221)
          ·
            refine ⟨6172313690052729913548229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32919006346947892872257221 6172313690052729913548229)
            ·
              refine ⟨1157308816884886858790293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6172313690052729913548229 1157308816884886858790293)
              ·
                refine ⟨54248850791479071505795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1157308816884886858790293 54248850791479071505795)
                ·
                  rfl

theorem cell22_1426265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 6].length) (baseStart_1426265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426265 prefixEnd_1426265 := by exact prefixLift 1426265
  have htrace : WordTrace (prefixWord ++ tailWord_1426265) baseStart_1426265 baseEnd_1426265 := by
    simpa [prefixWord, tailWord_1426265, baseEnd_1426265] using wordTrace_append hprefix tailTrace_1426265
  have hstable : (prefixWord ++ tailWord_1426265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426265).length < 2 ^ (prefixWord ++ tailWord_1426265).sum := by decide
  have hdescent : baseEnd_1426265 < baseStart_1426265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426297 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_1426297 : Nat := 118140960795 + 1426297 * 2 ^ 59
def prefixEnd_1426297 : Nat := 4983230072969 + 3 ^ 40 * 1426297 * 2
def baseEnd_1426297 : Nat := 488250611377274226752057

theorem tailTrace_1426297 : CollatzResearch.WordTrace tailWord_1426297 prefixEnd_1426297 488250611377274226752057 := by
  unfold tailWord_1426297
  simp only [CollatzResearch.WordTrace]
  refine ⟨52021325313777035979349145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34680883542518023986232763 52021325313777035979349145)
  ·
    refine ⟨39015993985332776984511859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52021325313777035979349145 39015993985332776984511859)
    ·
      refine ⟨58523990977999165476767789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39015993985332776984511859 58523990977999165476767789)
      ·
        refine ⟨21946496616749687053787921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58523990977999165476767789 21946496616749687053787921)
        ·
          refine ⟨16459872462562265290340941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21946496616749687053787921 16459872462562265290340941)
          ·
            refine ⟨6172452173460849483877853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16459872462562265290340941 6172452173460849483877853)
            ·
              refine ⟨2314669565047818556454195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6172452173460849483877853 2314669565047818556454195)
              ·
                refine ⟨3472004347571727834681293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314669565047818556454195 3472004347571727834681293)
                ·
                  refine ⟨1302001630339397938005485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3472004347571727834681293 1302001630339397938005485)
                  ·
                    refine ⟨488250611377274226752057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302001630339397938005485 488250611377274226752057)
                    ·
                      rfl

theorem cell22_1426297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_1426297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426297 prefixEnd_1426297 := by exact prefixLift 1426297
  have htrace : WordTrace (prefixWord ++ tailWord_1426297) baseStart_1426297 baseEnd_1426297 := by
    simpa [prefixWord, tailWord_1426297, baseEnd_1426297] using wordTrace_append hprefix tailTrace_1426297
  have hstable : (prefixWord ++ tailWord_1426297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426297).length < 2 ^ (prefixWord ++ tailWord_1426297).sum := by decide
  have hdescent : baseEnd_1426297 < baseStart_1426297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426385 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_1426385 : Nat := 118140960795 + 1426385 * 2 ^ 59
def prefixEnd_1426385 : Nat := 4983230072969 + 3 ^ 40 * 1426385 * 2
def baseEnd_1426385 : Nat := 488280735575671330551787

theorem tailTrace_1426385 : CollatzResearch.WordTrace tailWord_1426385 prefixEnd_1426385 488280735575671330551787 := by
  unfold tailWord_1426385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52024534937458227008552609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34683023291638818005701739 52024534937458227008552609)
  ·
    refine ⟨39018401203093670256414457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52024534937458227008552609 39018401203093670256414457)
    ·
      refine ⟨29263800902320252692310843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39018401203093670256414457 29263800902320252692310843)
      ·
        refine ⟨43895701353480379038466265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29263800902320252692310843 43895701353480379038466265)
        ·
          refine ⟨32921776015110284278849699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43895701353480379038466265 32921776015110284278849699)
          ·
            refine ⟨49382664022665426418274549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32921776015110284278849699 49382664022665426418274549)
            ·
              refine ⟨4629624752124883726713239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49382664022665426418274549 4629624752124883726713239)
              ·
                refine ⟨6944437128187325590069859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629624752124883726713239 6944437128187325590069859)
                ·
                  refine ⟨10416655692280988385104789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944437128187325590069859 10416655692280988385104789)
                  ·
                    refine ⟨488280735575671330551787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10416655692280988385104789 488280735575671330551787)
                    ·
                      rfl

theorem cell22_1426385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_1426385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426385 prefixEnd_1426385 := by exact prefixLift 1426385
  have htrace : WordTrace (prefixWord ++ tailWord_1426385) baseStart_1426385 baseEnd_1426385 := by
    simpa [prefixWord, tailWord_1426385, baseEnd_1426385] using wordTrace_append hprefix tailTrace_1426385
  have hstable : (prefixWord ++ tailWord_1426385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426385).length < 2 ^ (prefixWord ++ tailWord_1426385).sum := by decide
  have hdescent : baseEnd_1426385 < baseStart_1426385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426466 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1426466 : Nat := 118140960795 + 1426466 * 2 ^ 59
def prefixEnd_1426466 : Nat := 4983230072969 + 3 ^ 40 * 1426466 * 2
def baseEnd_1426466 : Nat := 488308463531014119276539

theorem tailTrace_1426466 : CollatzResearch.WordTrace tailWord_1426466 prefixEnd_1426466 488308463531014119276539 := by
  unfold tailWord_1426466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006872312541194460562813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34684992833443185228167501 13006872312541194460562813)
  ·
    refine ⟨4877577117202947922711055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13006872312541194460562813 4877577117202947922711055)
    ·
      refine ⟨7316365675804421884066583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877577117202947922711055 7316365675804421884066583)
      ·
        refine ⟨10974548513706632826099875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316365675804421884066583 10974548513706632826099875)
        ·
          refine ⟨16461822770559949239149813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974548513706632826099875 16461822770559949239149813)
          ·
            refine ⟨1543295884739995241170295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16461822770559949239149813 1543295884739995241170295)
            ·
              refine ⟨2314943827109992861755443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543295884739995241170295 2314943827109992861755443)
              ·
                refine ⟨3472415740664989292633165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314943827109992861755443 3472415740664989292633165)
                ·
                  refine ⟨1302155902749370984737437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3472415740664989292633165 1302155902749370984737437)
                  ·
                    refine ⟨488308463531014119276539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302155902749370984737437 488308463531014119276539)
                    ·
                      rfl

theorem cell22_1426466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1426466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426466 prefixEnd_1426466 := by exact prefixLift 1426466
  have htrace : WordTrace (prefixWord ++ tailWord_1426466) baseStart_1426466 baseEnd_1426466 := by
    simpa [prefixWord, tailWord_1426466, baseEnd_1426466] using wordTrace_append hprefix tailTrace_1426466
  have hstable : (prefixWord ++ tailWord_1426466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426466).length < 2 ^ (prefixWord ++ tailWord_1426466).sum := by decide
  have hdescent : baseEnd_1426466 < baseStart_1426466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426590 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1426590 : Nat := 118140960795 + 1426590 * 2 ^ 59
def prefixEnd_1426590 : Nat := 4983230072969 + 3 ^ 40 * 1426590 * 2
def baseEnd_1426590 : Nat := 488350911265119129176159

theorem tailTrace_1426590 : CollatzResearch.WordTrace tailWord_1426590 prefixEnd_1426590 488350911265119129176159 := by
  unfold tailWord_1426590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504001487714443377470653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34688007934477031346510149 6504001487714443377470653)
  ·
    refine ⟨2439000557892916266551495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6504001487714443377470653 2439000557892916266551495)
    ·
      refine ⟨3658500836839374399827243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439000557892916266551495 3658500836839374399827243)
      ·
        refine ⟨5487751255259061599740865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658500836839374399827243 5487751255259061599740865)
        ·
          refine ⟨4115813441444296199805649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5487751255259061599740865 4115813441444296199805649)
          ·
            refine ⟨3086860081083222149854237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115813441444296199805649 3086860081083222149854237)
            ·
              refine ⟨1157572530406208306195339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3086860081083222149854237 1157572530406208306195339)
              ·
                refine ⟨1736358795609312459293009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157572530406208306195339 1736358795609312459293009)
                ·
                  refine ⟨1302269096706984344469757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736358795609312459293009 1302269096706984344469757)
                  ·
                    refine ⟨488350911265119129176159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302269096706984344469757 488350911265119129176159)
                    ·
                      rfl

theorem cell22_1426590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1426590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426590 prefixEnd_1426590 := by exact prefixLift 1426590
  have htrace : WordTrace (prefixWord ++ tailWord_1426590) baseStart_1426590 baseEnd_1426590 := by
    simpa [prefixWord, tailWord_1426590, baseEnd_1426590] using wordTrace_append hprefix tailTrace_1426590
  have hstable : (prefixWord ++ tailWord_1426590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426590).length < 2 ^ (prefixWord ++ tailWord_1426590).sum := by decide
  have hdescent : baseEnd_1426590 < baseStart_1426590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426648 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_1426648 : Nat := 118140960795 + 1426648 * 2 ^ 59
def prefixEnd_1426648 : Nat := 4983230072969 + 3 ^ 40 * 1426648 * 2
def baseEnd_1426648 : Nat := 162790255283475437075327

theorem tailTrace_1426648 : CollatzResearch.WordTrace tailWord_1426648 prefixEnd_1426648 162790255283475437075327 := by
  unfold tailWord_1426648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26017063667752711462688299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34689418223670281950251065 26017063667752711462688299)
  ·
    refine ⟨39025595501629067194032449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26017063667752711462688299 39025595501629067194032449)
    ·
      refine ⟨29269196626221800395524337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39025595501629067194032449 29269196626221800395524337)
      ·
        refine ⟨21951897469666350296643253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29269196626221800395524337 21951897469666350296643253)
        ·
          refine ⟨2057990387781220340310305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21951897469666350296643253 2057990387781220340310305)
          ·
            refine ⟨1543492790835915255232729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057990387781220340310305 1543492790835915255232729)
            ·
              refine ⟨1157619593126936441424547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543492790835915255232729 1157619593126936441424547)
              ·
                refine ⟨1736429389690404662136821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157619593126936441424547 1736429389690404662136821)
                ·
                  refine ⟨162790255283475437075327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1736429389690404662136821 162790255283475437075327)
                  ·
                    rfl

theorem cell22_1426648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_1426648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426648 prefixEnd_1426648 := by exact prefixLift 1426648
  have htrace : WordTrace (prefixWord ++ tailWord_1426648) baseStart_1426648 baseEnd_1426648 := by
    simpa [prefixWord, tailWord_1426648, baseEnd_1426648] using wordTrace_append hprefix tailTrace_1426648
  have hstable : (prefixWord ++ tailWord_1426648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426648).length < 2 ^ (prefixWord ++ tailWord_1426648).sum := by decide
  have hdescent : baseEnd_1426648 < baseStart_1426648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426661 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_1426661 : Nat := 118140960795 + 1426661 * 2 ^ 59
def prefixEnd_1426661 : Nat := 4983230072969 + 3 ^ 40 * 1426661 * 2
def baseEnd_1426661 : Nat := 488375216016098610650941

theorem tailTrace_1426661 : CollatzResearch.WordTrace tailWord_1426661 prefixEnd_1426661 488375216016098610650941 := by
  unfold tailWord_1426661
  simp only [CollatzResearch.WordTrace]
  refine ⟨52034601484458326145599837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34689734322972217430399891 52034601484458326145599837)
  ·
    refine ⟨19512975556671872304599939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52034601484458326145599837 19512975556671872304599939)
    ·
      refine ⟨29269463335007808456899909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19512975556671872304599939 29269463335007808456899909)
      ·
        refine ⟨5488024375313964085668733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29269463335007808456899909 5488024375313964085668733)
        ·
          refine ⟨2058009140742736532125775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5488024375313964085668733 2058009140742736532125775)
          ·
            refine ⟨3087013711114104798188663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058009140742736532125775 3087013711114104798188663)
            ·
              refine ⟨4630520566671157197282995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087013711114104798188663 4630520566671157197282995)
              ·
                refine ⟨6945780850006735795924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630520566671157197282995 6945780850006735795924493)
                ·
                  refine ⟨2604667818752525923471685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6945780850006735795924493 2604667818752525923471685)
                  ·
                    refine ⟨488375216016098610650941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604667818752525923471685 488375216016098610650941)
                    ·
                      rfl

theorem cell22_1426661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_1426661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426661 prefixEnd_1426661 := by exact prefixLift 1426661
  have htrace : WordTrace (prefixWord ++ tailWord_1426661) baseStart_1426661 baseEnd_1426661 := by
    simpa [prefixWord, tailWord_1426661, baseEnd_1426661] using wordTrace_append hprefix tailTrace_1426661
  have hstable : (prefixWord ++ tailWord_1426661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426661).length < 2 ^ (prefixWord ++ tailWord_1426661).sum := by decide
  have hdescent : baseEnd_1426661 < baseStart_1426661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426687 : List Nat := [1, 1, 2, 2, 1, 15]
def baseStart_1426687 : Nat := 118140960795 + 1426687 * 2 ^ 59
def prefixEnd_1426687 : Nat := 4983230072969 + 3 ^ 40 * 1426687 * 2
def baseEnd_1426687 : Nat := 6029433535153619870381

theorem tailTrace_1426687 : CollatzResearch.WordTrace tailWord_1426687 prefixEnd_1426687 6029433535153619870381 := by
  unfold tailWord_1426687
  simp only [CollatzResearch.WordTrace]
  refine ⟨52035549782364132586046315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34690366521576088390697543 52035549782364132586046315)
  ·
    refine ⟨78053324673546198879069473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52035549782364132586046315 78053324673546198879069473)
    ·
      refine ⟨58539993505159649159302105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78053324673546198879069473 58539993505159649159302105)
      ·
        refine ⟨43904995128869736869476579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58539993505159649159302105 43904995128869736869476579)
        ·
          refine ⟨65857492693304605304214869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43904995128869736869476579 65857492693304605304214869)
          ·
            refine ⟨6029433535153619870381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 65857492693304605304214869 6029433535153619870381)
            ·
              rfl

theorem cell22_1426687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 15].length) (baseStart_1426687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426687 prefixEnd_1426687 := by exact prefixLift 1426687
  have htrace : WordTrace (prefixWord ++ tailWord_1426687) baseStart_1426687 baseEnd_1426687 := by
    simpa [prefixWord, tailWord_1426687, baseEnd_1426687] using wordTrace_append hprefix tailTrace_1426687
  have hstable : (prefixWord ++ tailWord_1426687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426687).length < 2 ^ (prefixWord ++ tailWord_1426687).sum := by decide
  have hdescent : baseEnd_1426687 < baseStart_1426687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426691 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 2, 3]
def baseStart_1426691 : Nat := 118140960795 + 1426691 * 2 ^ 59
def prefixEnd_1426691 : Nat := 4983230072969 + 3 ^ 40 * 1426691 * 2
def baseEnd_1426691 : Nat := 488385485629188532400849

theorem tailTrace_1426691 : CollatzResearch.WordTrace tailWord_1426691 prefixEnd_1426691 488385485629188532400849 := by
  unfold tailWord_1426691
  simp only [CollatzResearch.WordTrace]
  refine ⟨52035695674349641269191927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34690463782899760846127951 52035695674349641269191927)
  ·
    refine ⟨78053543511524461903787891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52035695674349641269191927 78053543511524461903787891)
    ·
      refine ⟨117080315267286692855681837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78053543511524461903787891 117080315267286692855681837)
      ·
        refine ⟨43905118225232509820880689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117080315267286692855681837 43905118225232509820880689)
        ·
          refine ⟨32928838668924382365660517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43905118225232509820880689 32928838668924382365660517)
          ·
            refine ⟨6174157250423321693561347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32928838668924382365660517 6174157250423321693561347)
            ·
              refine ⟨9261235875634982540342021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174157250423321693561347 9261235875634982540342021)
              ·
                refine ⟨1736481726681559226314129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9261235875634982540342021 1736481726681559226314129)
                ·
                  refine ⟨1302361295011169419735597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736481726681559226314129 1302361295011169419735597)
                  ·
                    refine ⟨488385485629188532400849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302361295011169419735597 488385485629188532400849)
                    ·
                      rfl

theorem cell22_1426691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].length) (baseStart_1426691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426691 prefixEnd_1426691 := by exact prefixLift 1426691
  have htrace : WordTrace (prefixWord ++ tailWord_1426691) baseStart_1426691 baseEnd_1426691 := by
    simpa [prefixWord, tailWord_1426691, baseEnd_1426691] using wordTrace_append hprefix tailTrace_1426691
  have hstable : (prefixWord ++ tailWord_1426691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426691).length < 2 ^ (prefixWord ++ tailWord_1426691).sum := by decide
  have hdescent : baseEnd_1426691 < baseStart_1426691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426753 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1426753 : Nat := 118140960795 + 1426753 * 2 ^ 59
def prefixEnd_1426753 : Nat := 4983230072969 + 3 ^ 40 * 1426753 * 2
def baseEnd_1426753 : Nat := 488406709496241037350659

theorem tailTrace_1426753 : CollatzResearch.WordTrace tailWord_1426753 prefixEnd_1426753 488406709496241037350659 := by
  unfold tailWord_1426753
  simp only [CollatzResearch.WordTrace]
  refine ⟨52037957000125025857948913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34691971333416683905299275 52037957000125025857948913)
  ·
    refine ⟨39028467750093769393461685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52037957000125025857948913 39028467750093769393461685)
    ·
      refine ⟨3658918851571290880637033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39028467750093769393461685 3658918851571290880637033)
      ·
        refine ⟨2744189138678468160477775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658918851571290880637033 2744189138678468160477775)
        ·
          refine ⟨4116283708017702240716663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744189138678468160477775 4116283708017702240716663)
          ·
            refine ⟨6174425562026553361074995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116283708017702240716663 6174425562026553361074995)
            ·
              refine ⟨9261638343039830041612493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174425562026553361074995 9261638343039830041612493)
              ·
                refine ⟨3473114378639936265604685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9261638343039830041612493 3473114378639936265604685)
                ·
                  refine ⟨1302417891989976099601757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3473114378639936265604685 1302417891989976099601757)
                  ·
                    refine ⟨488406709496241037350659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302417891989976099601757 488406709496241037350659)
                    ·
                      rfl

theorem cell22_1426753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1426753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426753 prefixEnd_1426753 := by exact prefixLift 1426753
  have htrace : WordTrace (prefixWord ++ tailWord_1426753) baseStart_1426753 baseEnd_1426753 := by
    simpa [prefixWord, tailWord_1426753, baseEnd_1426753] using wordTrace_append hprefix tailTrace_1426753
  have hstable : (prefixWord ++ tailWord_1426753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426753).length < 2 ^ (prefixWord ++ tailWord_1426753).sum := by decide
  have hdescent : baseEnd_1426753 < baseStart_1426753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426817 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 5]
def baseStart_1426817 : Nat := 118140960795 + 1426817 * 2 ^ 59
def prefixEnd_1426817 : Nat := 4983230072969 + 3 ^ 40 * 1426817 * 2
def baseEnd_1426817 : Nat := 162809539334722067916821

theorem tailTrace_1426817 : CollatzResearch.WordTrace tailWord_1426817 prefixEnd_1426817 162809539334722067916821 := by
  unfold tailWord_1426817
  simp only [CollatzResearch.WordTrace]
  refine ⟨52040291271893164788278705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34693527514595443192185803 52040291271893164788278705)
  ·
    refine ⟨39030218453919873591209029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52040291271893164788278705 39030218453919873591209029)
    ·
      refine ⟨7318165960109976298351693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39030218453919873591209029 7318165960109976298351693)
      ·
        refine ⟨2744312235041241111881885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7318165960109976298351693 2744312235041241111881885)
        ·
          refine ⟨1029117088140465416955707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2744312235041241111881885 1029117088140465416955707)
          ·
            refine ⟨1543675632210698125433561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029117088140465416955707 1543675632210698125433561)
            ·
              refine ⟨1157756724158023594075171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543675632210698125433561 1157756724158023594075171)
              ·
                refine ⟨1736635086237035391112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157756724158023594075171 1736635086237035391112757)
                ·
                  refine ⟨162809539334722067916821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1736635086237035391112757 162809539334722067916821)
                  ·
                    rfl

theorem cell22_1426817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_1426817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426817 prefixEnd_1426817 := by exact prefixLift 1426817
  have htrace : WordTrace (prefixWord ++ tailWord_1426817) baseStart_1426817 baseEnd_1426817 := by
    simpa [prefixWord, tailWord_1426817, baseEnd_1426817] using wordTrace_append hprefix tailTrace_1426817
  have hstable : (prefixWord ++ tailWord_1426817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426817).length < 2 ^ (prefixWord ++ tailWord_1426817).sum := by decide
  have hdescent : baseEnd_1426817 < baseStart_1426817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426841 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_1426841 : Nat := 118140960795 + 1426841 * 2 ^ 59
def prefixEnd_1426841 : Nat := 4983230072969 + 3 ^ 40 * 1426841 * 2
def baseEnd_1426841 : Nat := 488436833694638141150389

theorem tailTrace_1426841 : CollatzResearch.WordTrace tailWord_1426841 prefixEnd_1426841 488436833694638141150389 := by
  unfold tailWord_1426841
  simp only [CollatzResearch.WordTrace]
  refine ⟨52041166623806216887152377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34694111082537477924768251 52041166623806216887152377)
  ·
    refine ⟨39030874967854662665364283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52041166623806216887152377 39030874967854662665364283)
    ·
      refine ⟨58546312451781993998046425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39030874967854662665364283 58546312451781993998046425)
      ·
        refine ⟨43909734338836495498534819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58546312451781993998046425 43909734338836495498534819)
        ·
          refine ⟨65864601508254743247802229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43909734338836495498534819 65864601508254743247802229)
          ·
            refine ⟨6174806391398882179481459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65864601508254743247802229 6174806391398882179481459)
            ·
              refine ⟨9262209587098323269222189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174806391398882179481459 9262209587098323269222189)
              ·
                refine ⟨3473328595161871225958321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9262209587098323269222189 3473328595161871225958321)
                ·
                  refine ⟨2604996446371403419468741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473328595161871225958321 2604996446371403419468741)
                  ·
                    refine ⟨488436833694638141150389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604996446371403419468741 488436833694638141150389)
                    ·
                      rfl

theorem cell22_1426841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_1426841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426841 prefixEnd_1426841 := by exact prefixLift 1426841
  have htrace : WordTrace (prefixWord ++ tailWord_1426841) baseStart_1426841 baseEnd_1426841 := by
    simpa [prefixWord, tailWord_1426841, baseEnd_1426841] using wordTrace_append hprefix tailTrace_1426841
  have hstable : (prefixWord ++ tailWord_1426841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426841).length < 2 ^ (prefixWord ++ tailWord_1426841).sum := by decide
  have hdescent : baseEnd_1426841 < baseStart_1426841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426856 : List Nat := [2, 1, 6, 1, 12]
def baseStart_1426856 : Nat := 118140960795 + 1426856 * 2 ^ 59
def prefixEnd_1426856 : Nat := 4983230072969 + 3 ^ 40 * 1426856 * 2
def baseEnd_1426856 : Nat := 2010049253091288485701

theorem tailTrace_1426856 : CollatzResearch.WordTrace tailWord_1426856 prefixEnd_1426856 2010049253091288485701 := by
  unfold tailWord_1426856
  simp only [CollatzResearch.WordTrace]
  refine ⟨26020856859375937224474211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34694475812501249632632281 26020856859375937224474211)
  ·
    refine ⟨39031285289063905836711317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26020856859375937224474211 39031285289063905836711317)
    ·
      refine ⟨1829591497924870586095843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39031285289063905836711317 1829591497924870586095843)
      ·
        refine ⟨2744387246887305879143765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829591497924870586095843 2744387246887305879143765)
        ·
          refine ⟨2010049253091288485701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2744387246887305879143765 2010049253091288485701)
          ·
            rfl

theorem cell22_1426856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 12].length) (baseStart_1426856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426856 prefixEnd_1426856 := by exact prefixLift 1426856
  have htrace : WordTrace (prefixWord ++ tailWord_1426856) baseStart_1426856 baseEnd_1426856 := by
    simpa [prefixWord, tailWord_1426856, baseEnd_1426856] using wordTrace_append hprefix tailTrace_1426856
  have hstable : (prefixWord ++ tailWord_1426856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426856).length < 2 ^ (prefixWord ++ tailWord_1426856).sum := by decide
  have hdescent : baseEnd_1426856 < baseStart_1426856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426873 : List Nat := [1, 2, 1, 4, 4, 2, 1, 7]
def baseStart_1426873 : Nat := 118140960795 + 1426873 * 2 ^ 59
def prefixEnd_1426873 : Nat := 4983230072969 + 3 ^ 40 * 1426873 * 2
def baseEnd_1426873 : Nat := 54271976438733413816699

theorem tailTrace_1426873 : CollatzResearch.WordTrace tailWord_1426873 prefixEnd_1426873 54271976438733413816699 := by
  unfold tailWord_1426873
  simp only [CollatzResearch.WordTrace]
  refine ⟨52042333759690286352317273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34694889173126857568211515 52042333759690286352317273)
  ·
    refine ⟨39031750319767714764237955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52042333759690286352317273 39031750319767714764237955)
    ·
      refine ⟨58547625479651572146356933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39031750319767714764237955 58547625479651572146356933)
      ·
        refine ⟨10977679777434669777441925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58547625479651572146356933 10977679777434669777441925)
        ·
          refine ⟨2058314958269000583270361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10977679777434669777441925 2058314958269000583270361)
          ·
            refine ⟨1543736218701750437452771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058314958269000583270361 1543736218701750437452771)
            ·
              refine ⟨2315604328052625656179157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543736218701750437452771 2315604328052625656179157)
              ·
                refine ⟨54271976438733413816699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2315604328052625656179157 54271976438733413816699)
                ·
                  rfl

theorem cell22_1426873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 7].length) (baseStart_1426873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426873 prefixEnd_1426873 := by exact prefixLift 1426873
  have htrace : WordTrace (prefixWord ++ tailWord_1426873) baseStart_1426873 baseEnd_1426873 := by
    simpa [prefixWord, tailWord_1426873, baseEnd_1426873] using wordTrace_append hprefix tailTrace_1426873
  have hstable : (prefixWord ++ tailWord_1426873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426873).length < 2 ^ (prefixWord ++ tailWord_1426873).sum := by decide
  have hdescent : baseEnd_1426873 < baseStart_1426873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426888 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1426888 : Nat := 118140960795 + 1426888 * 2 ^ 59
def prefixEnd_1426888 : Nat := 4983230072969 + 3 ^ 40 * 1426888 * 2
def baseEnd_1426888 : Nat := 488452922755145685225245

theorem tailTrace_1426888 : CollatzResearch.WordTrace tailWord_1426888 prefixEnd_1426888 488452922755145685225245 := by
  unfold tailWord_1426888
  simp only [CollatzResearch.WordTrace]
  refine ⟨26021440427317971957056659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34695253903090629276075545 26021440427317971957056659)
  ·
    refine ⟨39032160640976957935584989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26021440427317971957056659 39032160640976957935584989)
    ·
      refine ⟨14637060240366359225844371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39032160640976957935584989 14637060240366359225844371)
      ·
        refine ⟨21955590360549538838766557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14637060240366359225844371 21955590360549538838766557)
        ·
          refine ⟨8233346385206077064537459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21955590360549538838766557 8233346385206077064537459)
          ·
            refine ⟨12350019577809115596806189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233346385206077064537459 12350019577809115596806189)
            ·
              refine ⟨4631257341678418348802321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350019577809115596806189 4631257341678418348802321)
              ·
                refine ⟨3473443006258813761601741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631257341678418348802321 3473443006258813761601741)
                ·
                  refine ⟨1302541127347055160600653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3473443006258813761601741 1302541127347055160600653)
                  ·
                    refine ⟨488452922755145685225245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302541127347055160600653 488452922755145685225245)
                    ·
                      rfl

theorem cell22_1426888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1426888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426888 prefixEnd_1426888 := by exact prefixLift 1426888
  have htrace : WordTrace (prefixWord ++ tailWord_1426888) baseStart_1426888 baseEnd_1426888 := by
    simpa [prefixWord, tailWord_1426888, baseEnd_1426888] using wordTrace_append hprefix tailTrace_1426888
  have hstable : (prefixWord ++ tailWord_1426888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426888).length < 2 ^ (prefixWord ++ tailWord_1426888).sum := by decide
  have hdescent : baseEnd_1426888 < baseStart_1426888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426901 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 7]
def baseStart_1426901 : Nat := 118140960795 + 1426901 * 2 ^ 59
def prefixEnd_1426901 : Nat := 4983230072969 + 3 ^ 40 * 1426901 * 2
def baseEnd_1426901 : Nat := 162819124306939328216735

theorem tailTrace_1426901 : CollatzResearch.WordTrace tailWord_1426901 prefixEnd_1426901 162819124306939328216735 := by
  unfold tailWord_1426901
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043355003588847134336557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34695570002392564756224371 52043355003588847134336557)
  ·
    refine ⟨19516258126345817675376209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52043355003588847134336557 19516258126345817675376209)
    ·
      refine ⟨14637193594759363256532157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19516258126345817675376209 14637193594759363256532157)
      ·
        refine ⟨5488947598034761221199559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14637193594759363256532157 5488947598034761221199559)
        ·
          refine ⟨8233421397052141831799339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488947598034761221199559 8233421397052141831799339)
          ·
            refine ⟨12350132095578212747699009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233421397052141831799339 12350132095578212747699009)
            ·
              refine ⟨9262599071683659560774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350132095578212747699009 9262599071683659560774257)
              ·
                refine ⟨6946949303762744670580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262599071683659560774257 6946949303762744670580693)
                ·
                  refine ⟨162819124306939328216735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6946949303762744670580693 162819124306939328216735)
                  ·
                    rfl

theorem cell22_1426901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_1426901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426901 prefixEnd_1426901 := by exact prefixLift 1426901
  have htrace : WordTrace (prefixWord ++ tailWord_1426901) baseStart_1426901 baseEnd_1426901 := by
    simpa [prefixWord, tailWord_1426901, baseEnd_1426901] using wordTrace_append hprefix tailTrace_1426901
  have hstable : (prefixWord ++ tailWord_1426901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426901).length < 2 ^ (prefixWord ++ tailWord_1426901).sum := by decide
  have hdescent : baseEnd_1426901 < baseStart_1426901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426905 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_1426905 : Nat := 118140960795 + 1426905 * 2 ^ 59
def prefixEnd_1426905 : Nat := 4983230072969 + 3 ^ 40 * 1426905 * 2
def baseEnd_1426905 : Nat := 488458742202563307550193

theorem tailTrace_1426905 : CollatzResearch.WordTrace tailWord_1426905 prefixEnd_1426905 488458742202563307550193 := by
  unfold tailWord_1426905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043500895574355817482169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34695667263716237211654779 52043500895574355817482169)
  ·
    refine ⟨39032625671680766863111627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52043500895574355817482169 39032625671680766863111627)
    ·
      refine ⟨58548938507521150294667441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39032625671680766863111627 58548938507521150294667441)
      ·
        refine ⟨43911703880640862721000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58548938507521150294667441 43911703880640862721000581)
        ·
          refine ⟨8233444477620161760187609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43911703880640862721000581 8233444477620161760187609)
          ·
            refine ⟨6175083358215121320140707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8233444477620161760187609 6175083358215121320140707)
            ·
              refine ⟨9262625037322681980211061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175083358215121320140707 9262625037322681980211061)
              ·
                refine ⟨868371097249001435644787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9262625037322681980211061 868371097249001435644787)
                ·
                  refine ⟨1302556645873502153467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868371097249001435644787 1302556645873502153467181)
                  ·
                    refine ⟨488458742202563307550193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302556645873502153467181 488458742202563307550193)
                    ·
                      rfl

theorem cell22_1426905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_1426905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426905 prefixEnd_1426905 := by exact prefixLift 1426905
  have htrace : WordTrace (prefixWord ++ tailWord_1426905) baseStart_1426905 baseEnd_1426905 := by
    simpa [prefixWord, tailWord_1426905, baseEnd_1426905] using wordTrace_append hprefix tailTrace_1426905
  have hstable : (prefixWord ++ tailWord_1426905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426905).length < 2 ^ (prefixWord ++ tailWord_1426905).sum := by decide
  have hdescent : baseEnd_1426905 < baseStart_1426905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426931 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_1426931 : Nat := 118140960795 + 1426931 * 2 ^ 59
def prefixEnd_1426931 : Nat := 4983230072969 + 3 ^ 40 * 1426931 * 2
def baseEnd_1426931 : Nat := 488467642533907906400113

theorem tailTrace_1426931 : CollatzResearch.WordTrace tailWord_1426931 prefixEnd_1426931 488467642533907906400113 := by
  unfold tailWord_1426931
  simp only [CollatzResearch.WordTrace]
  refine ⟨52044449193480162257928647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34696299462320108171952431 52044449193480162257928647)
  ·
    refine ⟨78066673790220243386892971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52044449193480162257928647 78066673790220243386892971)
    ·
      refine ⟨117100010685330365080339457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78066673790220243386892971 117100010685330365080339457)
      ·
        refine ⟨87825008013997773810254593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117100010685330365080339457 87825008013997773810254593)
        ·
          refine ⟨65868756010498330357690945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87825008013997773810254593 65868756010498330357690945)
          ·
            refine ⟨49401567007873747768268209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65868756010498330357690945 49401567007873747768268209)
            ·
              refine ⟨37051175255905310826201157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49401567007873747768268209 37051175255905310826201157)
              ·
                refine ⟨6947095360482245779912717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37051175255905310826201157 6947095360482245779912717)
                ·
                  refine ⟨2605160760180842167467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947095360482245779912717 2605160760180842167467269)
                  ·
                    refine ⟨488467642533907906400113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605160760180842167467269 488467642533907906400113)
                    ·
                      rfl

theorem cell22_1426931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_1426931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426931 prefixEnd_1426931 := by exact prefixLift 1426931
  have htrace : WordTrace (prefixWord ++ tailWord_1426931) baseStart_1426931 baseEnd_1426931 := by
    simpa [prefixWord, tailWord_1426931, baseEnd_1426931] using wordTrace_append hprefix tailTrace_1426931
  have hstable : (prefixWord ++ tailWord_1426931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426931).length < 2 ^ (prefixWord ++ tailWord_1426931).sum := by decide
  have hdescent : baseEnd_1426931 < baseStart_1426931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426961 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_1426961 : Nat := 118140960795 + 1426961 * 2 ^ 59
def prefixEnd_1426961 : Nat := 4983230072969 + 3 ^ 40 * 1426961 * 2
def baseEnd_1426961 : Nat := 488477912146997828150021

theorem tailTrace_1426961 : CollatzResearch.WordTrace tailWord_1426961 prefixEnd_1426961 488477912146997828150021 := by
  unfold tailWord_1426961
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045543383371477381520737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34697028922247651587680491 52045543383371477381520737)
  ·
    refine ⟨39034157537528608036140553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52045543383371477381520737 39034157537528608036140553)
    ·
      refine ⟨29275618153146456027105415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39034157537528608036140553 29275618153146456027105415)
      ·
        refine ⟨43913427229719684040658123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29275618153146456027105415 43913427229719684040658123)
        ·
          refine ⟨65870140844579526060987185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43913427229719684040658123 65870140844579526060987185)
          ·
            refine ⟨49402605633434644545740389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65870140844579526060987185 49402605633434644545740389)
            ·
              refine ⟨9262988556268995852326323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49402605633434644545740389 9262988556268995852326323)
              ·
                refine ⟨13894482834403493778489485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262988556268995852326323 13894482834403493778489485)
                ·
                  refine ⟨5210431062901310166933557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13894482834403493778489485 5210431062901310166933557)
                  ·
                    refine ⟨488477912146997828150021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5210431062901310166933557 488477912146997828150021)
                    ·
                      rfl

theorem cell22_1426961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_1426961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426961 prefixEnd_1426961 := by exact prefixLift 1426961
  have htrace : WordTrace (prefixWord ++ tailWord_1426961) baseStart_1426961 baseEnd_1426961 := by
    simpa [prefixWord, tailWord_1426961, baseEnd_1426961] using wordTrace_append hprefix tailTrace_1426961
  have hstable : (prefixWord ++ tailWord_1426961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426961).length < 2 ^ (prefixWord ++ tailWord_1426961).sum := by decide
  have hdescent : baseEnd_1426961 < baseStart_1426961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426995 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 2, 3]
def baseStart_1426995 : Nat := 118140960795 + 1426995 * 2 ^ 59
def prefixEnd_1426995 : Nat := 4983230072969 + 3 ^ 40 * 1426995 * 2
def baseEnd_1426995 : Nat := 488489551041833072799917

theorem tailTrace_1426995 : CollatzResearch.WordTrace tailWord_1426995 prefixEnd_1426995 488489551041833072799917 := by
  unfold tailWord_1426995
  simp only [CollatzResearch.WordTrace]
  refine ⟨52046783465248301188258439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34697855643498867458838959 52046783465248301188258439)
  ·
    refine ⟨78070175197872451782387659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52046783465248301188258439 78070175197872451782387659)
    ·
      refine ⟨117105262796808677673581489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78070175197872451782387659 117105262796808677673581489)
      ·
        refine ⟨87828947097606508255186117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117105262796808677673581489 87828947097606508255186117)
        ·
          refine ⟨16467927580801220297847397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87828947097606508255186117 16467927580801220297847397)
          ·
            refine ⟨3087736421400228805846387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16467927580801220297847397 3087736421400228805846387)
            ·
              refine ⟨4631604632100343208769581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087736421400228805846387 4631604632100343208769581)
              ·
                refine ⟨1736851737037628703288593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4631604632100343208769581 1736851737037628703288593)
                ·
                  refine ⟨1302638802778221527466445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736851737037628703288593 1302638802778221527466445)
                  ·
                    refine ⟨488489551041833072799917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302638802778221527466445 488489551041833072799917)
                    ·
                      rfl

theorem cell22_1426995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].length) (baseStart_1426995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1426995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1426995 prefixEnd_1426995 := by exact prefixLift 1426995
  have htrace : WordTrace (prefixWord ++ tailWord_1426995) baseStart_1426995 baseEnd_1426995 := by
    simpa [prefixWord, tailWord_1426995, baseEnd_1426995] using wordTrace_append hprefix tailTrace_1426995
  have hstable : (prefixWord ++ tailWord_1426995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426995).length < 2 ^ (prefixWord ++ tailWord_1426995).sum := by decide
  have hdescent : baseEnd_1426995 < baseStart_1426995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427117 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1427117 : Nat := 118140960795 + 1427117 * 2 ^ 59
def prefixEnd_1427117 : Nat := 4983230072969 + 3 ^ 40 * 1427117 * 2
def baseEnd_1427117 : Nat := 488531314135065421249543

theorem tailTrace_1427117 : CollatzResearch.WordTrace tailWord_1427117 prefixEnd_1427117 488531314135065421249543 := by
  unfold tailWord_1427117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52051233170806316024199605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34700822113870877349466403 52051233170806316024199605)
  ·
    refine ⟨4879803109763092127268713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52051233170806316024199605 4879803109763092127268713)
    ·
      refine ⟨3659852332322319095451535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4879803109763092127268713 3659852332322319095451535)
      ·
        refine ⟨5489778498483478643177303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659852332322319095451535 5489778498483478643177303)
        ·
          refine ⟨8234667747725217964765955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489778498483478643177303 8234667747725217964765955)
          ·
            refine ⟨12352001621587826947148933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234667747725217964765955 12352001621587826947148933)
            ·
              refine ⟨2316000304047717552590425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12352001621587826947148933 2316000304047717552590425)
              ·
                refine ⟨1737000228035788164442819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316000304047717552590425 1737000228035788164442819)
                ·
                  refine ⟨2605500342053682246664229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737000228035788164442819 2605500342053682246664229)
                  ·
                    refine ⟨488531314135065421249543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605500342053682246664229 488531314135065421249543)
                    ·
                      rfl

theorem cell22_1427117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1427117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427117 prefixEnd_1427117 := by exact prefixLift 1427117
  have htrace : WordTrace (prefixWord ++ tailWord_1427117) baseStart_1427117 baseEnd_1427117 := by
    simpa [prefixWord, tailWord_1427117, baseEnd_1427117] using wordTrace_append hprefix tailTrace_1427117
  have hstable : (prefixWord ++ tailWord_1427117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427117).length < 2 ^ (prefixWord ++ tailWord_1427117).sum := by decide
  have hdescent : baseEnd_1427117 < baseStart_1427117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427128 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1427128 : Nat := 118140960795 + 1427128 * 2 ^ 59
def prefixEnd_1427128 : Nat := 4983230072969 + 3 ^ 40 * 1427128 * 2
def baseEnd_1427128 : Nat := 488535079659865059224509

theorem tailTrace_1427128 : CollatzResearch.WordTrace tailWord_1427128 prefixEnd_1427128 488535079659865059224509 := by
  unfold tailWord_1427128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26025817186883232451425019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34701089582510976601900025 26025817186883232451425019)
  ·
    refine ⟨39038725780324848677137529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26025817186883232451425019 39038725780324848677137529)
    ·
      refine ⟨29279044335243636507853147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39038725780324848677137529 29279044335243636507853147)
      ·
        refine ⟨43918566502865454761779721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29279044335243636507853147 43918566502865454761779721)
        ·
          refine ⟨32938924877149091071334791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43918566502865454761779721 32938924877149091071334791)
          ·
            refine ⟨49408387315723636607002187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32938924877149091071334791 49408387315723636607002187)
            ·
              refine ⟨74112580973585454910503281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49408387315723636607002187 74112580973585454910503281)
              ·
                refine ⟨55584435730189091182877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74112580973585454910503281 55584435730189091182877461)
                ·
                  refine ⟨2605520424852613649197381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55584435730189091182877461 2605520424852613649197381)
                  ·
                    refine ⟨488535079659865059224509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605520424852613649197381 488535079659865059224509)
                    ·
                      rfl

theorem cell22_1427128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1427128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427128 prefixEnd_1427128 := by exact prefixLift 1427128
  have htrace : WordTrace (prefixWord ++ tailWord_1427128) baseStart_1427128 baseEnd_1427128 := by
    simpa [prefixWord, tailWord_1427128, baseEnd_1427128] using wordTrace_append hprefix tailTrace_1427128
  have hstable : (prefixWord ++ tailWord_1427128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427128).length < 2 ^ (prefixWord ++ tailWord_1427128).sum := by decide
  have hdescent : baseEnd_1427128 < baseStart_1427128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427130 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_1427130 : Nat := 118140960795 + 1427130 * 2 ^ 59
def prefixEnd_1427130 : Nat := 4983230072969 + 3 ^ 40 * 1427130 * 2
def baseEnd_1427130 : Nat := 488535764300737720674503

theorem tailTrace_1427130 : CollatzResearch.WordTrace tailWord_1427130 prefixEnd_1427130 488535764300737720674503 := by
  unfold tailWord_1427130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012926829939804811105711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34701138213172812829615229 13012926829939804811105711)
  ·
    refine ⟨19519390244909707216658567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012926829939804811105711 19519390244909707216658567)
    ·
      refine ⟨29279085367364560824987851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19519390244909707216658567 29279085367364560824987851)
      ·
        refine ⟨43918628051046841237481777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29279085367364560824987851 43918628051046841237481777)
        ·
          refine ⟨32938971038285130928111333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43918628051046841237481777 32938971038285130928111333)
          ·
            refine ⟨6176057069678462049020875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32938971038285130928111333 6176057069678462049020875)
            ·
              refine ⟨9264085604517693073531313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176057069678462049020875 9264085604517693073531313)
              ·
                refine ⟨6948064203388269805148485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264085604517693073531313 6948064203388269805148485)
                ·
                  refine ⟨1302762038135300588465341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6948064203388269805148485 1302762038135300588465341)
                  ·
                    refine ⟨488535764300737720674503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302762038135300588465341 488535764300737720674503)
                    ·
                      rfl

theorem cell22_1427130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_1427130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427130 prefixEnd_1427130 := by exact prefixLift 1427130
  have htrace : WordTrace (prefixWord ++ tailWord_1427130) baseStart_1427130 baseEnd_1427130 := by
    simpa [prefixWord, tailWord_1427130, baseEnd_1427130] using wordTrace_append hprefix tailTrace_1427130
  have hstable : (prefixWord ++ tailWord_1427130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427130).length < 2 ^ (prefixWord ++ tailWord_1427130).sum := by decide
  have hdescent : baseEnd_1427130 < baseStart_1427130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427132 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_1427132 : Nat := 118140960795 + 1427132 * 2 ^ 59
def prefixEnd_1427132 : Nat := 4983230072969 + 3 ^ 40 * 1427132 * 2
def baseEnd_1427132 : Nat := 162845482980536794041499

theorem tailTrace_1427132 : CollatzResearch.WordTrace tailWord_1427132 prefixEnd_1427132 162845482980536794041499 := by
  unfold tailWord_1427132
  simp only [CollatzResearch.WordTrace]
  refine ⟨26025890132875986792997825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34701186843834649057330433 26025890132875986792997825)
  ·
    refine ⟨19519417599656990094748369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26025890132875986792997825 19519417599656990094748369)
    ·
      refine ⟨14639563199742742571061277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19519417599656990094748369 14639563199742742571061277)
      ·
        refine ⟨5489836199903528464147979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14639563199742742571061277 5489836199903528464147979)
        ·
          refine ⟨8234754299855292696221969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489836199903528464147979 8234754299855292696221969)
          ·
            refine ⟨6176065724891469522166477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8234754299855292696221969 6176065724891469522166477)
            ·
              refine ⟨2316024646834301070812429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6176065724891469522166477 2316024646834301070812429)
              ·
                refine ⟨868509242562862901554661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2316024646834301070812429 868509242562862901554661)
                ·
                  refine ⟨162845482980536794041499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868509242562862901554661 162845482980536794041499)
                  ·
                    rfl

theorem cell22_1427132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_1427132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427132 prefixEnd_1427132 := by exact prefixLift 1427132
  have htrace : WordTrace (prefixWord ++ tailWord_1427132) baseStart_1427132 baseEnd_1427132 := by
    simpa [prefixWord, tailWord_1427132, baseEnd_1427132] using wordTrace_append hprefix tailTrace_1427132
  have hstable : (prefixWord ++ tailWord_1427132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427132).length < 2 ^ (prefixWord ++ tailWord_1427132).sum := by decide
  have hdescent : baseEnd_1427132 < baseStart_1427132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427149 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1427149 : Nat := 118140960795 + 1427149 * 2 ^ 59
def prefixEnd_1427149 : Nat := 4983230072969 + 3 ^ 40 * 1427149 * 2
def baseEnd_1427149 : Nat := 162847422796342668149815

theorem tailTrace_1427149 : CollatzResearch.WordTrace tailWord_1427149 prefixEnd_1427149 162847422796342668149815 := by
  unfold tailWord_1427149
  simp only [CollatzResearch.WordTrace]
  refine ⟨52052400306690385489364501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34701600204460256992909667 52052400306690385489364501)
  ·
    refine ⟨2439956264376111819813961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52052400306690385489364501 2439956264376111819813961)
    ·
      refine ⟨1829967198282083864860471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2439956264376111819813961 1829967198282083864860471)
      ·
        refine ⟨2744950797423125797290707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829967198282083864860471 2744950797423125797290707)
        ·
          refine ⟨4117426196134688695936061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744950797423125797290707 4117426196134688695936061)
          ·
            refine ⟨1544034823550508260976023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4117426196134688695936061 1544034823550508260976023)
            ·
              refine ⟨2316052235325762391464035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544034823550508260976023 2316052235325762391464035)
              ·
                refine ⟨3474078352988643587196053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316052235325762391464035 3474078352988643587196053)
                ·
                  refine ⟨162847422796342668149815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3474078352988643587196053 162847422796342668149815)
                  ·
                    rfl

theorem cell22_1427149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1427149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427149 prefixEnd_1427149 := by exact prefixLift 1427149
  have htrace : WordTrace (prefixWord ++ tailWord_1427149) baseStart_1427149 baseEnd_1427149 := by
    simpa [prefixWord, tailWord_1427149, baseEnd_1427149] using wordTrace_append hprefix tailTrace_1427149
  have hstable : (prefixWord ++ tailWord_1427149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427149).length < 2 ^ (prefixWord ++ tailWord_1427149).sum := by decide
  have hdescent : baseEnd_1427149 < baseStart_1427149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427235 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_1427235 : Nat := 118140960795 + 1427235 * 2 ^ 59
def prefixEnd_1427235 : Nat := 4983230072969 + 3 ^ 40 * 1427235 * 2
def baseEnd_1427235 : Nat := 488571707946552446799181

theorem tailTrace_1427235 : CollatzResearch.WordTrace tailWord_1427235 prefixEnd_1427235 488571707946552446799181 := by
  unfold tailWord_1427235
  simp only [CollatzResearch.WordTrace]
  refine ⟨52055536984378822176995159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34703691322919214784663439 52055536984378822176995159)
  ·
    refine ⟨78083305476568233265492739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52055536984378822176995159 78083305476568233265492739)
    ·
      refine ⟨117124958214852349898239109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78083305476568233265492739 117124958214852349898239109)
      ·
        refine ⟨21960929665284815605919833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117124958214852349898239109 21960929665284815605919833)
        ·
          refine ⟨16470697248963611704439875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21960929665284815605919833 16470697248963611704439875)
          ·
            refine ⟨24706045873445417556659813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16470697248963611704439875 24706045873445417556659813)
            ·
              refine ⟨4632383601271015791873715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24706045873445417556659813 4632383601271015791873715)
              ·
                refine ⟨6948575401906523687810573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632383601271015791873715 6948575401906523687810573)
                ·
                  refine ⟨2605715775714946382928965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6948575401906523687810573 2605715775714946382928965)
                  ·
                    refine ⟨488571707946552446799181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605715775714946382928965 488571707946552446799181)
                    ·
                      rfl

theorem cell22_1427235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_1427235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427235 prefixEnd_1427235 := by exact prefixLift 1427235
  have htrace : WordTrace (prefixWord ++ tailWord_1427235) baseStart_1427235 baseEnd_1427235 := by
    simpa [prefixWord, tailWord_1427235, baseEnd_1427235] using wordTrace_append hprefix tailTrace_1427235
  have hstable : (prefixWord ++ tailWord_1427235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427235).length < 2 ^ (prefixWord ++ tailWord_1427235).sum := by decide
  have hdescent : baseEnd_1427235 < baseStart_1427235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427267 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 4]
def baseStart_1427267 : Nat := 118140960795 + 1427267 * 2 ^ 59
def prefixEnd_1427267 : Nat := 4983230072969 + 3 ^ 40 * 1427267 * 2
def baseEnd_1427267 : Nat := 162860887400171676666361

theorem tailTrace_1427267 : CollatzResearch.WordTrace tailWord_1427267 prefixEnd_1427267 162860887400171676666361 := by
  unfold tailWord_1427267
  simp only [CollatzResearch.WordTrace]
  refine ⟨52056704120262891642160055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34704469413508594428106703 52056704120262891642160055)
  ·
    refine ⟨78085056180394337463240083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52056704120262891642160055 78085056180394337463240083)
    ·
      refine ⟨117127584270591506194860125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78085056180394337463240083 117127584270591506194860125)
      ·
        refine ⟨43922844101471814823072547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117127584270591506194860125 43922844101471814823072547)
        ·
          refine ⟨65884266152207722234608821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43922844101471814823072547 65884266152207722234608821)
          ·
            refine ⟨6176649951769473959494577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65884266152207722234608821 6176649951769473959494577)
            ·
              refine ⟨4632487463827105469620933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6176649951769473959494577 4632487463827105469620933)
              ·
                refine ⟨868591399467582275553925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4632487463827105469620933 868591399467582275553925)
                ·
                  refine ⟨162860887400171676666361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868591399467582275553925 162860887400171676666361)
                  ·
                    rfl

theorem cell22_1427267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 4].length) (baseStart_1427267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427267 prefixEnd_1427267 := by exact prefixLift 1427267
  have htrace : WordTrace (prefixWord ++ tailWord_1427267) baseStart_1427267 baseEnd_1427267 := by
    simpa [prefixWord, tailWord_1427267, baseEnd_1427267] using wordTrace_append hprefix tailTrace_1427267
  have hstable : (prefixWord ++ tailWord_1427267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427267).length < 2 ^ (prefixWord ++ tailWord_1427267).sum := by decide
  have hdescent : baseEnd_1427267 < baseStart_1427267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427282 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1427282 : Nat := 118140960795 + 1427282 * 2 ^ 59
def prefixEnd_1427282 : Nat := 4983230072969 + 3 ^ 40 * 1427282 * 2
def baseEnd_1427282 : Nat := 488587797007059990874037

theorem tailTrace_1427282 : CollatzResearch.WordTrace tailWord_1427282 prefixEnd_1427282 488587797007059990874037 := by
  unfold tailWord_1427282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014312803802137300989025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34704834143472366135970733 13014312803802137300989025)
  ·
    refine ⟨9760734602851602975741769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13014312803802137300989025 9760734602851602975741769)
    ·
      refine ⟨7320550952138702231806327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9760734602851602975741769 7320550952138702231806327)
      ·
        refine ⟨10980826428208053347709491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320550952138702231806327 10980826428208053347709491)
        ·
          refine ⟨16471239642312080021564237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10980826428208053347709491 16471239642312080021564237)
          ·
            refine ⟨6176714865867030008086589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16471239642312080021564237 6176714865867030008086589)
            ·
              refine ⟨2316268074700136253032471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6176714865867030008086589 2316268074700136253032471)
              ·
                refine ⟨3474402112050204379548707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316268074700136253032471 3474402112050204379548707)
                ·
                  refine ⟨5211603168075306569323061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474402112050204379548707 5211603168075306569323061)
                  ·
                    refine ⟨488587797007059990874037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5211603168075306569323061 488587797007059990874037)
                    ·
                      rfl

theorem cell22_1427282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1427282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427282 prefixEnd_1427282 := by exact prefixLift 1427282
  have htrace : WordTrace (prefixWord ++ tailWord_1427282) baseStart_1427282 baseEnd_1427282 := by
    simpa [prefixWord, tailWord_1427282, baseEnd_1427282] using wordTrace_append hprefix tailTrace_1427282
  have hstable : (prefixWord ++ tailWord_1427282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427282).length < 2 ^ (prefixWord ++ tailWord_1427282).sum := by decide
  have hdescent : baseEnd_1427282 < baseStart_1427282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427295 : List Nat := [1, 1, 2, 3, 1, 5, 1, 8]
def baseStart_1427295 : Nat := 118140960795 + 1427295 * 2 ^ 59
def prefixEnd_1427295 : Nat := 4983230072969 + 3 ^ 40 * 1427295 * 2
def baseEnd_1427295 : Nat := 54288027463636921144333

theorem tailTrace_1427295 : CollatzResearch.WordTrace tailWord_1427295 prefixEnd_1427295 54288027463636921144333 := by
  unfold tailWord_1427295
  simp only [CollatzResearch.WordTrace]
  refine ⟨52057725364161452424179339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34705150242774301616119559 52057725364161452424179339)
  ·
    refine ⟨78086588046242178636269009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52057725364161452424179339 78086588046242178636269009)
    ·
      refine ⟨58564941034681633977201757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78086588046242178636269009 58564941034681633977201757)
      ·
        refine ⟨21961852888005612741450659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58564941034681633977201757 21961852888005612741450659)
        ·
          refine ⟨32942779332008419112175989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961852888005612741450659 32942779332008419112175989)
          ·
            refine ⟨3088385562375789291766499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32942779332008419112175989 3088385562375789291766499)
            ·
              refine ⟨4632578343563683937649749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088385562375789291766499 4632578343563683937649749)
              ·
                refine ⟨54288027463636921144333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4632578343563683937649749 54288027463636921144333)
                ·
                  rfl

theorem cell22_1427295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 8].length) (baseStart_1427295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427295 prefixEnd_1427295 := by exact prefixLift 1427295
  have htrace : WordTrace (prefixWord ++ tailWord_1427295) baseStart_1427295 baseEnd_1427295 := by
    simpa [prefixWord, tailWord_1427295, baseEnd_1427295] using wordTrace_append hprefix tailTrace_1427295
  have hstable : (prefixWord ++ tailWord_1427295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427295).length < 2 ^ (prefixWord ++ tailWord_1427295).sum := by decide
  have hdescent : baseEnd_1427295 < baseStart_1427295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427318 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1427318 : Nat := 118140960795 + 1427318 * 2 ^ 59
def prefixEnd_1427318 : Nat := 4983230072969 + 3 ^ 40 * 1427318 * 2
def baseEnd_1427318 : Nat := 162866706847589298991309

theorem tailTrace_1427318 : CollatzResearch.WordTrace tailWord_1427318 prefixEnd_1427318 162866706847589298991309 := by
  unfold tailWord_1427318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253660265192382959516663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34705709495385418234844405 3253660265192382959516663)
  ·
    refine ⟨4880490397788574439274995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253660265192382959516663 4880490397788574439274995)
    ·
      refine ⟨7320735596682861658912493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880490397788574439274995 7320735596682861658912493)
      ·
        refine ⟨2745275848756073122092185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7320735596682861658912493 2745275848756073122092185)
        ·
          refine ⟨2058956886567054841569139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745275848756073122092185 2058956886567054841569139)
          ·
            refine ⟨3088435329850582262353709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058956886567054841569139 3088435329850582262353709)
            ·
              refine ⟨1158163248693968348382641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3088435329850582262353709 1158163248693968348382641)
              ·
                refine ⟨868622436520476261286981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158163248693968348382641 868622436520476261286981)
                ·
                  refine ⟨162866706847589298991309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868622436520476261286981 162866706847589298991309)
                  ·
                    rfl

theorem cell22_1427318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1427318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427318 prefixEnd_1427318 := by exact prefixLift 1427318
  have htrace : WordTrace (prefixWord ++ tailWord_1427318) baseStart_1427318 baseEnd_1427318 := by
    simpa [prefixWord, tailWord_1427318, baseEnd_1427318] using wordTrace_append hprefix tailTrace_1427318
  have hstable : (prefixWord ++ tailWord_1427318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427318).length < 2 ^ (prefixWord ++ tailWord_1427318).sum := by decide
  have hdescent : baseEnd_1427318 < baseStart_1427318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427325 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1427325 : Nat := 118140960795 + 1427325 * 2 ^ 59
def prefixEnd_1427325 : Nat := 4983230072969 + 3 ^ 40 * 1427325 * 2
def baseEnd_1427325 : Nat := 488602516785822212048905

theorem tailTrace_1427325 : CollatzResearch.WordTrace tailWord_1427325 prefixEnd_1427325 488602516785822212048905 := by
  unfold tailWord_1427325
  simp only [CollatzResearch.WordTrace]
  refine ⟨52058819554052767547771429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34705879702701845031847619 52058819554052767547771429)
  ·
    refine ⟨9761028666384893915207143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52058819554052767547771429 9761028666384893915207143)
    ·
      refine ⟨14641542999577340872810715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761028666384893915207143 14641542999577340872810715)
      ·
        refine ⟨21962314499366011309216073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641542999577340872810715 21962314499366011309216073)
        ·
          refine ⟨16471735874524508481912055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21962314499366011309216073 16471735874524508481912055)
          ·
            refine ⟨24707603811786762722868083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16471735874524508481912055 24707603811786762722868083)
            ·
              refine ⟨37061405717680144084302125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24707603811786762722868083 37061405717680144084302125)
              ·
                refine ⟨13898027144130054031613297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37061405717680144084302125 13898027144130054031613297)
                ·
                  refine ⟨10423520358097540523709973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13898027144130054031613297 10423520358097540523709973)
                  ·
                    refine ⟨488602516785822212048905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10423520358097540523709973 488602516785822212048905)
                    ·
                      rfl

theorem cell22_1427325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1427325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427325 prefixEnd_1427325 := by exact prefixLift 1427325
  have htrace : WordTrace (prefixWord ++ tailWord_1427325) baseStart_1427325 baseEnd_1427325 := by
    simpa [prefixWord, tailWord_1427325, baseEnd_1427325] using wordTrace_append hprefix tailTrace_1427325
  have hstable : (prefixWord ++ tailWord_1427325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427325).length < 2 ^ (prefixWord ++ tailWord_1427325).sum := by decide
  have hdescent : baseEnd_1427325 < baseStart_1427325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427329 : List Nat := [1, 2, 4, 4, 1, 1, 2, 7]
def baseStart_1427329 : Nat := 118140960795 + 1427329 * 2 ^ 59
def prefixEnd_1427329 : Nat := 4983230072969 + 3 ^ 40 * 1427329 * 2
def baseEnd_1427329 : Nat := 54289320674174170549877

theorem tailTrace_1427329 : CollatzResearch.WordTrace tailWord_1427329 prefixEnd_1427329 54289320674174170549877 := by
  unfold tailWord_1427329
  simp only [CollatzResearch.WordTrace]
  refine ⟨52058965446038276230917041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34705976964025517487278027 52058965446038276230917041)
  ·
    refine ⟨39044224084528707173187781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52058965446038276230917041 39044224084528707173187781)
    ·
      refine ⟨7320792015849132594972709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39044224084528707173187781 7320792015849132594972709)
      ·
        refine ⟨1372648502971712361557383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7320792015849132594972709 1372648502971712361557383)
        ·
          refine ⟨2058972754457568542336075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372648502971712361557383 2058972754457568542336075)
          ·
            refine ⟨3088459131686352813504113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058972754457568542336075 3088459131686352813504113)
            ·
              refine ⟨2316344348764764610128085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088459131686352813504113 2316344348764764610128085)
              ·
                refine ⟨54289320674174170549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2316344348764764610128085 54289320674174170549877)
                ·
                  rfl

theorem cell22_1427329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 7].length) (baseStart_1427329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427329 prefixEnd_1427329 := by exact prefixLift 1427329
  have htrace : WordTrace (prefixWord ++ tailWord_1427329) baseStart_1427329 baseEnd_1427329 := by
    simpa [prefixWord, tailWord_1427329, baseEnd_1427329] using wordTrace_append hprefix tailTrace_1427329
  have hstable : (prefixWord ++ tailWord_1427329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427329).length < 2 ^ (prefixWord ++ tailWord_1427329).sum := by decide
  have hdescent : baseEnd_1427329 < baseStart_1427329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427421 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1427421 : Nat := 118140960795 + 1427421 * 2 ^ 59
def prefixEnd_1427421 : Nat := 4983230072969 + 3 ^ 40 * 1427421 * 2
def baseEnd_1427421 : Nat := 488635379547709961648611

theorem tailTrace_1427421 : CollatzResearch.WordTrace tailWord_1427421 prefixEnd_1427421 488635379547709961648611 := by
  unfold tailWord_1427421
  simp only [CollatzResearch.WordTrace]
  refine ⟨52062320961704975943266117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34708213974469983962177411 52062320961704975943266117)
  ·
    refine ⟨9761685180319682989362397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52062320961704975943266117 9761685180319682989362397)
    ·
      refine ⟨3660631942619881121010899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9761685180319682989362397 3660631942619881121010899)
      ·
        refine ⟨5490947913929821681516349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660631942619881121010899 5490947913929821681516349)
        ·
          refine ⟨2059105467723683130568631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5490947913929821681516349 2059105467723683130568631)
          ·
            refine ⟨3088658201585524695852947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059105467723683130568631 3088658201585524695852947)
            ·
              refine ⟨4632987302378287043779421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088658201585524695852947 4632987302378287043779421)
              ·
                refine ⟨1737370238391857641417283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4632987302378287043779421 1737370238391857641417283)
                ·
                  refine ⟨2606055357587786462125925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737370238391857641417283 2606055357587786462125925)
                  ·
                    refine ⟨488635379547709961648611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2606055357587786462125925 488635379547709961648611)
                    ·
                      rfl

theorem cell22_1427421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1427421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427421 prefixEnd_1427421 := by exact prefixLift 1427421
  have htrace : WordTrace (prefixWord ++ tailWord_1427421) baseStart_1427421 baseEnd_1427421 := by
    simpa [prefixWord, tailWord_1427421, baseEnd_1427421] using wordTrace_append hprefix tailTrace_1427421
  have hstable : (prefixWord ++ tailWord_1427421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427421).length < 2 ^ (prefixWord ++ tailWord_1427421).sum := by decide
  have hdescent : baseEnd_1427421 < baseStart_1427421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427432 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1427432 : Nat := 118140960795 + 1427432 * 2 ^ 59
def prefixEnd_1427432 : Nat := 4983230072969 + 3 ^ 40 * 1427432 * 2
def baseEnd_1427432 : Nat := 488639145072509599623577

theorem tailTrace_1427432 : CollatzResearch.WordTrace tailWord_1427432 prefixEnd_1427432 488639145072509599623577 := by
  unfold tailWord_1427432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031361082332562410958275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34708481443110083214611033 26031361082332562410958275)
  ·
    refine ⟨39047041623498843616437413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26031361082332562410958275 39047041623498843616437413)
    ·
      refine ⟨7321320304406033178082015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39047041623498843616437413 7321320304406033178082015)
      ·
        refine ⟨10981980456609049767123023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7321320304406033178082015 10981980456609049767123023)
        ·
          refine ⟨16472970684913574650684535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981980456609049767123023 16472970684913574650684535)
          ·
            refine ⟨24709456027370361976026803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16472970684913574650684535 24709456027370361976026803)
            ·
              refine ⟨37064184041055542964040205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24709456027370361976026803 37064184041055542964040205)
              ·
                refine ⟨13899069015395828611515077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37064184041055542964040205 13899069015395828611515077)
                ·
                  refine ⟨2606075440386717864659077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13899069015395828611515077 2606075440386717864659077)
                  ·
                    refine ⟨488639145072509599623577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2606075440386717864659077 488639145072509599623577)
                    ·
                      rfl

theorem cell22_1427432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1427432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427432 prefixEnd_1427432 := by exact prefixLift 1427432
  have htrace : WordTrace (prefixWord ++ tailWord_1427432) baseStart_1427432 baseEnd_1427432 := by
    simpa [prefixWord, tailWord_1427432, baseEnd_1427432] using wordTrace_append hprefix tailTrace_1427432
  have hstable : (prefixWord ++ tailWord_1427432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427432).length < 2 ^ (prefixWord ++ tailWord_1427432).sum := by decide
  have hdescent : baseEnd_1427432 < baseStart_1427432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427434 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1427434 : Nat := 118140960795 + 1427434 * 2 ^ 59
def prefixEnd_1427434 : Nat := 4983230072969 + 3 ^ 40 * 1427434 * 2
def baseEnd_1427434 : Nat := 488639829713382261073571

theorem tailTrace_1427434 : CollatzResearch.WordTrace tailWord_1427434 prefixEnd_1427434 488639829713382261073571 := by
  unfold tailWord_1427434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015698777664469790872339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34708530073771919442326237 13015698777664469790872339)
  ·
    refine ⟨19523548166496704686308509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13015698777664469790872339 19523548166496704686308509)
    ·
      refine ⟨7321330562436264257365691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19523548166496704686308509 7321330562436264257365691)
      ·
        refine ⟨10981995843654396386048537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7321330562436264257365691 10981995843654396386048537)
        ·
          refine ⟨8236496882740797289536403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10981995843654396386048537 8236496882740797289536403)
          ·
            refine ⟨12354745324111195934304605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236496882740797289536403 12354745324111195934304605)
            ·
              refine ⟨4633029496541698475364227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12354745324111195934304605 4633029496541698475364227)
              ·
                refine ⟨6949544244812547713046341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633029496541698475364227 6949544244812547713046341)
                ·
                  refine ⟨1303039545902352696196189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6949544244812547713046341 1303039545902352696196189)
                  ·
                    refine ⟨488639829713382261073571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303039545902352696196189 488639829713382261073571)
                    ·
                      rfl

theorem cell22_1427434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1427434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427434 prefixEnd_1427434 := by exact prefixLift 1427434
  have htrace : WordTrace (prefixWord ++ tailWord_1427434) baseStart_1427434 baseEnd_1427434 := by
    simpa [prefixWord, tailWord_1427434, baseEnd_1427434] using wordTrace_append hprefix tailTrace_1427434
  have hstable : (prefixWord ++ tailWord_1427434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427434).length < 2 ^ (prefixWord ++ tailWord_1427434).sum := by decide
  have hdescent : baseEnd_1427434 < baseStart_1427434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427507 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_1427507 : Nat := 118140960795 + 1427507 * 2 ^ 59
def prefixEnd_1427507 : Nat := 4983230072969 + 3 ^ 40 * 1427507 * 2
def baseEnd_1427507 : Nat := 488664819105234403998347

theorem tailTrace_1427507 : CollatzResearch.WordTrace tailWord_1427507 prefixEnd_1427507 488664819105234403998347 := by
  unfold tailWord_1427507
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065457639393412630896775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34710305092928941753931183 52065457639393412630896775)
  ·
    refine ⟨78098186459090118946345163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52065457639393412630896775 78098186459090118946345163)
    ·
      refine ⟨117147279688635178419517745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78098186459090118946345163 117147279688635178419517745)
      ·
        refine ⟨87860459766476383814638309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117147279688635178419517745 87860459766476383814638309)
        ·
          refine ⟨16473836206214321965244683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87860459766476383814638309 16473836206214321965244683)
          ·
            refine ⟨24710754309321482947867025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16473836206214321965244683 24710754309321482947867025)
            ·
              refine ⟨18533065731991112210900269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24710754309321482947867025 18533065731991112210900269)
              ·
                refine ⟨6949899649496667079087601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18533065731991112210900269 6949899649496667079087601)
                ·
                  refine ⟨5212424737122500309315701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6949899649496667079087601 5212424737122500309315701)
                  ·
                    refine ⟨488664819105234403998347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5212424737122500309315701 488664819105234403998347)
                    ·
                      rfl

theorem cell22_1427507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_1427507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427507 prefixEnd_1427507 := by exact prefixLift 1427507
  have htrace : WordTrace (prefixWord ++ tailWord_1427507) baseStart_1427507 baseEnd_1427507 := by
    simpa [prefixWord, tailWord_1427507, baseEnd_1427507] using wordTrace_append hprefix tailTrace_1427507
  have hstable : (prefixWord ++ tailWord_1427507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427507).length < 2 ^ (prefixWord ++ tailWord_1427507).sum := by decide
  have hdescent : baseEnd_1427507 < baseStart_1427507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427569 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_1427569 : Nat := 118140960795 + 1427569 * 2 ^ 59
def prefixEnd_1427569 : Nat := 4983230072969 + 3 ^ 40 * 1427569 * 2
def baseEnd_1427569 : Nat := 488686042972286908948157

theorem tailTrace_1427569 : CollatzResearch.WordTrace tailWord_1427569 prefixEnd_1427569 488686042972286908948157 := by
  unfold tailWord_1427569
  simp only [CollatzResearch.WordTrace]
  refine ⟨52067718965168797219653761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34711812643445864813102507 52067718965168797219653761)
  ·
    refine ⟨39050789223876597914740321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52067718965168797219653761 39050789223876597914740321)
    ·
      refine ⟨29288091917907448436055241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39050789223876597914740321 29288091917907448436055241)
      ·
        refine ⟨21966068938430586327041431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29288091917907448436055241 21966068938430586327041431)
        ·
          refine ⟨32949103407645879490562147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21966068938430586327041431 32949103407645879490562147)
          ·
            refine ⟨49423655111468819235843221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32949103407645879490562147 49423655111468819235843221)
            ·
              refine ⟨2316733833350100901680151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49423655111468819235843221 2316733833350100901680151)
              ·
                refine ⟨3475100750025151352520227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316733833350100901680151 3475100750025151352520227)
                ·
                  refine ⟨5212651125037727028780341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475100750025151352520227 5212651125037727028780341)
                  ·
                    refine ⟨488686042972286908948157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5212651125037727028780341 488686042972286908948157)
                    ·
                      rfl

theorem cell22_1427569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_1427569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427569 prefixEnd_1427569 := by exact prefixLift 1427569
  have htrace : WordTrace (prefixWord ++ tailWord_1427569) baseStart_1427569 baseEnd_1427569 := by
    simpa [prefixWord, tailWord_1427569, baseEnd_1427569] using wordTrace_append hprefix tailTrace_1427569
  have hstable : (prefixWord ++ tailWord_1427569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427569).length < 2 ^ (prefixWord ++ tailWord_1427569).sum := by decide
  have hdescent : baseEnd_1427569 < baseStart_1427569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427620 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_1427620 : Nat := 118140960795 + 1427620 * 2 ^ 59
def prefixEnd_1427620 : Nat := 4983230072969 + 3 ^ 40 * 1427620 * 2
def baseEnd_1427620 : Nat := 488703501314539775923001

theorem tailTrace_1427620 : CollatzResearch.WordTrace tailWord_1427620 prefixEnd_1427620 488703501314539775923001 := by
  unfold tailWord_1427620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26034789543992016464880157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34713052725322688619840209 26034789543992016464880157)
  ·
    refine ⟨9763046078997006174330059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26034789543992016464880157 9763046078997006174330059)
    ·
      refine ⟨14644569118495509261495089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9763046078997006174330059 14644569118495509261495089)
      ·
        refine ⟨10983426838871631946121317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14644569118495509261495089 10983426838871631946121317)
        ·
          refine ⟨2059392532288430989897747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10983426838871631946121317 2059392532288430989897747)
          ·
            refine ⟨3089088798432646484846621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059392532288430989897747 3089088798432646484846621)
            ·
              refine ⟨1158408299412242431817483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3089088798432646484846621 1158408299412242431817483)
              ·
                refine ⟨1737612449118363647726225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158408299412242431817483 1737612449118363647726225)
                ·
                  refine ⟨1303209336838772735794669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737612449118363647726225 1303209336838772735794669)
                  ·
                    refine ⟨488703501314539775923001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303209336838772735794669 488703501314539775923001)
                    ·
                      rfl

theorem cell22_1427620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_1427620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427620 prefixEnd_1427620 := by exact prefixLift 1427620
  have htrace : WordTrace (prefixWord ++ tailWord_1427620) baseStart_1427620 baseEnd_1427620 := by
    simpa [prefixWord, tailWord_1427620, baseEnd_1427620] using wordTrace_append hprefix tailTrace_1427620
  have hstable : (prefixWord ++ tailWord_1427620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427620).length < 2 ^ (prefixWord ++ tailWord_1427620).sum := by decide
  have hdescent : baseEnd_1427620 < baseStart_1427620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427633 : List Nat := [1, 2, 2, 5, 2, 2, 2, 6]
def baseStart_1427633 : Nat := 118140960795 + 1427633 * 2 ^ 59
def prefixEnd_1427633 : Nat := 4983230072969 + 3 ^ 40 * 1427633 * 2
def baseEnd_1427633 : Nat := 54300883497801341705329

theorem tailTrace_1427633 : CollatzResearch.WordTrace tailWord_1427633 prefixEnd_1427633 54300883497801341705329 := by
  unfold tailWord_1427633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52070053236936936149983553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34713368824624624099989035 52070053236936936149983553)
  ·
    refine ⟨39052539927702702112487665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52070053236936936149983553 39052539927702702112487665)
    ·
      refine ⟨29289404945777026584365749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39052539927702702112487665 29289404945777026584365749)
      ·
        refine ⟨2745881713666596242284289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29289404945777026584365749 2745881713666596242284289)
        ·
          refine ⟨2059411285249947181713217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745881713666596242284289 2059411285249947181713217)
          ·
            refine ⟨1544558463937460386284913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059411285249947181713217 1544558463937460386284913)
            ·
              refine ⟨1158418847953095289713685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544558463937460386284913 1158418847953095289713685)
              ·
                refine ⟨54300883497801341705329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1158418847953095289713685 54300883497801341705329)
                ·
                  rfl

theorem cell22_1427633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 6].length) (baseStart_1427633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427633 prefixEnd_1427633 := by exact prefixLift 1427633
  have htrace : WordTrace (prefixWord ++ tailWord_1427633) baseStart_1427633 baseEnd_1427633 := by
    simpa [prefixWord, tailWord_1427633, baseEnd_1427633] using wordTrace_append hprefix tailTrace_1427633
  have hstable : (prefixWord ++ tailWord_1427633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427633).length < 2 ^ (prefixWord ++ tailWord_1427633).sum := by decide
  have hdescent : baseEnd_1427633 < baseStart_1427633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427738 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_1427738 : Nat := 118140960795 + 1427738 * 2 ^ 59
def prefixEnd_1427738 : Nat := 4983230072969 + 3 ^ 40 * 1427738 * 2
def baseEnd_1427738 : Nat := 488743895126026801472639

theorem tailTrace_1427738 : CollatzResearch.WordTrace tailWord_1427738 prefixEnd_1427738 488743895126026801472639 := by
  unfold tailWord_1427738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018470725389134770638967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34715921934371026055037245 13018470725389134770638967)
  ·
    refine ⟨19527706088083702155958451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018470725389134770638967 19527706088083702155958451)
    ·
      refine ⟨29291559132125553233937677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19527706088083702155958451 29291559132125553233937677)
      ·
        refine ⟨10984334674547082462726629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29291559132125553233937677 10984334674547082462726629)
        ·
          refine ⟨2059562751477577961761243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10984334674547082462726629 2059562751477577961761243)
          ·
            refine ⟨3089344127216366942641865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059562751477577961761243 3089344127216366942641865)
            ·
              refine ⟨2317008095412275206981399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089344127216366942641865 2317008095412275206981399)
              ·
                refine ⟨3475512143118412810472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317008095412275206981399 3475512143118412810472099)
                ·
                  refine ⟨5213268214677619215708149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475512143118412810472099 5213268214677619215708149)
                  ·
                    refine ⟨488743895126026801472639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5213268214677619215708149 488743895126026801472639)
                    ·
                      rfl

theorem cell22_1427738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_1427738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427738 prefixEnd_1427738 := by exact prefixLift 1427738
  have htrace : WordTrace (prefixWord ++ tailWord_1427738) baseStart_1427738 baseEnd_1427738 := by
    simpa [prefixWord, tailWord_1427738, baseEnd_1427738] using wordTrace_append hprefix tailTrace_1427738
  have hstable : (prefixWord ++ tailWord_1427738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427738).length < 2 ^ (prefixWord ++ tailWord_1427738).sum := by decide
  have hdescent : baseEnd_1427738 < baseStart_1427738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427757 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1427757 : Nat := 118140960795 + 1427757 * 2 ^ 59
def prefixEnd_1427757 : Nat := 4983230072969 + 3 ^ 40 * 1427757 * 2
def baseEnd_1427757 : Nat := 162916799738105695082527

theorem tailTrace_1427757 : CollatzResearch.WordTrace tailWord_1427757 prefixEnd_1427757 162916799738105695082527 := by
  unfold tailWord_1427757
  simp only [CollatzResearch.WordTrace]
  refine ⟨52074575888487705327497525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34716383925658470218331683 52074575888487705327497525)
  ·
    refine ⟨4881991489545722374452893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52074575888487705327497525 4881991489545722374452893)
    ·
      refine ⟨1830746808579645890419835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4881991489545722374452893 1830746808579645890419835)
      ·
        refine ⟨2746120212869468835629753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830746808579645890419835 2746120212869468835629753)
        ·
          refine ⟨2059590159652101626722315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746120212869468835629753 2059590159652101626722315)
          ·
            refine ⟨3089385239478152440083473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059590159652101626722315 3089385239478152440083473)
            ·
              refine ⟨2317038929608614330062605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089385239478152440083473 2317038929608614330062605)
              ·
                refine ⟨868889598603230373773477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2317038929608614330062605 868889598603230373773477)
                ·
                  refine ⟨162916799738105695082527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868889598603230373773477 162916799738105695082527)
                  ·
                    rfl

theorem cell22_1427757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1427757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427757 prefixEnd_1427757 := by exact prefixLift 1427757
  have htrace : WordTrace (prefixWord ++ tailWord_1427757) baseStart_1427757 baseEnd_1427757 := by
    simpa [prefixWord, tailWord_1427757, baseEnd_1427757] using wordTrace_append hprefix tailTrace_1427757
  have hstable : (prefixWord ++ tailWord_1427757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427757).length < 2 ^ (prefixWord ++ tailWord_1427757).sum := by decide
  have hdescent : baseEnd_1427757 < baseStart_1427757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427783 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1427783 : Nat := 118140960795 + 1427783 * 2 ^ 59
def prefixEnd_1427783 : Nat := 4983230072969 + 3 ^ 40 * 1427783 * 2
def baseEnd_1427783 : Nat := 488759299545661684097501

theorem tailTrace_1427783 : CollatzResearch.WordTrace tailWord_1427783 prefixEnd_1427783 488759299545661684097501 := by
  unfold tailWord_1427783
  simp only [CollatzResearch.WordTrace]
  refine ⟨52075524186393511767944003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34717016124262341178629335 52075524186393511767944003)
  ·
    refine ⟨78113286279590267651916005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52075524186393511767944003 78113286279590267651916005)
    ·
      refine ⟨14646241177423175184734251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78113286279590267651916005 14646241177423175184734251)
      ·
        refine ⟨21969361766134762777101377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646241177423175184734251 21969361766134762777101377)
        ·
          refine ⟨16477021324601072082826033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21969361766134762777101377 16477021324601072082826033)
          ·
            refine ⟨12357765993450804062119525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477021324601072082826033 12357765993450804062119525)
            ·
              refine ⟨2317081123772025761647411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12357765993450804062119525 2317081123772025761647411)
              ·
                refine ⟨3475621685658038642471117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317081123772025761647411 3475621685658038642471117)
                ·
                  refine ⟨1303358132121764490926669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3475621685658038642471117 1303358132121764490926669)
                  ·
                    refine ⟨488759299545661684097501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303358132121764490926669 488759299545661684097501)
                    ·
                      rfl

theorem cell22_1427783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1427783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427783 prefixEnd_1427783 := by exact prefixLift 1427783
  have htrace : WordTrace (prefixWord ++ tailWord_1427783) baseStart_1427783 baseEnd_1427783 := by
    simpa [prefixWord, tailWord_1427783, baseEnd_1427783] using wordTrace_append hprefix tailTrace_1427783
  have hstable : (prefixWord ++ tailWord_1427783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427783).length < 2 ^ (prefixWord ++ tailWord_1427783).sum := by decide
  have hdescent : baseEnd_1427783 < baseStart_1427783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427860 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1427860 : Nat := 118140960795 + 1427860 * 2 ^ 59
def prefixEnd_1427860 : Nat := 4983230072969 + 3 ^ 40 * 1427860 * 2
def baseEnd_1427860 : Nat := 488785658219259149922265

theorem tailTrace_1427860 : CollatzResearch.WordTrace tailWord_1427860 prefixEnd_1427860 488785658219259149922265 := by
  unfold tailWord_1427860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26039166303557276959248517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34718888404743035945664689 26039166303557276959248517)
  ·
    refine ⟨4882343681916989429859097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26039166303557276959248517 4882343681916989429859097)
    ·
      refine ⟨3661757761437742072394323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4882343681916989429859097 3661757761437742072394323)
      ·
        refine ⟨5492636642156613108591485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661757761437742072394323 5492636642156613108591485)
        ·
          refine ⟨2059738740808729915721807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5492636642156613108591485 2059738740808729915721807)
          ·
            refine ⟨3089608111213094873582711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059738740808729915721807 3089608111213094873582711)
            ·
              refine ⟨4634412166819642310374067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089608111213094873582711 4634412166819642310374067)
              ·
                refine ⟨6951618250229463465561101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634412166819642310374067 6951618250229463465561101)
                ·
                  refine ⟨2606856843836048799585413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951618250229463465561101 2606856843836048799585413)
                  ·
                    refine ⟨488785658219259149922265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2606856843836048799585413 488785658219259149922265)
                    ·
                      rfl

theorem cell22_1427860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1427860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427860 prefixEnd_1427860 := by exact prefixLift 1427860
  have htrace : WordTrace (prefixWord ++ tailWord_1427860) baseStart_1427860 baseEnd_1427860 := by
    simpa [prefixWord, tailWord_1427860, baseEnd_1427860] using wordTrace_append hprefix tailTrace_1427860
  have hstable : (prefixWord ++ tailWord_1427860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427860).length < 2 ^ (prefixWord ++ tailWord_1427860).sum := by decide
  have hdescent : baseEnd_1427860 < baseStart_1427860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427890 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_1427890 : Nat := 118140960795 + 1427890 * 2 ^ 59
def prefixEnd_1427890 : Nat := 4983230072969 + 3 ^ 40 * 1427890 * 2
def baseEnd_1427890 : Nat := 488795927832349071672173

theorem tailTrace_1427890 : CollatzResearch.WordTrace tailWord_1427890 prefixEnd_1427890 488795927832349071672173 := by
  unfold tailWord_1427890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13019856699251467260522281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34719617864670579361392749 13019856699251467260522281)
  ·
    refine ⟨9764892524438600445391711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13019856699251467260522281 9764892524438600445391711)
    ·
      refine ⟨14647338786657900668087567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764892524438600445391711 14647338786657900668087567)
      ·
        refine ⟨21971008179986851002131351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14647338786657900668087567 21971008179986851002131351)
        ·
          refine ⟨32956512269980276503197027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21971008179986851002131351 32956512269980276503197027)
          ·
            refine ⟨49434768404970414754795541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32956512269980276503197027 49434768404970414754795541)
            ·
              refine ⟨2317254768982988191631041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49434768404970414754795541 2317254768982988191631041)
              ·
                refine ⟨1737941076737241143723281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317254768982988191631041 1737941076737241143723281)
                ·
                  refine ⟨1303455807552930857792461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737941076737241143723281 1303455807552930857792461)
                  ·
                    refine ⟨488795927832349071672173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303455807552930857792461 488795927832349071672173)
                    ·
                      rfl

theorem cell22_1427890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_1427890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427890 prefixEnd_1427890 := by exact prefixLift 1427890
  have htrace : WordTrace (prefixWord ++ tailWord_1427890) baseStart_1427890 baseEnd_1427890 := by
    simpa [prefixWord, tailWord_1427890, baseEnd_1427890] using wordTrace_append hprefix tailTrace_1427890
  have hstable : (prefixWord ++ tailWord_1427890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427890).length < 2 ^ (prefixWord ++ tailWord_1427890).sum := by decide
  have hdescent : baseEnd_1427890 < baseStart_1427890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427965 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1427965 : Nat := 118140960795 + 1427965 * 2 ^ 59
def prefixEnd_1427965 : Nat := 4983230072969 + 3 ^ 40 * 1427965 * 2
def baseEnd_1427965 : Nat := 162940533955024625348981

theorem tailTrace_1427965 : CollatzResearch.WordTrace tailWord_1427965 prefixEnd_1427965 162940533955024625348981 := by
  unfold tailWord_1427965
  simp only [CollatzResearch.WordTrace]
  refine ⟨52082162271734156851069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34721441514489437900712899 52082162271734156851069349)
  ·
    refine ⟨9765405425950154409575503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52082162271734156851069349 9765405425950154409575503)
    ·
      refine ⟨14648108138925231614363255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9765405425950154409575503 14648108138925231614363255)
      ·
        refine ⟨21972162208387847421544883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14648108138925231614363255 21972162208387847421544883)
        ·
          refine ⟨32958243312581771132317325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21972162208387847421544883 32958243312581771132317325)
          ·
            refine ⟨12359341242218164174618997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32958243312581771132317325 12359341242218164174618997)
            ·
              refine ⟨1158688241457952891370531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12359341242218164174618997 1158688241457952891370531)
              ·
                refine ⟨1738032362186929337055797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158688241457952891370531 1738032362186929337055797)
                ·
                  refine ⟨162940533955024625348981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738032362186929337055797 162940533955024625348981)
                  ·
                    rfl

theorem cell22_1427965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1427965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1427965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1427965 prefixEnd_1427965 := by exact prefixLift 1427965
  have htrace : WordTrace (prefixWord ++ tailWord_1427965) baseStart_1427965 baseEnd_1427965 := by
    simpa [prefixWord, tailWord_1427965, baseEnd_1427965] using wordTrace_append hprefix tailTrace_1427965
  have hstable : (prefixWord ++ tailWord_1427965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427965).length < 2 ^ (prefixWord ++ tailWord_1427965).sum := by decide
  have hdescent : baseEnd_1427965 < baseStart_1427965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428010 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1428010 : Nat := 118140960795 + 1428010 * 2 ^ 59
def prefixEnd_1428010 : Nat := 4983230072969 + 3 ^ 40 * 1428010 * 2
def baseEnd_1428010 : Nat := 162945668761569586223935

theorem tailTrace_1428010 : CollatzResearch.WordTrace tailWord_1428010 prefixEnd_1428010 162945668761569586223935 := by
  unfold tailWord_1428010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020950889142782384114371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34722535704380753024304989 13020950889142782384114371)
  ·
    refine ⟨19531426333714173576171557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13020950889142782384114371 19531426333714173576171557)
    ·
      refine ⟨3662142437571407545532167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19531426333714173576171557 3662142437571407545532167)
      ·
        refine ⟨5493213656357111318298251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3662142437571407545532167 5493213656357111318298251)
        ·
          refine ⟨8239820484535666977447377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493213656357111318298251 8239820484535666977447377)
          ·
            refine ⟨6179865363401750233085533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8239820484535666977447377 6179865363401750233085533)
            ·
              refine ⟨2317449511275656337407075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6179865363401750233085533 2317449511275656337407075)
              ·
                refine ⟨3476174266913484506110613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317449511275656337407075 3476174266913484506110613)
                ·
                  refine ⟨162945668761569586223935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3476174266913484506110613 162945668761569586223935)
                  ·
                    rfl

theorem cell22_1428010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1428010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428010 prefixEnd_1428010 := by exact prefixLift 1428010
  have htrace : WordTrace (prefixWord ++ tailWord_1428010) baseStart_1428010 baseEnd_1428010 := by
    simpa [prefixWord, tailWord_1428010, baseEnd_1428010] using wordTrace_append hprefix tailTrace_1428010
  have hstable : (prefixWord ++ tailWord_1428010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428010).length < 2 ^ (prefixWord ++ tailWord_1428010).sum := by decide
  have hdescent : baseEnd_1428010 < baseStart_1428010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428023 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1428023 : Nat := 118140960795 + 1428023 * 2 ^ 59
def prefixEnd_1428023 : Nat := 4983230072969 + 3 ^ 40 * 1428023 * 2
def baseEnd_1428023 : Nat := 488841456450381058096765

theorem tailTrace_1428023 : CollatzResearch.WordTrace tailWord_1428023 prefixEnd_1428023 488841456450381058096765 := by
  unfold tailWord_1428023
  simp only [CollatzResearch.WordTrace]
  refine ⟨52084277705524032756680723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34722851803682688504453815 52084277705524032756680723)
  ·
    refine ⟨78126416558286049135021085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52084277705524032756680723 78126416558286049135021085)
    ·
      refine ⟨29297406209357268425632907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78126416558286049135021085 29297406209357268425632907)
      ·
        refine ⟨43946109314035902638449361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29297406209357268425632907 43946109314035902638449361)
        ·
          refine ⟨32959581985526926978837021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43946109314035902638449361 32959581985526926978837021)
          ·
            refine ⟨12359843244572597617063883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32959581985526926978837021 12359843244572597617063883)
            ·
              refine ⟨18539764866858896425595825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359843244572597617063883 18539764866858896425595825)
              ·
                refine ⟨13904823650144172319196869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18539764866858896425595825 13904823650144172319196869)
                ·
                  refine ⟨2607154434402032309849413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13904823650144172319196869 2607154434402032309849413)
                  ·
                    refine ⟨488841456450381058096765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607154434402032309849413 488841456450381058096765)
                    ·
                      rfl

theorem cell22_1428023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1428023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428023 prefixEnd_1428023 := by exact prefixLift 1428023
  have htrace : WordTrace (prefixWord ++ tailWord_1428023) baseStart_1428023 baseEnd_1428023 := by
    simpa [prefixWord, tailWord_1428023, baseEnd_1428023] using wordTrace_append hprefix tailTrace_1428023
  have hstable : (prefixWord ++ tailWord_1428023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428023).length < 2 ^ (prefixWord ++ tailWord_1428023).sum := by decide
  have hdescent : baseEnd_1428023 < baseStart_1428023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428068 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1428068 : Nat := 118140960795 + 1428068 * 2 ^ 59
def prefixEnd_1428068 : Nat := 4983230072969 + 3 ^ 40 * 1428068 * 2
def baseEnd_1428068 : Nat := 488856860870015940721627

theorem tailTrace_1428068 : CollatzResearch.WordTrace tailWord_1428068 prefixEnd_1428068 488856860870015940721627 := by
  unfold tailWord_1428068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042959495180502721034429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34723945993574003628045905 26042959495180502721034429)
  ·
    refine ⟨9766109810692688520387911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26042959495180502721034429 9766109810692688520387911)
    ·
      refine ⟨14649164716039032780581867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766109810692688520387911 14649164716039032780581867)
      ·
        refine ⟨21973747074058549170872801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649164716039032780581867 21973747074058549170872801)
        ·
          refine ⟨16480310305543911878154601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21973747074058549170872801 16480310305543911878154601)
          ·
            refine ⟨12360232729157933908615951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16480310305543911878154601 12360232729157933908615951)
            ·
              refine ⟨18540349093736900862923927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360232729157933908615951 18540349093736900862923927)
              ·
                refine ⟨27810523640605351294385891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18540349093736900862923927 27810523640605351294385891)
                ·
                  refine ⟨41715785460908026941578837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27810523640605351294385891 41715785460908026941578837)
                  ·
                    refine ⟨488856860870015940721627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41715785460908026941578837 488856860870015940721627)
                    ·
                      rfl

theorem cell22_1428068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1428068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428068 prefixEnd_1428068 := by exact prefixLift 1428068
  have htrace : WordTrace (prefixWord ++ tailWord_1428068) baseStart_1428068 baseEnd_1428068 := by
    simpa [prefixWord, tailWord_1428068, baseEnd_1428068] using wordTrace_append hprefix tailTrace_1428068
  have hstable : (prefixWord ++ tailWord_1428068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428068).length < 2 ^ (prefixWord ++ tailWord_1428068).sum := by decide
  have hdescent : baseEnd_1428068 < baseStart_1428068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428072 : List Nat := [2, 1, 4, 3, 2, 2, 1, 7]
def baseStart_1428072 : Nat := 118140960795 + 1428072 * 2 ^ 59
def prefixEnd_1428072 : Nat := 4983230072969 + 3 ^ 40 * 1428072 * 2
def baseEnd_1428072 : Nat := 54317581127973473735735

theorem tailTrace_1428072 : CollatzResearch.WordTrace tailWord_1428072 prefixEnd_1428072 54317581127973473735735 := by
  unfold tailWord_1428072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043032441173257062607235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34724043254897676083476313 26043032441173257062607235)
  ·
    refine ⟨39064548661759885593910853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26043032441173257062607235 39064548661759885593910853)
    ·
      refine ⟨7324602874079978548858285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39064548661759885593910853 7324602874079978548858285)
      ·
        refine ⟨2746726077779991955821857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7324602874079978548858285 2746726077779991955821857)
        ·
          refine ⟨2060044558334993966866393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746726077779991955821857 2060044558334993966866393)
          ·
            refine ⟨1545033418751245475149795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060044558334993966866393 1545033418751245475149795)
            ·
              refine ⟨2317550128126868212724693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545033418751245475149795 2317550128126868212724693)
              ·
                refine ⟨54317581127973473735735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2317550128126868212724693 54317581127973473735735)
                ·
                  rfl

theorem cell22_1428072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_1428072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428072 prefixEnd_1428072 := by exact prefixLift 1428072
  have htrace : WordTrace (prefixWord ++ tailWord_1428072) baseStart_1428072 baseEnd_1428072 := by
    simpa [prefixWord, tailWord_1428072, baseEnd_1428072] using wordTrace_append hprefix tailTrace_1428072
  have hstable : (prefixWord ++ tailWord_1428072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428072).length < 2 ^ (prefixWord ++ tailWord_1428072).sum := by decide
  have hdescent : baseEnd_1428072 < baseStart_1428072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428147 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 1, 4]
def baseStart_1428147 : Nat := 118140960795 + 1428147 * 2 ^ 59
def prefixEnd_1428147 : Nat := 4983230072969 + 3 ^ 40 * 1428147 * 2
def baseEnd_1428147 : Nat := 488883904184486067996385

theorem tailTrace_1428147 : CollatzResearch.WordTrace tailWord_1428147 prefixEnd_1428147 488883904184486067996385 := by
  unfold tailWord_1428147
  simp only [CollatzResearch.WordTrace]
  refine ⟨52088800357074801934194695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34725866904716534622796463 52088800357074801934194695)
  ·
    refine ⟨78133200535612202901292043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52088800357074801934194695 78133200535612202901292043)
    ·
      refine ⟨117199800803418304351938065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78133200535612202901292043 117199800803418304351938065)
      ·
        refine ⟨87899850602563728263953549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117199800803418304351938065 87899850602563728263953549)
        ·
          refine ⟨32962443975961398098982581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87899850602563728263953549 32962443975961398098982581)
          ·
            refine ⟨3090229122746381071779617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32962443975961398098982581 3090229122746381071779617)
            ·
              refine ⟨2317671842059785803834713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090229122746381071779617 2317671842059785803834713)
              ·
                refine ⟨1738253881544839352876035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317671842059785803834713 1738253881544839352876035)
                ·
                  refine ⟨2607380822317259029314053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738253881544839352876035 2607380822317259029314053)
                  ·
                    refine ⟨488883904184486067996385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607380822317259029314053 488883904184486067996385)
                    ·
                      rfl

theorem cell22_1428147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_1428147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428147 prefixEnd_1428147 := by exact prefixLift 1428147
  have htrace : WordTrace (prefixWord ++ tailWord_1428147) baseStart_1428147 baseEnd_1428147 := by
    simpa [prefixWord, tailWord_1428147, baseEnd_1428147] using wordTrace_append hprefix tailTrace_1428147
  have hstable : (prefixWord ++ tailWord_1428147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428147).length < 2 ^ (prefixWord ++ tailWord_1428147).sum := by decide
  have hdescent : baseEnd_1428147 < baseStart_1428147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428177 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_1428177 : Nat := 118140960795 + 1428177 * 2 ^ 59
def prefixEnd_1428177 : Nat := 4983230072969 + 3 ^ 40 * 1428177 * 2
def baseEnd_1428177 : Nat := 488894173797575989746293

theorem tailTrace_1428177 : CollatzResearch.WordTrace tailWord_1428177 prefixEnd_1428177 488894173797575989746293 := by
  unfold tailWord_1428177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52089894546966117057786785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34726596364644078038524523 52089894546966117057786785)
  ·
    refine ⟨39067420910224587793340089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52089894546966117057786785 39067420910224587793340089)
    ·
      refine ⟨29300565682668440845005067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39067420910224587793340089 29300565682668440845005067)
      ·
        refine ⟨43950848524002661267507601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29300565682668440845005067 43950848524002661267507601)
        ·
          refine ⟨32963136393001995950630701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43950848524002661267507601 32963136393001995950630701)
          ·
            refine ⟨12361176147375748481486513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32963136393001995950630701 12361176147375748481486513)
            ·
              refine ⟨9270882110531811361114885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12361176147375748481486513 9270882110531811361114885)
              ·
                refine ⟨1738290395724714630209041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9270882110531811361114885 1738290395724714630209041)
                ·
                  refine ⟨1303717796793535972656781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738290395724714630209041 1303717796793535972656781)
                  ·
                    refine ⟨488894173797575989746293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303717796793535972656781 488894173797575989746293)
                    ·
                      rfl

theorem cell22_1428177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_1428177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428177 prefixEnd_1428177 := by exact prefixLift 1428177
  have htrace : WordTrace (prefixWord ++ tailWord_1428177) baseStart_1428177 baseEnd_1428177 := by
    simpa [prefixWord, tailWord_1428177, baseEnd_1428177] using wordTrace_append hprefix tailTrace_1428177
  have hstable : (prefixWord ++ tailWord_1428177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428177).length < 2 ^ (prefixWord ++ tailWord_1428177).sum := by decide
  have hdescent : baseEnd_1428177 < baseStart_1428177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428239 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 1, 3]
def baseStart_1428239 : Nat := 118140960795 + 1428239 * 2 ^ 59
def prefixEnd_1428239 : Nat := 4983230072969 + 3 ^ 40 * 1428239 * 2
def baseEnd_1428239 : Nat := 488915397664628494696103

theorem tailTrace_1428239 : CollatzResearch.WordTrace tailWord_1428239 prefixEnd_1428239 488915397664628494696103 := by
  unfold tailWord_1428239
  simp only [CollatzResearch.WordTrace]
  refine ⟨52092155872741501646543771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34728103915161001097695847 52092155872741501646543771)
  ·
    refine ⟨78138233809112252469815657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52092155872741501646543771 78138233809112252469815657)
    ·
      refine ⟨58603675356834189352361743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78138233809112252469815657 58603675356834189352361743)
      ·
        refine ⟨87905513035251284028542615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603675356834189352361743 87905513035251284028542615)
        ·
          refine ⟨131858269552876926042813923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87905513035251284028542615 131858269552876926042813923)
          ·
            refine ⟨197787404329315389064220885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131858269552876926042813923 197787404329315389064220885)
            ·
              refine ⟨4635642288968329431192677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 197787404329315389064220885 4635642288968329431192677)
              ·
                refine ⟨869182929181561768348627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4635642288968329431192677 869182929181561768348627)
                ·
                  refine ⟨1303774393772342652522941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869182929181561768348627 1303774393772342652522941)
                  ·
                    refine ⟨488915397664628494696103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303774393772342652522941 488915397664628494696103)
                    ·
                      rfl

theorem cell22_1428239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_1428239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428239 prefixEnd_1428239 := by exact prefixLift 1428239
  have htrace : WordTrace (prefixWord ++ tailWord_1428239) baseStart_1428239 baseEnd_1428239 := by
    simpa [prefixWord, tailWord_1428239, baseEnd_1428239] using wordTrace_append hprefix tailTrace_1428239
  have hstable : (prefixWord ++ tailWord_1428239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428239).length < 2 ^ (prefixWord ++ tailWord_1428239).sum := by decide
  have hdescent : baseEnd_1428239 < baseStart_1428239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428252 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_1428252 : Nat := 118140960795 + 1428252 * 2 ^ 59
def prefixEnd_1428252 : Nat := 4983230072969 + 3 ^ 40 * 1428252 * 2
def baseEnd_1428252 : Nat := 162973282610100264707021

theorem tailTrace_1428252 : CollatzResearch.WordTrace tailWord_1428252 prefixEnd_1428252 162973282610100264707021 := by
  unfold tailWord_1428252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046315010847202433383505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34728420014462936577844673 26046315010847202433383505)
  ·
    refine ⟨19534736258135401825037629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26046315010847202433383505 19534736258135401825037629)
    ·
      refine ⟨7325526096800775684389111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19534736258135401825037629 7325526096800775684389111)
      ·
        refine ⟨10988289145201163526583667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325526096800775684389111 10988289145201163526583667)
        ·
          refine ⟨16482433717801745289875501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10988289145201163526583667 16482433717801745289875501)
          ·
            refine ⟨6180912644175654483703313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16482433717801745289875501 6180912644175654483703313)
            ·
              refine ⟨4635684483131740862777485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180912644175654483703313 4635684483131740862777485)
              ·
                refine ⟨1738381681174402823541557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4635684483131740862777485 1738381681174402823541557)
                ·
                  refine ⟨162973282610100264707021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738381681174402823541557 162973282610100264707021)
                  ·
                    rfl

theorem cell22_1428252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_1428252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428252 prefixEnd_1428252 := by exact prefixLift 1428252
  have htrace : WordTrace (prefixWord ++ tailWord_1428252) baseStart_1428252 baseEnd_1428252 := by
    simpa [prefixWord, tailWord_1428252, baseEnd_1428252] using wordTrace_append hprefix tailTrace_1428252
  have hstable : (prefixWord ++ tailWord_1428252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428252).length < 2 ^ (prefixWord ++ tailWord_1428252).sum := by decide
  have hdescent : baseEnd_1428252 < baseStart_1428252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428280 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_1428280 : Nat := 118140960795 + 1428280 * 2 ^ 59
def prefixEnd_1428280 : Nat := 4983230072969 + 3 ^ 40 * 1428280 * 2
def baseEnd_1428280 : Nat := 162976477600839351473659

theorem tailTrace_1428280 : CollatzResearch.WordTrace tailWord_1428280 prefixEnd_1428280 162976477600839351473659 := by
  unfold tailWord_1428280
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046825632796482824393147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34729100843728643765857529 26046825632796482824393147)
  ·
    refine ⟨39070238449194724236589721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26046825632796482824393147 39070238449194724236589721)
    ·
      refine ⟨29302678836896043177442291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39070238449194724236589721 29302678836896043177442291)
      ·
        refine ⟨43954018255344064766163437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29302678836896043177442291 43954018255344064766163437)
        ·
          refine ⟨16482756845754024287311289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43954018255344064766163437 16482756845754024287311289)
          ·
            refine ⟨12362067634315518215483467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16482756845754024287311289 12362067634315518215483467)
            ·
              refine ⟨18543101451473277323225201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12362067634315518215483467 18543101451473277323225201)
              ·
                refine ⟨13907326088604957992418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18543101451473277323225201 13907326088604957992418901)
                ·
                  refine ⟨162976477600839351473659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13907326088604957992418901 162976477600839351473659)
                  ·
                    rfl

theorem cell22_1428280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_1428280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428280 prefixEnd_1428280 := by exact prefixLift 1428280
  have htrace : WordTrace (prefixWord ++ tailWord_1428280) baseStart_1428280 baseEnd_1428280 := by
    simpa [prefixWord, tailWord_1428280, baseEnd_1428280] using wordTrace_append hprefix tailTrace_1428280
  have hstable : (prefixWord ++ tailWord_1428280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428280).length < 2 ^ (prefixWord ++ tailWord_1428280).sum := by decide
  have hdescent : baseEnd_1428280 < baseStart_1428280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428286 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1428286 : Nat := 118140960795 + 1428286 * 2 ^ 59
def prefixEnd_1428286 : Nat := 4983230072969 + 3 ^ 40 * 1428286 * 2
def baseEnd_1428286 : Nat := 162977162241712012923653

theorem tailTrace_1428286 : CollatzResearch.WordTrace tailWord_1428286 prefixEnd_1428286 162977162241712012923653 := by
  unfold tailWord_1428286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511733762946403584188089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34729246735714152449003141 6511733762946403584188089)
  ·
    refine ⟨4883800322209802688141067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6511733762946403584188089 4883800322209802688141067)
    ·
      refine ⟨7325700483314704032211601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883800322209802688141067 7325700483314704032211601)
      ·
        refine ⟨5494275362486028024158701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7325700483314704032211601 5494275362486028024158701)
        ·
          refine ⟨2060353260932260509059513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5494275362486028024158701 2060353260932260509059513)
          ·
            refine ⟨1545264945699195381794635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060353260932260509059513 1545264945699195381794635)
            ·
              refine ⟨2317897418548793072691953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545264945699195381794635 2317897418548793072691953)
              ·
                refine ⟨1738423063911594804518965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317897418548793072691953 1738423063911594804518965)
                ·
                  refine ⟨162977162241712012923653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738423063911594804518965 162977162241712012923653)
                  ·
                    rfl

theorem cell22_1428286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1428286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428286 prefixEnd_1428286 := by exact prefixLift 1428286
  have htrace : WordTrace (prefixWord ++ tailWord_1428286) baseStart_1428286 baseEnd_1428286 := by
    simpa [prefixWord, tailWord_1428286, baseEnd_1428286] using wordTrace_append hprefix tailTrace_1428286
  have hstable : (prefixWord ++ tailWord_1428286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428286).length < 2 ^ (prefixWord ++ tailWord_1428286).sum := by decide
  have hdescent : baseEnd_1428286 < baseStart_1428286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428297 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 6]
def baseStart_1428297 : Nat := 118140960795 + 1428297 * 2 ^ 59
def prefixEnd_1428297 : Nat := 4983230072969 + 3 ^ 40 * 1428297 * 2
def baseEnd_1428297 : Nat := 162978417416645225581975

theorem tailTrace_1428297 : CollatzResearch.WordTrace tailWord_1428297 prefixEnd_1428297 162978417416645225581975 := by
  unfold tailWord_1428297
  simp only [CollatzResearch.WordTrace]
  refine ⟨52094271306531377552155145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34729514204354251701436763 52094271306531377552155145)
  ·
    refine ⟨39070703479898533164116359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52094271306531377552155145 39070703479898533164116359)
    ·
      refine ⟨58606055219847799746174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39070703479898533164116359 58606055219847799746174539)
      ·
        refine ⟨87909082829771699619261809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58606055219847799746174539 87909082829771699619261809)
        ·
          refine ⟨65931812122328774714446357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87909082829771699619261809 65931812122328774714446357)
          ·
            refine ⟨3090553693234161314739673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65931812122328774714446357 3090553693234161314739673)
            ·
              refine ⟨2317915269925620986054755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090553693234161314739673 2317915269925620986054755)
              ·
                refine ⟨3476872904888431479082133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317915269925620986054755 3476872904888431479082133)
                ·
                  refine ⟨162978417416645225581975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3476872904888431479082133 162978417416645225581975)
                  ·
                    rfl

theorem cell22_1428297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_1428297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428297 prefixEnd_1428297 := by exact prefixLift 1428297
  have htrace : WordTrace (prefixWord ++ tailWord_1428297) baseStart_1428297 baseEnd_1428297 := by
    simpa [prefixWord, tailWord_1428297, baseEnd_1428297] using wordTrace_append hprefix tailTrace_1428297
  have hstable : (prefixWord ++ tailWord_1428297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428297).length < 2 ^ (prefixWord ++ tailWord_1428297).sum := by decide
  have hdescent : baseEnd_1428297 < baseStart_1428297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428316 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1428316 : Nat := 118140960795 + 1428316 * 2 ^ 59
def prefixEnd_1428316 : Nat := 4983230072969 + 3 ^ 40 * 1428316 * 2
def baseEnd_1428316 : Nat := 488941756338225960520867

theorem tailTrace_1428316 : CollatzResearch.WordTrace tailWord_1428316 prefixEnd_1428316 488941756338225960520867 := by
  unfold tailWord_1428316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26047482146731271898548401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34729976195641695864731201 26047482146731271898548401)
  ·
    refine ⟨19535611610048453923911301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26047482146731271898548401 19535611610048453923911301)
    ·
      refine ⟨3662927176884085110733369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19535611610048453923911301 3662927176884085110733369)
      ·
        refine ⟨2747195382663063833050027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3662927176884085110733369 2747195382663063833050027)
        ·
          refine ⟨4120793073994595749575041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747195382663063833050027 4120793073994595749575041)
          ·
            refine ⟨3090594805495946812181281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120793073994595749575041 3090594805495946812181281)
            ·
              refine ⟨2317946104121960109135961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090594805495946812181281 2317946104121960109135961)
              ·
                refine ⟨1738459578091470081851971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317946104121960109135961 1738459578091470081851971)
                ·
                  refine ⟨2607689367137205122777957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738459578091470081851971 2607689367137205122777957)
                  ·
                    refine ⟨488941756338225960520867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607689367137205122777957 488941756338225960520867)
                    ·
                      rfl

theorem cell22_1428316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1428316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428316 prefixEnd_1428316 := by exact prefixLift 1428316
  have htrace : WordTrace (prefixWord ++ tailWord_1428316) baseStart_1428316 baseEnd_1428316 := by
    simpa [prefixWord, tailWord_1428316, baseEnd_1428316] using wordTrace_append hprefix tailTrace_1428316
  have hstable : (prefixWord ++ tailWord_1428316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428316).length < 2 ^ (prefixWord ++ tailWord_1428316).sum := by decide
  have hdescent : baseEnd_1428316 < baseStart_1428316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428327 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1428327 : Nat := 118140960795 + 1428327 * 2 ^ 59
def prefixEnd_1428327 : Nat := 4983230072969 + 3 ^ 40 * 1428327 * 2
def baseEnd_1428327 : Nat := 488945521863025598495833

theorem tailTrace_1428327 : CollatzResearch.WordTrace tailWord_1428327 prefixEnd_1428327 488945521863025598495833 := by
  unfold tailWord_1428327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52095365496422692675747235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34730243664281795117164823 52095365496422692675747235)
  ·
    refine ⟨78143048244634039013620853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52095365496422692675747235 78143048244634039013620853)
    ·
      refine ⟨7325910772934441157526955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78143048244634039013620853 7325910772934441157526955)
      ·
        refine ⟨10988866159401661736290433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325910772934441157526955 10988866159401661736290433)
        ·
          refine ⟨8241649619551246302217825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988866159401661736290433 8241649619551246302217825)
          ·
            refine ⟨6181237214663434726663369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8241649619551246302217825 6181237214663434726663369)
            ·
              refine ⟨4635927910997576044997527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6181237214663434726663369 4635927910997576044997527)
              ·
                refine ⟨6953891866496364067496291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635927910997576044997527 6953891866496364067496291)
                ·
                  refine ⟨10430837799744546101244437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953891866496364067496291 10430837799744546101244437)
                  ·
                    refine ⟨488945521863025598495833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10430837799744546101244437 488945521863025598495833)
                    ·
                      rfl

theorem cell22_1428327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1428327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428327 prefixEnd_1428327 := by exact prefixLift 1428327
  have htrace : WordTrace (prefixWord ++ tailWord_1428327) baseStart_1428327 baseEnd_1428327 := by
    simpa [prefixWord, tailWord_1428327, baseEnd_1428327] using wordTrace_append hprefix tailTrace_1428327
  have hstable : (prefixWord ++ tailWord_1428327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428327).length < 2 ^ (prefixWord ++ tailWord_1428327).sum := by decide
  have hdescent : baseEnd_1428327 < baseStart_1428327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428408 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_1428408 : Nat := 118140960795 + 1428408 * 2 ^ 59
def prefixEnd_1428408 : Nat := 4983230072969 + 3 ^ 40 * 1428408 * 2
def baseEnd_1428408 : Nat := 488973249818368387220585

theorem tailTrace_1428408 : CollatzResearch.WordTrace tailWord_1428408 prefixEnd_1428408 488973249818368387220585 := by
  unfold tailWord_1428408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049159904564621754722939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34732213206086162339630585 26049159904564621754722939)
  ·
    refine ⟨39073739856846932632084409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26049159904564621754722939 39073739856846932632084409)
    ·
      refine ⟨29305304892635199474063307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39073739856846932632084409 29305304892635199474063307)
      ·
        refine ⟨43957957338952799211094961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29305304892635199474063307 43957957338952799211094961)
        ·
          refine ⟨32968468004214599408321221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43957957338952799211094961 32968468004214599408321221)
          ·
            refine ⟨6181587750790237389060229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32968468004214599408321221 6181587750790237389060229)
            ·
              refine ⟨1159047703273169510448793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6181587750790237389060229 1159047703273169510448793)
              ·
                refine ⟨869285777454877132836595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159047703273169510448793 869285777454877132836595)
                ·
                  refine ⟨1303928666182315699254893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869285777454877132836595 1303928666182315699254893)
                  ·
                    refine ⟨488973249818368387220585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303928666182315699254893 488973249818368387220585)
                    ·
                      rfl

theorem cell22_1428408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_1428408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428408 prefixEnd_1428408 := by exact prefixLift 1428408
  have htrace : WordTrace (prefixWord ++ tailWord_1428408) baseStart_1428408 baseEnd_1428408 := by
    simpa [prefixWord, tailWord_1428408, baseEnd_1428408] using wordTrace_append hprefix tailTrace_1428408
  have hstable : (prefixWord ++ tailWord_1428408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428408).length < 2 ^ (prefixWord ++ tailWord_1428408).sum := by decide
  have hdescent : baseEnd_1428408 < baseStart_1428408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428477 : List Nat := [1, 4, 1, 1, 1, 2, 1, 11]
def baseStart_1428477 : Nat := 118140960795 + 1428477 * 2 ^ 59
def prefixEnd_1428477 : Nat := 4983230072969 + 3 ^ 40 * 1428477 * 2
def baseEnd_1428477 : Nat := 54332985547608356360597

theorem tailTrace_1428477 : CollatzResearch.WordTrace tailWord_1428477 prefixEnd_1428477 54332985547608356360597 := by
  unfold tailWord_1428477
  simp only [CollatzResearch.WordTrace]
  refine ⟨52100836445879268293707685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34733890963919512195805123 52100836445879268293707685)
  ·
    refine ⟨9768906833602362805070191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52100836445879268293707685 9768906833602362805070191)
    ·
      refine ⟨14653360250403544207605287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768906833602362805070191 14653360250403544207605287)
      ·
        refine ⟨21980040375605316311407931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653360250403544207605287 21980040375605316311407931)
        ·
          refine ⟨32970060563407974467111897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21980040375605316311407931 32970060563407974467111897)
          ·
            refine ⟨24727545422555980850333923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32970060563407974467111897 24727545422555980850333923)
            ·
              refine ⟨37091318133833971275500885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24727545422555980850333923 37091318133833971275500885)
              ·
                refine ⟨54332985547608356360597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37091318133833971275500885 54332985547608356360597)
                ·
                  rfl

theorem cell22_1428477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 11].length) (baseStart_1428477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428477 prefixEnd_1428477 := by exact prefixLift 1428477
  have htrace : WordTrace (prefixWord ++ tailWord_1428477) baseStart_1428477 baseEnd_1428477 := by
    simpa [prefixWord, tailWord_1428477, baseEnd_1428477] using wordTrace_append hprefix tailTrace_1428477
  have hstable : (prefixWord ++ tailWord_1428477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428477).length < 2 ^ (prefixWord ++ tailWord_1428477).sum := by decide
  have hdescent : baseEnd_1428477 < baseStart_1428477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428481 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1428481 : Nat := 118140960795 + 1428481 * 2 ^ 59
def prefixEnd_1428481 : Nat := 4983230072969 + 3 ^ 40 * 1428481 * 2
def baseEnd_1428481 : Nat := 488998239210220530145361

theorem tailTrace_1428481 : CollatzResearch.WordTrace tailWord_1428481 prefixEnd_1428481 488998239210220530145361 := by
  unfold tailWord_1428481
  simp only [CollatzResearch.WordTrace]
  refine ⟨52100982337864776976853297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34733988225243184651235531 52100982337864776976853297)
  ·
    refine ⟨39075736753398582732639973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52100982337864776976853297 39075736753398582732639973)
    ·
      refine ⟨7326700641262234262369995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39075736753398582732639973 7326700641262234262369995)
      ·
        refine ⟨10990050961893351393554993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326700641262234262369995 10990050961893351393554993)
        ·
          refine ⟨8242538221420013545166245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990050961893351393554993 8242538221420013545166245)
          ·
            refine ⟨1545475916516252539718671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8242538221420013545166245 1545475916516252539718671)
            ·
              refine ⟨2318213874774378809578007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545475916516252539718671 2318213874774378809578007)
              ·
                refine ⟨3477320812161568214367011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318213874774378809578007 3477320812161568214367011)
                ·
                  refine ⟨5215981218242352321550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477320812161568214367011 5215981218242352321550517)
                  ·
                    refine ⟨488998239210220530145361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5215981218242352321550517 488998239210220530145361)
                    ·
                      rfl

theorem cell22_1428481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1428481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428481 prefixEnd_1428481 := by exact prefixLift 1428481
  have htrace : WordTrace (prefixWord ++ tailWord_1428481) baseStart_1428481 baseEnd_1428481 := by
    simpa [prefixWord, tailWord_1428481, baseEnd_1428481] using wordTrace_append hprefix tailTrace_1428481
  have hstable : (prefixWord ++ tailWord_1428481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428481).length < 2 ^ (prefixWord ++ tailWord_1428481).sum := by decide
  have hdescent : baseEnd_1428481 < baseStart_1428481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428494 : List Nat := [4, 1, 1, 2, 2, 3, 1, 8]
def baseStart_1428494 : Nat := 118140960795 + 1428494 * 2 ^ 59
def prefixEnd_1428494 : Nat := 4983230072969 + 3 ^ 40 * 1428494 * 2
def baseEnd_1428494 : Nat := 54333632152876981063369

theorem tailTrace_1428494 : CollatzResearch.WordTrace tailWord_1428494 prefixEnd_1428494 54333632152876981063369 := by
  unfold tailWord_1428494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512682060852210024634567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34734304324545120131384357 6512682060852210024634567)
  ·
    refine ⟨9769023091278315036951851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6512682060852210024634567 9769023091278315036951851)
    ·
      refine ⟨14653534636917472555427777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9769023091278315036951851 14653534636917472555427777)
      ·
        refine ⟨10990150977688104416570833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14653534636917472555427777 10990150977688104416570833)
        ·
          refine ⟨8242613233266078312428125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990150977688104416570833 8242613233266078312428125)
          ·
            refine ⟨3090979962474779367160547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8242613233266078312428125 3090979962474779367160547)
            ·
              refine ⟨4636469943712169050740821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090979962474779367160547 4636469943712169050740821)
              ·
                refine ⟨54333632152876981063369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4636469943712169050740821 54333632152876981063369)
                ·
                  rfl

theorem cell22_1428494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_1428494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428494 prefixEnd_1428494 := by exact prefixLift 1428494
  have htrace : WordTrace (prefixWord ++ tailWord_1428494) baseStart_1428494 baseEnd_1428494 := by
    simpa [prefixWord, tailWord_1428494, baseEnd_1428494] using wordTrace_append hprefix tailTrace_1428494
  have hstable : (prefixWord ++ tailWord_1428494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428494).length < 2 ^ (prefixWord ++ tailWord_1428494).sum := by decide
  have hdescent : baseEnd_1428494 < baseStart_1428494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428532 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1428532 : Nat := 118140960795 + 1428532 * 2 ^ 59
def prefixEnd_1428532 : Nat := 4983230072969 + 3 ^ 40 * 1428532 * 2
def baseEnd_1428532 : Nat := 489015697552473397120205

theorem tailTrace_1428532 : CollatzResearch.WordTrace tailWord_1428532 prefixEnd_1428532 489015697552473397120205 := by
  unfold tailWord_1428532
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051421230340006343479925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34735228307120008457973233 26051421230340006343479925)
  ·
    refine ⟨2442320740344375594701243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26051421230340006343479925 2442320740344375594701243)
    ·
      refine ⟨3663481110516563392051865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2442320740344375594701243 3663481110516563392051865)
      ·
        refine ⟨2747610832887422544038899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3663481110516563392051865 2747610832887422544038899)
        ·
          refine ⟨4121416249331133816058349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747610832887422544038899 4121416249331133816058349)
          ·
            refine ⟨1545531093499175181021881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4121416249331133816058349 1545531093499175181021881)
            ·
              refine ⟨1159148320124381385766411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545531093499175181021881 1159148320124381385766411)
              ·
                refine ⟨1738722480186572078649617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159148320124381385766411 1738722480186572078649617)
                ·
                  refine ⟨1304041860139929058987213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738722480186572078649617 1304041860139929058987213)
                  ·
                    refine ⟨489015697552473397120205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304041860139929058987213 489015697552473397120205)
                    ·
                      rfl

theorem cell22_1428532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1428532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428532 prefixEnd_1428532 := by exact prefixLift 1428532
  have htrace : WordTrace (prefixWord ++ tailWord_1428532) baseStart_1428532 baseEnd_1428532 := by
    simpa [prefixWord, tailWord_1428532, baseEnd_1428532] using wordTrace_append hprefix tailTrace_1428532
  have hstable : (prefixWord ++ tailWord_1428532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428532).length < 2 ^ (prefixWord ++ tailWord_1428532).sum := by decide
  have hdescent : baseEnd_1428532 < baseStart_1428532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428586 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1428586 : Nat := 118140960795 + 1428586 * 2 ^ 59
def prefixEnd_1428586 : Nat := 4983230072969 + 3 ^ 40 * 1428586 * 2
def baseEnd_1428586 : Nat := 489034182856035256270039

theorem tailTrace_1428586 : CollatzResearch.WordTrace tailWord_1428586 prefixEnd_1428586 489034182856035256270039 := by
  unfold tailWord_1428586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026203000621094977356403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34736541334989586606283741 13026203000621094977356403)
  ·
    refine ⟨19539304500931642466034605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13026203000621094977356403 19539304500931642466034605)
    ·
      refine ⟨7327239187849365924762977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19539304500931642466034605 7327239187849365924762977)
      ·
        refine ⟨5495429390887024443572233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327239187849365924762977 5495429390887024443572233)
        ·
          refine ⟨4121572043165268332679175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495429390887024443572233 4121572043165268332679175)
          ·
            refine ⟨6182358064747902499018763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121572043165268332679175 6182358064747902499018763)
            ·
              refine ⟨9273537097121853748528145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182358064747902499018763 9273537097121853748528145)
              ·
                refine ⟨6955152822841390311396109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273537097121853748528145 6955152822841390311396109)
                ·
                  refine ⟨2608182308565521366773541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6955152822841390311396109 2608182308565521366773541)
                  ·
                    refine ⟨489034182856035256270039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608182308565521366773541 489034182856035256270039)
                    ·
                      rfl

theorem cell22_1428586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1428586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428586 prefixEnd_1428586 := by exact prefixLift 1428586
  have htrace : WordTrace (prefixWord ++ tailWord_1428586) baseStart_1428586 baseEnd_1428586 := by
    simpa [prefixWord, tailWord_1428586, baseEnd_1428586] using wordTrace_append hprefix tailTrace_1428586
  have hstable : (prefixWord ++ tailWord_1428586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428586).length < 2 ^ (prefixWord ++ tailWord_1428586).sum := by decide
  have hdescent : baseEnd_1428586 < baseStart_1428586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428601 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 6]
def baseStart_1428601 : Nat := 118140960795 + 1428601 * 2 ^ 59
def prefixEnd_1428601 : Nat := 4983230072969 + 3 ^ 40 * 1428601 * 2
def baseEnd_1428601 : Nat := 163013105887526739048331

theorem tailTrace_1428601 : CollatzResearch.WordTrace tailWord_1428601 prefixEnd_1428601 163013105887526739048331 := by
  unfold tailWord_1428601
  simp only [CollatzResearch.WordTrace]
  refine ⟨52105359097430037471221657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34736906064953358314147771 52105359097430037471221657)
  ·
    refine ⟨39079019323072528103416243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52105359097430037471221657 39079019323072528103416243)
    ·
      refine ⟨58618528984608792155124365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39079019323072528103416243 58618528984608792155124365)
      ·
        refine ⟨21981948369228297058171637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58618528984608792155124365 21981948369228297058171637)
        ·
          refine ⟨2060807659615152849203591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21981948369228297058171637 2060807659615152849203591)
          ·
            refine ⟨3091211489422729273805387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060807659615152849203591 3091211489422729273805387)
            ·
              refine ⟨4636817234134093910708081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091211489422729273805387 4636817234134093910708081)
              ·
                refine ⟨3477612925600570433031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636817234134093910708081 3477612925600570433031061)
                ·
                  refine ⟨163013105887526739048331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3477612925600570433031061 163013105887526739048331)
                  ·
                    rfl

theorem cell22_1428601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_1428601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1428601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1428601 prefixEnd_1428601 := by exact prefixLift 1428601
  have htrace : WordTrace (prefixWord ++ tailWord_1428601) baseStart_1428601 baseEnd_1428601 := by
    simpa [prefixWord, tailWord_1428601, baseEnd_1428601] using wordTrace_append hprefix tailTrace_1428601
  have hstable : (prefixWord ++ tailWord_1428601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428601).length < 2 ^ (prefixWord ++ tailWord_1428601).sum := by decide
  have hdescent : baseEnd_1428601 < baseStart_1428601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
