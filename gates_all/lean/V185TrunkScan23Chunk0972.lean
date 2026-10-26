import V185TrunkScan23Chunk0971

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5753918 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5753918 : Nat := 118140960795 + 5753918 * 2 ^ 59
def prefixEnd_5753918 : Nat := 4983230072969 + 3 ^ 40 * 5753918 * 2
def baseEnd_5753918 : Nat := 2954525580556924003063219

theorem tailTrace_5753918 : CollatzResearch.WordTrace tailWord_5753918 prefixEnd_5753918 2954525580556924003063219 := by
  unfold tailWord_5753918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26232828796068156475435801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139908420245696834535657605 26232828796068156475435801)
  ·
    refine ⟨19674621597051117356576851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26232828796068156475435801 19674621597051117356576851)
    ·
      refine ⟨29511932395576676034865277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19674621597051117356576851 29511932395576676034865277)
      ·
        refine ⟨11066974648341253513074479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29511932395576676034865277 11066974648341253513074479)
        ·
          refine ⟨16600461972511880269611719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066974648341253513074479 16600461972511880269611719)
          ·
            refine ⟨24900692958767820404417579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16600461972511880269611719 24900692958767820404417579)
            ·
              refine ⟨37351039438151730606626369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24900692958767820404417579 37351039438151730606626369)
              ·
                refine ⟨28013279578613797954969777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37351039438151730606626369 28013279578613797954969777)
                ·
                  refine ⟨21009959683960348466227333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28013279578613797954969777 21009959683960348466227333)
                  ·
                    refine ⟨3939367440742565337417625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21009959683960348466227333 3939367440742565337417625)
                    ·
                      refine ⟨2954525580556924003063219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939367440742565337417625 2954525580556924003063219)
                      ·
                        rfl

theorem cell23_5753918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5753918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753918 prefixEnd_5753918 := by exact prefixLift 5753918
  have htrace : WordTrace (prefixWord ++ tailWord_5753918) baseStart_5753918 baseEnd_5753918 := by
    simpa [prefixWord, tailWord_5753918, baseEnd_5753918] using wordTrace_append hprefix tailTrace_5753918
  have hstable : (prefixWord ++ tailWord_5753918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753918).length < 2 ^ (prefixWord ++ tailWord_5753918).sum := by decide
  have hdescent : baseEnd_5753918 < baseStart_5753918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753941 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 6]
def baseStart_5753941 : Nat := 118140960795 + 5753941 * 2 ^ 59
def prefixEnd_5753941 : Nat := 4983230072969 + 3 ^ 40 * 5753941 * 2
def baseEnd_5753941 : Nat := 328281932290219712563957

theorem tailTrace_5753941 : CollatzResearch.WordTrace tailWord_5753941 prefixEnd_5753941 328281932290219712563957 := by
  unfold tailWord_5753941
  simp only [CollatzResearch.WordTrace]
  refine ⟨209863469247461926731573677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139908979498307951154382451 209863469247461926731573677)
  ·
    refine ⟨78698800967798222524340129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209863469247461926731573677 78698800967798222524340129)
    ·
      refine ⟨59024100725848666893255097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78698800967798222524340129 59024100725848666893255097)
      ·
        refine ⟨44268075544386500169941323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59024100725848666893255097 44268075544386500169941323)
        ·
          refine ⟨66402113316579750254911985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44268075544386500169941323 66402113316579750254911985)
          ·
            refine ⟨49801584987434812691183989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66402113316579750254911985 49801584987434812691183989)
            ·
              refine ⟨4668898592572013689798499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49801584987434812691183989 4668898592572013689798499)
              ·
                refine ⟨7003347888858020534697749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668898592572013689798499 7003347888858020534697749)
                ·
                  refine ⟨328281932290219712563957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7003347888858020534697749 328281932290219712563957)
                  ·
                    rfl

theorem cell23_5753941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_5753941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753941 prefixEnd_5753941 := by exact prefixLift 5753941
  have htrace : WordTrace (prefixWord ++ tailWord_5753941) baseStart_5753941 baseEnd_5753941 := by
    simpa [prefixWord, tailWord_5753941, baseEnd_5753941] using wordTrace_append hprefix tailTrace_5753941
  have hstable : (prefixWord ++ tailWord_5753941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753941).length < 2 ^ (prefixWord ++ tailWord_5753941).sum := by decide
  have hdescent : baseEnd_5753941 < baseStart_5753941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753951 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_5753951 : Nat := 118140960795 + 5753951 * 2 ^ 59
def prefixEnd_5753951 : Nat := 4983230072969 + 3 ^ 40 * 5753951 * 2
def baseEnd_5753951 : Nat := 2954542525418522373950567

theorem tailTrace_5753951 : CollatzResearch.WordTrace tailWord_5753951 prefixEnd_5753951 2954542525418522373950567 := by
  unfold tailWord_5753951
  simp only [CollatzResearch.WordTrace]
  refine ⟨209863833977425698439437707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139909222651617132292958471 209863833977425698439437707)
  ·
    refine ⟨314795750966138547659156561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209863833977425698439437707 314795750966138547659156561)
    ·
      refine ⟨236096813224603910744367421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314795750966138547659156561 236096813224603910744367421)
      ·
        refine ⟨88536304959226466529137783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236096813224603910744367421 88536304959226466529137783)
        ·
          refine ⟨132804457438839699793706675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88536304959226466529137783 132804457438839699793706675)
          ·
            refine ⟨199206686158259549690560013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132804457438839699793706675 199206686158259549690560013)
            ·
              refine ⟨74702507309347331133960005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199206686158259549690560013 74702507309347331133960005)
              ·
                refine ⟨14006720120502624587617501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74702507309347331133960005 14006720120502624587617501)
                ·
                  refine ⟨5252520045188484220356563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14006720120502624587617501 5252520045188484220356563)
                  ·
                    refine ⟨7878780067782726330534845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252520045188484220356563 7878780067782726330534845)
                    ·
                      refine ⟨2954542525418522373950567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878780067782726330534845 2954542525418522373950567)
                      ·
                        rfl

theorem cell23_5753951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_5753951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753951 prefixEnd_5753951 := by exact prefixLift 5753951
  have htrace : WordTrace (prefixWord ++ tailWord_5753951) baseStart_5753951 baseEnd_5753951 := by
    simpa [prefixWord, tailWord_5753951, baseEnd_5753951] using wordTrace_append hprefix tailTrace_5753951
  have hstable : (prefixWord ++ tailWord_5753951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753951).length < 2 ^ (prefixWord ++ tailWord_5753951).sum := by decide
  have hdescent : baseEnd_5753951 < baseStart_5753951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753961 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 5, 2]
def baseStart_5753961 : Nat := 118140960795 + 5753961 * 2 ^ 59
def prefixEnd_5753961 : Nat := 4983230072969 + 3 ^ 40 * 5753961 * 2
def baseEnd_5753961 : Nat := 2954547660225067334825521

theorem tailTrace_5753961 : CollatzResearch.WordTrace tailWord_5753961 prefixEnd_5753961 2954547660225067334825521 := by
  unfold tailWord_5753961
  simp only [CollatzResearch.WordTrace]
  refine ⟨209864198707389470147301737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139909465804926313431534491 209864198707389470147301737)
  ·
    refine ⟨157398149030542102610476303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209864198707389470147301737 157398149030542102610476303)
    ·
      refine ⟨236097223545813153915714455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157398149030542102610476303 236097223545813153915714455)
      ·
        refine ⟨354145835318719730873571683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236097223545813153915714455 354145835318719730873571683)
        ·
          refine ⟨531218752978079596310357525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354145835318719730873571683 531218752978079596310357525)
          ·
            refine ⟨24900879045847481077048009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 531218752978079596310357525 24900879045847481077048009)
            ·
              refine ⟨18675659284385610807786007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24900879045847481077048009 18675659284385610807786007)
              ·
                refine ⟨28013488926578416211679011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18675659284385610807786007 28013488926578416211679011)
                ·
                  refine ⟨42020233389867624317518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28013488926578416211679011 42020233389867624317518517)
                  ·
                    refine ⟨3939396880300089779767361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42020233389867624317518517 3939396880300089779767361)
                    ·
                      refine ⟨2954547660225067334825521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939396880300089779767361 2954547660225067334825521)
                      ·
                        rfl

theorem cell23_5753961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5, 2].length) (baseStart_5753961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753961 prefixEnd_5753961 := by exact prefixLift 5753961
  have htrace : WordTrace (prefixWord ++ tailWord_5753961) baseStart_5753961 baseEnd_5753961 := by
    simpa [prefixWord, tailWord_5753961, baseEnd_5753961] using wordTrace_append hprefix tailTrace_5753961
  have hstable : (prefixWord ++ tailWord_5753961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753961).length < 2 ^ (prefixWord ++ tailWord_5753961).sum := by decide
  have hdescent : baseEnd_5753961 < baseStart_5753961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753985 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5753985 : Nat := 118140960795 + 5753985 * 2 ^ 59
def prefixEnd_5753985 : Nat := 4983230072969 + 3 ^ 40 * 5753985 * 2
def baseEnd_5753985 : Nat := 2954559983760775240925411

theorem tailTrace_5753985 : CollatzResearch.WordTrace tailWord_5753985 prefixEnd_5753985 2954559983760775240925411 := by
  unfold tailWord_5753985
  simp only [CollatzResearch.WordTrace]
  refine ⟨209865074059302522246175409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139910049372868348164116939 209865074059302522246175409)
  ·
    refine ⟨157398805544476891684631557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209865074059302522246175409 157398805544476891684631557)
    ·
      refine ⟨29512276039589417190868417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157398805544476891684631557 29512276039589417190868417)
      ·
        refine ⟨22134207029692062893151313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29512276039589417190868417 22134207029692062893151313)
        ·
          refine ⟨16600655272269047169863485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22134207029692062893151313 16600655272269047169863485)
          ·
            refine ⟨6225245727100892688698807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16600655272269047169863485 6225245727100892688698807)
            ·
              refine ⟨9337868590651339033048211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225245727100892688698807 9337868590651339033048211)
              ·
                refine ⟨14006802885977008549572317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337868590651339033048211 14006802885977008549572317)
                ·
                  refine ⟨5252551082241378206089619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14006802885977008549572317 5252551082241378206089619)
                  ·
                    refine ⟨7878826623362067309134429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252551082241378206089619 7878826623362067309134429)
                    ·
                      refine ⟨2954559983760775240925411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878826623362067309134429 2954559983760775240925411)
                      ·
                        rfl

theorem cell23_5753985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5753985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753985 prefixEnd_5753985 := by exact prefixLift 5753985
  have htrace : WordTrace (prefixWord ++ tailWord_5753985) baseStart_5753985 baseEnd_5753985 := by
    simpa [prefixWord, tailWord_5753985, baseEnd_5753985] using wordTrace_append hprefix tailTrace_5753985
  have hstable : (prefixWord ++ tailWord_5753985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753985).length < 2 ^ (prefixWord ++ tailWord_5753985).sum := by decide
  have hdescent : baseEnd_5753985 < baseStart_5753985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754008 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5754008 : Nat := 118140960795 + 5754008 * 2 ^ 59
def prefixEnd_5754008 : Nat := 4983230072969 + 3 ^ 40 * 5754008 * 2
def baseEnd_5754008 : Nat := 2954571793815828650937805

theorem tailTrace_5754008 : CollatzResearch.WordTrace tailWord_5754008 prefixEnd_5754008 2954571793815828650937805 := by
  unfold tailWord_5754008
  simp only [CollatzResearch.WordTrace]
  refine ⟨104932956469109598587131339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139910608625479464782841785 104932956469109598587131339)
  ·
    refine ⟨157399434703664397880697009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104932956469109598587131339 157399434703664397880697009)
    ·
      refine ⟨118049576027748298410522757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157399434703664397880697009 118049576027748298410522757)
      ·
        refine ⟨22134295505202805951973017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118049576027748298410522757 22134295505202805951973017)
        ·
          refine ⟨16600721628902104463979763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22134295505202805951973017 16600721628902104463979763)
          ·
            refine ⟨24901082443353156695969645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16600721628902104463979763 24901082443353156695969645)
            ·
              refine ⟨9337905916257433760988617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24901082443353156695969645 9337905916257433760988617)
              ·
                refine ⟨7003429437193075320741463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9337905916257433760988617 7003429437193075320741463)
                ·
                  refine ⟨10505144155789612981112195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003429437193075320741463 10505144155789612981112195)
                  ·
                    refine ⟨15757716233684419471668293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10505144155789612981112195 15757716233684419471668293)
                    ·
                      refine ⟨2954571793815828650937805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15757716233684419471668293 2954571793815828650937805)
                      ·
                        rfl

theorem cell23_5754008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5754008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754008 prefixEnd_5754008 := by exact prefixLift 5754008
  have htrace : WordTrace (prefixWord ++ tailWord_5754008) baseStart_5754008 baseEnd_5754008 := by
    simpa [prefixWord, tailWord_5754008, baseEnd_5754008] using wordTrace_append hprefix tailTrace_5754008
  have hstable : (prefixWord ++ tailWord_5754008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754008).length < 2 ^ (prefixWord ++ tailWord_5754008).sum := by decide
  have hdescent : baseEnd_5754008 < baseStart_5754008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754018 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5754018 : Nat := 118140960795 + 5754018 * 2 ^ 59
def prefixEnd_5754018 : Nat := 4983230072969 + 3 ^ 40 * 5754018 * 2
def baseEnd_5754018 : Nat := 984858976207457870604253

theorem tailTrace_5754018 : CollatzResearch.WordTrace tailWord_5754018 prefixEnd_5754018 984858976207457870604253 := by
  unfold tailWord_5754018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52466569417045742220531677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139910851778788645921417805 52466569417045742220531677)
  ·
    refine ⟨19674963531392153332699379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52466569417045742220531677 19674963531392153332699379)
    ·
      refine ⟨29512445297088229999049069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19674963531392153332699379 29512445297088229999049069)
      ·
        refine ⟨11067166986408086249643401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29512445297088229999049069 11067166986408086249643401)
        ·
          refine ⟨8300375239806064687232551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11067166986408086249643401 8300375239806064687232551)
          ·
            refine ⟨12450562859709097030848827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300375239806064687232551 12450562859709097030848827)
            ·
              refine ⟨18675844289563645546273241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450562859709097030848827 18675844289563645546273241)
              ·
                refine ⟨14006883217172734159704931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18675844289563645546273241 14006883217172734159704931)
                ·
                  refine ⟨21010324825759101239557397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14006883217172734159704931 21010324825759101239557397)
                  ·
                    refine ⟨984858976207457870604253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21010324825759101239557397 984858976207457870604253)
                    ·
                      rfl

theorem cell23_5754018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5754018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754018 prefixEnd_5754018 := by exact prefixLift 5754018
  have htrace : WordTrace (prefixWord ++ tailWord_5754018) baseStart_5754018 baseEnd_5754018 := by
    simpa [prefixWord, tailWord_5754018, baseEnd_5754018] using wordTrace_append hprefix tailTrace_5754018
  have hstable : (prefixWord ++ tailWord_5754018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754018).length < 2 ^ (prefixWord ++ tailWord_5754018).sum := by decide
  have hdescent : baseEnd_5754018 < baseStart_5754018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754021 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_5754021 : Nat := 118140960795 + 5754021 * 2 ^ 59
def prefixEnd_5754021 : Nat := 4983230072969 + 3 ^ 40 * 5754021 * 2
def baseEnd_5754021 : Nat := 2954578469064337100075245

theorem tailTrace_5754021 : CollatzResearch.WordTrace tailWord_5754021 prefixEnd_5754021 2954578469064337100075245 := by
  unfold tailWord_5754021
  simp only [CollatzResearch.WordTrace]
  refine ⟨209866387087172100394485917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139910924724781400262990611 209866387087172100394485917)
  ·
    refine ⟨78699895157689537647932219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209866387087172100394485917 78699895157689537647932219)
    ·
      refine ⟨118049842736534306471898329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78699895157689537647932219 118049842736534306471898329)
      ·
        refine ⟨88537382052400729853923747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118049842736534306471898329 88537382052400729853923747)
        ·
          refine ⟨132806073078601094780885621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88537382052400729853923747 132806073078601094780885621)
          ·
            refine ⟨12450569351118852635708027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132806073078601094780885621 12450569351118852635708027)
            ·
              refine ⟨18675854026678278953562041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450569351118852635708027 18675854026678278953562041)
              ·
                refine ⟨14006890520008709215171531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18675854026678278953562041 14006890520008709215171531)
                ·
                  refine ⟨21010335780013063822757297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14006890520008709215171531 21010335780013063822757297)
                  ·
                    refine ⟨15757751835009797867067973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21010335780013063822757297 15757751835009797867067973)
                    ·
                      refine ⟨2954578469064337100075245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15757751835009797867067973 2954578469064337100075245)
                      ·
                        rfl

theorem cell23_5754021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_5754021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754021 prefixEnd_5754021 := by exact prefixLift 5754021
  have htrace : WordTrace (prefixWord ++ tailWord_5754021) baseStart_5754021 baseEnd_5754021 := by
    simpa [prefixWord, tailWord_5754021, baseEnd_5754021] using wordTrace_append hprefix tailTrace_5754021
  have hstable : (prefixWord ++ tailWord_5754021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754021).length < 2 ^ (prefixWord ++ tailWord_5754021).sum := by decide
  have hdescent : baseEnd_5754021 < baseStart_5754021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754048 : List Nat := [2, 1, 1, 2, 7, 1, 1, 8]
def baseStart_5754048 : Nat := 118140960795 + 5754048 * 2 ^ 59
def prefixEnd_5754048 : Nat := 4983230072969 + 3 ^ 40 * 5754048 * 2
def baseEnd_5754048 : Nat := 109429345668222536831023

theorem tailTrace_5754048 : CollatzResearch.WordTrace tailWord_5754048 prefixEnd_5754048 109429345668222536831023 := by
  unfold tailWord_5754048
  simp only [CollatzResearch.WordTrace]
  refine ⟨104933685929037142002859399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139911581238716189337145865 104933685929037142002859399)
  ·
    refine ⟨157400528893555713004289099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104933685929037142002859399 157400528893555713004289099)
    ·
      refine ⟨236100793340333569506433649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157400528893555713004289099 236100793340333569506433649)
      ·
        refine ⟨177075595005250177129825237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236100793340333569506433649 177075595005250177129825237)
        ·
          refine ⟨4150209257935551026480279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177075595005250177129825237 4150209257935551026480279)
          ·
            refine ⟨6225313886903326539720419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150209257935551026480279 6225313886903326539720419)
            ·
              refine ⟨9337970830354989809580629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225313886903326539720419 9337970830354989809580629)
              ·
                refine ⟨109429345668222536831023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9337970830354989809580629 109429345668222536831023)
                ·
                  rfl

theorem cell23_5754048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 8].length) (baseStart_5754048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754048 prefixEnd_5754048 := by exact prefixLift 5754048
  have htrace : WordTrace (prefixWord ++ tailWord_5754048) baseStart_5754048 baseEnd_5754048 := by
    simpa [prefixWord, tailWord_5754048, baseEnd_5754048] using wordTrace_append hprefix tailTrace_5754048
  have hstable : (prefixWord ++ tailWord_5754048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754048).length < 2 ^ (prefixWord ++ tailWord_5754048).sum := by decide
  have hdescent : baseEnd_5754048 < baseStart_5754048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754058 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_5754058 : Nat := 118140960795 + 5754058 * 2 ^ 59
def prefixEnd_5754058 : Nat := 4983230072969 + 3 ^ 40 * 5754058 * 2
def baseEnd_5754058 : Nat := 2954597467848553455312575

theorem tailTrace_5754058 : CollatzResearch.WordTrace tailWord_5754058 prefixEnd_5754058 2954597467848553455312575 := by
  unfold tailWord_5754058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52466934147009513928395707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139911824392025370475721885 52466934147009513928395707)
  ·
    refine ⟨78700401220514270892593561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52466934147009513928395707 78700401220514270892593561)
    ·
      refine ⟨59025300915385703169445171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78700401220514270892593561 59025300915385703169445171)
      ·
        refine ⟨88537951373078554754167757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59025300915385703169445171 88537951373078554754167757)
        ·
          refine ⟨33201731764904458032812909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88537951373078554754167757 33201731764904458032812909)
          ·
            refine ⟨12450649411839171762304841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33201731764904458032812909 12450649411839171762304841)
            ·
              refine ⟨9337987058879378821728631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12450649411839171762304841 9337987058879378821728631)
              ·
                refine ⟨14006980588319068232592947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337987058879378821728631 14006980588319068232592947)
                ·
                  refine ⟨21010470882478602348889421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14006980588319068232592947 21010470882478602348889421)
                  ·
                    refine ⟨7878926580929475880833533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21010470882478602348889421 7878926580929475880833533)
                    ·
                      refine ⟨2954597467848553455312575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878926580929475880833533 2954597467848553455312575)
                      ·
                        rfl

theorem cell23_5754058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_5754058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754058 prefixEnd_5754058 := by exact prefixLift 5754058
  have htrace : WordTrace (prefixWord ++ tailWord_5754058) baseStart_5754058 baseEnd_5754058 := by
    simpa [prefixWord, tailWord_5754058, baseEnd_5754058] using wordTrace_append hprefix tailTrace_5754058
  have hstable : (prefixWord ++ tailWord_5754058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754058).length < 2 ^ (prefixWord ++ tailWord_5754058).sum := by decide
  have hdescent : baseEnd_5754058 < baseStart_5754058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754074 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_5754074 : Nat := 118140960795 + 5754074 * 2 ^ 59
def prefixEnd_5754074 : Nat := 4983230072969 + 3 ^ 40 * 5754074 * 2
def baseEnd_5754074 : Nat := 984868561179675130904167

theorem tailTrace_5754074 : CollatzResearch.WordTrace tailWord_5754074 prefixEnd_5754074 984868561179675130904167 := by
  unfold tailWord_5754074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52467080038995022611541319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139912213437320060297443517 52467080038995022611541319)
  ·
    refine ⟨78700620058492533917311979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52467080038995022611541319 78700620058492533917311979)
    ·
      refine ⟨118050930087738800875967969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78700620058492533917311979 118050930087738800875967969)
      ·
        refine ⟨88538197565804100656975977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118050930087738800875967969 88538197565804100656975977)
        ·
          refine ⟨66403648174353075492731983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88538197565804100656975977 66403648174353075492731983)
          ·
            refine ⟨99605472261529613239097975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66403648174353075492731983 99605472261529613239097975)
            ·
              refine ⟨149408208392294419858646963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99605472261529613239097975 149408208392294419858646963)
              ·
                refine ⟨224112312588441629787970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149408208392294419858646963 224112312588441629787970445)
                ·
                  refine ⟨84042117220665611170488917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224112312588441629787970445 84042117220665611170488917)
                  ·
                    refine ⟨984868561179675130904167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84042117220665611170488917 984868561179675130904167)
                    ·
                      rfl

theorem cell23_5754074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_5754074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754074 prefixEnd_5754074 := by exact prefixLift 5754074
  have htrace : WordTrace (prefixWord ++ tailWord_5754074) baseStart_5754074 baseEnd_5754074 := by
    simpa [prefixWord, tailWord_5754074, baseEnd_5754074] using wordTrace_append hprefix tailTrace_5754074
  have hstable : (prefixWord ++ tailWord_5754074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754074).length < 2 ^ (prefixWord ++ tailWord_5754074).sum := by decide
  have hdescent : baseEnd_5754074 < baseStart_5754074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754111 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_5754111 : Nat := 118140960795 + 5754111 * 2 ^ 59
def prefixEnd_5754111 : Nat := 4983230072969 + 3 ^ 40 * 5754111 * 2
def baseEnd_5754111 : Nat := 2954624682323241747949831

theorem tailTrace_5754111 : CollatzResearch.WordTrace tailWord_5754111 prefixEnd_5754111 2954624682323241747949831 := by
  unfold tailWord_5754111
  simp only [CollatzResearch.WordTrace]
  refine ⟨209869669656846045765262187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139913113104564030510174791 209869669656846045765262187)
  ·
    refine ⟨314804504485269068647893281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209869669656846045765262187 314804504485269068647893281)
    ·
      refine ⟨236103378363951801485919961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314804504485269068647893281 236103378363951801485919961)
      ·
        refine ⟨177077533772963851114439971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236103378363951801485919961 177077533772963851114439971)
        ·
          refine ⟨265616300659445776671659957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177077533772963851114439971 265616300659445776671659957)
          ·
            refine ⟨24901528186823041562968121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265616300659445776671659957 24901528186823041562968121)
            ·
              refine ⟨18676146140117281172226091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24901528186823041562968121 18676146140117281172226091)
              ·
                refine ⟨28014219210175921758339137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18676146140117281172226091 28014219210175921758339137)
                ·
                  refine ⟨21010664407631941318754353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28014219210175921758339137 21010664407631941318754353)
                  ·
                    refine ⟨15757998305723955989065765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21010664407631941318754353 15757998305723955989065765)
                    ·
                      refine ⟨2954624682323241747949831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15757998305723955989065765 2954624682323241747949831)
                      ·
                        rfl

theorem cell23_5754111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_5754111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754111 prefixEnd_5754111 := by exact prefixLift 5754111
  have htrace : WordTrace (prefixWord ++ tailWord_5754111) baseStart_5754111 baseEnd_5754111 := by
    simpa [prefixWord, tailWord_5754111, baseEnd_5754111] using wordTrace_append hprefix tailTrace_5754111
  have hstable : (prefixWord ++ tailWord_5754111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754111).length < 2 ^ (prefixWord ++ tailWord_5754111).sum := by decide
  have hdescent : baseEnd_5754111 < baseStart_5754111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754115 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 4, 2]
def baseStart_5754115 : Nat := 118140960795 + 5754115 * 2 ^ 59
def prefixEnd_5754115 : Nat := 4983230072969 + 3 ^ 40 * 5754115 * 2
def baseEnd_5754115 : Nat := 2954626736245859732299813

theorem tailTrace_5754115 : CollatzResearch.WordTrace tailWord_5754115 prefixEnd_5754115 2954626736245859732299813 := by
  unfold tailWord_5754115
  simp only [CollatzResearch.WordTrace]
  refine ⟨209869815548831554448407799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139913210365887702965605199 209869815548831554448407799)
  ·
    refine ⟨314804723323247331672611699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209869815548831554448407799 314804723323247331672611699)
    ·
      refine ⟨472207084984870997508917549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314804723323247331672611699 472207084984870997508917549)
      ·
        refine ⟨177077656869326624065844081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472207084984870997508917549 177077656869326624065844081)
        ·
          refine ⟨132808242651994968049383061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177077656869326624065844081 132808242651994968049383061)
          ·
            refine ⟨6225386374312264127314831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132808242651994968049383061 6225386374312264127314831)
            ·
              refine ⟨9338079561468396190972247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225386374312264127314831 9338079561468396190972247)
              ·
                refine ⟨14007119342202594286458371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338079561468396190972247 14007119342202594286458371)
                ·
                  refine ⟨21010679013303891429687557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14007119342202594286458371 21010679013303891429687557)
                  ·
                    refine ⟨3939502314994479643066417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21010679013303891429687557 3939502314994479643066417)
                    ·
                      refine ⟨2954626736245859732299813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939502314994479643066417 2954626736245859732299813)
                      ·
                        rfl

theorem cell23_5754115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_5754115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754115 prefixEnd_5754115 := by exact prefixLift 5754115
  have htrace : WordTrace (prefixWord ++ tailWord_5754115) baseStart_5754115 baseEnd_5754115 := by
    simpa [prefixWord, tailWord_5754115, baseEnd_5754115] using wordTrace_append hprefix tailTrace_5754115
  have hstable : (prefixWord ++ tailWord_5754115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754115).length < 2 ^ (prefixWord ++ tailWord_5754115).sum := by decide
  have hdescent : baseEnd_5754115 < baseStart_5754115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754161 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5754161 : Nat := 118140960795 + 5754161 * 2 ^ 59
def prefixEnd_5754161 : Nat := 4983230072969 + 3 ^ 40 * 5754161 * 2
def baseEnd_5754161 : Nat := 2954650356355966552324601

theorem tailTrace_5754161 : CollatzResearch.WordTrace tailWord_5754161 prefixEnd_5754161 2954650356355966552324601 := by
  unfold tailWord_5754161
  simp only [CollatzResearch.WordTrace]
  refine ⟨209871493306664904304582337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139914328871109936203054891 209871493306664904304582337)
  ·
    refine ⟨157403619979998678228436753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209871493306664904304582337 157403619979998678228436753)
    ·
      refine ⟨118052714984999008671327565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157403619979998678228436753 118052714984999008671327565)
      ·
        refine ⟨44269768119374628251747837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118052714984999008671327565 44269768119374628251747837)
        ·
          refine ⟨16601163044765485594405439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44269768119374628251747837 16601163044765485594405439)
          ·
            refine ⟨24901744567148228391608159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16601163044765485594405439 24901744567148228391608159)
            ·
              refine ⟨37352616850722342587412239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24901744567148228391608159 37352616850722342587412239)
              ·
                refine ⟨56028925276083513881118359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37352616850722342587412239 56028925276083513881118359)
                ·
                  refine ⟨84043387914125270821677539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56028925276083513881118359 84043387914125270821677539)
                  ·
                    refine ⟨126065081871187906232516309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84043387914125270821677539 126065081871187906232516309)
                    ·
                      refine ⟨2954650356355966552324601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126065081871187906232516309 2954650356355966552324601)
                      ·
                        rfl

theorem cell23_5754161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5754161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754161 prefixEnd_5754161 := by exact prefixLift 5754161
  have htrace : WordTrace (prefixWord ++ tailWord_5754161) baseStart_5754161 baseEnd_5754161 := by
    simpa [prefixWord, tailWord_5754161, baseEnd_5754161] using wordTrace_append hprefix tailTrace_5754161
  have hstable : (prefixWord ++ tailWord_5754161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754161).length < 2 ^ (prefixWord ++ tailWord_5754161).sum := by decide
  have hdescent : baseEnd_5754161 < baseStart_5754161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754166 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5754166 : Nat := 118140960795 + 5754166 * 2 ^ 59
def prefixEnd_5754166 : Nat := 4983230072969 + 3 ^ 40 * 5754166 * 2
def baseEnd_5754166 : Nat := 2954652923759239032762079

theorem tailTrace_5754166 : CollatzResearch.WordTrace tailWord_5754166 prefixEnd_5754166 2954652923759239032762079 := by
  unfold tailWord_5754166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116979729477924384907147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139914450447764526772342901 13116979729477924384907147)
  ·
    refine ⟨19675469594216886577360721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13116979729477924384907147 19675469594216886577360721)
    ·
      refine ⟨14756602195662664933020541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19675469594216886577360721 14756602195662664933020541)
      ·
        refine ⟨5533725823373499349882703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14756602195662664933020541 5533725823373499349882703)
        ·
          refine ⟨8300588735060249024824055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533725823373499349882703 8300588735060249024824055)
          ·
            refine ⟨12450883102590373537236083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300588735060249024824055 12450883102590373537236083)
            ·
              refine ⟨18676324653885560305854125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450883102590373537236083 18676324653885560305854125)
              ·
                refine ⟨7003621745207085114695297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18676324653885560305854125 7003621745207085114695297)
                ·
                  refine ⟨5252716308905313836021473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003621745207085114695297 5252716308905313836021473)
                  ·
                    refine ⟨3939537231678985377016105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252716308905313836021473 3939537231678985377016105)
                    ·
                      refine ⟨2954652923759239032762079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939537231678985377016105 2954652923759239032762079)
                      ·
                        rfl

theorem cell23_5754166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5754166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754166 prefixEnd_5754166 := by exact prefixLift 5754166
  have htrace : WordTrace (prefixWord ++ tailWord_5754166) baseStart_5754166 baseEnd_5754166 := by
    simpa [prefixWord, tailWord_5754166, baseEnd_5754166] using wordTrace_append hprefix tailTrace_5754166
  have hstable : (prefixWord ++ tailWord_5754166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754166).length < 2 ^ (prefixWord ++ tailWord_5754166).sum := by decide
  have hdescent : baseEnd_5754166 < baseStart_5754166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754188 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5754188 : Nat := 118140960795 + 5754188 * 2 ^ 59
def prefixEnd_5754188 : Nat := 4983230072969 + 3 ^ 40 * 5754188 * 2
def baseEnd_5754188 : Nat := 2954664220333637946686977

theorem tailTrace_5754188 : CollatzResearch.WordTrace tailWord_5754188 prefixEnd_5754188 2954664220333637946686977 := by
  unfold tailWord_5754188
  simp only [CollatzResearch.WordTrace]
  refine ⟨104936239038783543957907609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139914985385044725277210145 104936239038783543957907609)
  ·
    refine ⟨78702179279087657968430707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104936239038783543957907609 78702179279087657968430707)
    ·
      refine ⟨118053268918631486952646061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78702179279087657968430707 118053268918631486952646061)
      ·
        refine ⟨44269975844486807607242273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118053268918631486952646061 44269975844486807607242273)
        ·
          refine ⟨33202481883365105705431705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44269975844486807607242273 33202481883365105705431705)
          ·
            refine ⟨24901861412523829279073779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33202481883365105705431705 24901861412523829279073779)
            ·
              refine ⟨37352792118785743918610669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24901861412523829279073779 37352792118785743918610669)
              ·
                refine ⟨14007297044544653969479001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37352792118785743918610669 14007297044544653969479001)
                ·
                  refine ⟨10505472783408490477109251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14007297044544653969479001 10505472783408490477109251)
                  ·
                    refine ⟨15758209175112735715663877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10505472783408490477109251 15758209175112735715663877)
                    ·
                      refine ⟨2954664220333637946686977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15758209175112735715663877 2954664220333637946686977)
                      ·
                        rfl

theorem cell23_5754188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5754188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754188 prefixEnd_5754188 := by exact prefixLift 5754188
  have htrace : WordTrace (prefixWord ++ tailWord_5754188) baseStart_5754188 baseEnd_5754188 := by
    simpa [prefixWord, tailWord_5754188, baseEnd_5754188] using wordTrace_append hprefix tailTrace_5754188
  have hstable : (prefixWord ++ tailWord_5754188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754188).length < 2 ^ (prefixWord ++ tailWord_5754188).sum := by decide
  have hdescent : baseEnd_5754188 < baseStart_5754188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754191 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_5754191 : Nat := 118140960795 + 5754191 * 2 ^ 59
def prefixEnd_5754191 : Nat := 4983230072969 + 3 ^ 40 * 5754191 * 2
def baseEnd_5754191 : Nat := 2954665760775601434949463

theorem tailTrace_5754191 : CollatzResearch.WordTrace tailWord_5754191 prefixEnd_5754191 2954665760775601434949463 := by
  unfold tailWord_5754191
  simp only [CollatzResearch.WordTrace]
  refine ⟨209872587496556219428174427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139915058331037479618782951 209872587496556219428174427)
  ·
    refine ⟨314808881244834329142261641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209872587496556219428174427 314808881244834329142261641)
    ·
      refine ⟨236106660933625746856696231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314808881244834329142261641 236106660933625746856696231)
      ·
        refine ⟨354159991400438620285044347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236106660933625746856696231 354159991400438620285044347)
        ·
          refine ⟨531239987100657930427566521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354159991400438620285044347 531239987100657930427566521)
          ·
            refine ⟨398429990325493447820674891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531239987100657930427566521 398429990325493447820674891)
            ·
              refine ⟨597644985488240171731012337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398429990325493447820674891 597644985488240171731012337)
              ·
                refine ⟨448233739116180128798259253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597644985488240171731012337 448233739116180128798259253)
                ·
                  refine ⟨42021913042141887074836805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 448233739116180128798259253 42021913042141887074836805)
                  ·
                    refine ⟨7879108695401603826531901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42021913042141887074836805 7879108695401603826531901)
                    ·
                      refine ⟨2954665760775601434949463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879108695401603826531901 2954665760775601434949463)
                      ·
                        rfl

theorem cell23_5754191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_5754191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754191 prefixEnd_5754191 := by exact prefixLift 5754191
  have htrace : WordTrace (prefixWord ++ tailWord_5754191) baseStart_5754191 baseEnd_5754191 := by
    simpa [prefixWord, tailWord_5754191, baseEnd_5754191] using wordTrace_append hprefix tailTrace_5754191
  have hstable : (prefixWord ++ tailWord_5754191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754191).length < 2 ^ (prefixWord ++ tailWord_5754191).sum := by decide
  have hdescent : baseEnd_5754191 < baseStart_5754191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754242 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5754242 : Nat := 118140960795 + 5754242 * 2 ^ 59
def prefixEnd_5754242 : Nat := 4983230072969 + 3 ^ 40 * 5754242 * 2
def baseEnd_5754242 : Nat := 2954691948288980735411729

theorem tailTrace_5754242 : CollatzResearch.WordTrace tailWord_5754242 prefixEnd_5754242 2954691948288980735411729 := by
  unfold tailWord_5754242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52468611904842863784570245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139916298412914303425520653 52468611904842863784570245)
  ·
    refine ⟨9837864732158036959606921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52468611904842863784570245 9837864732158036959606921)
    ·
      refine ⟨7378398549118527719705191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9837864732158036959606921 7378398549118527719705191)
      ·
        refine ⟨11067597823677791579557787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378398549118527719705191 11067597823677791579557787)
        ·
          refine ⟨16601396735516687369336681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067597823677791579557787 16601396735516687369336681)
          ·
            refine ⟨12451047551637515527002511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16601396735516687369336681 12451047551637515527002511)
            ·
              refine ⟨18676571327456273290503767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12451047551637515527002511 18676571327456273290503767)
              ·
                refine ⟨28014856991184409935755651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18676571327456273290503767 28014856991184409935755651)
                ·
                  refine ⟨42022285486776614903633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28014856991184409935755651 42022285486776614903633477)
                  ·
                    refine ⟨7879178528770615294431277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42022285486776614903633477 7879178528770615294431277)
                    ·
                      refine ⟨2954691948288980735411729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879178528770615294431277 2954691948288980735411729)
                      ·
                        rfl

theorem cell23_5754242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5754242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754242 prefixEnd_5754242 := by exact prefixLift 5754242
  have htrace : WordTrace (prefixWord ++ tailWord_5754242) baseStart_5754242 baseEnd_5754242 := by
    simpa [prefixWord, tailWord_5754242, baseEnd_5754242] using wordTrace_append hprefix tailTrace_5754242
  have hstable : (prefixWord ++ tailWord_5754242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754242).length < 2 ^ (prefixWord ++ tailWord_5754242).sum := by decide
  have hdescent : baseEnd_5754242 < baseStart_5754242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754272 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 1, 1, 3]
def baseStart_5754272 : Nat := 118140960795 + 5754272 * 2 ^ 59
def prefixEnd_5754272 : Nat := 4983230072969 + 3 ^ 40 * 5754272 * 2
def baseEnd_5754272 : Nat := 2954707352708615618036591

theorem tailTrace_5754272 : CollatzResearch.WordTrace tailWord_5754272 prefixEnd_5754272 2954707352708615618036591 := by
  unfold tailWord_5754272
  simp only [CollatzResearch.WordTrace]
  refine ⟨104937770904631385130936535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139917027872841846841248713 104937770904631385130936535)
  ·
    refine ⟨157406656356947077696404803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104937770904631385130936535 157406656356947077696404803)
    ·
      refine ⟨236109984535420616544607205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157406656356947077696404803 236109984535420616544607205)
      ·
        refine ⟨44270622100391365602113851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236109984535420616544607205 44270622100391365602113851)
        ·
          refine ⟨66405933150587048403170777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44270622100391365602113851 66405933150587048403170777)
          ·
            refine ⟨49804449862940286302378083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66405933150587048403170777 49804449862940286302378083)
            ·
              refine ⟨74706674794410429453567125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49804449862940286302378083 74706674794410429453567125)
              ·
                refine ⟨3501875380987988880635959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74706674794410429453567125 3501875380987988880635959)
                ·
                  refine ⟨5252813071481983320953939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501875380987988880635959 5252813071481983320953939)
                  ·
                    refine ⟨7879219607222974981430909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252813071481983320953939 7879219607222974981430909)
                    ·
                      refine ⟨2954707352708615618036591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879219607222974981430909 2954707352708615618036591)
                      ·
                        rfl

theorem cell23_5754272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_5754272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754272 prefixEnd_5754272 := by exact prefixLift 5754272
  have htrace : WordTrace (prefixWord ++ tailWord_5754272) baseStart_5754272 baseEnd_5754272 := by
    simpa [prefixWord, tailWord_5754272, baseEnd_5754272] using wordTrace_append hprefix tailTrace_5754272
  have hstable : (prefixWord ++ tailWord_5754272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754272).length < 2 ^ (prefixWord ++ tailWord_5754272).sum := by decide
  have hdescent : baseEnd_5754272 < baseStart_5754272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754295 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_5754295 : Nat := 118140960795 + 5754295 * 2 ^ 59
def prefixEnd_5754295 : Nat := 4983230072969 + 3 ^ 40 * 5754295 * 2
def baseEnd_5754295 : Nat := 2954719162763669028048985

theorem tailTrace_5754295 : CollatzResearch.WordTrace tailWord_5754295 prefixEnd_5754295 2954719162763669028048985 := by
  unfold tailWord_5754295
  simp only [CollatzResearch.WordTrace]
  refine ⟨209876380688179445189960339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139917587125452963459973559 209876380688179445189960339)
  ·
    refine ⟨314814571032269167784940509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209876380688179445189960339 314814571032269167784940509)
    ·
      refine ⟨118055464137100937919352691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314814571032269167784940509 118055464137100937919352691)
      ·
        refine ⟨177083196205651406879029037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118055464137100937919352691 177083196205651406879029037)
        ·
          refine ⟨66406198577119277579635889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177083196205651406879029037 66406198577119277579635889)
          ·
            refine ⟨49804648932839458184726917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66406198577119277579635889 49804648932839458184726917)
            ·
              refine ⟨9338371674907398409636297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49804648932839458184726917 9338371674907398409636297)
              ·
                refine ⟨7003778756180548807227223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9338371674907398409636297 7003778756180548807227223)
                ·
                  refine ⟨10505668134270823210840835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003778756180548807227223 10505668134270823210840835)
                  ·
                    refine ⟨15758502201406234816261253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10505668134270823210840835 15758502201406234816261253)
                    ·
                      refine ⟨2954719162763669028048985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15758502201406234816261253 2954719162763669028048985)
                      ·
                        rfl

theorem cell23_5754295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_5754295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754295 prefixEnd_5754295 := by exact prefixLift 5754295
  have htrace : WordTrace (prefixWord ++ tailWord_5754295) baseStart_5754295 baseEnd_5754295 := by
    simpa [prefixWord, tailWord_5754295, baseEnd_5754295] using wordTrace_append hprefix tailTrace_5754295
  have hstable : (prefixWord ++ tailWord_5754295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754295).length < 2 ^ (prefixWord ++ tailWord_5754295).sum := by decide
  have hdescent : baseEnd_5754295 < baseStart_5754295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754315 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 3]
def baseStart_5754315 : Nat := 118140960795 + 5754315 * 2 ^ 59
def prefixEnd_5754315 : Nat := 4983230072969 + 3 ^ 40 * 5754315 * 2
def baseEnd_5754315 : Nat := 2954729432376758949798893

theorem tailTrace_5754315 : CollatzResearch.WordTrace tailWord_5754315 prefixEnd_5754315 2954729432376758949798893 := by
  unfold tailWord_5754315
  simp only [CollatzResearch.WordTrace]
  refine ⟨209877110148106988605688399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139918073432071325737125599 209877110148106988605688399)
  ·
    refine ⟨314815665222160482908532599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209877110148106988605688399 314815665222160482908532599)
    ·
      refine ⟨472223497833240724362798899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314815665222160482908532599 472223497833240724362798899)
      ·
        refine ⟨708335246749861086544198349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472223497833240724362798899 708335246749861086544198349)
        ·
          refine ⟨265625717531197907454074381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708335246749861086544198349 265625717531197907454074381)
          ·
            refine ⟨99609644074199215295277893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265625717531197907454074381 99609644074199215295277893)
            ·
              refine ⟨18676808263912352867864605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99609644074199215295277893 18676808263912352867864605)
              ·
                refine ⟨7003803098967132325449227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18676808263912352867864605 7003803098967132325449227)
                ·
                  refine ⟨10505704648450698488173841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003803098967132325449227 10505704648450698488173841)
                  ·
                    refine ⟨7879278486338023866130381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10505704648450698488173841 7879278486338023866130381)
                    ·
                      refine ⟨2954729432376758949798893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879278486338023866130381 2954729432376758949798893)
                      ·
                        rfl

theorem cell23_5754315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 3].length) (baseStart_5754315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754315 prefixEnd_5754315 := by exact prefixLift 5754315
  have htrace : WordTrace (prefixWord ++ tailWord_5754315) baseStart_5754315 baseEnd_5754315 := by
    simpa [prefixWord, tailWord_5754315, baseEnd_5754315] using wordTrace_append hprefix tailTrace_5754315
  have hstable : (prefixWord ++ tailWord_5754315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754315).length < 2 ^ (prefixWord ++ tailWord_5754315).sum := by decide
  have hdescent : baseEnd_5754315 < baseStart_5754315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754329 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 3, 2, 2]
def baseStart_5754329 : Nat := 118140960795 + 5754329 * 2 ^ 59
def prefixEnd_5754329 : Nat := 4983230072969 + 3 ^ 40 * 5754329 * 2
def baseEnd_5754329 : Nat := 2954736621105921895023829

theorem tailTrace_5754329 : CollatzResearch.WordTrace tailWord_5754329 prefixEnd_5754329 2954736621105921895023829 := by
  unfold tailWord_5754329
  simp only [CollatzResearch.WordTrace]
  refine ⟨209877620770056268996698041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139918413846704179331132027 209877620770056268996698041)
  ·
    refine ⟨157408215577542201747523531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209877620770056268996698041 157408215577542201747523531)
    ·
      refine ⟨236112323366313302621285297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157408215577542201747523531 236112323366313302621285297)
      ·
        refine ⟨177084242524734976965963973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236112323366313302621285297 177084242524734976965963973)
        ·
          refine ⟨33203295473387808181118245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177084242524734976965963973 33203295473387808181118245)
          ·
            refine ⟨6225617901260214033959671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33203295473387808181118245 6225617901260214033959671)
            ·
              refine ⟨9338426851890321050939507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225617901260214033959671 9338426851890321050939507)
              ·
                refine ⟨14007640277835481576409261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338426851890321050939507 14007640277835481576409261)
                ·
                  refine ⟨5252865104188305591153473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14007640277835481576409261 5252865104188305591153473)
                  ·
                    refine ⟨3939648828141229193365105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252865104188305591153473 3939648828141229193365105)
                    ·
                      refine ⟨2954736621105921895023829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939648828141229193365105 2954736621105921895023829)
                      ·
                        rfl

theorem cell23_5754329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_5754329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754329 prefixEnd_5754329 := by exact prefixLift 5754329
  have htrace : WordTrace (prefixWord ++ tailWord_5754329) baseStart_5754329 baseEnd_5754329 := by
    simpa [prefixWord, tailWord_5754329, baseEnd_5754329] using wordTrace_append hprefix tailTrace_5754329
  have hstable : (prefixWord ++ tailWord_5754329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754329).length < 2 ^ (prefixWord ++ tailWord_5754329).sum := by decide
  have hdescent : baseEnd_5754329 < baseStart_5754329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754331 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 9]
def baseStart_5754331 : Nat := 118140960795 + 5754331 * 2 ^ 59
def prefixEnd_5754331 : Nat := 4983230072969 + 3 ^ 40 * 5754331 * 2
def baseEnd_5754331 : Nat := 984912549355743629066273

theorem tailTrace_5754331 : CollatzResearch.WordTrace tailWord_5754331 prefixEnd_5754331 984912549355743629066273 := by
  unfold tailWord_5754331
  simp only [CollatzResearch.WordTrace]
  refine ⟨209877693716049023338270847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139918462477366015558847231 209877693716049023338270847)
  ·
    refine ⟨314816540574073535007406271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209877693716049023338270847 314816540574073535007406271)
    ·
      refine ⟨472224810861110302511109407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314816540574073535007406271 472224810861110302511109407)
      ·
        refine ⟨708337216291665453766664111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472224810861110302511109407 708337216291665453766664111)
        ·
          refine ⟨1062505824437498180649996167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708337216291665453766664111 1062505824437498180649996167)
          ·
            refine ⟨1593758736656247270974994251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062505824437498180649996167 1593758736656247270974994251)
            ·
              refine ⟨2390638104984370906462491377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593758736656247270974994251 2390638104984370906462491377)
              ·
                refine ⟨1792978578738278179846868533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390638104984370906462491377 1792978578738278179846868533)
                ·
                  refine ⟨168091741756713579360643925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792978578738278179846868533 168091741756713579360643925)
                  ·
                    refine ⟨984912549355743629066273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168091741756713579360643925 984912549355743629066273)
                    ·
                      rfl

theorem cell23_5754331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_5754331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754331 prefixEnd_5754331 := by exact prefixLift 5754331
  have htrace : WordTrace (prefixWord ++ tailWord_5754331) baseStart_5754331 baseEnd_5754331 := by
    simpa [prefixWord, tailWord_5754331, baseEnd_5754331] using wordTrace_append hprefix tailTrace_5754331
  have hstable : (prefixWord ++ tailWord_5754331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754331).length < 2 ^ (prefixWord ++ tailWord_5754331).sum := by decide
  have hdescent : baseEnd_5754331 < baseStart_5754331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754339 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 2, 4]
def baseStart_5754339 : Nat := 118140960795 + 5754339 * 2 ^ 59
def prefixEnd_5754339 : Nat := 4983230072969 + 3 ^ 40 * 5754339 * 2
def baseEnd_5754339 : Nat := 984913918637488951966261

theorem tailTrace_5754339 : CollatzResearch.WordTrace tailWord_5754339 prefixEnd_5754339 984913918637488951966261 := by
  unfold tailWord_5754339
  simp only [CollatzResearch.WordTrace]
  refine ⟨209877985500020040704562071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139918657000013360469708047 209877985500020040704562071)
  ·
    refine ⟨314816978250030061056843107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209877985500020040704562071 314816978250030061056843107)
    ·
      refine ⟨472225467375045091585264661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314816978250030061056843107 472225467375045091585264661)
      ·
        refine ⟨22135568783205238668059281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 472225467375045091585264661 22135568783205238668059281)
        ·
          refine ⟨16601676587403929001044461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22135568783205238668059281 16601676587403929001044461)
          ·
            refine ⟨6225628720276473375391673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16601676587403929001044461 6225628720276473375391673)
            ·
              refine ⟨4669221540207355031543755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225628720276473375391673 4669221540207355031543755)
              ·
                refine ⟨7003832310311032547315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669221540207355031543755 7003832310311032547315633)
                ·
                  refine ⟨5252874232733274410486725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003832310311032547315633 5252874232733274410486725)
                  ·
                    refine ⟨984913918637488951966261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5252874232733274410486725 984913918637488951966261)
                    ·
                      rfl

theorem cell23_5754339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 4].length) (baseStart_5754339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754339 prefixEnd_5754339 := by exact prefixLift 5754339
  have htrace : WordTrace (prefixWord ++ tailWord_5754339) baseStart_5754339 baseEnd_5754339 := by
    simpa [prefixWord, tailWord_5754339, baseEnd_5754339] using wordTrace_append hprefix tailTrace_5754339
  have hstable : (prefixWord ++ tailWord_5754339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754339).length < 2 ^ (prefixWord ++ tailWord_5754339).sum := by decide
  have hdescent : baseEnd_5754339 < baseStart_5754339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754366 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5754366 : Nat := 118140960795 + 5754366 * 2 ^ 59
def prefixEnd_5754366 : Nat := 4983230072969 + 3 ^ 40 * 5754366 * 2
def baseEnd_5754366 : Nat := 2954755619890138250261159

theorem tailTrace_5754366 : CollatzResearch.WordTrace tailWord_5754366 prefixEnd_5754366 2954755619890138250261159 := by
  unfold tailWord_5754366
  simp only [CollatzResearch.WordTrace]
  refine ⟨26234871283865278039474369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139919313513948149543863301 26234871283865278039474369)
  ·
    refine ⟨19676153462898958529605777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26234871283865278039474369 19676153462898958529605777)
    ·
      refine ⟨14757115097174218897204333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19676153462898958529605777 14757115097174218897204333)
      ·
        refine ⟨5533918161440332086451625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14757115097174218897204333 5533918161440332086451625)
        ·
          refine ⟨4150438621080249064838719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5533918161440332086451625 4150438621080249064838719)
          ·
            refine ⟨6225657931620373597258079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150438621080249064838719 6225657931620373597258079)
            ·
              refine ⟨9338486897430560395887119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225657931620373597258079 9338486897430560395887119)
              ·
                refine ⟨14007730346145840593830679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338486897430560395887119 14007730346145840593830679)
                ·
                  refine ⟨21011595519218760890746019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14007730346145840593830679 21011595519218760890746019)
                  ·
                    refine ⟨31517393278828141336119029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21011595519218760890746019 31517393278828141336119029)
                    ·
                      refine ⟨2954755619890138250261159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31517393278828141336119029 2954755619890138250261159)
                      ·
                        rfl

theorem cell23_5754366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5754366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754366 prefixEnd_5754366 := by exact prefixLift 5754366
  have htrace : WordTrace (prefixWord ++ tailWord_5754366) baseStart_5754366 baseEnd_5754366 := by
    simpa [prefixWord, tailWord_5754366, baseEnd_5754366] using wordTrace_append hprefix tailTrace_5754366
  have hstable : (prefixWord ++ tailWord_5754366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754366).length < 2 ^ (prefixWord ++ tailWord_5754366).sum := by decide
  have hdescent : baseEnd_5754366 < baseStart_5754366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754374 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5754374 : Nat := 118140960795 + 5754374 * 2 ^ 59
def prefixEnd_5754374 : Nat := 4983230072969 + 3 ^ 40 * 5754374 * 2
def baseEnd_5754374 : Nat := 2954759727735374218961123

theorem tailTrace_5754374 : CollatzResearch.WordTrace tailWord_5754374 prefixEnd_5754374 2954759727735374218961123 := by
  unfold tailWord_5754374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558726939215413802565193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139919508036595494454724117 6558726939215413802565193)
  ·
    refine ⟨4919045204411560351923895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6558726939215413802565193 4919045204411560351923895)
    ·
      refine ⟨7378567806617340527885843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919045204411560351923895 7378567806617340527885843)
      ·
        refine ⟨11067851709926010791828765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378567806617340527885843 11067851709926010791828765)
        ·
          refine ⟨4150444391222254046935787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11067851709926010791828765 4150444391222254046935787)
          ·
            refine ⟨6225666586833381070403681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150444391222254046935787 6225666586833381070403681)
            ·
              refine ⟨4669249940125035802802761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225666586833381070403681 4669249940125035802802761)
              ·
                refine ⟨3501937455093776852102071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669249940125035802802761 3501937455093776852102071)
                ·
                  refine ⟨5252906182640665278153107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501937455093776852102071 5252906182640665278153107)
                  ·
                    refine ⟨7879359273960997917229661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252906182640665278153107 7879359273960997917229661)
                    ·
                      refine ⟨2954759727735374218961123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879359273960997917229661 2954759727735374218961123)
                      ·
                        rfl

theorem cell23_5754374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5754374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754374 prefixEnd_5754374 := by exact prefixLift 5754374
  have htrace : WordTrace (prefixWord ++ tailWord_5754374) baseStart_5754374 baseEnd_5754374 := by
    simpa [prefixWord, tailWord_5754374, baseEnd_5754374] using wordTrace_append hprefix tailTrace_5754374
  have hstable : (prefixWord ++ tailWord_5754374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754374).length < 2 ^ (prefixWord ++ tailWord_5754374).sum := by decide
  have hdescent : baseEnd_5754374 < baseStart_5754374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754379 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 3]
def baseStart_5754379 : Nat := 118140960795 + 5754379 * 2 ^ 59
def prefixEnd_5754379 : Nat := 4983230072969 + 3 ^ 40 * 5754379 * 2
def baseEnd_5754379 : Nat := 2954762295138646699398599

theorem tailTrace_5754379 : CollatzResearch.WordTrace tailWord_5754379 prefixEnd_5754379 2954762295138646699398599 := by
  unfold tailWord_5754379
  simp only [CollatzResearch.WordTrace]
  refine ⟨209879444419875127536018191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139919629613250085024012127 209879444419875127536018191)
  ·
    refine ⟨314819166629812691304027287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209879444419875127536018191 314819166629812691304027287)
    ·
      refine ⟨472228749944719036956040931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314819166629812691304027287 472228749944719036956040931)
      ·
        refine ⟨708343124917078555434061397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472228749944719036956040931 708343124917078555434061397)
        ·
          refine ⟨8300895995122014321492907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 708343124917078555434061397 8300895995122014321492907)
          ·
            refine ⟨12451343992683021482239361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300895995122014321492907 12451343992683021482239361)
            ·
              refine ⟨9338507994512266111679521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451343992683021482239361 9338507994512266111679521)
              ·
                refine ⟨7003880995884199583759641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9338507994512266111679521 7003880995884199583759641)
                ·
                  refine ⟨5252910746913149687819731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003880995884199583759641 5252910746913149687819731)
                  ·
                    refine ⟨7879366120369724531729597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252910746913149687819731 7879366120369724531729597)
                    ·
                      refine ⟨2954762295138646699398599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879366120369724531729597 2954762295138646699398599)
                      ·
                        rfl

theorem cell23_5754379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 3].length) (baseStart_5754379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754379 prefixEnd_5754379 := by exact prefixLift 5754379
  have htrace : WordTrace (prefixWord ++ tailWord_5754379) baseStart_5754379 baseEnd_5754379 := by
    simpa [prefixWord, tailWord_5754379, baseEnd_5754379] using wordTrace_append hprefix tailTrace_5754379
  have hstable : (prefixWord ++ tailWord_5754379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754379).length < 2 ^ (prefixWord ++ tailWord_5754379).sum := by decide
  have hdescent : baseEnd_5754379 < baseStart_5754379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754380 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_5754380 : Nat := 118140960795 + 5754380 * 2 ^ 59
def prefixEnd_5754380 : Nat := 4983230072969 + 3 ^ 40 * 5754380 * 2
def baseEnd_5754380 : Nat := 2954762808619301195486095

theorem tailTrace_5754380 : CollatzResearch.WordTrace tailWord_5754380 prefixEnd_5754380 2954762808619301195486095 := by
  unfold tailWord_5754380
  simp only [CollatzResearch.WordTrace]
  refine ⟨104939740446435752353402297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139919653928581003137869729 104939740446435752353402297)
  ·
    refine ⟨78704805334826814265051723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104939740446435752353402297 78704805334826814265051723)
    ·
      refine ⟨118057208002240221397577585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78704805334826814265051723 118057208002240221397577585)
      ·
        refine ⟨88542906001680166048183189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118057208002240221397577585 88542906001680166048183189)
        ·
          refine ⟨4150448718828757783508587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88542906001680166048183189 4150448718828757783508587)
          ·
            refine ⟨6225673078243136675262881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150448718828757783508587 6225673078243136675262881)
            ·
              refine ⟨4669254808682352506447161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225673078243136675262881 4669254808682352506447161)
              ·
                refine ⟨3501941106511764379835371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669254808682352506447161 3501941106511764379835371)
                ·
                  refine ⟨5252911659767646569753057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501941106511764379835371 5252911659767646569753057)
                  ·
                    refine ⟨3939683744825734927314793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252911659767646569753057 3939683744825734927314793)
                    ·
                      refine ⟨2954762808619301195486095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939683744825734927314793 2954762808619301195486095)
                      ·
                        rfl

theorem cell23_5754380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_5754380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754380 prefixEnd_5754380 := by exact prefixLift 5754380
  have htrace : WordTrace (prefixWord ++ tailWord_5754380) baseStart_5754380 baseEnd_5754380 := by
    simpa [prefixWord, tailWord_5754380, baseEnd_5754380] using wordTrace_append hprefix tailTrace_5754380
  have hstable : (prefixWord ++ tailWord_5754380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754380).length < 2 ^ (prefixWord ++ tailWord_5754380).sum := by decide
  have hdescent : baseEnd_5754380 < baseStart_5754380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754385 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_5754385 : Nat := 118140960795 + 5754385 * 2 ^ 59
def prefixEnd_5754385 : Nat := 4983230072969 + 3 ^ 40 * 5754385 * 2
def baseEnd_5754385 : Nat := 2954765376022573675923571

theorem tailTrace_5754385 : CollatzResearch.WordTrace tailWord_5754385 prefixEnd_5754385 2954765376022573675923571 := by
  unfold tailWord_5754385
  simp only [CollatzResearch.WordTrace]
  refine ⟨209879663257853390560736609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139919775505235593707157739 209879663257853390560736609)
  ·
    refine ⟨157409747443390042920552457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209879663257853390560736609 157409747443390042920552457)
    ·
      refine ⟨118057310582542532190414343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157409747443390042920552457 118057310582542532190414343)
      ·
        refine ⟨177085965873813798285621515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118057310582542532190414343 177085965873813798285621515)
        ·
          refine ⟨265628948810720697428432273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177085965873813798285621515 265628948810720697428432273)
          ·
            refine ⟨199221711608040523071324205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265628948810720697428432273 199221711608040523071324205)
            ·
              refine ⟨74708141853015196151746577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199221711608040523071324205 74708141853015196151746577)
              ·
                refine ⟨56031106389761397113809933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74708141853015196151746577 56031106389761397113809933)
                ·
                  refine ⟨21011664896160523917678725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56031106389761397113809933 21011664896160523917678725)
                  ·
                    refine ⟨3939687168030098234564761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21011664896160523917678725 3939687168030098234564761)
                    ·
                      refine ⟨2954765376022573675923571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939687168030098234564761 2954765376022573675923571)
                      ·
                        rfl

theorem cell23_5754385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_5754385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754385 prefixEnd_5754385 := by exact prefixLift 5754385
  have htrace : WordTrace (prefixWord ++ tailWord_5754385) baseStart_5754385 baseEnd_5754385 := by
    simpa [prefixWord, tailWord_5754385, baseEnd_5754385] using wordTrace_append hprefix tailTrace_5754385
  have hstable : (prefixWord ++ tailWord_5754385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754385).length < 2 ^ (prefixWord ++ tailWord_5754385).sum := by decide
  have hdescent : baseEnd_5754385 < baseStart_5754385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754402 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_5754402 : Nat := 118140960795 + 5754402 * 2 ^ 59
def prefixEnd_5754402 : Nat := 4983230072969 + 3 ^ 40 * 5754402 * 2
def baseEnd_5754402 : Nat := 2954774105193700109410993

theorem tailTrace_5754402 : CollatzResearch.WordTrace tailWord_5754402 prefixEnd_5754402 2954774105193700109410993 := by
  unfold tailWord_5754402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52470070824697950616026365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139920188865861201642736973 52470070824697950616026365)
  ·
    refine ⟨19676276559261731481009887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52470070824697950616026365 19676276559261731481009887)
    ·
      refine ⟨29514414838892597221514831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19676276559261731481009887 29514414838892597221514831)
      ·
        refine ⟨44271622258338895832272247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29514414838892597221514831 44271622258338895832272247)
        ·
          refine ⟨66407433387508343748408371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44271622258338895832272247 66407433387508343748408371)
          ·
            refine ⟨99611150081262515622612557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66407433387508343748408371 99611150081262515622612557)
            ·
              refine ⟨37354181280473443358479709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99611150081262515622612557 37354181280473443358479709)
              ·
                refine ⟨14007817980177541259429891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37354181280473443358479709 14007817980177541259429891)
                ·
                  refine ⟨21011726970266311889144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14007817980177541259429891 21011726970266311889144837)
                  ·
                    refine ⟨3939698806924933479214657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21011726970266311889144837 3939698806924933479214657)
                    ·
                      refine ⟨2954774105193700109410993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939698806924933479214657 2954774105193700109410993)
                      ·
                        rfl

theorem cell23_5754402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_5754402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754402 prefixEnd_5754402 := by exact prefixLift 5754402
  have htrace : WordTrace (prefixWord ++ tailWord_5754402) baseStart_5754402 baseEnd_5754402 := by
    simpa [prefixWord, tailWord_5754402, baseEnd_5754402] using wordTrace_append hprefix tailTrace_5754402
  have hstable : (prefixWord ++ tailWord_5754402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754402).length < 2 ^ (prefixWord ++ tailWord_5754402).sum := by decide
  have hdescent : baseEnd_5754402 < baseStart_5754402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754418 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5754418 : Nat := 118140960795 + 5754418 * 2 ^ 59
def prefixEnd_5754418 : Nat := 4983230072969 + 3 ^ 40 * 5754418 * 2
def baseEnd_5754418 : Nat := 2954782320884172046810919

theorem tailTrace_5754418 : CollatzResearch.WordTrace tailWord_5754418 prefixEnd_5754418 2954782320884172046810919 := by
  unfold tailWord_5754418
  simp only [CollatzResearch.WordTrace]
  refine ⟨52470216716683459299171977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139920577911155891464458605 52470216716683459299171977)
  ·
    refine ⟨39352662537512594474378983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52470216716683459299171977 39352662537512594474378983)
    ·
      refine ⟨59028993806268891711568475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39352662537512594474378983 59028993806268891711568475)
      ·
        refine ⟨88543490709403337567352713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59028993806268891711568475 88543490709403337567352713)
        ·
          refine ⟨66407618032052503175514535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88543490709403337567352713 66407618032052503175514535)
          ·
            refine ⟨99611427048078754763271803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66407618032052503175514535 99611427048078754763271803)
            ·
              refine ⟨149417140572118132144907705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99611427048078754763271803 149417140572118132144907705)
              ·
                refine ⟨112062855429088599108680779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149417140572118132144907705 112062855429088599108680779)
                ·
                  refine ⟨168094283143632898663021169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112062855429088599108680779 168094283143632898663021169)
                  ·
                    refine ⟨126070712357724673997265877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168094283143632898663021169 126070712357724673997265877)
                    ·
                      refine ⟨2954782320884172046810919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126070712357724673997265877 2954782320884172046810919)
                      ·
                        rfl

theorem cell23_5754418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5754418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754418 prefixEnd_5754418 := by exact prefixLift 5754418
  have htrace : WordTrace (prefixWord ++ tailWord_5754418) baseStart_5754418 baseEnd_5754418 := by
    simpa [prefixWord, tailWord_5754418, baseEnd_5754418] using wordTrace_append hprefix tailTrace_5754418
  have hstable : (prefixWord ++ tailWord_5754418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754418).length < 2 ^ (prefixWord ++ tailWord_5754418).sum := by decide
  have hdescent : baseEnd_5754418 < baseStart_5754418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754448 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_5754448 : Nat := 118140960795 + 5754448 * 2 ^ 59
def prefixEnd_5754448 : Nat := 4983230072969 + 3 ^ 40 * 5754448 * 2
def baseEnd_5754448 : Nat := 2954797725303806929435781

theorem tailTrace_5754448 : CollatzResearch.WordTrace tailWord_5754448 prefixEnd_5754448 2954797725303806929435781 := by
  unfold tailWord_5754448
  simp only [CollatzResearch.WordTrace]
  refine ⟨104940980528312576160139999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139921307371083434880186665 104940980528312576160139999)
  ·
    refine ⟨157411470792468864240209999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104940980528312576160139999 157411470792468864240209999)
    ·
      refine ⟨236117206188703296360314999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157411470792468864240209999 236117206188703296360314999)
      ·
        refine ⟨354175809283054944540472499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236117206188703296360314999 354175809283054944540472499)
        ·
          refine ⟨531263713924582416810708749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354175809283054944540472499 531263713924582416810708749)
          ·
            refine ⟨199223892721718406304015781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531263713924582416810708749 199223892721718406304015781)
            ·
              refine ⟨37354479885322201182002959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199223892721718406304015781 37354479885322201182002959)
              ·
                refine ⟨56031719827983301773004439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37354479885322201182002959 56031719827983301773004439)
                ·
                  refine ⟨84047579741974952659506659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56031719827983301773004439 84047579741974952659506659)
                  ·
                    refine ⟨126071369612962428989259989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84047579741974952659506659 126071369612962428989259989)
                    ·
                      refine ⟨2954797725303806929435781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126071369612962428989259989 2954797725303806929435781)
                      ·
                        rfl

theorem cell23_5754448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_5754448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754448 prefixEnd_5754448 := by exact prefixLift 5754448
  have htrace : WordTrace (prefixWord ++ tailWord_5754448) baseStart_5754448 baseEnd_5754448 := by
    simpa [prefixWord, tailWord_5754448, baseEnd_5754448] using wordTrace_append hprefix tailTrace_5754448
  have hstable : (prefixWord ++ tailWord_5754448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754448).length < 2 ^ (prefixWord ++ tailWord_5754448).sum := by decide
  have hdescent : baseEnd_5754448 < baseStart_5754448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754529 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5754529 : Nat := 118140960795 + 5754529 * 2 ^ 59
def prefixEnd_5754529 : Nat := 4983230072969 + 3 ^ 40 * 5754529 * 2
def baseEnd_5754529 : Nat := 2954839317236821112522909

theorem tailTrace_5754529 : CollatzResearch.WordTrace tailWord_5754529 prefixEnd_5754529 2954839317236821112522909 := by
  unfold tailWord_5754529
  simp only [CollatzResearch.WordTrace]
  refine ⟨209884915369331703153978641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139923276912887802102652427 209884915369331703153978641)
  ·
    refine ⟨157413686526998777365483981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209884915369331703153978641 157413686526998777365483981)
    ·
      refine ⟨59030132447624541512056493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157413686526998777365483981 59030132447624541512056493)
      ·
        refine ⟨22136299667859203067021185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59030132447624541512056493 22136299667859203067021185)
        ·
          refine ⟨16602224750894402300265889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22136299667859203067021185 16602224750894402300265889)
          ·
            refine ⟨12451668563170801725199417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16602224750894402300265889 12451668563170801725199417)
            ·
              refine ⟨9338751422378101293899563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451668563170801725199417 9338751422378101293899563)
              ·
                refine ⟨14008127133567151940849345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338751422378101293899563 14008127133567151940849345)
                ·
                  refine ⟨10506095350175363955637009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14008127133567151940849345 10506095350175363955637009)
                  ·
                    refine ⟨7879571512631522966727757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10506095350175363955637009 7879571512631522966727757)
                    ·
                      refine ⟨2954839317236821112522909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879571512631522966727757 2954839317236821112522909)
                      ·
                        rfl

theorem cell23_5754529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5754529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754529 prefixEnd_5754529 := by exact prefixLift 5754529
  have htrace : WordTrace (prefixWord ++ tailWord_5754529) baseStart_5754529 baseEnd_5754529 := by
    simpa [prefixWord, tailWord_5754529, baseEnd_5754529] using wordTrace_append hprefix tailTrace_5754529
  have hstable : (prefixWord ++ tailWord_5754529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754529).length < 2 ^ (prefixWord ++ tailWord_5754529).sum := by decide
  have hdescent : baseEnd_5754529 < baseStart_5754529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754549 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 6]
def baseStart_5754549 : Nat := 118140960795 + 5754549 * 2 ^ 59
def prefixEnd_5754549 : Nat := 4983230072969 + 3 ^ 40 * 5754549 * 2
def baseEnd_5754549 : Nat := 328316620761101226030313

theorem tailTrace_5754549 : CollatzResearch.WordTrace tailWord_5754549 prefixEnd_5754549 328316620761101226030313 := by
  unfold tailWord_5754549
  simp only [CollatzResearch.WordTrace]
  refine ⟨209885644829259246569706701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139923763219506164379804467 209885644829259246569706701)
  ·
    refine ⟨78707116810972217463640013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209885644829259246569706701 78707116810972217463640013)
    ·
      refine ⟨29515168804114581548865005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78707116810972217463640013 29515168804114581548865005)
      ·
        refine ⟨11068188301542968080824377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29515168804114581548865005 11068188301542968080824377)
        ·
          refine ⟨8301141226157226060618283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11068188301542968080824377 8301141226157226060618283)
          ·
            refine ⟨12451711839235839090927425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301141226157226060618283 12451711839235839090927425)
            ·
              refine ⟨9338783879426879318195569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451711839235839090927425 9338783879426879318195569)
              ·
                refine ⟨7004087909570159488646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9338783879426879318195569 7004087909570159488646677)
                ·
                  refine ⟨328316620761101226030313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7004087909570159488646677 328316620761101226030313)
                  ·
                    rfl

theorem cell23_5754549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_5754549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754549 prefixEnd_5754549 := by exact prefixLift 5754549
  have htrace : WordTrace (prefixWord ++ tailWord_5754549) baseStart_5754549 baseEnd_5754549 := by
    simpa [prefixWord, tailWord_5754549, baseEnd_5754549] using wordTrace_append hprefix tailTrace_5754549
  have hstable : (prefixWord ++ tailWord_5754549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754549).length < 2 ^ (prefixWord ++ tailWord_5754549).sum := by decide
  have hdescent : baseEnd_5754549 < baseStart_5754549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754566 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5754566 : Nat := 118140960795 + 5754566 * 2 ^ 59
def prefixEnd_5754566 : Nat := 4983230072969 + 3 ^ 40 * 5754566 * 2
def baseEnd_5754566 : Nat := 328317590669004163084471

theorem tailTrace_5754566 : CollatzResearch.WordTrace tailWord_5754566 prefixEnd_5754566 328317590669004163084471 := by
  unfold tailWord_5754566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558945777193676827283611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139924176580131772315383701 6558945777193676827283611)
  ·
    refine ⟨9838418665790515240925417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6558945777193676827283611 9838418665790515240925417)
    ·
      refine ⟨7378813999342886430694063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9838418665790515240925417 7378813999342886430694063)
      ·
        refine ⟨11068220999014329646041095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378813999342886430694063 11068220999014329646041095)
        ·
          refine ⟨16602331498521494469061643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068220999014329646041095 16602331498521494469061643)
          ·
            refine ⟨24903497247782241703592465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16602331498521494469061643 24903497247782241703592465)
            ·
              refine ⟨18677622935836681277694349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24903497247782241703592465 18677622935836681277694349)
              ·
                refine ⟨7004108600938755479135381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18677622935836681277694349 7004108600938755479135381)
                ·
                  refine ⟨328317590669004163084471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7004108600938755479135381 328317590669004163084471)
                  ·
                    rfl

theorem cell23_5754566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5754566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754566 prefixEnd_5754566 := by exact prefixLift 5754566
  have htrace : WordTrace (prefixWord ++ tailWord_5754566) baseStart_5754566 baseEnd_5754566 := by
    simpa [prefixWord, tailWord_5754566, baseEnd_5754566] using wordTrace_append hprefix tailTrace_5754566
  have hstable : (prefixWord ++ tailWord_5754566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754566).length < 2 ^ (prefixWord ++ tailWord_5754566).sum := by decide
  have hdescent : baseEnd_5754566 < baseStart_5754566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754586 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_5754586 : Nat := 118140960795 + 5754586 * 2 ^ 59
def prefixEnd_5754586 : Nat := 4983230072969 + 3 ^ 40 * 5754586 * 2
def baseEnd_5754586 : Nat := 2954868585634127389510147

theorem tailTrace_5754586 : CollatzResearch.WordTrace tailWord_5754586 prefixEnd_5754586 2954868585634127389510147 := by
  unfold tailWord_5754586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52471748582531300472200903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139924662886750134592535741 52471748582531300472200903)
  ·
    refine ⟨78707622873796950708301355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52471748582531300472200903 78707622873796950708301355)
    ·
      refine ⟨118061434310695426062452033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78707622873796950708301355 118061434310695426062452033)
      ·
        refine ⟨88546075733021569546839025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118061434310695426062452033 88546075733021569546839025)
        ·
          refine ⟨66409556799766177160129269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88546075733021569546839025 66409556799766177160129269)
          ·
            refine ⟨6225895949978079108762119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66409556799766177160129269 6225895949978079108762119)
            ·
              refine ⟨9338843924967118663143179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225895949978079108762119 9338843924967118663143179)
              ·
                refine ⟨14008265887450677994714769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338843924967118663143179 14008265887450677994714769)
                ·
                  refine ⟨10506199415588008496036077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14008265887450677994714769 10506199415588008496036077)
                  ·
                    refine ⟨3939824780845503186013529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10506199415588008496036077 3939824780845503186013529)
                    ·
                      refine ⟨2954868585634127389510147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939824780845503186013529 2954868585634127389510147)
                      ·
                        rfl

theorem cell23_5754586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_5754586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754586 prefixEnd_5754586 := by exact prefixLift 5754586
  have htrace : WordTrace (prefixWord ++ tailWord_5754586) baseStart_5754586 baseEnd_5754586 := by
    simpa [prefixWord, tailWord_5754586, baseEnd_5754586] using wordTrace_append hprefix tailTrace_5754586
  have hstable : (prefixWord ++ tailWord_5754586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754586).length < 2 ^ (prefixWord ++ tailWord_5754586).sum := by decide
  have hdescent : baseEnd_5754586 < baseStart_5754586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754593 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_5754593 : Nat := 118140960795 + 5754593 * 2 ^ 59
def prefixEnd_5754593 : Nat := 4983230072969 + 3 ^ 40 * 5754593 * 2
def baseEnd_5754593 : Nat := 2954872179998708862122615

theorem tailTrace_5754593 : CollatzResearch.WordTrace tailWord_5754593 prefixEnd_5754593 2954872179998708862122615 := by
  unfold tailWord_5754593
  simp only [CollatzResearch.WordTrace]
  refine ⟨209887249641099842084308433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139924833094066561389538955 209887249641099842084308433)
  ·
    refine ⟨157415437230824881563231325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209887249641099842084308433 157415437230824881563231325)
    ·
      refine ⟨59030788961559330586211747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157415437230824881563231325 59030788961559330586211747)
      ·
        refine ⟨88546183442338995879317621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59030788961559330586211747 88546183442338995879317621)
        ·
          refine ⟨8301204697719280863686027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88546183442338995879317621 8301204697719280863686027)
          ·
            refine ⟨12451807046578921295529041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301204697719280863686027 12451807046578921295529041)
            ·
              refine ⟨9338855284934190971646781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451807046578921295529041 9338855284934190971646781)
              ·
                refine ⟨3502070731850321614367543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338855284934190971646781 3502070731850321614367543)
                ·
                  refine ⟨5253106097775482421551315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502070731850321614367543 5253106097775482421551315)
                  ·
                    refine ⟨7879659146663223632326973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253106097775482421551315 7879659146663223632326973)
                    ·
                      refine ⟨2954872179998708862122615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879659146663223632326973 2954872179998708862122615)
                      ·
                        rfl

theorem cell23_5754593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_5754593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754593 prefixEnd_5754593 := by exact prefixLift 5754593
  have htrace : WordTrace (prefixWord ++ tailWord_5754593) baseStart_5754593 baseEnd_5754593 := by
    simpa [prefixWord, tailWord_5754593, baseEnd_5754593] using wordTrace_append hprefix tailTrace_5754593
  have hstable : (prefixWord ++ tailWord_5754593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754593).length < 2 ^ (prefixWord ++ tailWord_5754593).sum := by decide
  have hdescent : baseEnd_5754593 < baseStart_5754593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754609 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_5754609 : Nat := 118140960795 + 5754609 * 2 ^ 59
def prefixEnd_5754609 : Nat := 4983230072969 + 3 ^ 40 * 5754609 * 2
def baseEnd_5754609 : Nat := 984960131896393599840847

theorem tailTrace_5754609 : CollatzResearch.WordTrace tailWord_5754609 prefixEnd_5754609 984960131896393599840847 := by
  unfold tailWord_5754609
  simp only [CollatzResearch.WordTrace]
  refine ⟨209887833209041876816890881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139925222139361251211260587 209887833209041876816890881)
  ·
    refine ⟨157415874906781407612668161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209887833209041876816890881 157415874906781407612668161)
    ·
      refine ⟨118061906180086055709501121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157415874906781407612668161 118061906180086055709501121)
      ·
        refine ⟨88546429635064541782125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118061906180086055709501121 88546429635064541782125841)
        ·
          refine ⟨66409822226298406336594381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88546429635064541782125841 66409822226298406336594381)
          ·
            refine ⟨24903683334861902376222893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66409822226298406336594381 24903683334861902376222893)
            ·
              refine ⟨9338881250573213391083585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24903683334861902376222893 9338881250573213391083585)
              ·
                refine ⟨7004160937929910043312689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9338881250573213391083585 7004160937929910043312689)
                ·
                  refine ⟨5253120703447432532484517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7004160937929910043312689 5253120703447432532484517)
                  ·
                    refine ⟨984960131896393599840847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253120703447432532484517 984960131896393599840847)
                    ·
                      rfl

theorem cell23_5754609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_5754609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754609 prefixEnd_5754609 := by exact prefixLift 5754609
  have htrace : WordTrace (prefixWord ++ tailWord_5754609) baseStart_5754609 baseEnd_5754609 := by
    simpa [prefixWord, tailWord_5754609, baseEnd_5754609] using wordTrace_append hprefix tailTrace_5754609
  have hstable : (prefixWord ++ tailWord_5754609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754609).length < 2 ^ (prefixWord ++ tailWord_5754609).sum := by decide
  have hdescent : baseEnd_5754609 < baseStart_5754609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754635 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 7]
def baseStart_5754635 : Nat := 118140960795 + 5754635 * 2 ^ 59
def prefixEnd_5754635 : Nat := 4983230072969 + 3 ^ 40 * 5754635 * 2
def baseEnd_5754635 : Nat := 984964582062065899265807

theorem tailTrace_5754635 : CollatzResearch.WordTrace tailWord_5754635 prefixEnd_5754635 984964582062065899265807 := by
  unfold tailWord_5754635
  simp only [CollatzResearch.WordTrace]
  refine ⟨209888781506947683257337359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139925854337965122171558239 209888781506947683257337359)
  ·
    refine ⟨314833172260421524886006039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209888781506947683257337359 314833172260421524886006039)
    ·
      refine ⟨472249758390632287329009059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314833172260421524886006039 472249758390632287329009059)
      ·
        refine ⟨708374637585948430993513589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472249758390632287329009059 708374637585948430993513589)
        ·
          refine ⟨66410122273682665405641899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 708374637585948430993513589 66410122273682665405641899)
          ·
            refine ⟨99615183410523998108462849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66410122273682665405641899 99615183410523998108462849)
            ·
              refine ⟨74711387557892998581347137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99615183410523998108462849 74711387557892998581347137)
              ·
                refine ⟨56033540668419748936010353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74711387557892998581347137 56033540668419748936010353)
                ·
                  refine ⟨42025155501314811702007765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56033540668419748936010353 42025155501314811702007765)
                  ·
                    refine ⟨984964582062065899265807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42025155501314811702007765 984964582062065899265807)
                    ·
                      rfl

theorem cell23_5754635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_5754635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754635 prefixEnd_5754635 := by exact prefixLift 5754635
  have htrace : WordTrace (prefixWord ++ tailWord_5754635) baseStart_5754635 baseEnd_5754635 := by
    simpa [prefixWord, tailWord_5754635, baseEnd_5754635] using wordTrace_append hprefix tailTrace_5754635
  have hstable : (prefixWord ++ tailWord_5754635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754635).length < 2 ^ (prefixWord ++ tailWord_5754635).sum := by decide
  have hdescent : baseEnd_5754635 < baseStart_5754635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754644 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5754644 : Nat := 118140960795 + 5754644 * 2 ^ 59
def prefixEnd_5754644 : Nat := 4983230072969 + 3 ^ 40 * 5754644 * 2
def baseEnd_5754644 : Nat := 2954898367512088162584881

theorem tailTrace_5754644 : CollatzResearch.WordTrace tailWord_5754644 prefixEnd_5754644 2954898367512088162584881 := by
  unfold tailWord_5754644
  simp only [CollatzResearch.WordTrace]
  refine ⟨104944554881957538897207493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139926073175943385196276657 104944554881957538897207493)
  ·
    refine ⟨19677104040367038543226405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104944554881957538897207493 19677104040367038543226405)
    ·
      refine ⟨3689457007568819726854951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19677104040367038543226405 3689457007568819726854951)
      ·
        refine ⟨5534185511353229590282427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689457007568819726854951 5534185511353229590282427)
        ·
          refine ⟨8301278267029844385423641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534185511353229590282427 8301278267029844385423641)
          ·
            refine ⟨6225958700272383289067731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8301278267029844385423641 6225958700272383289067731)
            ·
              refine ⟨9338938050408574933601597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225958700272383289067731 9338938050408574933601597)
              ·
                refine ⟨3502101768903215600100599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338938050408574933601597 3502101768903215600100599)
                ·
                  refine ⟨5253152653354823400150899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502101768903215600100599 5253152653354823400150899)
                  ·
                    refine ⟨7879728980032235100226349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253152653354823400150899 7879728980032235100226349)
                    ·
                      refine ⟨2954898367512088162584881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7879728980032235100226349 2954898367512088162584881)
                      ·
                        rfl

theorem cell23_5754644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5754644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754644 prefixEnd_5754644 := by exact prefixLift 5754644
  have htrace : WordTrace (prefixWord ++ tailWord_5754644) baseStart_5754644 baseEnd_5754644 := by
    simpa [prefixWord, tailWord_5754644, baseEnd_5754644] using wordTrace_append hprefix tailTrace_5754644
  have hstable : (prefixWord ++ tailWord_5754644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754644).length < 2 ^ (prefixWord ++ tailWord_5754644).sum := by decide
  have hdescent : baseEnd_5754644 < baseStart_5754644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754650 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_5754650 : Nat := 118140960795 + 5754650 * 2 ^ 59
def prefixEnd_5754650 : Nat := 4983230072969 + 3 ^ 40 * 5754650 * 2
def baseEnd_5754650 : Nat := 2954901448396015139109853

theorem tailTrace_5754650 : CollatzResearch.WordTrace tailWord_5754650 prefixEnd_5754650 2954901448396015139109853 := by
  unfold tailWord_5754650
  simp only [CollatzResearch.WordTrace]
  refine ⟨52472332150473335204783351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139926219067928893879422269 52472332150473335204783351)
  ·
    refine ⟨78708498225710002807175027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52472332150473335204783351 78708498225710002807175027)
    ·
      refine ⟨118062747338565004210762541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78708498225710002807175027 118062747338565004210762541)
      ·
        refine ⟨44273530251961876579035953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118062747338565004210762541 44273530251961876579035953)
        ·
          refine ⟨33205147688971407434276965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44273530251961876579035953 33205147688971407434276965)
          ·
            refine ⟨6225965191682138893926931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33205147688971407434276965 6225965191682138893926931)
            ·
              refine ⟨9338947787523208340890397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225965191682138893926931 9338947787523208340890397)
              ·
                refine ⟨3502105420321203127833899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338947787523208340890397 3502105420321203127833899)
                ·
                  refine ⟨5253158130481804691750849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502105420321203127833899 5253158130481804691750849)
                  ·
                    refine ⟨3939868597861353518813137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5253158130481804691750849 3939868597861353518813137)
                    ·
                      refine ⟨2954901448396015139109853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939868597861353518813137 2954901448396015139109853)
                      ·
                        rfl

theorem cell23_5754650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_5754650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754650 prefixEnd_5754650 := by exact prefixLift 5754650
  have htrace : WordTrace (prefixWord ++ tailWord_5754650) baseStart_5754650 baseEnd_5754650 := by
    simpa [prefixWord, tailWord_5754650, baseEnd_5754650] using wordTrace_append hprefix tailTrace_5754650
  have hstable : (prefixWord ++ tailWord_5754650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754650).length < 2 ^ (prefixWord ++ tailWord_5754650).sum := by decide
  have hdescent : baseEnd_5754650 < baseStart_5754650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754702 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5754702 : Nat := 118140960795 + 5754702 * 2 ^ 59
def prefixEnd_5754702 : Nat := 4983230072969 + 3 ^ 40 * 5754702 * 2
def baseEnd_5754702 : Nat := 2954928149390048935659613

theorem tailTrace_5754702 : CollatzResearch.WordTrace tailWord_5754702 prefixEnd_5754702 2954928149390048935659613 := by
  unfold tailWord_5754702
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236403149713119212503295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139927483465136635800017573 26236403149713119212503295)
  ·
    refine ⟨39354604724569678818754943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236403149713119212503295 39354604724569678818754943)
    ·
      refine ⟨59031907086854518228132415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39354604724569678818754943 59031907086854518228132415)
      ·
        refine ⟨88547860630281777342198623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59031907086854518228132415 88547860630281777342198623)
        ·
          refine ⟨132821790945422666013297935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88547860630281777342198623 132821790945422666013297935)
          ·
            refine ⟨199232686418133999019946903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132821790945422666013297935 199232686418133999019946903)
            ·
              refine ⟨298849029627200998529920355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199232686418133999019946903 298849029627200998529920355)
              ·
                refine ⟨448273544440801497794880533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298849029627200998529920355 448273544440801497794880533)
                ·
                  refine ⟨21012822395662570209135025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 448273544440801497794880533 21012822395662570209135025)
                  ·
                    refine ⟨15759616796746927656851269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21012822395662570209135025 15759616796746927656851269)
                    ·
                      refine ⟨2954928149390048935659613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15759616796746927656851269 2954928149390048935659613)
                      ·
                        rfl

theorem cell23_5754702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5754702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754702 prefixEnd_5754702 := by exact prefixLift 5754702
  have htrace : WordTrace (prefixWord ++ tailWord_5754702) baseStart_5754702 baseEnd_5754702 := by
    simpa [prefixWord, tailWord_5754702, baseEnd_5754702] using wordTrace_append hprefix tailTrace_5754702
  have hstable : (prefixWord ++ tailWord_5754702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754702).length < 2 ^ (prefixWord ++ tailWord_5754702).sum := by decide
  have hdescent : baseEnd_5754702 < baseStart_5754702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754706 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_5754706 : Nat := 118140960795 + 5754706 * 2 ^ 59
def prefixEnd_5754706 : Nat := 4983230072969 + 3 ^ 40 * 5754706 * 2
def baseEnd_5754706 : Nat := 2954930203312666920009595

theorem tailTrace_5754706 : CollatzResearch.WordTrace tailWord_5754706 prefixEnd_5754706 2954930203312666920009595 := by
  unfold tailWord_5754706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52472842772422615595792993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139927580726460308255447981 52472842772422615595792993)
  ·
    refine ⟨39354632079316961696844745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52472842772422615595792993 39354632079316961696844745)
    ·
      refine ⟨29515974059487721272633559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39354632079316961696844745 29515974059487721272633559)
      ·
        refine ⟨44273961089231581908950339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29515974059487721272633559 44273961089231581908950339)
        ·
          refine ⟨66410941633847372863425509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44273961089231581908950339 66410941633847372863425509)
          ·
            refine ⟨12452051556346382411892283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66410941633847372863425509 12452051556346382411892283)
            ·
              refine ⟨18678077334519573617838425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12452051556346382411892283 18678077334519573617838425)
              ·
                refine ⟨14008558000889680213378819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18678077334519573617838425 14008558000889680213378819)
                ·
                  refine ⟨21012837001334520320068229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14008558000889680213378819 21012837001334520320068229)
                  ·
                    refine ⟨3939906937750222560012793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21012837001334520320068229 3939906937750222560012793)
                    ·
                      refine ⟨2954930203312666920009595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939906937750222560012793 2954930203312666920009595)
                      ·
                        rfl

theorem cell23_5754706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_5754706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754706 prefixEnd_5754706 := by exact prefixLift 5754706
  have htrace : WordTrace (prefixWord ++ tailWord_5754706) baseStart_5754706 baseEnd_5754706 := by
    simpa [prefixWord, tailWord_5754706, baseEnd_5754706] using wordTrace_append hprefix tailTrace_5754706
  have hstable : (prefixWord ++ tailWord_5754706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754706).length < 2 ^ (prefixWord ++ tailWord_5754706).sum := by decide
  have hdescent : baseEnd_5754706 < baseStart_5754706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754749 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_5754749 : Nat := 118140960795 + 5754749 * 2 ^ 59
def prefixEnd_5754749 : Nat := 4983230072969 + 3 ^ 40 * 5754749 * 2
def baseEnd_5754749 : Nat := 2954952282980810251771897

theorem tailTrace_5754749 : CollatzResearch.WordTrace tailWord_5754749 prefixEnd_5754749 2954952282980810251771897 := by
  unfold tailWord_5754749
  simp only [CollatzResearch.WordTrace]
  refine ⟨209892939428534680726987301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139928626285689787151324867 209892939428534680726987301)
  ·
    refine ⟨39354926142850252636310119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209892939428534680726987301 39354926142850252636310119)
    ·
      refine ⟨59032389214275378954465179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39354926142850252636310119 59032389214275378954465179)
      ·
        refine ⟨88548583821413068431697769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59032389214275378954465179 88548583821413068431697769)
        ·
          refine ⟨66411437866059801323773327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88548583821413068431697769 66411437866059801323773327)
          ·
            refine ⟨99617156799089701985659991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66411437866059801323773327 99617156799089701985659991)
            ·
              refine ⟨149425735198634552978489987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99617156799089701985659991 149425735198634552978489987)
              ·
                refine ⟨224138602797951829467734981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149425735198634552978489987 224138602797951829467734981)
                ·
                  refine ⟨42025988024615968025200309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224138602797951829467734981 42025988024615968025200309)
                  ·
                    refine ⟨3939936377307747002362529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42025988024615968025200309 3939936377307747002362529)
                    ·
                      refine ⟨2954952282980810251771897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939936377307747002362529 2954952282980810251771897)
                      ·
                        rfl

theorem cell23_5754749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_5754749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754749 prefixEnd_5754749 := by exact prefixLift 5754749
  have htrace : WordTrace (prefixWord ++ tailWord_5754749) baseStart_5754749 baseEnd_5754749 := by
    simpa [prefixWord, tailWord_5754749, baseEnd_5754749] using wordTrace_append hprefix tailTrace_5754749
  have hstable : (prefixWord ++ tailWord_5754749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754749).length < 2 ^ (prefixWord ++ tailWord_5754749).sum := by decide
  have hdescent : baseEnd_5754749 < baseStart_5754749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754759 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 7]
def baseStart_5754759 : Nat := 118140960795 + 5754759 * 2 ^ 59
def prefixEnd_5754759 : Nat := 4983230072969 + 3 ^ 40 * 5754759 * 2
def baseEnd_5754759 : Nat := 984985805929118404215617

theorem tailTrace_5754759 : CollatzResearch.WordTrace tailWord_5754759 prefixEnd_5754759 984985805929118404215617 := by
  unfold tailWord_5754759
  simp only [CollatzResearch.WordTrace]
  refine ⟨209893304158498452434851331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139928869438998968289900887 209893304158498452434851331)
  ·
    refine ⟨314839956237747678652276997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209893304158498452434851331 314839956237747678652276997)
    ·
      refine ⟨59032491794577689747301937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314839956237747678652276997 59032491794577689747301937)
      ·
        refine ⟨44274368845933267310476453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59032491794577689747301937 44274368845933267310476453)
        ·
          refine ⟨8301444158612487620714335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44274368845933267310476453 8301444158612487620714335)
          ·
            refine ⟨12452166237918731431071503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301444158612487620714335 12452166237918731431071503)
            ·
              refine ⟨18678249356878097146607255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12452166237918731431071503 18678249356878097146607255)
              ·
                refine ⟨28017374035317145719910883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18678249356878097146607255 28017374035317145719910883)
                ·
                  refine ⟨42026061052975718579866325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28017374035317145719910883 42026061052975718579866325)
                  ·
                    refine ⟨984985805929118404215617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42026061052975718579866325 984985805929118404215617)
                    ·
                      rfl

theorem cell23_5754759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_5754759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754759 prefixEnd_5754759 := by exact prefixLift 5754759
  have htrace : WordTrace (prefixWord ++ tailWord_5754759) baseStart_5754759 baseEnd_5754759 := by
    simpa [prefixWord, tailWord_5754759, baseEnd_5754759] using wordTrace_append hprefix tailTrace_5754759
  have hstable : (prefixWord ++ tailWord_5754759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754759).length < 2 ^ (prefixWord ++ tailWord_5754759).sum := by decide
  have hdescent : baseEnd_5754759 < baseStart_5754759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754856 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5754856 : Nat := 118140960795 + 5754856 * 2 ^ 59
def prefixEnd_5754856 : Nat := 4983230072969 + 3 ^ 40 * 5754856 * 2
def baseEnd_5754856 : Nat := 2955007225410841333133905

theorem tailTrace_5754856 : CollatzResearch.WordTrace tailWord_5754856 prefixEnd_5754856 2955007225410841333133905 := by
  unfold tailWord_5754856
  simp only [CollatzResearch.WordTrace]
  refine ⟨104948421019573519000566211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139931228026098025334088281 104948421019573519000566211)
  ·
    refine ⟨157422631529360278500849317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104948421019573519000566211 157422631529360278500849317)
    ·
      refine ⟨29516743411755052218909247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157422631529360278500849317 29516743411755052218909247)
      ·
        refine ⟨44275115117632578328363871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29516743411755052218909247 44275115117632578328363871)
        ·
          refine ⟨66412672676448867492545807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44275115117632578328363871 66412672676448867492545807)
          ·
            refine ⟨99619009014673301238818711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66412672676448867492545807 99619009014673301238818711)
            ·
              refine ⟨149428513522009951858228067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99619009014673301238818711 149428513522009951858228067)
              ·
                refine ⟨224142770283014927787342101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149428513522009951858228067 224142770283014927787342101)
                ·
                  refine ⟨10506692357016324740031661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224142770283014927787342101 10506692357016324740031661)
                  ·
                    refine ⟨3940009633881121777511873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10506692357016324740031661 3940009633881121777511873)
                    ·
                      refine ⟨2955007225410841333133905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940009633881121777511873 2955007225410841333133905)
                      ·
                        rfl

theorem cell23_5754856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5754856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754856 prefixEnd_5754856 := by exact prefixLift 5754856
  have htrace : WordTrace (prefixWord ++ tailWord_5754856) baseStart_5754856 baseEnd_5754856 := by
    simpa [prefixWord, tailWord_5754856, baseEnd_5754856] using wordTrace_append hprefix tailTrace_5754856
  have hstable : (prefixWord ++ tailWord_5754856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754856).length < 2 ^ (prefixWord ++ tailWord_5754856).sum := by decide
  have hdescent : baseEnd_5754856 < baseStart_5754856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754873 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 2, 3, 2]
def baseStart_5754873 : Nat := 118140960795 + 5754873 * 2 ^ 59
def prefixEnd_5754873 : Nat := 4983230072969 + 3 ^ 40 * 5754873 * 2
def baseEnd_5754873 : Nat := 2955015954581967766621327

theorem tailTrace_5754873 : CollatzResearch.WordTrace tailWord_5754873 prefixEnd_5754873 2955015954581967766621327 := by
  unfold tailWord_5754873
  simp only [CollatzResearch.WordTrace]
  refine ⟨209897462080085449904501273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139931641386723633269667515 209897462080085449904501273)
  ·
    refine ⟨157423096560064087428375955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209897462080085449904501273 157423096560064087428375955)
    ·
      refine ⟨236134644840096131142563933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157423096560064087428375955 236134644840096131142563933)
      ·
        refine ⟨88550491815036049178461475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236134644840096131142563933 88550491815036049178461475)
        ·
          refine ⟨132825737722554073767692213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88550491815036049178461475 132825737722554073767692213)
          ·
            refine ⟨12452412911489444415721145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132825737722554073767692213 12452412911489444415721145)
            ·
              refine ⟨9339309683617083311790859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12452412911489444415721145 9339309683617083311790859)
              ·
                refine ⟨14008964525425624967686289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339309683617083311790859 14008964525425624967686289)
                ·
                  refine ⟨10506723394069218725764717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14008964525425624967686289 10506723394069218725764717)
                  ·
                    refine ⟨3940021272775957022161769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10506723394069218725764717 3940021272775957022161769)
                    ·
                      refine ⟨2955015954581967766621327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940021272775957022161769 2955015954581967766621327)
                      ·
                        rfl

theorem cell23_5754873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_5754873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754873 prefixEnd_5754873 := by exact prefixLift 5754873
  have htrace : WordTrace (prefixWord ++ tailWord_5754873) baseStart_5754873 baseEnd_5754873 := by
    simpa [prefixWord, tailWord_5754873, baseEnd_5754873] using wordTrace_append hprefix tailTrace_5754873
  have hstable : (prefixWord ++ tailWord_5754873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754873).length < 2 ^ (prefixWord ++ tailWord_5754873).sum := by decide
  have hdescent : baseEnd_5754873 < baseStart_5754873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754879 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 6, 4]
def baseStart_5754879 : Nat := 118140960795 + 5754879 * 2 ^ 59
def prefixEnd_5754879 : Nat := 4983230072969 + 3 ^ 40 * 5754879 * 2
def baseEnd_5754879 : Nat := 985006345155298247715433

theorem tailTrace_5754879 : CollatzResearch.WordTrace tailWord_5754879 prefixEnd_5754879 985006345155298247715433 := by
  unfold tailWord_5754879
  simp only [CollatzResearch.WordTrace]
  refine ⟨209897680918063712929219691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139931787278709141952813127 209897680918063712929219691)
  ·
    refine ⟨314846521377095569393829537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209897680918063712929219691 314846521377095569393829537)
    ·
      refine ⟨236134891032821677045372153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314846521377095569393829537 236134891032821677045372153)
      ·
        refine ⟨177101168274616257784029115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236134891032821677045372153 177101168274616257784029115)
        ·
          refine ⟨265651752411924386676043673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177101168274616257784029115 265651752411924386676043673)
          ·
            refine ⟨199238814308943290007032755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265651752411924386676043673 199238814308943290007032755)
            ·
              refine ⟨298858221463414935010549133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199238814308943290007032755 298858221463414935010549133)
              ·
                refine ⟨112071833048780600628955925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298858221463414935010549133 112071833048780600628955925)
                ·
                  refine ⟨5253367174161590654482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112071833048780600628955925 5253367174161590654482309)
                  ·
                    refine ⟨985006345155298247715433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253367174161590654482309 985006345155298247715433)
                    ·
                      rfl

theorem cell23_5754879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_5754879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754879 prefixEnd_5754879 := by exact prefixLift 5754879
  have htrace : WordTrace (prefixWord ++ tailWord_5754879) baseStart_5754879 baseEnd_5754879 := by
    simpa [prefixWord, tailWord_5754879, baseEnd_5754879] using wordTrace_append hprefix tailTrace_5754879
  have hstable : (prefixWord ++ tailWord_5754879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754879).length < 2 ^ (prefixWord ++ tailWord_5754879).sum := by decide
  have hdescent : baseEnd_5754879 < baseStart_5754879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754906 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_5754906 : Nat := 118140960795 + 5754906 * 2 ^ 59
def prefixEnd_5754906 : Nat := 4983230072969 + 3 ^ 40 * 5754906 * 2
def baseEnd_5754906 : Nat := 2955032899443566137508675

theorem tailTrace_5754906 : CollatzResearch.WordTrace tailWord_5754906 prefixEnd_5754906 2955032899443566137508675 := by
  unfold tailWord_5754906
  simp only [CollatzResearch.WordTrace]
  refine ⟨52474666422241474135113143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139932443792643931026968381 52474666422241474135113143)
  ·
    refine ⟨78711999633362211202669715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52474666422241474135113143 78711999633362211202669715)
    ·
      refine ⟨118067999450043316804004573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78711999633362211202669715 118067999450043316804004573)
      ·
        refine ⟨44275499793766243801501715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118067999450043316804004573 44275499793766243801501715)
        ·
          refine ⟨66413249690649365702252573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44275499793766243801501715 66413249690649365702252573)
          ·
            refine ⟨24904968633993512138344715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66413249690649365702252573 24904968633993512138344715)
            ·
              refine ⟨37357452950990268207517073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24904968633993512138344715 37357452950990268207517073)
              ·
                refine ⟨28018089713242701155637805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37357452950990268207517073 28018089713242701155637805)
                ·
                  refine ⟨10506783642466012933364177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28018089713242701155637805 10506783642466012933364177)
                  ·
                    refine ⟨7880087731849509700023133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10506783642466012933364177 7880087731849509700023133)
                    ·
                      refine ⟨2955032899443566137508675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880087731849509700023133 2955032899443566137508675)
                      ·
                        rfl

theorem cell23_5754906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_5754906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754906 prefixEnd_5754906 := by exact prefixLift 5754906
  have htrace : WordTrace (prefixWord ++ tailWord_5754906) baseStart_5754906 baseEnd_5754906 := by
    simpa [prefixWord, tailWord_5754906, baseEnd_5754906] using wordTrace_append hprefix tailTrace_5754906
  have hstable : (prefixWord ++ tailWord_5754906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754906).length < 2 ^ (prefixWord ++ tailWord_5754906).sum := by decide
  have hdescent : baseEnd_5754906 < baseStart_5754906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754937 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5754937 : Nat := 118140960795 + 5754937 * 2 ^ 59
def prefixEnd_5754937 : Nat := 4983230072969 + 3 ^ 40 * 5754937 * 2
def baseEnd_5754937 : Nat := 2955048817343855516221033

theorem tailTrace_5754937 : CollatzResearch.WordTrace tailWord_5754937 prefixEnd_5754937 2955048817343855516221033 := by
  unfold tailWord_5754937
  simp only [CollatzResearch.WordTrace]
  refine ⟨209899796351853588834831065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139933197567902392556554043 209899796351853588834831065)
  ·
    refine ⟨157424847263890191626123299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209899796351853588834831065 157424847263890191626123299)
    ·
      refine ⟨236137270895835287439184949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157424847263890191626123299 236137270895835287439184949)
      ·
        refine ⟨22137869146484558197423589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236137270895835287439184949 22137869146484558197423589)
        ·
          refine ⟨4150850464965854662016923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22137869146484558197423589 4150850464965854662016923)
          ·
            refine ⟨6226275697448781993025385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150850464965854662016923 6226275697448781993025385)
            ·
              refine ⟨4669706773086586494769039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226275697448781993025385 4669706773086586494769039)
              ·
                refine ⟨7004560159629879742153559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669706773086586494769039 7004560159629879742153559)
                ·
                  refine ⟨10506840239444819613230339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004560159629879742153559 10506840239444819613230339)
                  ·
                    refine ⟨15760260359167229419845509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10506840239444819613230339 15760260359167229419845509)
                    ·
                      refine ⟨2955048817343855516221033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15760260359167229419845509 2955048817343855516221033)
                      ·
                        rfl

theorem cell23_5754937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5754937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754937 prefixEnd_5754937 := by exact prefixLift 5754937
  have htrace : WordTrace (prefixWord ++ tailWord_5754937) baseStart_5754937 baseEnd_5754937 := by
    simpa [prefixWord, tailWord_5754937, baseEnd_5754937] using wordTrace_append hprefix tailTrace_5754937
  have hstable : (prefixWord ++ tailWord_5754937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754937).length < 2 ^ (prefixWord ++ tailWord_5754937).sum := by decide
  have hdescent : baseEnd_5754937 < baseStart_5754937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754969 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_5754969 : Nat := 118140960795 + 5754969 * 2 ^ 59
def prefixEnd_5754969 : Nat := 4983230072969 + 3 ^ 40 * 5754969 * 2
def baseEnd_5754969 : Nat := 985021749574933130340295

theorem tailTrace_5754969 : CollatzResearch.WordTrace tailWord_5754969 prefixEnd_5754969 985021749574933130340295 := by
  unfold tailWord_5754969
  simp only [CollatzResearch.WordTrace]
  refine ⟨209900963487737658299995961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139933975658491772199997307 209900963487737658299995961)
  ·
    refine ⟨157425722615803243724996971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209900963487737658299995961 157425722615803243724996971)
    ·
      refine ⟨236138583923704865587495457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157425722615803243724996971 236138583923704865587495457)
      ·
        refine ⟨177103937942778649190621593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236138583923704865587495457 177103937942778649190621593)
        ·
          refine ⟨132827953457083986892966195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177103937942778649190621593 132827953457083986892966195)
          ·
            refine ⟨199241930185625980339449293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132827953457083986892966195 199241930185625980339449293)
            ·
              refine ⟨74715723819609742627293485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199241930185625980339449293 74715723819609742627293485)
              ·
                refine ⟨28018396432353653485235057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74715723819609742627293485 28018396432353653485235057)
                ·
                  refine ⟨21013797324265240113926293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28018396432353653485235057 21013797324265240113926293)
                  ·
                    refine ⟨985021749574933130340295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21013797324265240113926293 985021749574933130340295)
                    ·
                      rfl

theorem cell23_5754969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_5754969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754969 prefixEnd_5754969 := by exact prefixLift 5754969
  have htrace : WordTrace (prefixWord ++ tailWord_5754969) baseStart_5754969 baseEnd_5754969 := by
    simpa [prefixWord, tailWord_5754969, baseEnd_5754969] using wordTrace_append hprefix tailTrace_5754969
  have hstable : (prefixWord ++ tailWord_5754969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754969).length < 2 ^ (prefixWord ++ tailWord_5754969).sum := by decide
  have hdescent : baseEnd_5754969 < baseStart_5754969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754970 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_5754970 : Nat := 118140960795 + 5754970 * 2 ^ 59
def prefixEnd_5754970 : Nat := 4983230072969 + 3 ^ 40 * 5754970 * 2
def baseEnd_5754970 : Nat := 2955065762205453887108381

theorem tailTrace_5754970 : CollatzResearch.WordTrace tailWord_5754970 prefixEnd_5754970 2955065762205453887108381 := by
  unfold tailWord_5754970
  simp only [CollatzResearch.WordTrace]
  refine ⟨52475249990183508867695591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139933999973822690313854909 52475249990183508867695591)
  ·
    refine ⟨78712874985275263301543387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52475249990183508867695591 78712874985275263301543387)
    ·
      refine ⟨118069312477912894952315081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78712874985275263301543387 118069312477912894952315081)
      ·
        refine ⟨88551984358434671214236311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118069312477912894952315081 88551984358434671214236311)
        ·
          refine ⟨132827976537652006821354467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88551984358434671214236311 132827976537652006821354467)
          ·
            refine ⟨199241964806478010232031701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132827976537652006821354467 199241964806478010232031701)
            ·
              refine ⟨4669733550151828364813243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 199241964806478010232031701 4669733550151828364813243)
              ·
                refine ⟨7004600325227742547219865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669733550151828364813243 7004600325227742547219865)
                ·
                  refine ⟨5253450243920806910414899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7004600325227742547219865 5253450243920806910414899)
                  ·
                    refine ⟨7880175365881210365622349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253450243920806910414899 7880175365881210365622349)
                    ·
                      refine ⟨2955065762205453887108381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880175365881210365622349 2955065762205453887108381)
                      ·
                        rfl

theorem cell23_5754970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_5754970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754970 prefixEnd_5754970 := by exact prefixLift 5754970
  have htrace : WordTrace (prefixWord ++ tailWord_5754970) baseStart_5754970 baseEnd_5754970 := by
    simpa [prefixWord, tailWord_5754970, baseEnd_5754970] using wordTrace_append hprefix tailTrace_5754970
  have hstable : (prefixWord ++ tailWord_5754970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754970).length < 2 ^ (prefixWord ++ tailWord_5754970).sum := by decide
  have hdescent : baseEnd_5754970 < baseStart_5754970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754974 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5754974 : Nat := 118140960795 + 5754974 * 2 ^ 59
def prefixEnd_5754974 : Nat := 4983230072969 + 3 ^ 40 * 5754974 * 2
def baseEnd_5754974 : Nat := 2955067816128071871458363

theorem tailTrace_5754974 : CollatzResearch.WordTrace tailWord_5754974 prefixEnd_5754974 2955067816128071871458363 := by
  unfold tailWord_5754974
  simp only [CollatzResearch.WordTrace]
  refine ⟨26237643231589943019240997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139934097235146362769285317 26237643231589943019240997)
  ·
    refine ⟨4919558105923114316107687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26237643231589943019240997 4919558105923114316107687)
    ·
      refine ⟨7379337158884671474161531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919558105923114316107687 7379337158884671474161531)
      ·
        refine ⟨11069005738327007211242297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379337158884671474161531 11069005738327007211242297)
        ·
          refine ⟨8301754303745255408431723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11069005738327007211242297 8301754303745255408431723)
          ·
            refine ⟨12452631455617883112647585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301754303745255408431723 12452631455617883112647585)
            ·
              refine ⟨9339473591713412334485689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12452631455617883112647585 9339473591713412334485689)
              ·
                refine ⟨7004605193785059250864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9339473591713412334485689 7004605193785059250864267)
                ·
                  refine ⟨10506907790677588876296401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004605193785059250864267 10506907790677588876296401)
                  ·
                    refine ⟨7880180843008191657222301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10506907790677588876296401 7880180843008191657222301)
                    ·
                      refine ⟨2955067816128071871458363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880180843008191657222301 2955067816128071871458363)
                      ·
                        rfl

theorem cell23_5754974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5754974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754974 prefixEnd_5754974 := by exact prefixLift 5754974
  have htrace : WordTrace (prefixWord ++ tailWord_5754974) baseStart_5754974 baseEnd_5754974 := by
    simpa [prefixWord, tailWord_5754974, baseEnd_5754974] using wordTrace_append hprefix tailTrace_5754974
  have hstable : (prefixWord ++ tailWord_5754974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754974).length < 2 ^ (prefixWord ++ tailWord_5754974).sum := by decide
  have hdescent : baseEnd_5754974 < baseStart_5754974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5754993 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_5754993 : Nat := 118140960795 + 5754993 * 2 ^ 59
def prefixEnd_5754993 : Nat := 4983230072969 + 3 ^ 40 * 5754993 * 2
def baseEnd_5754993 : Nat := 2955077572260507297120775

theorem tailTrace_5754993 : CollatzResearch.WordTrace tailWord_5754993 prefixEnd_5754993 2955077572260507297120775 := by
  unfold tailWord_5754993
  simp only [CollatzResearch.WordTrace]
  refine ⟨209901838839650710398869633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139934559226433806932579755 209901838839650710398869633)
  ·
    refine ⟨157426379129738032799152225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209901838839650710398869633 157426379129738032799152225)
    ·
      refine ⟨118069784347303524599364169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157426379129738032799152225 118069784347303524599364169)
      ·
        refine ⟨88552338260477643449523127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118069784347303524599364169 88552338260477643449523127)
        ·
          refine ⟨132828507390716465174284691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88552338260477643449523127 132828507390716465174284691)
          ·
            refine ⟨199242761086074697761427037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132828507390716465174284691 199242761086074697761427037)
            ·
              refine ⟨74716035407278011660535139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199242761086074697761427037 74716035407278011660535139)
              ·
                refine ⟨112074053110917017490802709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74716035407278011660535139 112074053110917017490802709)
                ·
                  refine ⟨5253471239574235194881377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112074053110917017490802709 5253471239574235194881377)
                  ·
                    refine ⟨3940103429680676396161033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5253471239574235194881377 3940103429680676396161033)
                    ·
                      refine ⟨2955077572260507297120775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940103429680676396161033 2955077572260507297120775)
                      ·
                        rfl

theorem cell23_5754993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_5754993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5754993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5754993 prefixEnd_5754993 := by exact prefixLift 5754993
  have htrace : WordTrace (prefixWord ++ tailWord_5754993) baseStart_5754993 baseEnd_5754993 := by
    simpa [prefixWord, tailWord_5754993, baseEnd_5754993] using wordTrace_append hprefix tailTrace_5754993
  have hstable : (prefixWord ++ tailWord_5754993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5754993).length < 2 ^ (prefixWord ++ tailWord_5754993).sum := by decide
  have hdescent : baseEnd_5754993 < baseStart_5754993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5754993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755083 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 4, 2]
def baseStart_5755083 : Nat := 118140960795 + 5755083 * 2 ^ 59
def prefixEnd_5755083 : Nat := 4983230072969 + 3 ^ 40 * 5755083 * 2
def baseEnd_5755083 : Nat := 2955123785519411944995361

theorem tailTrace_5755083 : CollatzResearch.WordTrace tailWord_5755083 prefixEnd_5755083 2955123785519411944995361 := by
  unfold tailWord_5755083
  simp only [CollatzResearch.WordTrace]
  refine ⟨209905121409324655769645903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139936747606216437179763935 209905121409324655769645903)
  ·
    refine ⟨314857682113986983654468855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209905121409324655769645903 314857682113986983654468855)
    ·
      refine ⟨472286523170980475481703283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314857682113986983654468855 472286523170980475481703283)
      ·
        refine ⟨708429784756470713222554925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472286523170980475481703283 708429784756470713222554925)
        ·
          refine ⟨265661169283676517458458097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708429784756470713222554925 265661169283676517458458097)
          ·
            refine ⟨199245876962757388093843573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265661169283676517458458097 199245876962757388093843573)
            ·
              refine ⟨18679300965258505133797835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199245876962757388093843573 18679300965258505133797835)
              ·
                refine ⟨28018951447887757700696753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18679300965258505133797835 28018951447887757700696753)
                ·
                  refine ⟨21014213585915818275522565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28018951447887757700696753 21014213585915818275522565)
                  ·
                    refine ⟨3940165047359215926660481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21014213585915818275522565 3940165047359215926660481)
                    ·
                      refine ⟨2955123785519411944995361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940165047359215926660481 2955123785519411944995361)
                      ·
                        rfl

theorem cell23_5755083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4, 2].length) (baseStart_5755083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755083 prefixEnd_5755083 := by exact prefixLift 5755083
  have htrace : WordTrace (prefixWord ++ tailWord_5755083) baseStart_5755083 baseEnd_5755083 := by
    simpa [prefixWord, tailWord_5755083, baseEnd_5755083] using wordTrace_append hprefix tailTrace_5755083
  have hstable : (prefixWord ++ tailWord_5755083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755083).length < 2 ^ (prefixWord ++ tailWord_5755083).sum := by decide
  have hdescent : baseEnd_5755083 < baseStart_5755083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755136 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_5755136 : Nat := 118140960795 + 5755136 * 2 ^ 59
def prefixEnd_5755136 : Nat := 4983230072969 + 3 ^ 40 * 5755136 * 2
def baseEnd_5755136 : Nat := 985050333331366745877539

theorem tailTrace_5755136 : CollatzResearch.WordTrace tailWord_5755136 prefixEnd_5755136 985050333331366745877539 := by
  unfold tailWord_5755136
  simp only [CollatzResearch.WordTrace]
  refine ⟨104953527239066322910662631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139938036318755097214216841 104953527239066322910662631)
  ·
    refine ⟨157430290858599484365993947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104953527239066322910662631 157430290858599484365993947)
    ·
      refine ⟨236145436287899226548990921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157430290858599484365993947 236145436287899226548990921)
      ·
        refine ⟨177109077215924419911743191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236145436287899226548990921 177109077215924419911743191)
        ·
          refine ⟨265663615823886629867614787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177109077215924419911743191 265663615823886629867614787)
          ·
            refine ⟨398495423735829944801422181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265663615823886629867614787 398495423735829944801422181)
            ·
              refine ⟨74717891950468114650266659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398495423735829944801422181 74717891950468114650266659)
              ·
                refine ⟨112076837925702171975399989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74717891950468114650266659 112076837925702171975399989)
                ·
                  refine ⟨10507203555534578622693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112076837925702171975399989 10507203555534578622693749)
                  ·
                    refine ⟨985050333331366745877539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507203555534578622693749 985050333331366745877539)
                    ·
                      rfl

theorem cell23_5755136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_5755136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755136 prefixEnd_5755136 := by exact prefixLift 5755136
  have htrace : WordTrace (prefixWord ++ tailWord_5755136) baseStart_5755136 baseEnd_5755136 := by
    simpa [prefixWord, tailWord_5755136, baseEnd_5755136] using wordTrace_append hprefix tailTrace_5755136
  have hstable : (prefixWord ++ tailWord_5755136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755136).length < 2 ^ (prefixWord ++ tailWord_5755136).sum := by decide
  have hdescent : baseEnd_5755136 < baseStart_5755136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755146 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5755146 : Nat := 118140960795 + 5755146 * 2 ^ 59
def prefixEnd_5755146 : Nat := 4983230072969 + 3 ^ 40 * 5755146 * 2
def baseEnd_5755146 : Nat := 2955156134800645198507571

theorem tailTrace_5755146 : CollatzResearch.WordTrace tailWord_5755146 prefixEnd_5755146 2955156134800645198507571 := by
  unfold tailWord_5755146
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476854802024104382297323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139938279472064278352792861 52476854802024104382297323)
  ·
    refine ⟨78715282203036156573445985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52476854802024104382297323 78715282203036156573445985)
    ·
      refine ⟨59036461652277117430084489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78715282203036156573445985 59036461652277117430084489)
      ·
        refine ⟨44277346239207838072563367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59036461652277117430084489 44277346239207838072563367)
        ·
          refine ⟨66416019358811757108845051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44277346239207838072563367 66416019358811757108845051)
          ·
            refine ⟨99624029038217635663267577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66416019358811757108845051 99624029038217635663267577)
            ·
              refine ⟨74718021778663226747450683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99624029038217635663267577 74718021778663226747450683)
              ·
                refine ⟨112077032667994840121176025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74718021778663226747450683 112077032667994840121176025)
                ·
                  refine ⟨84057774500996130090882019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112077032667994840121176025 84057774500996130090882019)
                  ·
                    refine ⟨126086661751494195136323029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84057774500996130090882019 126086661751494195136323029)
                    ·
                      refine ⟨2955156134800645198507571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126086661751494195136323029 2955156134800645198507571)
                      ·
                        rfl

theorem cell23_5755146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5755146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755146 prefixEnd_5755146 := by exact prefixLift 5755146
  have htrace : WordTrace (prefixWord ++ tailWord_5755146) baseStart_5755146 baseEnd_5755146 := by
    simpa [prefixWord, tailWord_5755146, baseEnd_5755146] using wordTrace_append hprefix tailTrace_5755146
  have hstable : (prefixWord ++ tailWord_5755146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755146).length < 2 ^ (prefixWord ++ tailWord_5755146).sum := by decide
  have hdescent : baseEnd_5755146 < baseStart_5755146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755150 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5755150 : Nat := 118140960795 + 5755150 * 2 ^ 59
def prefixEnd_5755150 : Nat := 4983230072969 + 3 ^ 40 * 5755150 * 2
def baseEnd_5755150 : Nat := 2955158188723263182857553

theorem tailTrace_5755150 : CollatzResearch.WordTrace tailWord_5755150 prefixEnd_5755150 2955158188723263182857553 := by
  unfold tailWord_5755150
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238445637510240776541863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139938376733387950808223269 26238445637510240776541863)
  ·
    refine ⟨39357668456265361164812795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26238445637510240776541863 39357668456265361164812795)
    ·
      refine ⟨59036502684398041747219193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39357668456265361164812795 59036502684398041747219193)
      ·
        refine ⟨44277377013298531310414395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59036502684398041747219193 44277377013298531310414395)
        ·
          refine ⟨66416065519947796965621593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44277377013298531310414395 66416065519947796965621593)
          ·
            refine ⟨49812049139960847724216195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66416065519947796965621593 49812049139960847724216195)
            ·
              refine ⟨74718073709941271586324293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49812049139960847724216195 74718073709941271586324293)
              ·
                refine ⟨14009638820613988422435805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74718073709941271586324293 14009638820613988422435805)
                ·
                  refine ⟨5253614557730245658413427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14009638820613988422435805 5253614557730245658413427)
                  ·
                    refine ⟨7880421836595368487620141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253614557730245658413427 7880421836595368487620141)
                    ·
                      refine ⟨2955158188723263182857553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880421836595368487620141 2955158188723263182857553)
                      ·
                        rfl

theorem cell23_5755150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5755150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755150 prefixEnd_5755150 := by exact prefixLift 5755150
  have htrace : WordTrace (prefixWord ++ tailWord_5755150) baseStart_5755150 baseEnd_5755150 := by
    simpa [prefixWord, tailWord_5755150, baseEnd_5755150] using wordTrace_append hprefix tailTrace_5755150
  have hstable : (prefixWord ++ tailWord_5755150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755150).length < 2 ^ (prefixWord ++ tailWord_5755150).sum := by decide
  have hdescent : baseEnd_5755150 < baseStart_5755150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755153 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_5755153 : Nat := 118140960795 + 5755153 * 2 ^ 59
def prefixEnd_5755153 : Nat := 4983230072969 + 3 ^ 40 * 5755153 * 2
def baseEnd_5755153 : Nat := 985053243055075557040013

theorem tailTrace_5755153 : CollatzResearch.WordTrace tailWord_5755153 prefixEnd_5755153 985053243055075557040013 := by
  unfold tailWord_5755153
  simp only [CollatzResearch.WordTrace]
  refine ⟨209907674519071057724694113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139938449679380705149796075 209907674519071057724694113)
  ·
    refine ⟨157430755889303293293520585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209907674519071057724694113 157430755889303293293520585)
    ·
      refine ⟨118073066916977469970140439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157430755889303293293520585 118073066916977469970140439)
      ·
        refine ⟨177109600375466204955210659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118073066916977469970140439 177109600375466204955210659)
        ·
          refine ⟨265664400563199307432815989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177109600375466204955210659 265664400563199307432815989)
          ·
            refine ⟨24906037552799935071826499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265664400563199307432815989 24906037552799935071826499)
            ·
              refine ⟨37359056329199902607739749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24906037552799935071826499 37359056329199902607739749)
              ·
                refine ⟨7004823061724981738951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37359056329199902607739749 7004823061724981738951203)
                ·
                  refine ⟨10507234592587472608426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004823061724981738951203 10507234592587472608426805)
                  ·
                    refine ⟨985053243055075557040013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507234592587472608426805 985053243055075557040013)
                    ·
                      rfl

theorem cell23_5755153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_5755153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755153 prefixEnd_5755153 := by exact prefixLift 5755153
  have htrace : WordTrace (prefixWord ++ tailWord_5755153) baseStart_5755153 baseEnd_5755153 := by
    simpa [prefixWord, tailWord_5755153, baseEnd_5755153] using wordTrace_append hprefix tailTrace_5755153
  have hstable : (prefixWord ++ tailWord_5755153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755153).length < 2 ^ (prefixWord ++ tailWord_5755153).sum := by decide
  have hdescent : baseEnd_5755153 < baseStart_5755153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755160 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5755160 : Nat := 118140960795 + 5755160 * 2 ^ 59
def prefixEnd_5755160 : Nat := 4983230072969 + 3 ^ 40 * 5755160 * 2
def baseEnd_5755160 : Nat := 2955163323529808143732507

theorem tailTrace_5755160 : CollatzResearch.WordTrace tailWord_5755160 prefixEnd_5755160 2955163323529808143732507 := by
  unfold tailWord_5755160
  simp only [CollatzResearch.WordTrace]
  refine ⟨104953964915022848960099467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139938619886697131946799289 104953964915022848960099467)
  ·
    refine ⟨157430947372534273440149201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104953964915022848960099467 157430947372534273440149201)
    ·
      refine ⟨118073210529400705080111901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157430947372534273440149201 118073210529400705080111901)
      ·
        refine ⟨44277453948525264405041963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118073210529400705080111901 44277453948525264405041963)
        ·
          refine ⟨66416180922787896607562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44277453948525264405041963 66416180922787896607562945)
          ·
            refine ⟨49812135692090922455672209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66416180922787896607562945 49812135692090922455672209)
            ·
              refine ⟨37359101769068191841754157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49812135692090922455672209 37359101769068191841754157)
              ·
                refine ⟨14009663163400571940657809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37359101769068191841754157 14009663163400571940657809)
                ·
                  refine ⟨10507247372550428955493357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14009663163400571940657809 10507247372550428955493357)
                  ·
                    refine ⟨3940217764706410858310009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10507247372550428955493357 3940217764706410858310009)
                    ·
                      refine ⟨2955163323529808143732507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940217764706410858310009 2955163323529808143732507)
                      ·
                        rfl

theorem cell23_5755160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5755160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755160 prefixEnd_5755160 := by exact prefixLift 5755160
  have htrace : WordTrace (prefixWord ++ tailWord_5755160) baseStart_5755160 baseEnd_5755160 := by
    simpa [prefixWord, tailWord_5755160, baseEnd_5755160] using wordTrace_append hprefix tailTrace_5755160
  have hstable : (prefixWord ++ tailWord_5755160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755160).length < 2 ^ (prefixWord ++ tailWord_5755160).sum := by decide
  have hdescent : baseEnd_5755160 < baseStart_5755160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755170 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5755170 : Nat := 118140960795 + 5755170 * 2 ^ 59
def prefixEnd_5755170 : Nat := 4983230072969 + 3 ^ 40 * 5755170 * 2
def baseEnd_5755170 : Nat := 985056152778784368202487

theorem tailTrace_5755170 : CollatzResearch.WordTrace tailWord_5755170 prefixEnd_5755170 985056152778784368202487 := by
  unfold tailWord_5755170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477073640002367407015741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139938863040006313085375309 52477073640002367407015741)
  ·
    refine ⟨19678902615000887777630903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52477073640002367407015741 19678902615000887777630903)
    ·
      refine ⟨29518353922501331666446355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19678902615000887777630903 29518353922501331666446355)
      ·
        refine ⟨44277530883751997499669533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29518353922501331666446355 44277530883751997499669533)
        ·
          refine ⟨16604074081406999062376075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44277530883751997499669533 16604074081406999062376075)
          ·
            refine ⟨24906111122110498593564113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16604074081406999062376075 24906111122110498593564113)
            ·
              refine ⟨18679583341582873945173085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24906111122110498593564113 18679583341582873945173085)
              ·
                refine ⟨7004843753093577729439907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18679583341582873945173085 7004843753093577729439907)
                ·
                  refine ⟨10507265629640366594159861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004843753093577729439907 10507265629640366594159861)
                  ·
                    refine ⟨985056152778784368202487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507265629640366594159861 985056152778784368202487)
                    ·
                      rfl

theorem cell23_5755170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5755170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755170 prefixEnd_5755170 := by exact prefixLift 5755170
  have htrace : WordTrace (prefixWord ++ tailWord_5755170) baseStart_5755170 baseEnd_5755170 := by
    simpa [prefixWord, tailWord_5755170, baseEnd_5755170] using wordTrace_append hprefix tailTrace_5755170
  have hstable : (prefixWord ++ tailWord_5755170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755170).length < 2 ^ (prefixWord ++ tailWord_5755170).sum := by decide
  have hdescent : baseEnd_5755170 < baseStart_5755170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755183 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 4, 4]
def baseStart_5755183 : Nat := 118140960795 + 5755183 * 2 ^ 59
def prefixEnd_5755183 : Nat := 4983230072969 + 3 ^ 40 * 5755183 * 2
def baseEnd_5755183 : Nat := 985058377861620517914967

theorem tailTrace_5755183 : CollatzResearch.WordTrace tailWord_5755183 prefixEnd_5755183 985058377861620517914967 := by
  unfold tailWord_5755183
  simp only [CollatzResearch.WordTrace]
  refine ⟨209908768708962372848286203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139939179139308248565524135 209908768708962372848286203)
  ·
    refine ⟨314863153063443559272429305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209908768708962372848286203 314863153063443559272429305)
    ·
      refine ⟨236147364797582669454321979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314863153063443559272429305 236147364797582669454321979)
      ·
        refine ⟨354221047196374004181482969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236147364797582669454321979 354221047196374004181482969)
        ·
          refine ⟨265665785397280503136112227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354221047196374004181482969 265665785397280503136112227)
          ·
            refine ⟨398498678095920754704168341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265665785397280503136112227 398498678095920754704168341)
            ·
              refine ⟨18679625535746285376757891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 398498678095920754704168341 18679625535746285376757891)
              ·
                refine ⟨28019438303619428065136837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18679625535746285376757891 28019438303619428065136837)
                ·
                  refine ⟨5253644681928642762213157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28019438303619428065136837 5253644681928642762213157)
                  ·
                    refine ⟨985058377861620517914967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253644681928642762213157 985058377861620517914967)
                    ·
                      rfl

theorem cell23_5755183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_5755183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755183 prefixEnd_5755183 := by exact prefixLift 5755183
  have htrace : WordTrace (prefixWord ++ tailWord_5755183) baseStart_5755183 baseEnd_5755183 := by
    simpa [prefixWord, tailWord_5755183, baseEnd_5755183] using wordTrace_append hprefix tailTrace_5755183
  have hstable : (prefixWord ++ tailWord_5755183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755183).length < 2 ^ (prefixWord ++ tailWord_5755183).sum := by decide
  have hdescent : baseEnd_5755183 < baseStart_5755183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755204 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5755204 : Nat := 118140960795 + 5755204 * 2 ^ 59
def prefixEnd_5755204 : Nat := 4983230072969 + 3 ^ 40 * 5755204 * 2
def baseEnd_5755204 : Nat := 985061972226201990527435

theorem tailTrace_5755204 : CollatzResearch.WordTrace tailWord_5755204 prefixEnd_5755204 985061972226201990527435 := by
  unfold tailWord_5755204
  simp only [CollatzResearch.WordTrace]
  refine ⟨104954767320943146717400333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139939689761257528956533777 104954767320943146717400333)
  ·
    refine ⟨39358037745353680019025125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104954767320943146717400333 39358037745353680019025125)
    ·
      refine ⟨7379632077253815003567211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39358037745353680019025125 7379632077253815003567211)
      ·
        refine ⟨11069448115880722505350817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379632077253815003567211 11069448115880722505350817)
        ·
          refine ⟨8302086086910541879013113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11069448115880722505350817 8302086086910541879013113)
          ·
            refine ⟨6226564565182906409259835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302086086910541879013113 6226564565182906409259835)
            ·
              refine ⟨9339846847774359613889753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226564565182906409259835 9339846847774359613889753)
              ·
                refine ⟨7004885135830769710417315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9339846847774359613889753 7004885135830769710417315)
                ·
                  refine ⟨10507327703746154565625973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004885135830769710417315 10507327703746154565625973)
                  ·
                    refine ⟨985061972226201990527435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507327703746154565625973 985061972226201990527435)
                    ·
                      rfl

theorem cell23_5755204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5755204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755204 prefixEnd_5755204 := by exact prefixLift 5755204
  have htrace : WordTrace (prefixWord ++ tailWord_5755204) baseStart_5755204 baseEnd_5755204 := by
    simpa [prefixWord, tailWord_5755204, baseEnd_5755204] using wordTrace_append hprefix tailTrace_5755204
  have hstable : (prefixWord ++ tailWord_5755204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755204).length < 2 ^ (prefixWord ++ tailWord_5755204).sum := by decide
  have hdescent : baseEnd_5755204 < baseStart_5755204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755220 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5755220 : Nat := 118140960795 + 5755220 * 2 ^ 59
def prefixEnd_5755220 : Nat := 4983230072969 + 3 ^ 40 * 5755220 * 2
def baseEnd_5755220 : Nat := 2955194132369077908982231

theorem tailTrace_5755220 : CollatzResearch.WordTrace tailWord_5755220 prefixEnd_5755220 2955194132369077908982231 := by
  unfold tailWord_5755220
  simp only [CollatzResearch.WordTrace]
  refine ⟨104955059104914164083691557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139940078806552218778255409 104955059104914164083691557)
  ·
    refine ⟨19679073582171405765692167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104955059104914164083691557 19679073582171405765692167)
    ·
      refine ⟨29518610373257108648538251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679073582171405765692167 29518610373257108648538251)
      ·
        refine ⟨44277915559885662972807377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29518610373257108648538251 44277915559885662972807377)
        ·
          refine ⟨33208436669914247229605533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44277915559885662972807377 33208436669914247229605533)
          ·
            refine ⟨12453163751217842711102075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33208436669914247229605533 12453163751217842711102075)
            ·
              refine ⟨18679745626826764066653113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12453163751217842711102075 18679745626826764066653113)
              ·
                refine ⟨14009809220120073049989835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18679745626826764066653113 14009809220120073049989835)
                ·
                  refine ⟨21014713830180109574984753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14009809220120073049989835 21014713830180109574984753)
                  ·
                    refine ⟨15761035372635082181238565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21014713830180109574984753 15761035372635082181238565)
                    ·
                      refine ⟨2955194132369077908982231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15761035372635082181238565 2955194132369077908982231)
                      ·
                        rfl

theorem cell23_5755220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5755220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755220 prefixEnd_5755220 := by exact prefixLift 5755220
  have htrace : WordTrace (prefixWord ++ tailWord_5755220) baseStart_5755220 baseEnd_5755220 := by
    simpa [prefixWord, tailWord_5755220, baseEnd_5755220] using wordTrace_append hprefix tailTrace_5755220
  have hstable : (prefixWord ++ tailWord_5755220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755220).length < 2 ^ (prefixWord ++ tailWord_5755220).sum := by decide
  have hdescent : baseEnd_5755220 < baseStart_5755220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755254 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5755254 : Nat := 118140960795 + 5755254 * 2 ^ 59
def prefixEnd_5755254 : Nat := 4983230072969 + 3 ^ 40 * 5755254 * 2
def baseEnd_5755254 : Nat := 2955211590711330775957075

theorem tailTrace_5755254 : CollatzResearch.WordTrace tailWord_5755254 prefixEnd_5755254 2955211590711330775957075 := by
  unfold tailWord_5755254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119459893231571998382551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139940905527803434649413877 13119459893231571998382551)
  ·
    refine ⟨19679189839847357997573827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119459893231571998382551 19679189839847357997573827)
    ·
      refine ⟨29518784759771036996360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679189839847357997573827 29518784759771036996360741)
      ·
        refine ⟨5534772142457069436817639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29518784759771036996360741 5534772142457069436817639)
        ·
          refine ⟨8302158213685604155226459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534772142457069436817639 8302158213685604155226459)
          ·
            refine ⟨12453237320528406232839689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302158213685604155226459 12453237320528406232839689)
            ·
              refine ⟨9339927990396304674629767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12453237320528406232839689 9339927990396304674629767)
              ·
                refine ⟨14009891985594457011944651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339927990396304674629767 14009891985594457011944651)
                ·
                  refine ⟨21014837978391685517916977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14009891985594457011944651 21014837978391685517916977)
                  ·
                    refine ⟨15761128483793764138437733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21014837978391685517916977 15761128483793764138437733)
                    ·
                      refine ⟨2955211590711330775957075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15761128483793764138437733 2955211590711330775957075)
                      ·
                        rfl

theorem cell23_5755254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5755254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755254 prefixEnd_5755254 := by exact prefixLift 5755254
  have htrace : WordTrace (prefixWord ++ tailWord_5755254) baseStart_5755254 baseEnd_5755254 := by
    simpa [prefixWord, tailWord_5755254, baseEnd_5755254] using wordTrace_append hprefix tailTrace_5755254
  have hstable : (prefixWord ++ tailWord_5755254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755254).length < 2 ^ (prefixWord ++ tailWord_5755254).sum := by decide
  have hdescent : baseEnd_5755254 < baseStart_5755254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_5755333 : Nat := 118140960795 + 5755333 * 2 ^ 59
def prefixEnd_5755333 : Nat := 4983230072969 + 3 ^ 40 * 5755333 * 2
def baseEnd_5755333 : Nat := 985084051894345322289737

theorem tailTrace_5755333 : CollatzResearch.WordTrace tailWord_5755333 prefixEnd_5755333 985084051894345322289737 := by
  unfold tailWord_5755333
  simp only [CollatzResearch.WordTrace]
  refine ⟨209914239658418948466246653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139942826438945965644164435 209914239658418948466246653)
  ·
    refine ⟨78717839871907105674842495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209914239658418948466246653 78717839871907105674842495)
    ·
      refine ⟨118076759807860658512263743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78717839871907105674842495 118076759807860658512263743)
      ·
        refine ⟨177115139711790987768395615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118076759807860658512263743 177115139711790987768395615)
        ·
          refine ⟨265672709567686481652593423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177115139711790987768395615 265672709567686481652593423)
          ·
            refine ⟨398509064351529722478890135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265672709567686481652593423 398509064351529722478890135)
            ·
              refine ⟨597763596527294583718335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398509064351529722478890135 597763596527294583718335203)
              ·
                refine ⟨896645394790941875577502805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597763596527294583718335203 896645394790941875577502805)
                ·
                  refine ⟨10507563220206350104423861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 896645394790941875577502805 10507563220206350104423861)
                  ·
                    refine ⟨985084051894345322289737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507563220206350104423861 985084051894345322289737)
                    ·
                      rfl

theorem cell23_5755333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_5755333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755333 prefixEnd_5755333 := by exact prefixLift 5755333
  have htrace : WordTrace (prefixWord ++ tailWord_5755333) baseStart_5755333 baseEnd_5755333 := by
    simpa [prefixWord, tailWord_5755333, baseEnd_5755333] using wordTrace_append hprefix tailTrace_5755333
  have hstable : (prefixWord ++ tailWord_5755333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755333).length < 2 ^ (prefixWord ++ tailWord_5755333).sum := by decide
  have hdescent : baseEnd_5755333 < baseStart_5755333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755343 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_5755343 : Nat := 118140960795 + 5755343 * 2 ^ 59
def prefixEnd_5755343 : Nat := 4983230072969 + 3 ^ 40 * 5755343 * 2
def baseEnd_5755343 : Nat := 2955257290489580927744165

theorem tailTrace_5755343 : CollatzResearch.WordTrace tailWord_5755343 prefixEnd_5755343 2955257290489580927744165 := by
  unfold tailWord_5755343
  simp only [CollatzResearch.WordTrace]
  refine ⟨209914604388382720174110683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139943069592255146782740455 209914604388382720174110683)
  ·
    refine ⟨314871906582574080261166025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209914604388382720174110683 314871906582574080261166025)
    ·
      refine ⟨236153929936930560195874519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314871906582574080261166025 236153929936930560195874519)
      ·
        refine ⟨354230894905395840293811779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236153929936930560195874519 354230894905395840293811779)
        ·
          refine ⟨531346342358093760440717669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354230894905395840293811779 531346342358093760440717669)
          ·
            refine ⟨99627439192142580082634563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 531346342358093760440717669 99627439192142580082634563)
            ·
              refine ⟨149441158788213870123951845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99627439192142580082634563 149441158788213870123951845)
              ·
                refine ⟨28020217272790100648240971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149441158788213870123951845 28020217272790100648240971)
                ·
                  refine ⟨42030325909185150972361457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28020217272790100648240971 42030325909185150972361457)
                  ·
                    refine ⟨31522744431888863229271093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42030325909185150972361457 31522744431888863229271093)
                    ·
                      refine ⟨2955257290489580927744165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31522744431888863229271093 2955257290489580927744165)
                      ·
                        rfl

theorem cell23_5755343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_5755343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755343 prefixEnd_5755343 := by exact prefixLift 5755343
  have htrace : WordTrace (prefixWord ++ tailWord_5755343) baseStart_5755343 baseEnd_5755343 := by
    simpa [prefixWord, tailWord_5755343, baseEnd_5755343] using wordTrace_append hprefix tailTrace_5755343
  have hstable : (prefixWord ++ tailWord_5755343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755343).length < 2 ^ (prefixWord ++ tailWord_5755343).sum := by decide
  have hdescent : baseEnd_5755343 < baseStart_5755343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755357 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5755357 : Nat := 118140960795 + 5755357 * 2 ^ 59
def prefixEnd_5755357 : Nat := 4983230072969 + 3 ^ 40 * 5755357 * 2
def baseEnd_5755357 : Nat := 2955264479218743872969101

theorem tailTrace_5755357 : CollatzResearch.WordTrace tailWord_5755357 prefixEnd_5755357 2955264479218743872969101 := by
  unfold tailWord_5755357
  simp only [CollatzResearch.WordTrace]
  refine ⟨209915115010332000565120325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139943410006888000376746883 209915115010332000565120325)
  ·
    refine ⟨39359084064437250105960061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209915115010332000565120325 39359084064437250105960061)
    ·
      refine ⟨14759656524163968789735023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39359084064437250105960061 14759656524163968789735023)
      ·
        refine ⟨22139484786245953184602535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14759656524163968789735023 22139484786245953184602535)
        ·
          refine ⟨33209227179368929776903803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22139484786245953184602535 33209227179368929776903803)
          ·
            refine ⟨49813840769053394665355705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33209227179368929776903803 49813840769053394665355705)
            ·
              refine ⟨37360380576790045999016779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49813840769053394665355705 37360380576790045999016779)
              ·
                refine ⟨56040570865185068998525169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37360380576790045999016779 56040570865185068998525169)
                ·
                  refine ⟨42030428148888801748893877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56040570865185068998525169 42030428148888801748893877)
                  ·
                    refine ⟨3940352638958325163958801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42030428148888801748893877 3940352638958325163958801)
                    ·
                      refine ⟨2955264479218743872969101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940352638958325163958801 2955264479218743872969101)
                      ·
                        rfl

theorem cell23_5755357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5755357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755357 prefixEnd_5755357 := by exact prefixLift 5755357
  have htrace : WordTrace (prefixWord ++ tailWord_5755357) baseStart_5755357 baseEnd_5755357 := by
    simpa [prefixWord, tailWord_5755357, baseEnd_5755357] using wordTrace_append hprefix tailTrace_5755357
  have hstable : (prefixWord ++ tailWord_5755357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755357).length < 2 ^ (prefixWord ++ tailWord_5755357).sum := by decide
  have hdescent : baseEnd_5755357 < baseStart_5755357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755365 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5755365 : Nat := 118140960795 + 5755365 * 2 ^ 59
def prefixEnd_5755365 : Nat := 4983230072969 + 3 ^ 40 * 5755365 * 2
def baseEnd_5755365 : Nat := 2955268587063979841669065

theorem tailTrace_5755365 : CollatzResearch.WordTrace tailWord_5755365 prefixEnd_5755365 2955268587063979841669065 := by
  unfold tailWord_5755365
  simp only [CollatzResearch.WordTrace]
  refine ⟨209915406794303017931411549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139943604529535345287607699 209915406794303017931411549)
  ·
    refine ⟨78718277547863631724279331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209915406794303017931411549 78718277547863631724279331)
    ·
      refine ⟨118077416321795447586418997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78718277547863631724279331 118077416321795447586418997)
      ·
        refine ⟨11069757780168323211226781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118077416321795447586418997 11069757780168323211226781)
        ·
          refine ⟨4151159167563121204210043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11069757780168323211226781 4151159167563121204210043)
          ·
            refine ⟨6226738751344681806315065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151159167563121204210043 6226738751344681806315065)
            ·
              refine ⟨4670054063508511354736299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226738751344681806315065 4670054063508511354736299)
              ·
                refine ⟨7005081095262767032104449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670054063508511354736299 7005081095262767032104449)
                ·
                  refine ⟨5253810821447075274078337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005081095262767032104449 5253810821447075274078337)
                  ·
                    refine ⟨3940358116085306455558753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5253810821447075274078337 3940358116085306455558753)
                    ·
                      refine ⟨2955268587063979841669065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940358116085306455558753 2955268587063979841669065)
                      ·
                        rfl

theorem cell23_5755365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5755365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755365 prefixEnd_5755365 := by exact prefixLift 5755365
  have htrace : WordTrace (prefixWord ++ tailWord_5755365) baseStart_5755365 baseEnd_5755365 := by
    simpa [prefixWord, tailWord_5755365, baseEnd_5755365] using wordTrace_append hprefix tailTrace_5755365
  have hstable : (prefixWord ++ tailWord_5755365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755365).length < 2 ^ (prefixWord ++ tailWord_5755365).sum := by decide
  have hdescent : baseEnd_5755365 < baseStart_5755365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755431 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5755431 : Nat := 118140960795 + 5755431 * 2 ^ 59
def prefixEnd_5755431 : Nat := 4983230072969 + 3 ^ 40 * 5755431 * 2
def baseEnd_5755431 : Nat := 985100825595725527814587

theorem tailTrace_5755431 : CollatzResearch.WordTrace tailWord_5755431 prefixEnd_5755431 985100825595725527814587 := by
  unfold tailWord_5755431
  simp only [CollatzResearch.WordTrace]
  refine ⟨209917814012063911203314147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139945209341375940802209431 209917814012063911203314147)
  ·
    refine ⟨314876721018095866804971221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209917814012063911203314147 314876721018095866804971221)
    ·
      refine ⟨7379923148861621878241513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 314876721018095866804971221 7379923148861621878241513)
      ·
        refine ⟨5534942361646216408681135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379923148861621878241513 5534942361646216408681135)
        ·
          refine ⟨8302413542469324613021703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534942361646216408681135 8302413542469324613021703)
          ·
            refine ⟨12453620313703986919532555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302413542469324613021703 12453620313703986919532555)
            ·
              refine ⟨18680430470555980379298833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12453620313703986919532555 18680430470555980379298833)
              ·
                refine ⟨14010322852916985284474125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18680430470555980379298833 14010322852916985284474125)
                ·
                  refine ⟨5253871069843869481677797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14010322852916985284474125 5253871069843869481677797)
                  ·
                    refine ⟨985100825595725527814587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253871069843869481677797 985100825595725527814587)
                    ·
                      rfl

theorem cell23_5755431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5755431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755431 prefixEnd_5755431 := by exact prefixLift 5755431
  have htrace : WordTrace (prefixWord ++ tailWord_5755431) baseStart_5755431 baseEnd_5755431 := by
    simpa [prefixWord, tailWord_5755431, baseEnd_5755431] using wordTrace_append hprefix tailTrace_5755431
  have hstable : (prefixWord ++ tailWord_5755431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755431).length < 2 ^ (prefixWord ++ tailWord_5755431).sum := by decide
  have hdescent : baseEnd_5755431 < baseStart_5755431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755440 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_5755440 : Nat := 118140960795 + 5755440 * 2 ^ 59
def prefixEnd_5755440 : Nat := 4983230072969 + 3 ^ 40 * 5755440 * 2
def baseEnd_5755440 : Nat := 985102366037689016077073

theorem tailTrace_5755440 : CollatzResearch.WordTrace tailWord_5755440 prefixEnd_5755440 985102366037689016077073 := by
  unfold tailWord_5755440
  simp only [CollatzResearch.WordTrace]
  refine ⟨104959071134515652870195887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139945428179354203826927849 104959071134515652870195887)
  ·
    refine ⟨157438606701773479305293831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104959071134515652870195887 157438606701773479305293831)
    ·
      refine ⟨236157910052660218957940747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157438606701773479305293831 236157910052660218957940747)
      ·
        refine ⟨354236865078990328436911121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236157910052660218957940747 354236865078990328436911121)
        ·
          refine ⟨265677648809242746327683341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354236865078990328436911121 265677648809242746327683341)
          ·
            refine ⟨99629118303466029872881253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265677648809242746327683341 99629118303466029872881253)
            ·
              refine ⟨18680459681899880601165235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99629118303466029872881253 18680459681899880601165235)
              ·
                refine ⟨28020689522849820901747853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18680459681899880601165235 28020689522849820901747853)
                ·
                  refine ⟨10507758571068682838155445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28020689522849820901747853 10507758571068682838155445)
                  ·
                    refine ⟨985102366037689016077073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10507758571068682838155445 985102366037689016077073)
                    ·
                      rfl

theorem cell23_5755440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_5755440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755440 prefixEnd_5755440 := by exact prefixLift 5755440
  have htrace : WordTrace (prefixWord ++ tailWord_5755440) baseStart_5755440 baseEnd_5755440 := by
    simpa [prefixWord, tailWord_5755440, baseEnd_5755440] using wordTrace_append hprefix tailTrace_5755440
  have hstable : (prefixWord ++ tailWord_5755440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755440).length < 2 ^ (prefixWord ++ tailWord_5755440).sum := by decide
  have hdescent : baseEnd_5755440 < baseStart_5755440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755447 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_5755447 : Nat := 118140960795 + 5755447 * 2 ^ 59
def prefixEnd_5755447 : Nat := 4983230072969 + 3 ^ 40 * 5755447 * 2
def baseEnd_5755447 : Nat := 2955310692477648520843687

theorem tailTrace_5755447 : CollatzResearch.WordTrace tailWord_5755447 prefixEnd_5755447 2955310692477648520843687 := by
  unfold tailWord_5755447
  simp only [CollatzResearch.WordTrace]
  refine ⟨209918397580005945935896595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139945598386670630623931063 209918397580005945935896595)
  ·
    refine ⟨314877596370008918903844893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209918397580005945935896595 314877596370008918903844893)
    ·
      refine ⟨118079098638753344588941835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314877596370008918903844893 118079098638753344588941835)
      ·
        refine ⟨177118647958130016883412753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118079098638753344588941835 177118647958130016883412753)
        ·
          refine ⟨132838985968597512662559565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177118647958130016883412753 132838985968597512662559565)
          ·
            refine ⟨49814619738224067248459837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132838985968597512662559565 49814619738224067248459837)
            ·
              refine ⟨18680482401834025218172439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49814619738224067248459837 18680482401834025218172439)
              ·
                refine ⟨28020723602751037827258659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18680482401834025218172439 28020723602751037827258659)
                ·
                  refine ⟨42031085404126556740887989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28020723602751037827258659 42031085404126556740887989)
                  ·
                    refine ⟨3940414256636864694458249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42031085404126556740887989 3940414256636864694458249)
                    ·
                      refine ⟨2955310692477648520843687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940414256636864694458249 2955310692477648520843687)
                      ·
                        rfl

theorem cell23_5755447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_5755447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755447 prefixEnd_5755447 := by exact prefixLift 5755447
  have htrace : WordTrace (prefixWord ++ tailWord_5755447) baseStart_5755447 baseEnd_5755447 := by
    simpa [prefixWord, tailWord_5755447, baseEnd_5755447] using wordTrace_append hprefix tailTrace_5755447
  have hstable : (prefixWord ++ tailWord_5755447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755447).length < 2 ^ (prefixWord ++ tailWord_5755447).sum := by decide
  have hdescent : baseEnd_5755447 < baseStart_5755447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755470 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_5755470 : Nat := 118140960795 + 5755470 * 2 ^ 59
def prefixEnd_5755470 : Nat := 4983230072969 + 3 ^ 40 * 5755470 * 2
def baseEnd_5755470 : Nat := 985107500844233976952027

theorem tailTrace_5755470 : CollatzResearch.WordTrace tailWord_5755470 prefixEnd_5755470 985107500844233976952027 := by
  unfold tailWord_5755470
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239904557365327607997983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139946157639281747242655909 26239904557365327607997983)
  ·
    refine ⟨39359856836047991411996975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26239904557365327607997983 39359856836047991411996975)
    ·
      refine ⟨59039785254071987117995463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39359856836047991411996975 59039785254071987117995463)
      ·
        refine ⟨88559677881107980676993195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59039785254071987117995463 88559677881107980676993195)
        ·
          refine ⟨132839516821661971015489793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88559677881107980676993195 132839516821661971015489793)
          ·
            refine ⟨99629637616246478261617345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132839516821661971015489793 99629637616246478261617345)
            ·
              refine ⟨74722228212184858696213009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99629637616246478261617345 74722228212184858696213009)
              ·
                refine ⟨56041671159138644022159757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74722228212184858696213009 56041671159138644022159757)
                ·
                  refine ⟨21015626684676991508309909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56041671159138644022159757 21015626684676991508309909)
                  ·
                    refine ⟨985107500844233976952027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21015626684676991508309909 985107500844233976952027)
                    ·
                      rfl

theorem cell23_5755470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_5755470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755470 prefixEnd_5755470 := by exact prefixLift 5755470
  have htrace : WordTrace (prefixWord ++ tailWord_5755470) baseStart_5755470 baseEnd_5755470 := by
    simpa [prefixWord, tailWord_5755470, baseEnd_5755470] using wordTrace_append hprefix tailTrace_5755470
  have hstable : (prefixWord ++ tailWord_5755470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755470).length < 2 ^ (prefixWord ++ tailWord_5755470).sum := by decide
  have hdescent : baseEnd_5755470 < baseStart_5755470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755480 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5755480 : Nat := 118140960795 + 5755480 * 2 ^ 59
def prefixEnd_5755480 : Nat := 4983230072969 + 3 ^ 40 * 5755480 * 2
def baseEnd_5755480 : Nat := 2955327637339246891731035

theorem tailTrace_5755480 : CollatzResearch.WordTrace tailWord_5755480 prefixEnd_5755480 2955327637339246891731035 := by
  unfold tailWord_5755480
  simp only [CollatzResearch.WordTrace]
  refine ⟨104959800594443196285923947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139946400792590928381231929 104959800594443196285923947)
  ·
    refine ⟨157439700891664794428885921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104959800594443196285923947 157439700891664794428885921)
    ·
      refine ⟨118079775668748595821664441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157439700891664794428885921 118079775668748595821664441)
      ·
        refine ⟨88559831751561446866248331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118079775668748595821664441 88559831751561446866248331)
        ·
          refine ⟨132839747627342170299372497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88559831751561446866248331 132839747627342170299372497)
          ·
            refine ⟨99629810720506627724529373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132839747627342170299372497 99629810720506627724529373)
            ·
              refine ⟨37361179020189985396698515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99629810720506627724529373 37361179020189985396698515)
              ·
                refine ⟨56041768530284978095047773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37361179020189985396698515 56041768530284978095047773)
                ·
                  refine ⟨21015663198856866785642915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56041768530284978095047773 21015663198856866785642915)
                  ·
                    refine ⟨31523494798285300178464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21015663198856866785642915 31523494798285300178464373)
                    ·
                      refine ⟨2955327637339246891731035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31523494798285300178464373 2955327637339246891731035)
                      ·
                        rfl

theorem cell23_5755480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5755480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755480 prefixEnd_5755480 := by exact prefixLift 5755480
  have htrace : WordTrace (prefixWord ++ tailWord_5755480) baseStart_5755480 baseEnd_5755480 := by
    simpa [prefixWord, tailWord_5755480, baseEnd_5755480] using wordTrace_append hprefix tailTrace_5755480
  have hstable : (prefixWord ++ tailWord_5755480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755480).length < 2 ^ (prefixWord ++ tailWord_5755480).sum := by decide
  have hdescent : baseEnd_5755480 < baseStart_5755480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755487 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 2, 4]
def baseStart_5755487 : Nat := 118140960795 + 5755487 * 2 ^ 59
def prefixEnd_5755487 : Nat := 4983230072969 + 3 ^ 40 * 5755487 * 2
def baseEnd_5755487 : Nat := 985110410567942788114501

theorem tailTrace_5755487 : CollatzResearch.WordTrace tailWord_5755487 prefixEnd_5755487 985110410567942788114501 := by
  unfold tailWord_5755487
  simp only [CollatzResearch.WordTrace]
  refine ⟨209919856499861032767352715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139946570999907355178235143 209919856499861032767352715)
  ·
    refine ⟨314879784749791549151029073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209919856499861032767352715 314879784749791549151029073)
    ·
      refine ⟨236159838562343661863271805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314879784749791549151029073 236159838562343661863271805)
      ·
        refine ⟨88559939460878873198726927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236159838562343661863271805 88559939460878873198726927)
        ·
          refine ⟨132839909191318309798090391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88559939460878873198726927 132839909191318309798090391)
          ·
            refine ⟨199259863786977464697135587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132839909191318309798090391 199259863786977464697135587)
            ·
              refine ⟨298889795680466197045703381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199259863786977464697135587 298889795680466197045703381)
              ·
                refine ⟨7005229586260926493258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 298889795680466197045703381 7005229586260926493258673)
                ·
                  refine ⟨5253922189695694869944005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005229586260926493258673 5253922189695694869944005)
                  ·
                    refine ⟨985110410567942788114501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253922189695694869944005 985110410567942788114501)
                    ·
                      rfl

theorem cell23_5755487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_5755487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755487 prefixEnd_5755487 := by exact prefixLift 5755487
  have htrace : WordTrace (prefixWord ++ tailWord_5755487) baseStart_5755487 baseEnd_5755487 := by
    simpa [prefixWord, tailWord_5755487, baseEnd_5755487] using wordTrace_append hprefix tailTrace_5755487
  have hstable : (prefixWord ++ tailWord_5755487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755487).length < 2 ^ (prefixWord ++ tailWord_5755487).sum := by decide
  have hdescent : baseEnd_5755487 < baseStart_5755487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755517 : List Nat := [1, 4, 1, 1, 5, 2, 9]
def baseStart_5755517 : Nat := 118140960795 + 5755517 * 2 ^ 59
def prefixEnd_5755517 : Nat := 4983230072969 + 3 ^ 40 * 5755517 * 2
def baseEnd_5755517 : Nat := 36485760939795842555165

theorem tailTrace_5755517 : CollatzResearch.WordTrace tailWord_5755517 prefixEnd_5755517 36485760939795842555165 := by
  unfold tailWord_5755517
  simp only [CollatzResearch.WordTrace]
  refine ⟨209920950689752347890944805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139947300459834898593963203 209920950689752347890944805)
  ·
    refine ⟨39360178254328565229552151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209920950689752347890944805 39360178254328565229552151)
    ·
      refine ⟨59040267381492847844328227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39360178254328565229552151 59040267381492847844328227)
      ·
        refine ⟨88560401072239271766492341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59040267381492847844328227 88560401072239271766492341)
        ·
          refine ⟨8302537600522431728108657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88560401072239271766492341 8302537600522431728108657)
          ·
            refine ⟨6226903200391823796081493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302537600522431728108657 6226903200391823796081493)
            ·
              refine ⟨36485760939795842555165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6226903200391823796081493 36485760939795842555165)
              ·
                rfl

theorem cell23_5755517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 9].length) (baseStart_5755517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755517 prefixEnd_5755517 := by exact prefixLift 5755517
  have htrace : WordTrace (prefixWord ++ tailWord_5755517) baseStart_5755517 baseEnd_5755517 := by
    simpa [prefixWord, tailWord_5755517, baseEnd_5755517] using wordTrace_append hprefix tailTrace_5755517
  have hstable : (prefixWord ++ tailWord_5755517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755517).length < 2 ^ (prefixWord ++ tailWord_5755517).sum := by decide
  have hdescent : baseEnd_5755517 < baseStart_5755517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755522 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5755522 : Nat := 118140960795 + 5755522 * 2 ^ 59
def prefixEnd_5755522 : Nat := 4983230072969 + 3 ^ 40 * 5755522 * 2
def baseEnd_5755522 : Nat := 2955349203526735727405843

theorem tailTrace_5755522 : CollatzResearch.WordTrace tailWord_5755522 prefixEnd_5755522 2955349203526735727405843 := by
  unfold tailWord_5755522
  simp only [CollatzResearch.WordTrace]
  refine ⟨52480283263683558436219205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139947422036489489163251213 52480283263683558436219205)
  ·
    refine ⟨9840053111940667206791101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52480283263683558436219205 9840053111940667206791101)
    ·
      refine ⟨3690019916977750202546663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9840053111940667206791101 3690019916977750202546663)
      ·
        refine ⟨5535029875466625303819995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690019916977750202546663 5535029875466625303819995)
        ·
          refine ⟨8302544813199937955729993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535029875466625303819995 8302544813199937955729993)
          ·
            refine ⟨6226908609899953466797495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302544813199937955729993 6226908609899953466797495)
            ·
              refine ⟨9340362914849930200196243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226908609899953466797495 9340362914849930200196243)
              ·
                refine ⟨14010544372274895300294365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340362914849930200196243 14010544372274895300294365)
                ·
                  refine ⟨5253954139603085737610387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14010544372274895300294365 5253954139603085737610387)
                  ·
                    refine ⟨7880931209404628606415581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253954139603085737610387 7880931209404628606415581)
                    ·
                      refine ⟨2955349203526735727405843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880931209404628606415581 2955349203526735727405843)
                      ·
                        rfl

theorem cell23_5755522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5755522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755522 prefixEnd_5755522 := by exact prefixLift 5755522
  have htrace : WordTrace (prefixWord ++ tailWord_5755522) baseStart_5755522 baseEnd_5755522 := by
    simpa [prefixWord, tailWord_5755522, baseEnd_5755522] using wordTrace_append hprefix tailTrace_5755522
  have hstable : (prefixWord ++ tailWord_5755522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755522).length < 2 ^ (prefixWord ++ tailWord_5755522).sum := by decide
  have hdescent : baseEnd_5755522 < baseStart_5755522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755538 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_5755538 : Nat := 118140960795 + 5755538 * 2 ^ 59
def prefixEnd_5755538 : Nat := 4983230072969 + 3 ^ 40 * 5755538 * 2
def baseEnd_5755538 : Nat := 985119139739069221601923

theorem tailTrace_5755538 : CollatzResearch.WordTrace tailWord_5755538 prefixEnd_5755538 985119139739069221601923 := by
  unfold tailWord_5755538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52480429155669067119364817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139947811081784178984972845 52480429155669067119364817)
  ·
    refine ⟨39360321866751800339523613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52480429155669067119364817 39360321866751800339523613)
    ·
      refine ⟨14760120700031925127321355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39360321866751800339523613 14760120700031925127321355)
      ·
        refine ⟨22140181050047887690982033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760120700031925127321355 22140181050047887690982033)
        ·
          refine ⟨16605135787535915768236525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22140181050047887690982033 16605135787535915768236525)
          ·
            refine ⟨6226925920325968413088697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16605135787535915768236525 6226925920325968413088697)
            ·
              refine ⟨4670194440244476309816523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226925920325968413088697 4670194440244476309816523)
              ·
                refine ⟨7005291660366714464724785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670194440244476309816523 7005291660366714464724785)
                ·
                  refine ⟨5253968745275035848543589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005291660366714464724785 5253968745275035848543589)
                  ·
                    refine ⟨985119139739069221601923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253968745275035848543589 985119139739069221601923)
                    ·
                      rfl

theorem cell23_5755538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_5755538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755538 prefixEnd_5755538 := by exact prefixLift 5755538
  have htrace : WordTrace (prefixWord ++ tailWord_5755538) baseStart_5755538 baseEnd_5755538 := by
    simpa [prefixWord, tailWord_5755538, baseEnd_5755538] using wordTrace_append hprefix tailTrace_5755538
  have hstable : (prefixWord ++ tailWord_5755538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755538).length < 2 ^ (prefixWord ++ tailWord_5755538).sum := by decide
  have hdescent : baseEnd_5755538 < baseStart_5755538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755600 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_5755600 : Nat := 118140960795 + 5755600 * 2 ^ 59
def prefixEnd_5755600 : Nat := 4983230072969 + 3 ^ 40 * 5755600 * 2
def baseEnd_5755600 : Nat := 2955389255017786422230483

theorem tailTrace_5755600 : CollatzResearch.WordTrace tailWord_5755600 prefixEnd_5755600 2955389255017786422230483 := by
  unfold tailWord_5755600
  simp only [CollatzResearch.WordTrace]
  refine ⟨104961988974225826533108127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139949318632301102044144169 104961988974225826533108127)
  ·
    refine ⟨157442983461338739799662191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104961988974225826533108127 157442983461338739799662191)
    ·
      refine ⟨236164475192008109699493287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157442983461338739799662191 236164475192008109699493287)
      ·
        refine ⟨354246712788012164549239931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236164475192008109699493287 354246712788012164549239931)
        ·
          refine ⟨531370069182018246823859897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354246712788012164549239931 531370069182018246823859897)
          ·
            refine ⟨398527551886513685117894923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531370069182018246823859897 398527551886513685117894923)
            ·
              refine ⟨597791327829770527676842385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398527551886513685117894923 597791327829770527676842385)
              ·
                refine ⟨448343495872327895757631789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597791327829770527676842385 448343495872327895757631789)
                ·
                  refine ⟨168128810952122960909111921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448343495872327895757631789 168128810952122960909111921)
                  ·
                    refine ⟨126096608214092220681833941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168128810952122960909111921 126096608214092220681833941)
                    ·
                      refine ⟨2955389255017786422230483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126096608214092220681833941 2955389255017786422230483)
                      ·
                        rfl

theorem cell23_5755600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_5755600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755600 prefixEnd_5755600 := by exact prefixLift 5755600
  have htrace : WordTrace (prefixWord ++ tailWord_5755600) baseStart_5755600 baseEnd_5755600 := by
    simpa [prefixWord, tailWord_5755600, baseEnd_5755600] using wordTrace_append hprefix tailTrace_5755600
  have hstable : (prefixWord ++ tailWord_5755600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755600).length < 2 ^ (prefixWord ++ tailWord_5755600).sum := by decide
  have hdescent : baseEnd_5755600 < baseStart_5755600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755601 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_5755601 : Nat := 118140960795 + 5755601 * 2 ^ 59
def prefixEnd_5755601 : Nat := 4983230072969 + 3 ^ 40 * 5755601 * 2
def baseEnd_5755601 : Nat := 2955389768498440918317979

theorem tailTrace_5755601 : CollatzResearch.WordTrace tailWord_5755601 prefixEnd_5755601 2955389768498440918317979 := by
  unfold tailWord_5755601
  simp only [CollatzResearch.WordTrace]
  refine ⟨209924014421448030237002657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139949342947632020158001771 209924014421448030237002657)
  ·
    refine ⟨157443010816086022677751993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209924014421448030237002657 157443010816086022677751993)
    ·
      refine ⟨118082258112064517008313995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157443010816086022677751993 118082258112064517008313995)
      ·
        refine ⟨177123387168096775512470993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118082258112064517008313995 177123387168096775512470993)
        ·
          refine ⟨132842540376072581634353245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177123387168096775512470993 132842540376072581634353245)
          ·
            refine ⟨49815952641027218112882467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132842540376072581634353245 49815952641027218112882467)
            ·
              refine ⟨74723928961540827169323701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49815952641027218112882467 74723928961540827169323701)
              ·
                refine ⟨7005368340144452547124097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74723928961540827169323701 7005368340144452547124097)
                ·
                  refine ⟨5254026255108339410343073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005368340144452547124097 5254026255108339410343073)
                  ·
                    refine ⟨3940519691331254557757305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254026255108339410343073 3940519691331254557757305)
                    ·
                      refine ⟨2955389768498440918317979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940519691331254557757305 2955389768498440918317979)
                      ·
                        rfl

theorem cell23_5755601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_5755601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755601 prefixEnd_5755601 := by exact prefixLift 5755601
  have htrace : WordTrace (prefixWord ++ tailWord_5755601) baseStart_5755601 baseEnd_5755601 := by
    simpa [prefixWord, tailWord_5755601, baseEnd_5755601] using wordTrace_append hprefix tailTrace_5755601
  have hstable : (prefixWord ++ tailWord_5755601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755601).length < 2 ^ (prefixWord ++ tailWord_5755601).sum := by decide
  have hdescent : baseEnd_5755601 < baseStart_5755601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755607 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 7]
def baseStart_5755607 : Nat := 118140960795 + 5755607 * 2 ^ 59
def prefixEnd_5755607 : Nat := 4983230072969 + 3 ^ 40 * 5755607 * 2
def baseEnd_5755607 : Nat := 328376983264707543871439

theorem tailTrace_5755607 : CollatzResearch.WordTrace tailWord_5755607 prefixEnd_5755607 328376983264707543871439 := by
  unfold tailWord_5755607
  simp only [CollatzResearch.WordTrace]
  refine ⟨209924233259426293261721075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139949488839617528841147383 209924233259426293261721075)
  ·
    refine ⟨314886349889139439892581613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209924233259426293261721075 314886349889139439892581613)
    ·
      refine ⟨118082381208427289959718105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314886349889139439892581613 118082381208427289959718105)
      ·
        refine ⟨88561785906320467469788579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118082381208427289959718105 88561785906320467469788579)
        ·
          refine ⟨132842678859480701204682869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88561785906320467469788579 132842678859480701204682869)
          ·
            refine ⟨12454001143076315737939019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132842678859480701204682869 12454001143076315737939019)
            ·
              refine ⟨18681001714614473606908529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454001143076315737939019 18681001714614473606908529)
              ·
                refine ⟨14010751285960855205181397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18681001714614473606908529 14010751285960855205181397)
                ·
                  refine ⟨328376983264707543871439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14010751285960855205181397 328376983264707543871439)
                  ·
                    rfl

theorem cell23_5755607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 7].length) (baseStart_5755607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755607 prefixEnd_5755607 := by exact prefixLift 5755607
  have htrace : WordTrace (prefixWord ++ tailWord_5755607) baseStart_5755607 baseEnd_5755607 := by
    simpa [prefixWord, tailWord_5755607, baseEnd_5755607] using wordTrace_append hprefix tailTrace_5755607
  have hstable : (prefixWord ++ tailWord_5755607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755607).length < 2 ^ (prefixWord ++ tailWord_5755607).sum := by decide
  have hdescent : baseEnd_5755607 < baseStart_5755607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755634 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5755634 : Nat := 118140960795 + 5755634 * 2 ^ 59
def prefixEnd_5755634 : Nat := 4983230072969 + 3 ^ 40 * 5755634 * 2
def baseEnd_5755634 : Nat := 2955406713360039289205327

theorem tailTrace_5755634 : CollatzResearch.WordTrace tailWord_5755634 prefixEnd_5755634 2955406713360039289205327 := by
  unfold tailWord_5755634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52481304507582119218238489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139950145353552317915302637 52481304507582119218238489)
  ·
    refine ⟨39360978380686589413678867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52481304507582119218238489 39360978380686589413678867)
    ·
      refine ⟨59041467571029884120518301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39360978380686589413678867 59041467571029884120518301)
      ·
        refine ⟨22140550339136206545194363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59041467571029884120518301 22140550339136206545194363)
        ·
          refine ⟨33210825508704309817791545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22140550339136206545194363 33210825508704309817791545)
          ·
            refine ⟨24908119131528232363343659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33210825508704309817791545 24908119131528232363343659)
            ·
              refine ⟨37362178697292348545015489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24908119131528232363343659 37362178697292348545015489)
              ·
                refine ⟨28021634022969261408761617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37362178697292348545015489 28021634022969261408761617)
                ·
                  refine ⟨21016225517226946056571213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28021634022969261408761617 21016225517226946056571213)
                  ·
                    refine ⟨7881084568960104771214205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21016225517226946056571213 7881084568960104771214205)
                    ·
                      refine ⟨2955406713360039289205327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881084568960104771214205 2955406713360039289205327)
                      ·
                        rfl

theorem cell23_5755634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5755634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755634 prefixEnd_5755634 := by exact prefixLift 5755634
  have htrace : WordTrace (prefixWord ++ tailWord_5755634) baseStart_5755634 baseEnd_5755634 := by
    simpa [prefixWord, tailWord_5755634, baseEnd_5755634] using wordTrace_append hprefix tailTrace_5755634
  have hstable : (prefixWord ++ tailWord_5755634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755634).length < 2 ^ (prefixWord ++ tailWord_5755634).sum := by decide
  have hdescent : baseEnd_5755634 < baseStart_5755634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755657 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_5755657 : Nat := 118140960795 + 5755657 * 2 ^ 59
def prefixEnd_5755657 : Nat := 4983230072969 + 3 ^ 40 * 5755657 * 2
def baseEnd_5755657 : Nat := 2955418523415092699217721

theorem tailTrace_5755657 : CollatzResearch.WordTrace tailWord_5755657 prefixEnd_5755657 2955418523415092699217721 := by
  unfold tailWord_5755657
  simp only [CollatzResearch.WordTrace]
  refine ⟨209926056909245151801041225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139950704606163434534027483 209926056909245151801041225)
  ·
    refine ⟨157444542681933863850780919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209926056909245151801041225 157444542681933863850780919)
    ·
      refine ⟨236166814022900795776171379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157444542681933863850780919 236166814022900795776171379)
      ·
        refine ⟨354250221034351193664257069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236166814022900795776171379 354250221034351193664257069)
        ·
          refine ⟨132843832887881697624096401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354250221034351193664257069 132843832887881697624096401)
          ·
            refine ⟨99632874665911273218072301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132843832887881697624096401 99632874665911273218072301)
            ·
              refine ⟨37362327999716727456777113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99632874665911273218072301 37362327999716727456777113)
              ·
                refine ⟨28021745999787545592582835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37362327999716727456777113 28021745999787545592582835)
                ·
                  refine ⟨42032618999681318388874253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28021745999787545592582835 42032618999681318388874253)
                  ·
                    refine ⟨15762232124880494395827845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42032618999681318388874253 15762232124880494395827845)
                    ·
                      refine ⟨2955418523415092699217721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15762232124880494395827845 2955418523415092699217721)
                      ·
                        rfl

theorem cell23_5755657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_5755657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755657 prefixEnd_5755657 := by exact prefixLift 5755657
  have htrace : WordTrace (prefixWord ++ tailWord_5755657) baseStart_5755657 baseEnd_5755657 := by
    simpa [prefixWord, tailWord_5755657, baseEnd_5755657] using wordTrace_append hprefix tailTrace_5755657
  have hstable : (prefixWord ++ tailWord_5755657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755657).length < 2 ^ (prefixWord ++ tailWord_5755657).sum := by decide
  have hdescent : baseEnd_5755657 < baseStart_5755657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755674 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_5755674 : Nat := 118140960795 + 5755674 * 2 ^ 59
def prefixEnd_5755674 : Nat := 4983230072969 + 3 ^ 40 * 5755674 * 2
def baseEnd_5755674 : Nat := 2955427252586219132705143

theorem tailTrace_5755674 : CollatzResearch.WordTrace tailWord_5755674 prefixEnd_5755674 2955427252586219132705143 := by
  unfold tailWord_5755674
  simp only [CollatzResearch.WordTrace]
  refine ⟨52481669237545890926102519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139951117966789042469606717 52481669237545890926102519)
  ·
    refine ⟨78722503856318836389153779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52481669237545890926102519 78722503856318836389153779)
    ·
      refine ⟨118083755784478254583730669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78722503856318836389153779 118083755784478254583730669)
      ·
        refine ⟨44281408419179345468899001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118083755784478254583730669 44281408419179345468899001)
        ·
          refine ⟨33211056314384509101674251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44281408419179345468899001 33211056314384509101674251)
          ·
            refine ⟨49816584471576763652511377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33211056314384509101674251 49816584471576763652511377)
            ·
              refine ⟨37362438353682572739383533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49816584471576763652511377 37362438353682572739383533)
              ·
                refine ⟨14010914382630964777268825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37362438353682572739383533 14010914382630964777268825)
                ·
                  refine ⟨10508185786973223582951619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14010914382630964777268825 10508185786973223582951619)
                  ·
                    refine ⟨15762278680459835374427429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10508185786973223582951619 15762278680459835374427429)
                    ·
                      refine ⟨2955427252586219132705143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15762278680459835374427429 2955427252586219132705143)
                      ·
                        rfl

theorem cell23_5755674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_5755674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755674 prefixEnd_5755674 := by exact prefixLift 5755674
  have htrace : WordTrace (prefixWord ++ tailWord_5755674) baseStart_5755674 baseEnd_5755674 := by
    simpa [prefixWord, tailWord_5755674, baseEnd_5755674] using wordTrace_append hprefix tailTrace_5755674
  have hstable : (prefixWord ++ tailWord_5755674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755674).length < 2 ^ (prefixWord ++ tailWord_5755674).sum := by decide
  have hdescent : baseEnd_5755674 < baseStart_5755674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755697 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 8]
def baseStart_5755697 : Nat := 118140960795 + 5755697 * 2 ^ 59
def prefixEnd_5755697 : Nat := 4983230072969 + 3 ^ 40 * 5755697 * 2
def baseEnd_5755697 : Nat := 328382118071252504746393

theorem tailTrace_5755697 : CollatzResearch.WordTrace tailWord_5755697 prefixEnd_5755697 328382118071252504746393 := by
  unfold tailWord_5755697
  simp only [CollatzResearch.WordTrace]
  refine ⟨209927515829100238632497345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139951677219400159088331563 209927515829100238632497345)
  ·
    refine ⟨157445636871825178974373009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209927515829100238632497345 157445636871825178974373009)
    ·
      refine ⟨118084227653868884230779757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157445636871825178974373009 118084227653868884230779757)
      ·
        refine ⟨44281585370200831586542409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118084227653868884230779757 44281585370200831586542409)
        ·
          refine ⟨33211189027650623689906807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44281585370200831586542409 33211189027650623689906807)
          ·
            refine ⟨49816783541475935534860211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33211189027650623689906807 49816783541475935534860211)
            ·
              refine ⟨74725175312213903302290317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49816783541475935534860211 74725175312213903302290317)
              ·
                refine ⟨28021940742080213738358869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74725175312213903302290317 28021940742080213738358869)
                ·
                  refine ⟨328382118071252504746393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28021940742080213738358869 328382118071252504746393)
                  ·
                    rfl

theorem cell23_5755697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_5755697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755697 prefixEnd_5755697 := by exact prefixLift 5755697
  have htrace : WordTrace (prefixWord ++ tailWord_5755697) baseStart_5755697 baseEnd_5755697 := by
    simpa [prefixWord, tailWord_5755697, baseEnd_5755697] using wordTrace_append hprefix tailTrace_5755697
  have hstable : (prefixWord ++ tailWord_5755697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755697).length < 2 ^ (prefixWord ++ tailWord_5755697).sum := by decide
  have hdescent : baseEnd_5755697 < baseStart_5755697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755701 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5755701 : Nat := 118140960795 + 5755701 * 2 ^ 59
def prefixEnd_5755701 : Nat := 4983230072969 + 3 ^ 40 * 5755701 * 2
def baseEnd_5755701 : Nat := 985147038854630175689173

theorem tailTrace_5755701 : CollatzResearch.WordTrace tailWord_5755701 prefixEnd_5755701 985147038854630175689173 := by
  unfold tailWord_5755701
  simp only [CollatzResearch.WordTrace]
  refine ⟨209927661721085747315642957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139951774480723831543761971 209927661721085747315642957)
  ·
    refine ⟨78722873145407155243366109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209927661721085747315642957 78722873145407155243366109)
    ·
      refine ⟨29521077429527683216262291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78722873145407155243366109 29521077429527683216262291)
      ·
        refine ⟨44281616144291524824393437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29521077429527683216262291 44281616144291524824393437)
        ·
          refine ⟨16605606054109321809147539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44281616144291524824393437 16605606054109321809147539)
          ·
            refine ⟨24908409081163982713721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605606054109321809147539 24908409081163982713721309)
            ·
              refine ⟨9340653405436493517645491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24908409081163982713721309 9340653405436493517645491)
              ·
                refine ⟨14010980108154740276468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340653405436493517645491 14010980108154740276468237)
                ·
                  refine ⟨5254117540558027603675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14010980108154740276468237 5254117540558027603675589)
                  ·
                    refine ⟨985147038854630175689173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254117540558027603675589 985147038854630175689173)
                    ·
                      rfl

theorem cell23_5755701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5755701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755701 prefixEnd_5755701 := by exact prefixLift 5755701
  have htrace : WordTrace (prefixWord ++ tailWord_5755701) baseStart_5755701 baseEnd_5755701 := by
    simpa [prefixWord, tailWord_5755701, baseEnd_5755701] using wordTrace_append hprefix tailTrace_5755701
  have hstable : (prefixWord ++ tailWord_5755701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755701).length < 2 ^ (prefixWord ++ tailWord_5755701).sum := by decide
  have hdescent : baseEnd_5755701 < baseStart_5755701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755787 : List Nat := [1, 1, 1, 1, 4, 2, 2, 11]
def baseStart_5755787 : Nat := 118140960795 + 5755787 * 2 ^ 59
def prefixEnd_5755787 : Nat := 4983230072969 + 3 ^ 40 * 5755787 * 2
def baseEnd_5755787 : Nat := 109462417625932488540449

theorem tailTrace_5755787 : CollatzResearch.WordTrace tailWord_5755787 prefixEnd_5755787 109462417625932488540449 := by
  unfold tailWord_5755787
  simp only [CollatzResearch.WordTrace]
  refine ⟨209930798398774184003273615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139953865599182789335515743 209930798398774184003273615)
  ·
    refine ⟨314896197598161276004910423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209930798398774184003273615 314896197598161276004910423)
    ·
      refine ⟨472344296397241914007365635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314896197598161276004910423 472344296397241914007365635)
      ·
        refine ⟨708516444595862871011048453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472344296397241914007365635 708516444595862871011048453)
        ·
          refine ⟨132846833361724288314571585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 708516444595862871011048453 132846833361724288314571585)
          ·
            refine ⟨99635125021293216235928689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132846833361724288314571585 99635125021293216235928689)
            ·
              refine ⟨74726343765969912176946517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99635125021293216235928689 74726343765969912176946517)
              ·
                refine ⟨109462417625932488540449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74726343765969912176946517 109462417625932488540449)
                ·
                  rfl

theorem cell23_5755787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 11].length) (baseStart_5755787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755787 prefixEnd_5755787 := by exact prefixLift 5755787
  have htrace : WordTrace (prefixWord ++ tailWord_5755787) baseStart_5755787 baseEnd_5755787 := by
    simpa [prefixWord, tailWord_5755787, baseEnd_5755787] using wordTrace_append hprefix tailTrace_5755787
  have hstable : (prefixWord ++ tailWord_5755787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755787).length < 2 ^ (prefixWord ++ tailWord_5755787).sum := by decide
  have hdescent : baseEnd_5755787 < baseStart_5755787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755825 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_5755825 : Nat := 118140960795 + 5755825 * 2 ^ 59
def prefixEnd_5755825 : Nat := 4983230072969 + 3 ^ 40 * 5755825 * 2
def baseEnd_5755825 : Nat := 985168262721682680638983

theorem tailTrace_5755825 : CollatzResearch.WordTrace tailWord_5755825 prefixEnd_5755825 985168262721682680638983 := by
  unfold tailWord_5755825
  simp only [CollatzResearch.WordTrace]
  refine ⟨209932184372636516493156929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139954789581757677662104619 209932184372636516493156929)
  ·
    refine ⟨157449138279477387369867697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209932184372636516493156929 157449138279477387369867697)
    ·
      refine ⟨118086853709608040527400773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157449138279477387369867697 118086853709608040527400773)
      ·
        refine ⟨22141285070551507598887645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118086853709608040527400773 22141285070551507598887645)
        ·
          refine ⟨8302981901456815349582867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22141285070551507598887645 8302981901456815349582867)
          ·
            refine ⟨12454472852185223024374301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302981901456815349582867 12454472852185223024374301)
            ·
              refine ⟨4670427319569458634140363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12454472852185223024374301 4670427319569458634140363)
              ·
                refine ⟨7005640979354187951210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670427319569458634140363 7005640979354187951210545)
                ·
                  refine ⟨5254230734515640963407909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005640979354187951210545 5254230734515640963407909)
                  ·
                    refine ⟨985168262721682680638983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254230734515640963407909 985168262721682680638983)
                    ·
                      rfl

theorem cell23_5755825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_5755825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755825 prefixEnd_5755825 := by exact prefixLift 5755825
  have htrace : WordTrace (prefixWord ++ tailWord_5755825) baseStart_5755825 baseEnd_5755825 := by
    simpa [prefixWord, tailWord_5755825, baseEnd_5755825] using wordTrace_append hprefix tailTrace_5755825
  have hstable : (prefixWord ++ tailWord_5755825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755825).length < 2 ^ (prefixWord ++ tailWord_5755825).sum := by decide
  have hdescent : baseEnd_5755825 < baseStart_5755825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755828 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5755828 : Nat := 118140960795 + 5755828 * 2 ^ 59
def prefixEnd_5755828 : Nat := 4983230072969 + 3 ^ 40 * 5755828 * 2
def baseEnd_5755828 : Nat := 2955506328607011530179435

theorem tailTrace_5755828 : CollatzResearch.WordTrace tailWord_5755828 prefixEnd_5755828 2955506328607011530179435 := by
  unfold tailWord_5755828
  simp only [CollatzResearch.WordTrace]
  refine ⟨104966146895812824002758069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139954862527750432003677425 104966146895812824002758069)
  ·
    refine ⟨9840576271482452250258569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104966146895812824002758069 9840576271482452250258569)
    ·
      refine ⟨7380432203611839187693927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9840576271482452250258569 7380432203611839187693927)
      ·
        refine ⟨11070648305417758781540891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380432203611839187693927 11070648305417758781540891)
        ·
          refine ⟨16605972458126638172311337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070648305417758781540891 16605972458126638172311337)
          ·
            refine ⟨12454479343594978629233503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16605972458126638172311337 12454479343594978629233503)
            ·
              refine ⟨18681719015392467943850255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454479343594978629233503 18681719015392467943850255)
              ·
                refine ⟨28022578523088701915775383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18681719015392467943850255 28022578523088701915775383)
                ·
                  refine ⟨42033867784633052873663075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28022578523088701915775383 42033867784633052873663075)
                  ·
                    refine ⟨63050801676949579310494613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42033867784633052873663075 63050801676949579310494613)
                    ·
                      refine ⟨2955506328607011530179435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63050801676949579310494613 2955506328607011530179435)
                      ·
                        rfl

theorem cell23_5755828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5755828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755828 prefixEnd_5755828 := by exact prefixLift 5755828
  have htrace : WordTrace (prefixWord ++ tailWord_5755828) baseStart_5755828 baseEnd_5755828 := by
    simpa [prefixWord, tailWord_5755828, baseEnd_5755828] using wordTrace_append hprefix tailTrace_5755828
  have hstable : (prefixWord ++ tailWord_5755828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755828).length < 2 ^ (prefixWord ++ tailWord_5755828).sum := by decide
  have hdescent : baseEnd_5755828 < baseStart_5755828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755831 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_5755831 : Nat := 118140960795 + 5755831 * 2 ^ 59
def prefixEnd_5755831 : Nat := 4983230072969 + 3 ^ 40 * 5755831 * 2
def baseEnd_5755831 : Nat := 2955507869048975018441921

theorem tailTrace_5755831 : CollatzResearch.WordTrace tailWord_5755831 prefixEnd_5755831 2955507869048975018441921 := by
  unfold tailWord_5755831
  simp only [CollatzResearch.WordTrace]
  refine ⟨209932403210614779517875347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139954935473743186345250231 209932403210614779517875347)
  ·
    refine ⟨314898604815922169276813021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209932403210614779517875347 314898604815922169276813021)
    ·
      refine ⟨118086976805970813478804883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314898604815922169276813021 118086976805970813478804883)
      ·
        refine ⟨177130465208956220218207325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118086976805970813478804883 177130465208956220218207325)
        ·
          refine ⟨66423924453358582581827747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177130465208956220218207325 66423924453358582581827747)
          ·
            refine ⟨99635886680037873872741621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66423924453358582581827747 99635886680037873872741621)
            ·
              refine ⟨9340864376253550675569527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99635886680037873872741621 9340864376253550675569527)
              ·
                refine ⟨14011296564380326013354291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340864376253550675569527 14011296564380326013354291)
                ·
                  refine ⟨21016944846570489020031437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14011296564380326013354291 21016944846570489020031437)
                  ·
                    refine ⟨7881354317463933382511789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21016944846570489020031437 7881354317463933382511789)
                    ·
                      refine ⟨2955507869048975018441921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881354317463933382511789 2955507869048975018441921)
                      ·
                        rfl

theorem cell23_5755831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_5755831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755831 prefixEnd_5755831 := by exact prefixLift 5755831
  have htrace : WordTrace (prefixWord ++ tailWord_5755831) baseStart_5755831 baseEnd_5755831 := by
    simpa [prefixWord, tailWord_5755831, baseEnd_5755831] using wordTrace_append hprefix tailTrace_5755831
  have hstable : (prefixWord ++ tailWord_5755831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755831).length < 2 ^ (prefixWord ++ tailWord_5755831).sum := by decide
  have hdescent : baseEnd_5755831 < baseStart_5755831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755882 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_5755882 : Nat := 118140960795 + 5755882 * 2 ^ 59
def prefixEnd_5755882 : Nat := 4983230072969 + 3 ^ 40 * 5755882 * 2
def baseEnd_5755882 : Nat := 2955534056562354318904187

theorem tailTrace_5755882 : CollatzResearch.WordTrace tailWord_5755882 prefixEnd_5755882 2955534056562354318904187 := by
  unfold tailWord_5755882
  simp only [CollatzResearch.WordTrace]
  refine ⟨52483565833357503806995475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139956175555620010151987933 52483565833357503806995475)
  ·
    refine ⟨78725348750036255710493213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52483565833357503806995475 78725348750036255710493213)
    ·
      refine ⟨29522005781263595891434955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78725348750036255710493213 29522005781263595891434955)
      ·
        refine ⟨44283008671895393837152433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29522005781263595891434955 44283008671895393837152433)
        ·
          refine ⟨33212256503921545377864325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44283008671895393837152433 33212256503921545377864325)
          ·
            refine ⟨6227298094485289758349561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33212256503921545377864325 6227298094485289758349561)
            ·
              refine ⟨4670473570863967318762171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227298094485289758349561 4670473570863967318762171)
              ·
                refine ⟨7005710356295950978143257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670473570863967318762171 7005710356295950978143257)
                ·
                  refine ⟨5254282767221963233607443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005710356295950978143257 5254282767221963233607443)
                  ·
                    refine ⟨7881424150832944850411165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254282767221963233607443 7881424150832944850411165)
                    ·
                      refine ⟨2955534056562354318904187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881424150832944850411165 2955534056562354318904187)
                      ·
                        rfl

theorem cell23_5755882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_5755882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755882 prefixEnd_5755882 := by exact prefixLift 5755882
  have htrace : WordTrace (prefixWord ++ tailWord_5755882) baseStart_5755882 baseEnd_5755882 := by
    simpa [prefixWord, tailWord_5755882, baseEnd_5755882] using wordTrace_append hprefix tailTrace_5755882
  have hstable : (prefixWord ++ tailWord_5755882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755882).length < 2 ^ (prefixWord ++ tailWord_5755882).sum := by decide
  have hdescent : baseEnd_5755882 < baseStart_5755882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755928 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 5]
def baseStart_5755928 : Nat := 118140960795 + 5755928 * 2 ^ 59
def prefixEnd_5755928 : Nat := 4983230072969 + 3 ^ 40 * 5755928 * 2
def baseEnd_5755928 : Nat := 328395297408051237658775

theorem tailTrace_5755928 : CollatzResearch.WordTrace tailWord_5755928 prefixEnd_5755928 328395297408051237658775 := by
  unfold tailWord_5755928
  simp only [CollatzResearch.WordTrace]
  refine ⟨104967970545631682542078219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139957294060842243389437625 104967970545631682542078219)
  ·
    refine ⟨157451955818447523813117329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104967970545631682542078219 157451955818447523813117329)
    ·
      refine ⟨118088966863835642859837997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157451955818447523813117329 118088966863835642859837997)
      ·
        refine ⟨44283362573938366072439249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118088966863835642859837997 44283362573938366072439249)
        ·
          refine ⟨33212521930453774554329437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44283362573938366072439249 33212521930453774554329437)
          ·
            refine ⟨12454695723920165457873539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33212521930453774554329437 12454695723920165457873539)
            ·
              refine ⟨18682043585880248186810309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454695723920165457873539 18682043585880248186810309)
              ·
                refine ⟨3502883172352546535026933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18682043585880248186810309 3502883172352546535026933)
                ·
                  refine ⟨328395297408051237658775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3502883172352546535026933 328395297408051237658775)
                  ·
                    rfl

theorem cell23_5755928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 5].length) (baseStart_5755928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755928 prefixEnd_5755928 := by exact prefixLift 5755928
  have htrace : WordTrace (prefixWord ++ tailWord_5755928) baseStart_5755928 baseEnd_5755928 := by
    simpa [prefixWord, tailWord_5755928, baseEnd_5755928] using wordTrace_append hprefix tailTrace_5755928
  have hstable : (prefixWord ++ tailWord_5755928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755928).length < 2 ^ (prefixWord ++ tailWord_5755928).sum := by decide
  have hdescent : baseEnd_5755928 < baseStart_5755928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755938 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_5755938 : Nat := 118140960795 + 5755938 * 2 ^ 59
def prefixEnd_5755938 : Nat := 4983230072969 + 3 ^ 40 * 5755938 * 2
def baseEnd_5755938 : Nat := 2955562811479006099803929

theorem tailTrace_5755938 : CollatzResearch.WordTrace tailWord_5755938 prefixEnd_5755938 2955562811479006099803929 := by
  unfold tailWord_5755938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484076455306784198005117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139957537214151424528013645 52484076455306784198005117)
  ·
    refine ⟨19681528670740044074251919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52484076455306784198005117 19681528670740044074251919)
    ·
      refine ⟨29522293006110066111377879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19681528670740044074251919 29522293006110066111377879)
      ·
        refine ⟨44283439509165099167066819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29522293006110066111377879 44283439509165099167066819)
        ·
          refine ⟨66425159263747648750600229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44283439509165099167066819 66425159263747648750600229)
          ·
            refine ⟨12454717361952684140737543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66425159263747648750600229 12454717361952684140737543)
            ·
              refine ⟨18682076042929026211106315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454717361952684140737543 18682076042929026211106315)
              ·
                refine ⟨28023114064393539316659473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18682076042929026211106315 28023114064393539316659473)
                ·
                  refine ⟨21017335548295154487494605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28023114064393539316659473 21017335548295154487494605)
                  ·
                    refine ⟨7881500830610682932810477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21017335548295154487494605 7881500830610682932810477)
                    ·
                      refine ⟨2955562811479006099803929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881500830610682932810477 2955562811479006099803929)
                      ·
                        rfl

theorem cell23_5755938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_5755938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755938 prefixEnd_5755938 := by exact prefixLift 5755938
  have htrace : WordTrace (prefixWord ++ tailWord_5755938) baseStart_5755938 baseEnd_5755938 := by
    simpa [prefixWord, tailWord_5755938, baseEnd_5755938] using wordTrace_append hprefix tailTrace_5755938
  have hstable : (prefixWord ++ tailWord_5755938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755938).length < 2 ^ (prefixWord ++ tailWord_5755938).sum := by decide
  have hdescent : baseEnd_5755938 < baseStart_5755938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755958 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5755958 : Nat := 118140960795 + 5755958 * 2 ^ 59
def prefixEnd_5755958 : Nat := 4983230072969 + 3 ^ 40 * 5755958 * 2
def baseEnd_5755958 : Nat := 985191027030698673851279

theorem tailTrace_5755958 : CollatzResearch.WordTrace tailWord_5755958 prefixEnd_5755958 985191027030698673851279 := by
  unfold tailWord_5755958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121064705072167512984283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139958023520769786805165685 13121064705072167512984283)
  ·
    refine ⟨19681597057608251269476425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13121064705072167512984283 19681597057608251269476425)
    ·
      refine ⟨14761197793206188452107319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19681597057608251269476425 14761197793206188452107319)
      ·
        refine ⟨22141796689809282678160979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14761197793206188452107319 22141796689809282678160979)
        ·
          refine ⟨33212695034713924017241469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22141796689809282678160979 33212695034713924017241469)
          ·
            refine ⟨12454760638017721506465551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33212695034713924017241469 12454760638017721506465551)
            ·
              refine ⟨18682140957026582259698327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454760638017721506465551 18682140957026582259698327)
              ·
                refine ⟨28023211435539873389547491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18682140957026582259698327 28023211435539873389547491)
                ·
                  refine ⟨42034817153309810084321237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28023211435539873389547491 42034817153309810084321237)
                  ·
                    refine ⟨985191027030698673851279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42034817153309810084321237 985191027030698673851279)
                    ·
                      rfl

theorem cell23_5755958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5755958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755958 prefixEnd_5755958 := by exact prefixLift 5755958
  have htrace : WordTrace (prefixWord ++ tailWord_5755958) baseStart_5755958 baseEnd_5755958 := by
    simpa [prefixWord, tailWord_5755958, baseEnd_5755958] using wordTrace_append hprefix tailTrace_5755958
  have hstable : (prefixWord ++ tailWord_5755958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755958).length < 2 ^ (prefixWord ++ tailWord_5755958).sum := by decide
  have hdescent : baseEnd_5755958 < baseStart_5755958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755971 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 5, 4]
def baseStart_5755971 : Nat := 118140960795 + 5755971 * 2 ^ 59
def prefixEnd_5755971 : Nat := 4983230072969 + 3 ^ 40 * 5755971 * 2
def baseEnd_5755971 : Nat := 985193252113534823563759

theorem tailTrace_5755971 : CollatzResearch.WordTrace tailWord_5755971 prefixEnd_5755971 985193252113534823563759 := by
  unfold tailWord_5755971
  simp only [CollatzResearch.WordTrace]
  refine ⟨209937509430107583427971767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139958339620071722285314511 209937509430107583427971767)
  ·
    refine ⟨314906264145161375141957651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209937509430107583427971767 314906264145161375141957651)
    ·
      refine ⟨472359396217742062712936477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314906264145161375141957651 472359396217742062712936477)
      ·
        refine ⟨177134773581653273517351179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472359396217742062712936477 177134773581653273517351179)
        ·
          refine ⟨265702160372479910276026769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177134773581653273517351179 265702160372479910276026769)
          ·
            refine ⟨199276620279359932707020077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265702160372479910276026769 199276620279359932707020077)
            ·
              refine ⟨74728732604759974765132529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199276620279359932707020077 74728732604759974765132529)
              ·
                refine ⟨56046549453569981073849397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74728732604759974765132529 56046549453569981073849397)
                ·
                  refine ⟨5254364011272185725673381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56046549453569981073849397 5254364011272185725673381)
                  ·
                    refine ⟨985193252113534823563759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254364011272185725673381 985193252113534823563759)
                    ·
                      rfl

theorem cell23_5755971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 4].length) (baseStart_5755971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755971 prefixEnd_5755971 := by exact prefixLift 5755971
  have htrace : WordTrace (prefixWord ++ tailWord_5755971) baseStart_5755971 baseEnd_5755971 := by
    simpa [prefixWord, tailWord_5755971, baseEnd_5755971] using wordTrace_append hprefix tailTrace_5755971
  have hstable : (prefixWord ++ tailWord_5755971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755971).length < 2 ^ (prefixWord ++ tailWord_5755971).sum := by decide
  have hdescent : baseEnd_5755971 < baseStart_5755971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755978 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_5755978 : Nat := 118140960795 + 5755978 * 2 ^ 59
def prefixEnd_5755978 : Nat := 4983230072969 + 3 ^ 40 * 5755978 * 2
def baseEnd_5755978 : Nat := 2955583350705185943303745

theorem tailTrace_5755978 : CollatzResearch.WordTrace tailWord_5755978 prefixEnd_5755978 2955583350705185943303745 := by
  unfold tailWord_5755978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484441185270555905869147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139958509827388149082317725 52484441185270555905869147)
  ·
    refine ⟨78726661777905833858803721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52484441185270555905869147 78726661777905833858803721)
    ·
      refine ⟨59044996333429375394102791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78726661777905833858803721 59044996333429375394102791)
      ·
        refine ⟨88567494500144063091154187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59044996333429375394102791 88567494500144063091154187)
        ·
          refine ⟨132851241750216094636731281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88567494500144063091154187 132851241750216094636731281)
          ·
            refine ⟨99638431312662070977548461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132851241750216094636731281 99638431312662070977548461)
            ·
              refine ⟨37364411742248276616580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99638431312662070977548461 37364411742248276616580673)
              ·
                refine ⟨28023308806686207462435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37364411742248276616580673 28023308806686207462435505)
                ·
                  refine ⟨21017481605014655596826629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28023308806686207462435505 21017481605014655596826629)
                  ·
                    refine ⟨3940777800940247924404993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21017481605014655596826629 3940777800940247924404993)
                    ·
                      refine ⟨2955583350705185943303745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940777800940247924404993 2955583350705185943303745)
                      ·
                        rfl

theorem cell23_5755978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_5755978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755978 prefixEnd_5755978 := by exact prefixLift 5755978
  have htrace : WordTrace (prefixWord ++ tailWord_5755978) baseStart_5755978 baseEnd_5755978 := by
    simpa [prefixWord, tailWord_5755978, baseEnd_5755978] using wordTrace_append hprefix tailTrace_5755978
  have hstable : (prefixWord ++ tailWord_5755978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755978).length < 2 ^ (prefixWord ++ tailWord_5755978).sum := by decide
  have hdescent : baseEnd_5755978 < baseStart_5755978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755988 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_5755988 : Nat := 118140960795 + 5755988 * 2 ^ 59
def prefixEnd_5755988 : Nat := 4983230072969 + 3 ^ 40 * 5755988 * 2
def baseEnd_5755988 : Nat := 985196161837243634726233

theorem tailTrace_5755988 : CollatzResearch.WordTrace tailWord_5755988 prefixEnd_5755988 985196161837243634726233 := by
  unfold tailWord_5755988
  simp only [CollatzResearch.WordTrace]
  refine ⟨104969064735522997665670309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139958752980697330220893745 104969064735522997665670309)
  ·
    refine ⟨19681699637910562062313183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104969064735522997665670309 19681699637910562062313183)
    ·
      refine ⟨29522549456865843093469775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19681699637910562062313183 29522549456865843093469775)
      ·
        refine ⟨44283824185298764640204663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29522549456865843093469775 44283824185298764640204663)
        ·
          refine ⟨66425736277948146960306995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44283824185298764640204663 66425736277948146960306995)
          ·
            refine ⟨99638604416922220440460493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66425736277948146960306995 99638604416922220440460493)
            ·
              refine ⟨37364476656345832665172685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99638604416922220440460493 37364476656345832665172685)
              ·
                refine ⟨14011678746129687249439757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37364476656345832665172685 14011678746129687249439757)
                ·
                  refine ⟨5254379529798632718539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14011678746129687249439757 5254379529798632718539909)
                  ·
                    refine ⟨985196161837243634726233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254379529798632718539909 985196161837243634726233)
                    ·
                      rfl

theorem cell23_5755988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_5755988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755988 prefixEnd_5755988 := by exact prefixLift 5755988
  have htrace : WordTrace (prefixWord ++ tailWord_5755988) baseStart_5755988 baseEnd_5755988 := by
    simpa [prefixWord, tailWord_5755988, baseEnd_5755988] using wordTrace_append hprefix tailTrace_5755988
  have hstable : (prefixWord ++ tailWord_5755988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755988).length < 2 ^ (prefixWord ++ tailWord_5755988).sum := by decide
  have hdescent : baseEnd_5755988 < baseStart_5755988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756001 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 6]
def baseStart_5756001 : Nat := 118140960795 + 5756001 * 2 ^ 59
def prefixEnd_5756001 : Nat := 4983230072969 + 3 ^ 40 * 5756001 * 2
def baseEnd_5756001 : Nat := 328399462306693261479571

theorem tailTrace_5756001 : CollatzResearch.WordTrace tailWord_5756001 prefixEnd_5756001 328399462306693261479571 := by
  unfold tailWord_5756001
  simp only [CollatzResearch.WordTrace]
  refine ⟨209938603619998898551563857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139959069079999265701042571 209938603619998898551563857)
  ·
    refine ⟨157453952714999173913672893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209938603619998898551563857 157453952714999173913672893)
    ·
      refine ⟨59045232268124690217627335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157453952714999173913672893 59045232268124690217627335)
      ·
        refine ⟨88567848402187035326441003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59045232268124690217627335 88567848402187035326441003)
        ·
          refine ⟨132851772603280552989661505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88567848402187035326441003 132851772603280552989661505)
          ·
            refine ⟨99638829452460414742246129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132851772603280552989661505 99638829452460414742246129)
            ·
              refine ⟨74729122089345311056684597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99638829452460414742246129 74729122089345311056684597)
              ·
                refine ⟨7005855195876122911564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74729122089345311056684597 7005855195876122911564181)
                ·
                  refine ⟨328399462306693261479571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7005855195876122911564181 328399462306693261479571)
                  ·
                    rfl

theorem cell23_5756001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_5756001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756001 prefixEnd_5756001 := by exact prefixLift 5756001
  have htrace : WordTrace (prefixWord ++ tailWord_5756001) baseStart_5756001 baseEnd_5756001 := by
    simpa [prefixWord, tailWord_5756001, baseEnd_5756001] using wordTrace_append hprefix tailTrace_5756001
  have hstable : (prefixWord ++ tailWord_5756001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756001).length < 2 ^ (prefixWord ++ tailWord_5756001).sum := by decide
  have hdescent : baseEnd_5756001 < baseStart_5756001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756096 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 1, 1, 3]
def baseStart_5756096 : Nat := 118140960795 + 5756096 * 2 ^ 59
def prefixEnd_5756096 : Nat := 4983230072969 + 3 ^ 40 * 5756096 * 2
def baseEnd_5756096 : Nat := 2955643941422416481628203

theorem tailTrace_5756096 : CollatzResearch.WordTrace tailWord_5756096 prefixEnd_5756096 2955643941422416481628203 := by
  unfold tailWord_5756096
  simp only [CollatzResearch.WordTrace]
  refine ⟨104971034277327364888136071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139961379036436486517514761 104971034277327364888136071)
  ·
    refine ⟨157456551415991047332204107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104971034277327364888136071 157456551415991047332204107)
    ·
      refine ⟨236184827123986570998306161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157456551415991047332204107 236184827123986570998306161)
      ·
        refine ⟨177138620342989928248729621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236184827123986570998306161 177138620342989928248729621)
        ·
          refine ⟨8303372828577652886659201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177138620342989928248729621 8303372828577652886659201)
          ·
            refine ⟨6227529621433239664994401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8303372828577652886659201 6227529621433239664994401)
            ·
              refine ⟨4670647216074929748745801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227529621433239664994401 4670647216074929748745801)
              ·
                refine ⟨3502985412056197311559351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4670647216074929748745801 3502985412056197311559351)
                ·
                  refine ⟨5254478118084295967339027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502985412056197311559351 5254478118084295967339027)
                  ·
                    refine ⟨7881717177126443951008541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254478118084295967339027 7881717177126443951008541)
                    ·
                      refine ⟨2955643941422416481628203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881717177126443951008541 2955643941422416481628203)
                      ·
                        rfl

theorem cell23_5756096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_5756096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756096 prefixEnd_5756096 := by exact prefixLift 5756096
  have htrace : WordTrace (prefixWord ++ tailWord_5756096) baseStart_5756096 baseEnd_5756096 := by
    simpa [prefixWord, tailWord_5756096, baseEnd_5756096] using wordTrace_append hprefix tailTrace_5756096
  have hstable : (prefixWord ++ tailWord_5756096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756096).length < 2 ^ (prefixWord ++ tailWord_5756096).sum := by decide
  have hdescent : baseEnd_5756096 < baseStart_5756096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756121 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_5756121 : Nat := 118140960795 + 5756121 * 2 ^ 59
def prefixEnd_5756121 : Nat := 4983230072969 + 3 ^ 40 * 5756121 * 2
def baseEnd_5756121 : Nat := 985218926146259627938529

theorem tailTrace_5756121 : CollatzResearch.WordTrace tailWord_5756121 prefixEnd_5756121 985218926146259627938529 := by
  unfold tailWord_5756121
  simp only [CollatzResearch.WordTrace]
  refine ⟨209942980379564159045932217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139961986919709439363954811 209942980379564159045932217)
  ·
    refine ⟨157457235284673119284449163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209942980379564159045932217 157457235284673119284449163)
    ·
      refine ⟨236185852927009678926673745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157457235284673119284449163 236185852927009678926673745)
      ·
        refine ⟨177139389695257259195005309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236185852927009678926673745 177139389695257259195005309)
        ·
          refine ⟨66427271135721472198126991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177139389695257259195005309 66427271135721472198126991)
          ·
            refine ⟨99640906703582208297190487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66427271135721472198126991 99640906703582208297190487)
            ·
              refine ⟨149461360055373312445785731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99640906703582208297190487 149461360055373312445785731)
              ·
                refine ⟨224192040083059968668678597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149461360055373312445785731 224192040083059968668678597)
                ·
                  refine ⟨42036007515573744125377237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224192040083059968668678597 42036007515573744125377237)
                  ·
                    refine ⟨985218926146259627938529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42036007515573744125377237 985218926146259627938529)
                    ·
                      rfl

theorem cell23_5756121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_5756121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756121 prefixEnd_5756121 := by exact prefixLift 5756121
  have htrace : WordTrace (prefixWord ++ tailWord_5756121) baseStart_5756121 baseEnd_5756121 := by
    simpa [prefixWord, tailWord_5756121, baseEnd_5756121] using wordTrace_append hprefix tailTrace_5756121
  have hstable : (prefixWord ++ tailWord_5756121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756121).length < 2 ^ (prefixWord ++ tailWord_5756121).sum := by decide
  have hdescent : baseEnd_5756121 < baseStart_5756121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756151 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 8]
def baseStart_5756151 : Nat := 118140960795 + 5756151 * 2 ^ 59
def prefixEnd_5756151 : Nat := 4983230072969 + 3 ^ 40 * 5756151 * 2
def baseEnd_5756151 : Nat := 985224060952804588813483

theorem tailTrace_5756151 : CollatzResearch.WordTrace tailWord_5756151 prefixEnd_5756151 985224060952804588813483 := by
  unfold tailWord_5756151
  simp only [CollatzResearch.WordTrace]
  refine ⟨209944074569455474169524307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139962716379636982779682871 209944074569455474169524307)
  ·
    refine ⟨314916111854183211254286461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209944074569455474169524307 314916111854183211254286461)
    ·
      refine ⟨118093541945318704220357423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314916111854183211254286461 118093541945318704220357423)
      ·
        refine ⟨177140312917978056330536135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118093541945318704220357423 177140312917978056330536135)
        ·
          refine ⟨265710469376967084495804203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177140312917978056330536135 265710469376967084495804203)
          ·
            refine ⟨398565704065450626743706305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265710469376967084495804203 398565704065450626743706305)
            ·
              refine ⟨298924278049087970057779729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398565704065450626743706305 298924278049087970057779729)
              ·
                refine ⟨224193208536815977543334797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298924278049087970057779729 224193208536815977543334797)
                ·
                  refine ⟨84072453201305991578750549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224193208536815977543334797 84072453201305991578750549)
                  ·
                    refine ⟨985224060952804588813483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84072453201305991578750549 985224060952804588813483)
                    ·
                      rfl

theorem cell23_5756151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_5756151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756151 prefixEnd_5756151 := by exact prefixLift 5756151
  have htrace : WordTrace (prefixWord ++ tailWord_5756151) baseStart_5756151 baseEnd_5756151 := by
    simpa [prefixWord, tailWord_5756151, baseEnd_5756151] using wordTrace_append hprefix tailTrace_5756151
  have hstable : (prefixWord ++ tailWord_5756151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756151).length < 2 ^ (prefixWord ++ tailWord_5756151).sum := by decide
  have hdescent : baseEnd_5756151 < baseStart_5756151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756188 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5756188 : Nat := 118140960795 + 5756188 * 2 ^ 59
def prefixEnd_5756188 : Nat := 4983230072969 + 3 ^ 40 * 5756188 * 2
def baseEnd_5756188 : Nat := 2955691181642630121677779

theorem tailTrace_5756188 : CollatzResearch.WordTrace tailWord_5756188 prefixEnd_5756188 2955691181642630121677779 := by
  unfold tailWord_5756188
  simp only [CollatzResearch.WordTrace]
  refine ⟨104972712035160714744310609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139963616046880952992414145 104972712035160714744310609)
  ·
    refine ⟨78729534026370536058232957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104972712035160714744310609 78729534026370536058232957)
    ·
      refine ⟨29523575259888951021837359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78729534026370536058232957 29523575259888951021837359)
      ·
        refine ⟨44285362889833426532756039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29523575259888951021837359 44285362889833426532756039)
        ·
          refine ⟨66428044334750139799134059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44285362889833426532756039 66428044334750139799134059)
          ·
            refine ⟨99642066502125209698701089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66428044334750139799134059 99642066502125209698701089)
            ·
              refine ⟨74731549876593907274025817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99642066502125209698701089 74731549876593907274025817)
              ·
                refine ⟨56048662407445430455519363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74731549876593907274025817 56048662407445430455519363)
                ·
                  refine ⟨84072993611168145683279045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56048662407445430455519363 84072993611168145683279045)
                  ·
                    refine ⟨15763686302094027315614821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84072993611168145683279045 15763686302094027315614821)
                    ·
                      refine ⟨2955691181642630121677779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15763686302094027315614821 2955691181642630121677779)
                      ·
                        rfl

theorem cell23_5756188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5756188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756188 prefixEnd_5756188 := by exact prefixLift 5756188
  have htrace : WordTrace (prefixWord ++ tailWord_5756188) baseStart_5756188 baseEnd_5756188 := by
    simpa [prefixWord, tailWord_5756188, baseEnd_5756188] using wordTrace_append hprefix tailTrace_5756188
  have hstable : (prefixWord ++ tailWord_5756188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756188).length < 2 ^ (prefixWord ++ tailWord_5756188).sum := by decide
  have hdescent : baseEnd_5756188 < baseStart_5756188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756230 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5756230 : Nat := 118140960795 + 5756230 * 2 ^ 59
def prefixEnd_5756230 : Nat := 4983230072969 + 3 ^ 40 * 5756230 * 2
def baseEnd_5756230 : Nat := 2955712747830118957352587

theorem tailTrace_5756230 : CollatzResearch.WordTrace tailWord_5756230 prefixEnd_5756230 2955712747830118957352587 := by
  unfold tailWord_5756230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560842373005289708176567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139964637290779513774433429 6560842373005289708176567)
  ·
    refine ⟨9841263559507934562264851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6560842373005289708176567 9841263559507934562264851)
    ·
      refine ⟨14761895339261901843397277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9841263559507934562264851 14761895339261901843397277)
      ·
        refine ⟨5535710752223213191273979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14761895339261901843397277 5535710752223213191273979)
        ·
          refine ⟨8303566128334819786910969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535710752223213191273979 8303566128334819786910969)
          ·
            refine ⟨6227674596251114840183227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8303566128334819786910969 6227674596251114840183227)
            ·
              refine ⟨9341511894376672260274841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227674596251114840183227 9341511894376672260274841)
              ·
                refine ⟨7006133920782504195206131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341511894376672260274841 7006133920782504195206131)
                ·
                  refine ⟨10509200881173756292809197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006133920782504195206131 10509200881173756292809197)
                  ·
                    refine ⟨3940950330440158609803449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10509200881173756292809197 3940950330440158609803449)
                    ·
                      refine ⟨2955712747830118957352587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3940950330440158609803449 2955712747830118957352587)
                      ·
                        rfl

theorem cell23_5756230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5756230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756230 prefixEnd_5756230 := by exact prefixLift 5756230
  have htrace : WordTrace (prefixWord ++ tailWord_5756230) baseStart_5756230 baseEnd_5756230 := by
    simpa [prefixWord, tailWord_5756230, baseEnd_5756230] using wordTrace_append hprefix tailTrace_5756230
  have hstable : (prefixWord ++ tailWord_5756230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756230).length < 2 ^ (prefixWord ++ tailWord_5756230).sum := by decide
  have hdescent : baseEnd_5756230 < baseStart_5756230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756238 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5756238 : Nat := 118140960795 + 5756238 * 2 ^ 59
def prefixEnd_5756238 : Nat := 4983230072969 + 3 ^ 40 * 5756238 * 2
def baseEnd_5756238 : Nat := 2955716855675354926052549

theorem tailTrace_5756238 : CollatzResearch.WordTrace tailWord_5756238 prefixEnd_5756238 2955716855675354926052549 := by
  unfold tailWord_5756238
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243405965017536003492671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139964831813426858685294245 26243405965017536003492671)
  ·
    refine ⟨39365108947526304005239007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26243405965017536003492671 39365108947526304005239007)
    ·
      refine ⟨59047663421289456007858511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39365108947526304005239007 59047663421289456007858511)
      ·
        refine ⟨88571495131934184011787767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59047663421289456007858511 88571495131934184011787767)
        ·
          refine ⟨132857242697901276017681651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88571495131934184011787767 132857242697901276017681651)
          ·
            refine ⟨199285864046851914026522477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132857242697901276017681651 199285864046851914026522477)
            ·
              refine ⟨74732199017569467759945929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199285864046851914026522477 74732199017569467759945929)
              ·
                refine ⟨56049149263177100819959447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74732199017569467759945929 56049149263177100819959447)
                ·
                  refine ⟨84073723894765651229939171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56049149263177100819959447 84073723894765651229939171)
                  ·
                    refine ⟨126110585842148476844908757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84073723894765651229939171 126110585842148476844908757)
                    ·
                      refine ⟨2955716855675354926052549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126110585842148476844908757 2955716855675354926052549)
                      ·
                        rfl

theorem cell23_5756238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5756238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756238 prefixEnd_5756238 := by exact prefixLift 5756238
  have htrace : WordTrace (prefixWord ++ tailWord_5756238) baseStart_5756238 baseEnd_5756238 := by
    simpa [prefixWord, tailWord_5756238, baseEnd_5756238] using wordTrace_append hprefix tailTrace_5756238
  have hstable : (prefixWord ++ tailWord_5756238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756238).length < 2 ^ (prefixWord ++ tailWord_5756238).sum := by decide
  have hdescent : baseEnd_5756238 < baseStart_5756238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756245 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_5756245 : Nat := 118140960795 + 5756245 * 2 ^ 59
def prefixEnd_5756245 : Nat := 4983230072969 + 3 ^ 40 * 5756245 * 2
def baseEnd_5756245 : Nat := 985240150013312132888339

theorem tailTrace_5756245 : CollatzResearch.WordTrace tailWord_5756245 prefixEnd_5756245 985240150013312132888339 := by
  unfold tailWord_5756245
  simp only [CollatzResearch.WordTrace]
  refine ⟨209947503031114928223446189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139965002020743285482297459 209947503031114928223446189)
  ·
    refine ⟨78730313636668098083792321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209947503031114928223446189 78730313636668098083792321)
    ·
      refine ⟨59047735227501073562844241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78730313636668098083792321 59047735227501073562844241)
      ·
        refine ⟨44285801420625805172133181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59047735227501073562844241 44285801420625805172133181)
        ·
          refine ⟨16607175532734676939549943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44285801420625805172133181 16607175532734676939549943)
          ·
            refine ⟨24910763299102015409324915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16607175532734676939549943 24910763299102015409324915)
            ·
              refine ⟨37366144948653023113987373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24910763299102015409324915 37366144948653023113987373)
              ·
                refine ⟨14012304355744883667745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37366144948653023113987373 14012304355744883667745265)
                ·
                  refine ⟨10509228266808662750808949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14012304355744883667745265 10509228266808662750808949)
                  ·
                    refine ⟨985240150013312132888339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10509228266808662750808949 985240150013312132888339)
                    ·
                      rfl

theorem cell23_5756245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_5756245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756245 prefixEnd_5756245 := by exact prefixLift 5756245
  have htrace : WordTrace (prefixWord ++ tailWord_5756245) baseStart_5756245 baseEnd_5756245 := by
    simpa [prefixWord, tailWord_5756245, baseEnd_5756245] using wordTrace_append hprefix tailTrace_5756245
  have hstable : (prefixWord ++ tailWord_5756245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756245).length < 2 ^ (prefixWord ++ tailWord_5756245).sum := by decide
  have hdescent : baseEnd_5756245 < baseStart_5756245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756266 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_5756266 : Nat := 118140960795 + 5756266 * 2 ^ 59
def prefixEnd_5756266 : Nat := 4983230072969 + 3 ^ 40 * 5756266 * 2
def baseEnd_5756266 : Nat := 328414581459297868500269

theorem tailTrace_5756266 : CollatzResearch.WordTrace tailWord_5756266 prefixEnd_5756266 328414581459297868500269 := by
  unfold tailWord_5756266
  simp only [CollatzResearch.WordTrace]
  refine ⟨52487067241009712202490163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139965512642692565873307101 52487067241009712202490163)
  ·
    refine ⟨78730600861514568303735245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52487067241009712202490163 78730600861514568303735245)
    ·
      refine ⟨29523975323067963113900717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78730600861514568303735245 29523975323067963113900717)
      ·
        refine ⟨11071490746150486167712769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29523975323067963113900717 11071490746150486167712769)
        ·
          refine ⟨8303618059612864625784577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11071490746150486167712769 8303618059612864625784577)
          ·
            refine ⟨6227713544709648469338433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8303618059612864625784577 6227713544709648469338433)
            ·
              refine ⟨4670785158532236352003825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227713544709648469338433 4670785158532236352003825)
              ·
                refine ⟨3503088868899177264002869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4670785158532236352003825 3503088868899177264002869)
                ·
                  refine ⟨328414581459297868500269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3503088868899177264002869 328414581459297868500269)
                  ·
                    rfl

theorem cell23_5756266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_5756266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756266 prefixEnd_5756266 := by exact prefixLift 5756266
  have htrace : WordTrace (prefixWord ++ tailWord_5756266) baseStart_5756266 baseEnd_5756266 := by
    simpa [prefixWord, tailWord_5756266, baseEnd_5756266] using wordTrace_append hprefix tailTrace_5756266
  have hstable : (prefixWord ++ tailWord_5756266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756266).length < 2 ^ (prefixWord ++ tailWord_5756266).sum := by decide
  have hdescent : baseEnd_5756266 < baseStart_5756266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756285 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_5756285 : Nat := 118140960795 + 5756285 * 2 ^ 59
def prefixEnd_5756285 : Nat := 4983230072969 + 3 ^ 40 * 5756285 * 2
def baseEnd_5756285 : Nat := 2955740989266116242164833

theorem tailTrace_5756285 : CollatzResearch.WordTrace tailWord_5756285 prefixEnd_5756285 2955740989266116242164833 := by
  unfold tailWord_5756285
  simp only [CollatzResearch.WordTrace]
  refine ⟨209948961950970015054902309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139965974633980010036601539 209948961950970015054902309)
  ·
    refine ⟨39365430365806877822794183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209948961950970015054902309 39365430365806877822794183)
    ·
      refine ⟨59048145548710316734191275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39365430365806877822794183 59048145548710316734191275)
      ·
        refine ⟨88572218323065475101286913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59048145548710316734191275 88572218323065475101286913)
        ·
          refine ⟨66429163742299106325965185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88572218323065475101286913 66429163742299106325965185)
          ·
            refine ⟨49821872806724329744473889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66429163742299106325965185 49821872806724329744473889)
            ·
              refine ⟨37366404605043247308355417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49821872806724329744473889 37366404605043247308355417)
              ·
                refine ⟨28024803453782435481266563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37366404605043247308355417 28024803453782435481266563)
                ·
                  refine ⟨42037205180673653221899845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28024803453782435481266563 42037205180673653221899845)
                  ·
                    refine ⟨7881975971376309979106221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42037205180673653221899845 7881975971376309979106221)
                    ·
                      refine ⟨2955740989266116242164833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7881975971376309979106221 2955740989266116242164833)
                      ·
                        rfl

theorem cell23_5756285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_5756285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756285 prefixEnd_5756285 := by exact prefixLift 5756285
  have htrace : WordTrace (prefixWord ++ tailWord_5756285) baseStart_5756285 baseEnd_5756285 := by
    simpa [prefixWord, tailWord_5756285, baseEnd_5756285] using wordTrace_append hprefix tailTrace_5756285
  have hstable : (prefixWord ++ tailWord_5756285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756285).length < 2 ^ (prefixWord ++ tailWord_5756285).sum := by decide
  have hdescent : baseEnd_5756285 < baseStart_5756285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756292 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_5756292 : Nat := 118140960795 + 5756292 * 2 ^ 59
def prefixEnd_5756292 : Nat := 4983230072969 + 3 ^ 40 * 5756292 * 2
def baseEnd_5756292 : Nat := 985248194543565904925767

theorem tailTrace_5756292 : CollatzResearch.WordTrace tailWord_5756292 prefixEnd_5756292 985248194543565904925767 := by
  unfold tailWord_5756292
  simp only [CollatzResearch.WordTrace]
  refine ⟨104974608630972327625203565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139966144841296436833604753 104974608630972327625203565)
  ·
    refine ⟨39365478236614622859451337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104974608630972327625203565 39365478236614622859451337)
    ·
      refine ⟨29524108677460967144588503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39365478236614622859451337 29524108677460967144588503)
      ·
        refine ⟨44286163016191450716882755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29524108677460967144588503 44286163016191450716882755)
        ·
          refine ⟨66429244524287176075324133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44286163016191450716882755 66429244524287176075324133)
          ·
            refine ⟨12455483348303845514123275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66429244524287176075324133 12455483348303845514123275)
            ·
              refine ⟨18683225022455768271184913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455483348303845514123275 18683225022455768271184913)
              ·
                refine ⟨14012418766841826203388685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18683225022455768271184913 14012418766841826203388685)
                ·
                  refine ⟨5254657037565684826270757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14012418766841826203388685 5254657037565684826270757)
                  ·
                    refine ⟨985248194543565904925767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254657037565684826270757 985248194543565904925767)
                    ·
                      rfl

theorem cell23_5756292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_5756292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756292 prefixEnd_5756292 := by exact prefixLift 5756292
  have htrace : WordTrace (prefixWord ++ tailWord_5756292) baseStart_5756292 baseEnd_5756292 := by
    simpa [prefixWord, tailWord_5756292, baseEnd_5756292] using wordTrace_append hprefix tailTrace_5756292
  have hstable : (prefixWord ++ tailWord_5756292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756292).length < 2 ^ (prefixWord ++ tailWord_5756292).sum := by decide
  have hdescent : baseEnd_5756292 < baseStart_5756292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756322 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_5756322 : Nat := 118140960795 + 5756322 * 2 ^ 59
def prefixEnd_5756322 : Nat := 4983230072969 + 3 ^ 40 * 5756322 * 2
def baseEnd_5756322 : Nat := 328417776450036955266907

theorem tailTrace_5756322 : CollatzResearch.WordTrace tailWord_5756322 prefixEnd_5756322 328417776450036955266907 := by
  unfold tailWord_5756322
  simp only [CollatzResearch.WordTrace]
  refine ⟨52487577862958992593499805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139966874301223980249332813 52487577862958992593499805)
  ·
    refine ⟨19682841698609622222562427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52487577862958992593499805 19682841698609622222562427)
    ·
      refine ⟨29524262547914433333843641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19682841698609622222562427 29524262547914433333843641)
      ·
        refine ⟨22143196910935825000382731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29524262547914433333843641 22143196910935825000382731)
        ·
          refine ⟨33214795366403737500574097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22143196910935825000382731 33214795366403737500574097)
          ·
            refine ⟨24911096524802803125430573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33214795366403737500574097 24911096524802803125430573)
            ·
              refine ⟨9341661196801051172036465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24911096524802803125430573 9341661196801051172036465)
              ·
                refine ⟨7006245897600788379027349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341661196801051172036465 7006245897600788379027349)
                ·
                  refine ⟨328417776450036955266907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7006245897600788379027349 328417776450036955266907)
                  ·
                    rfl

theorem cell23_5756322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_5756322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756322 prefixEnd_5756322 := by exact prefixLift 5756322
  have htrace : WordTrace (prefixWord ++ tailWord_5756322) baseStart_5756322 baseEnd_5756322 := by
    simpa [prefixWord, tailWord_5756322, baseEnd_5756322] using wordTrace_append hprefix tailTrace_5756322
  have hstable : (prefixWord ++ tailWord_5756322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756322).length < 2 ^ (prefixWord ++ tailWord_5756322).sum := by decide
  have hdescent : baseEnd_5756322 < baseStart_5756322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756332 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_5756332 : Nat := 118140960795 + 5756332 * 2 ^ 59
def prefixEnd_5756332 : Nat := 4983230072969 + 3 ^ 40 * 5756332 * 2
def baseEnd_5756332 : Nat := 2955765122856877558277117

theorem tailTrace_5756332 : CollatzResearch.WordTrace tailWord_5756332 prefixEnd_5756332 2955765122856877558277117 := by
  unfold tailWord_5756332
  simp only [CollatzResearch.WordTrace]
  refine ⟨104975338090899871040931625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139967117454533161387908833 104975338090899871040931625)
  ·
    refine ⟨78731503568174903280698719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104975338090899871040931625 78731503568174903280698719)
    ·
      refine ⟨118097255352262354921048079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78731503568174903280698719 118097255352262354921048079)
      ·
        refine ⟨177145883028393532381572119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118097255352262354921048079 177145883028393532381572119)
        ·
          refine ⟨265718824542590298572358179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177145883028393532381572119 265718824542590298572358179)
          ·
            refine ⟨398578236813885447858537269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265718824542590298572358179 398578236813885447858537269)
            ·
              refine ⟨37366709701301760736737869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398578236813885447858537269 37366709701301760736737869)
              ·
                refine ⟨14012516137988160276276701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37366709701301760736737869 14012516137988160276276701)
                ·
                  refine ⟨5254693551745560103603763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14012516137988160276276701 5254693551745560103603763)
                  ·
                    refine ⟨7882040327618340155405645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254693551745560103603763 7882040327618340155405645)
                    ·
                      refine ⟨2955765122856877558277117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882040327618340155405645 2955765122856877558277117)
                      ·
                        rfl

theorem cell23_5756332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_5756332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756332 prefixEnd_5756332 := by exact prefixLift 5756332
  have htrace : WordTrace (prefixWord ++ tailWord_5756332) baseStart_5756332 baseEnd_5756332 := by
    simpa [prefixWord, tailWord_5756332, baseEnd_5756332] using wordTrace_append hprefix tailTrace_5756332
  have hstable : (prefixWord ++ tailWord_5756332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756332).length < 2 ^ (prefixWord ++ tailWord_5756332).sum := by decide
  have hdescent : baseEnd_5756332 < baseStart_5756332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756355 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4]
def baseStart_5756355 : Nat := 118140960795 + 5756355 * 2 ^ 59
def prefixEnd_5756355 : Nat := 4983230072969 + 3 ^ 40 * 5756355 * 2
def baseEnd_5756355 : Nat := 2955776932911930968289511

theorem tailTrace_5756355 : CollatzResearch.WordTrace tailWord_5756355 prefixEnd_5756355 2955776932911930968289511 := by
  unfold tailWord_5756355
  simp only [CollatzResearch.WordTrace]
  refine ⟨209951515060716417009950519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139967676707144278006633679 209951515060716417009950519)
  ·
    refine ⟨314927272591074625514925779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209951515060716417009950519 314927272591074625514925779)
    ·
      refine ⟨472390908886611938272388669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314927272591074625514925779 472390908886611938272388669)
      ·
        refine ⟨177146590832479476852145751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472390908886611938272388669 177146590832479476852145751)
        ·
          refine ⟨265719886248719215278218627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177146590832479476852145751 265719886248719215278218627)
          ·
            refine ⟨398579829373078822917327941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265719886248719215278218627 398579829373078822917327941)
            ·
              refine ⟨74733718007452279296998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398579829373078822917327941 74733718007452279296998989)
              ·
                refine ⟨28025144252794604736374621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74733718007452279296998989 28025144252794604736374621)
                ·
                  refine ⟨10509429094797976776140483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28025144252794604736374621 10509429094797976776140483)
                  ·
                    refine ⟨15764143642196965164210725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10509429094797976776140483 15764143642196965164210725)
                    ·
                      refine ⟨2955776932911930968289511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15764143642196965164210725 2955776932911930968289511)
                      ·
                        rfl

theorem cell23_5756355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_5756355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756355 prefixEnd_5756355 := by exact prefixLift 5756355
  have htrace : WordTrace (prefixWord ++ tailWord_5756355) baseStart_5756355 baseEnd_5756355 := by
    simpa [prefixWord, tailWord_5756355, baseEnd_5756355] using wordTrace_append hprefix tailTrace_5756355
  have hstable : (prefixWord ++ tailWord_5756355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756355).length < 2 ^ (prefixWord ++ tailWord_5756355).sum := by decide
  have hdescent : baseEnd_5756355 < baseStart_5756355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756366 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_5756366 : Nat := 118140960795 + 5756366 * 2 ^ 59
def prefixEnd_5756366 : Nat := 4983230072969 + 3 ^ 40 * 5756366 * 2
def baseEnd_5756366 : Nat := 2955782581199130425251961

theorem tailTrace_5756366 : CollatzResearch.WordTrace tailWord_5756366 prefixEnd_5756366 2955782581199130425251961 := by
  unfold tailWord_5756366
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243989532959570736075119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139967944175784377259067301 26243989532959570736075119)
  ·
    refine ⟨39365984299439356104112679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26243989532959570736075119 39365984299439356104112679)
    ·
      refine ⟨59048976449159034156169019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39365984299439356104112679 59048976449159034156169019)
      ·
        refine ⟨88573464673738551234253529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59048976449159034156169019 88573464673738551234253529)
        ·
          refine ⟨66430098505303913425690147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88573464673738551234253529 66430098505303913425690147)
          ·
            refine ⟨99645147757955870138535221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66430098505303913425690147 99645147757955870138535221)
            ·
              refine ⟨9341732602308362825487677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99645147757955870138535221 9341732602308362825487677)
              ·
                refine ⟨3503149725865636059557879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9341732602308362825487677 3503149725865636059557879)
                ·
                  refine ⟨5254724588798454089336819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503149725865636059557879 5254724588798454089336819)
                  ·
                    refine ⟨7882086883197681134005229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254724588798454089336819 7882086883197681134005229)
                    ·
                      refine ⟨2955782581199130425251961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882086883197681134005229 2955782581199130425251961)
                      ·
                        rfl

theorem cell23_5756366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_5756366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756366 prefixEnd_5756366 := by exact prefixLift 5756366
  have htrace : WordTrace (prefixWord ++ tailWord_5756366) baseStart_5756366 baseEnd_5756366 := by
    simpa [prefixWord, tailWord_5756366, baseEnd_5756366] using wordTrace_append hprefix tailTrace_5756366
  have hstable : (prefixWord ++ tailWord_5756366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756366).length < 2 ^ (prefixWord ++ tailWord_5756366).sum := by decide
  have hdescent : baseEnd_5756366 < baseStart_5756366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756385 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5756385 : Nat := 118140960795 + 5756385 * 2 ^ 59
def prefixEnd_5756385 : Nat := 4983230072969 + 3 ^ 40 * 5756385 * 2
def baseEnd_5756385 : Nat := 2955792337331565850914373

theorem tailTrace_5756385 : CollatzResearch.WordTrace tailWord_5756385 prefixEnd_5756385 2955792337331565850914373 := by
  unfold tailWord_5756385
  simp only [CollatzResearch.WordTrace]
  refine ⟨209952609250607732133542609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139968406167071821422361739 209952609250607732133542609)
  ·
    refine ⟨157464456937955799100156957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209952609250607732133542609 157464456937955799100156957)
    ·
      refine ⟨59049171351733424662558859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157464456937955799100156957 59049171351733424662558859)
      ·
        refine ⟨88573757027600136993838289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59049171351733424662558859 88573757027600136993838289)
        ·
          refine ⟨66430317770700102745378717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88573757027600136993838289 66430317770700102745378717)
          ·
            refine ⟨24911369164012538529517019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66430317770700102745378717 24911369164012538529517019)
            ·
              refine ⟨37367053746018807794275529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24911369164012538529517019 37367053746018807794275529)
              ·
                refine ⟨28025290309514105845706647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37367053746018807794275529 28025290309514105845706647)
                ·
                  refine ⟨42037935464271158768559971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28025290309514105845706647 42037935464271158768559971)
                  ·
                    refine ⟨63056903196406738152839957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42037935464271158768559971 63056903196406738152839957)
                    ·
                      refine ⟨2955792337331565850914373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63056903196406738152839957 2955792337331565850914373)
                      ·
                        rfl

theorem cell23_5756385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5756385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756385 prefixEnd_5756385 := by exact prefixLift 5756385
  have htrace : WordTrace (prefixWord ++ tailWord_5756385) baseStart_5756385 baseEnd_5756385 := by
    simpa [prefixWord, tailWord_5756385, baseEnd_5756385] using wordTrace_append hprefix tailTrace_5756385
  have hstable : (prefixWord ++ tailWord_5756385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756385).length < 2 ^ (prefixWord ++ tailWord_5756385).sum := by decide
  have hdescent : baseEnd_5756385 < baseStart_5756385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756392 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5756392 : Nat := 118140960795 + 5756392 * 2 ^ 59
def prefixEnd_5756392 : Nat := 4983230072969 + 3 ^ 40 * 5756392 * 2
def baseEnd_5756392 : Nat := 2955795931696147323526841

theorem tailTrace_5756392 : CollatzResearch.WordTrace tailWord_5756392 prefixEnd_5756392 2955795931696147323526841 := by
  unfold tailWord_5756392
  simp only [CollatzResearch.WordTrace]
  refine ⟨104976432280791186164523715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139968576374388248219364953 104976432280791186164523715)
  ·
    refine ⟨157464648421186779246785573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104976432280791186164523715 157464648421186779246785573)
    ·
      refine ⟨29524621578972521108772295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157464648421186779246785573 29524621578972521108772295)
      ·
        refine ⟨44286932368458781663158443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29524621578972521108772295 44286932368458781663158443)
        ·
          refine ⟨66430398552688172494737665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44286932368458781663158443 66430398552688172494737665)
          ·
            refine ⟨49822798914516129371053249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66430398552688172494737665 49822798914516129371053249)
            ·
              refine ⟨37367099185887097028289937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49822798914516129371053249 37367099185887097028289937)
              ·
                refine ⟨28025324389415322771217453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37367099185887097028289937 28025324389415322771217453)
                ·
                  refine ⟨10509496646030746039206545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28025324389415322771217453 10509496646030746039206545)
                  ·
                    refine ⟨7882122484523059529404909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10509496646030746039206545 7882122484523059529404909)
                    ·
                      refine ⟨2955795931696147323526841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882122484523059529404909 2955795931696147323526841)
                      ·
                        rfl

theorem cell23_5756392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5756392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756392 prefixEnd_5756392 := by exact prefixLift 5756392
  have htrace : WordTrace (prefixWord ++ tailWord_5756392) baseStart_5756392 baseEnd_5756392 := by
    simpa [prefixWord, tailWord_5756392, baseEnd_5756392] using wordTrace_append hprefix tailTrace_5756392
  have hstable : (prefixWord ++ tailWord_5756392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756392).length < 2 ^ (prefixWord ++ tailWord_5756392).sum := by decide
  have hdescent : baseEnd_5756392 < baseStart_5756392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756399 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 2, 4]
def baseStart_5756399 : Nat := 118140960795 + 5756399 * 2 ^ 59
def prefixEnd_5756399 : Nat := 4983230072969 + 3 ^ 40 * 5756399 * 2
def baseEnd_5756399 : Nat := 985266508686909598713103

theorem tailTrace_5756399 : CollatzResearch.WordTrace tailWord_5756399 prefixEnd_5756399 985266508686909598713103 := by
  unfold tailWord_5756399
  simp only [CollatzResearch.WordTrace]
  refine ⟨209953119872557012524552251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139968746581704675016368167 209953119872557012524552251)
  ·
    refine ⟨314929679808835518786828377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209953119872557012524552251 314929679808835518786828377)
    ·
      refine ⟨236197259856626639090121283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314929679808835518786828377 236197259856626639090121283)
      ·
        refine ⟨354295889784939958635181925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236197259856626639090121283 354295889784939958635181925)
        ·
          refine ⟨66430479334676242244096611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354295889784939958635181925 66430479334676242244096611)
          ·
            refine ⟨99645719002014363366144917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66430479334676242244096611 99645719002014363366144917)
            ·
              refine ⟨4670893078219423282788043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99645719002014363366144917 4670893078219423282788043)
              ·
                refine ⟨7006339617329134924182065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670893078219423282788043 7006339617329134924182065)
                ·
                  refine ⟨5254754712996851193136549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006339617329134924182065 5254754712996851193136549)
                  ·
                    refine ⟨985266508686909598713103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254754712996851193136549 985266508686909598713103)
                    ·
                      rfl

theorem cell23_5756399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_5756399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756399 prefixEnd_5756399 := by exact prefixLift 5756399
  have htrace : WordTrace (prefixWord ++ tailWord_5756399) baseStart_5756399 baseEnd_5756399 := by
    simpa [prefixWord, tailWord_5756399, baseEnd_5756399] using wordTrace_append hprefix tailTrace_5756399
  have hstable : (prefixWord ++ tailWord_5756399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756399).length < 2 ^ (prefixWord ++ tailWord_5756399).sum := by decide
  have hdescent : baseEnd_5756399 < baseStart_5756399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756402 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5756402 : Nat := 118140960795 + 5756402 * 2 ^ 59
def prefixEnd_5756402 : Nat := 4983230072969 + 3 ^ 40 * 5756402 * 2
def baseEnd_5756402 : Nat := 2955801066502692284401795

theorem tailTrace_5756402 : CollatzResearch.WordTrace tailWord_5756402 prefixEnd_5756402 2955801066502692284401795 := by
  unfold tailWord_5756402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52488307322886536009227865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139968819527697429357940973 52488307322886536009227865)
  ·
    refine ⟨39366230492164902006920899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52488307322886536009227865 39366230492164902006920899)
    ·
      refine ⟨59049345738247353010381349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39366230492164902006920899 59049345738247353010381349)
      ·
        refine ⟨11071752325921378689446503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59049345738247353010381349 11071752325921378689446503)
        ·
          refine ⟨16607628488882068034169755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11071752325921378689446503 16607628488882068034169755)
          ·
            refine ⟨24911442733323102051254633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16607628488882068034169755 24911442733323102051254633)
            ·
              refine ⟨18683582049992326538440975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24911442733323102051254633 18683582049992326538440975)
              ·
                refine ⟨28025373074988489807661463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18683582049992326538440975 28025373074988489807661463)
                ·
                  refine ⟨42038059612482734711492195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28025373074988489807661463 42038059612482734711492195)
                  ·
                    refine ⟨63057089418724102067238293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42038059612482734711492195 63057089418724102067238293)
                    ·
                      refine ⟨2955801066502692284401795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63057089418724102067238293 2955801066502692284401795)
                      ·
                        rfl

theorem cell23_5756402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5756402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756402 prefixEnd_5756402 := by exact prefixLift 5756402
  have htrace : WordTrace (prefixWord ++ tailWord_5756402) baseStart_5756402 baseEnd_5756402 := by
    simpa [prefixWord, tailWord_5756402, baseEnd_5756402] using wordTrace_append hprefix tailTrace_5756402
  have hstable : (prefixWord ++ tailWord_5756402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756402).length < 2 ^ (prefixWord ++ tailWord_5756402).sum := by decide
  have hdescent : baseEnd_5756402 < baseStart_5756402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756406 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5756406 : Nat := 118140960795 + 5756406 * 2 ^ 59
def prefixEnd_5756406 : Nat := 4983230072969 + 3 ^ 40 * 5756406 * 2
def baseEnd_5756406 : Nat := 2955803120425310268751777

theorem tailTrace_5756406 : CollatzResearch.WordTrace tailWord_5756406 prefixEnd_5756406 2955803120425310268751777 := by
  unfold tailWord_5756406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122085948970728295003567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139968916789021101813371381 13122085948970728295003567)
  ·
    refine ⟨19683128923456092442505351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13122085948970728295003567 19683128923456092442505351)
    ·
      refine ⟨29524693385184138663758027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19683128923456092442505351 29524693385184138663758027)
      ·
        refine ⟨44287040077776207995637041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29524693385184138663758027 44287040077776207995637041)
        ·
          refine ⟨33215280058332155996727781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44287040077776207995637041 33215280058332155996727781)
          ·
            refine ⟨6227865010937279249386459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33215280058332155996727781 6227865010937279249386459)
            ·
              refine ⟨9341797516405918874079689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227865010937279249386459 9341797516405918874079689)
              ·
                refine ⟨7006348137304439155559767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341797516405918874079689 7006348137304439155559767)
                ·
                  refine ⟨10509522205956658733339651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006348137304439155559767 10509522205956658733339651)
                  ·
                    refine ⟨15764283308934988100009477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10509522205956658733339651 15764283308934988100009477)
                    ·
                      refine ⟨2955803120425310268751777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15764283308934988100009477 2955803120425310268751777)
                      ·
                        rfl

theorem cell23_5756406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5756406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756406 prefixEnd_5756406 := by exact prefixLift 5756406
  have htrace : WordTrace (prefixWord ++ tailWord_5756406) baseStart_5756406 baseEnd_5756406 := by
    simpa [prefixWord, tailWord_5756406, baseEnd_5756406] using wordTrace_append hprefix tailTrace_5756406
  have hstable : (prefixWord ++ tailWord_5756406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756406).length < 2 ^ (prefixWord ++ tailWord_5756406).sum := by decide
  have hdescent : baseEnd_5756406 < baseStart_5756406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756426 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_5756426 : Nat := 118140960795 + 5756426 * 2 ^ 59
def prefixEnd_5756426 : Nat := 4983230072969 + 3 ^ 40 * 5756426 * 2
def baseEnd_5756426 : Nat := 2955813390038400190501685

theorem tailTrace_5756426 : CollatzResearch.WordTrace tailWord_5756426 prefixEnd_5756426 2955813390038400190501685 := by
  unfold tailWord_5756426
  simp only [CollatzResearch.WordTrace]
  refine ⟨52488526160864799033946283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139969403095639464090523421 52488526160864799033946283)
  ·
    refine ⟨78732789241297198550919425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52488526160864799033946283 78732789241297198550919425)
    ·
      refine ⟨59049591930972898913189569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78732789241297198550919425 59049591930972898913189569)
      ·
        refine ⟨44287193948229674184892177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59049591930972898913189569 44287193948229674184892177)
        ·
          refine ⟨33215395461172255638669133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44287193948229674184892177 33215395461172255638669133)
          ·
            refine ⟨12455773297939595864500925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33215395461172255638669133 12455773297939595864500925)
            ·
              refine ⟨4670914986727348449187847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12455773297939595864500925 4670914986727348449187847)
              ·
                refine ⟨7006372480091022673781771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670914986727348449187847 7006372480091022673781771)
                ·
                  refine ⟨10509558720136534010672657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006372480091022673781771 10509558720136534010672657)
                  ·
                    refine ⟨7882169040102400508004493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10509558720136534010672657 7882169040102400508004493)
                    ·
                      refine ⟨2955813390038400190501685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882169040102400508004493 2955813390038400190501685)
                      ·
                        rfl

theorem cell23_5756426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_5756426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756426 prefixEnd_5756426 := by exact prefixLift 5756426
  have htrace : WordTrace (prefixWord ++ tailWord_5756426) baseStart_5756426 baseEnd_5756426 := by
    simpa [prefixWord, tailWord_5756426, baseEnd_5756426] using wordTrace_append hprefix tailTrace_5756426
  have hstable : (prefixWord ++ tailWord_5756426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756426).length < 2 ^ (prefixWord ++ tailWord_5756426).sum := by decide
  have hdescent : baseEnd_5756426 < baseStart_5756426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756429 : List Nat := [1, 7, 1, 1, 2, 11]
def baseStart_5756429 : Nat := 118140960795 + 5756429 * 2 ^ 59
def prefixEnd_5756429 : Nat := 4983230072969 + 3 ^ 40 * 5756429 * 2
def baseEnd_5756429 : Nat := 12163847450536476044297

theorem tailTrace_5756429 : CollatzResearch.WordTrace tailWord_5756429 prefixEnd_5756429 12163847450536476044297 := by
  unfold tailWord_5756429
  simp only [CollatzResearch.WordTrace]
  refine ⟨209954214062448327648144341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139969476041632218432096227 209954214062448327648144341)
  ·
    refine ⟨4920801892088632679253383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 209954214062448327648144341 4920801892088632679253383)
    ·
      refine ⟨7381202838132949018880075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920801892088632679253383 7381202838132949018880075)
      ·
        refine ⟨11071804257199423528320113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381202838132949018880075 11071804257199423528320113)
        ·
          refine ⟨8303853192899567646240085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11071804257199423528320113 8303853192899567646240085)
          ·
            refine ⟨12163847450536476044297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8303853192899567646240085 12163847450536476044297)
            ·
              rfl

theorem cell23_5756429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 11].length) (baseStart_5756429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756429 prefixEnd_5756429 := by exact prefixLift 5756429
  have htrace : WordTrace (prefixWord ++ tailWord_5756429) baseStart_5756429 baseEnd_5756429 := by
    simpa [prefixWord, tailWord_5756429, baseEnd_5756429] using wordTrace_append hprefix tailTrace_5756429
  have hstable : (prefixWord ++ tailWord_5756429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756429).length < 2 ^ (prefixWord ++ tailWord_5756429).sum := by decide
  have hdescent : baseEnd_5756429 < baseStart_5756429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756449 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5756449 : Nat := 118140960795 + 5756449 * 2 ^ 59
def prefixEnd_5756449 : Nat := 4983230072969 + 3 ^ 40 * 5756449 * 2
def baseEnd_5756449 : Nat := 2955825200093453600514079

theorem tailTrace_5756449 : CollatzResearch.WordTrace tailWord_5756449 prefixEnd_5756449 2955825200093453600514079 := by
  unfold tailWord_5756449
  simp only [CollatzResearch.WordTrace]
  refine ⟨209954943522375871063872401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139969962348250580709248267 209954943522375871063872401)
  ·
    refine ⟨157466207641781903297904301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209954943522375871063872401 157466207641781903297904301)
    ·
      refine ⟨59049827865668213736714113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157466207641781903297904301 59049827865668213736714113)
      ·
        refine ⟨44287370899251160302535585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59049827865668213736714113 44287370899251160302535585)
        ·
          refine ⟨33215528174438370226901689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44287370899251160302535585 33215528174438370226901689)
          ·
            refine ⟨24911646130828777670176267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33215528174438370226901689 24911646130828777670176267)
            ·
              refine ⟨37367469196243166505264401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24911646130828777670176267 37367469196243166505264401)
              ·
                refine ⟨28025601897182374878948301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37367469196243166505264401 28025601897182374878948301)
                ·
                  refine ⟨10509600711443390579605613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28025601897182374878948301 10509600711443390579605613)
                  ·
                    refine ⟨3941100266791271467352105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10509600711443390579605613 3941100266791271467352105)
                    ·
                      refine ⟨2955825200093453600514079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941100266791271467352105 2955825200093453600514079)
                      ·
                        rfl

theorem cell23_5756449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5756449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756449 prefixEnd_5756449 := by exact prefixLift 5756449
  have htrace : WordTrace (prefixWord ++ tailWord_5756449) baseStart_5756449 baseEnd_5756449 := by
    simpa [prefixWord, tailWord_5756449, baseEnd_5756449] using wordTrace_append hprefix tailTrace_5756449
  have hstable : (prefixWord ++ tailWord_5756449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756449).length < 2 ^ (prefixWord ++ tailWord_5756449).sum := by decide
  have hdescent : baseEnd_5756449 < baseStart_5756449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756456 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5756456 : Nat := 118140960795 + 5756456 * 2 ^ 59
def prefixEnd_5756456 : Nat := 4983230072969 + 3 ^ 40 * 5756456 * 2
def baseEnd_5756456 : Nat := 2955828794458035073126547

theorem tailTrace_5756456 : CollatzResearch.WordTrace tailWord_5756456 prefixEnd_5756456 2955828794458035073126547 := by
  unfold tailWord_5756456
  simp only [CollatzResearch.WordTrace]
  refine ⟨104977599416675255629688611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139970132555567007506251481 104977599416675255629688611)
  ·
    refine ⟨157466399125012883444532917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104977599416675255629688611 157466399125012883444532917)
    ·
      refine ⟨14762474917969957822924961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157466399125012883444532917 14762474917969957822924961)
      ·
        refine ⟨11071856188477468367193721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14762474917969957822924961 11071856188477468367193721)
        ·
          refine ⟨8303892141358101275395291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11071856188477468367193721 8303892141358101275395291)
          ·
            refine ⟨12455838212037151913092937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303892141358101275395291 12455838212037151913092937)
            ·
              refine ⟨9341878659027863934819703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12455838212037151913092937 9341878659027863934819703)
              ·
                refine ⟨14012817988541795902229555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9341878659027863934819703 14012817988541795902229555)
                ·
                  refine ⟨21019226982812693853344333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14012817988541795902229555 21019226982812693853344333)
                  ·
                    refine ⟨7882210118554760195004125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21019226982812693853344333 7882210118554760195004125)
                    ·
                      refine ⟨2955828794458035073126547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882210118554760195004125 2955828794458035073126547)
                      ·
                        rfl

theorem cell23_5756456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5756456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756456 prefixEnd_5756456 := by exact prefixLift 5756456
  have htrace : WordTrace (prefixWord ++ tailWord_5756456) baseStart_5756456 baseEnd_5756456 := by
    simpa [prefixWord, tailWord_5756456, baseEnd_5756456] using wordTrace_append hprefix tailTrace_5756456
  have hstable : (prefixWord ++ tailWord_5756456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756456).length < 2 ^ (prefixWord ++ tailWord_5756456).sum := by decide
  have hdescent : baseEnd_5756456 < baseStart_5756456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756479 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 4, 2]
def baseStart_5756479 : Nat := 118140960795 + 5756479 * 2 ^ 59
def prefixEnd_5756479 : Nat := 4983230072969 + 3 ^ 40 * 5756479 * 2
def baseEnd_5756479 : Nat := 2955840604513088483138941

theorem tailTrace_5756479 : CollatzResearch.WordTrace tailWord_5756479 prefixEnd_5756479 2955840604513088483138941 := by
  unfold tailWord_5756479
  simp only [CollatzResearch.WordTrace]
  refine ⟨209956037712267186187464491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139970691808178124124976327 209956037712267186187464491)
  ·
    refine ⟨314934056568400779281196737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209956037712267186187464491 314934056568400779281196737)
    ·
      refine ⟨236200542426300584460897553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314934056568400779281196737 236200542426300584460897553)
      ·
        refine ⟨177150406819725438345673165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236200542426300584460897553 177150406819725438345673165)
        ·
          refine ⟨66431402557397039379627437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177150406819725438345673165 66431402557397039379627437)
          ·
            refine ⟨24911775959023889767360289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66431402557397039379627437 24911775959023889767360289)
            ·
              refine ⟨18683831969267917325520217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24911775959023889767360289 18683831969267917325520217)
              ·
                refine ⟨14012873976950937994140163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18683831969267917325520217 14012873976950937994140163)
                ·
                  refine ⟨21019310965426406991210245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14012873976950937994140163 21019310965426406991210245)
                  ·
                    refine ⟨3941120806017451310851921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21019310965426406991210245 3941120806017451310851921)
                    ·
                      refine ⟨2955840604513088483138941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941120806017451310851921 2955840604513088483138941)
                      ·
                        rfl

theorem cell23_5756479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_5756479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756479 prefixEnd_5756479 := by exact prefixLift 5756479
  have htrace : WordTrace (prefixWord ++ tailWord_5756479) baseStart_5756479 baseEnd_5756479 := by
    simpa [prefixWord, tailWord_5756479, baseEnd_5756479] using wordTrace_append hprefix tailTrace_5756479
  have hstable : (prefixWord ++ tailWord_5756479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756479).length < 2 ^ (prefixWord ++ tailWord_5756479).sum := by decide
  have hdescent : baseEnd_5756479 < baseStart_5756479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756485 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 9]
def baseStart_5756485 : Nat := 118140960795 + 5756485 * 2 ^ 59
def prefixEnd_5756485 : Nat := 4983230072969 + 3 ^ 40 * 5756485 * 2
def baseEnd_5756485 : Nat := 328427076155223939962657

theorem tailTrace_5756485 : CollatzResearch.WordTrace tailWord_5756485 prefixEnd_5756485 328427076155223939962657 := by
  unfold tailWord_5756485
  simp only [CollatzResearch.WordTrace]
  refine ⟨209956256550245449212182909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139970837700163632808121939 209956256550245449212182909)
  ·
    refine ⟨78733596206342043454568591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209956256550245449212182909 78733596206342043454568591)
    ·
      refine ⟨118100394309513065181852887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78733596206342043454568591 118100394309513065181852887)
      ·
        refine ⟨177150591464269597772779331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118100394309513065181852887 177150591464269597772779331)
        ·
          refine ⟨265725887196404396659168997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177150591464269597772779331 265725887196404396659168997)
          ·
            refine ⟨49823603849325824373594187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265725887196404396659168997 49823603849325824373594187)
            ·
              refine ⟨74735405773988736560391281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49823603849325824373594187 74735405773988736560391281)
              ·
                refine ⟨56051554330491552420293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74735405773988736560391281 56051554330491552420293461)
                ·
                  refine ⟨328427076155223939962657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56051554330491552420293461 328427076155223939962657)
                  ·
                    rfl

theorem cell23_5756485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_5756485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756485 prefixEnd_5756485 := by exact prefixLift 5756485
  have htrace : WordTrace (prefixWord ++ tailWord_5756485) baseStart_5756485 baseEnd_5756485 := by
    simpa [prefixWord, tailWord_5756485, baseEnd_5756485] using wordTrace_append hprefix tailTrace_5756485
  have hstable : (prefixWord ++ tailWord_5756485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756485).length < 2 ^ (prefixWord ++ tailWord_5756485).sum := by decide
  have hdescent : baseEnd_5756485 < baseStart_5756485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756492 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5756492 : Nat := 118140960795 + 5756492 * 2 ^ 59
def prefixEnd_5756492 : Nat := 4983230072969 + 3 ^ 40 * 5756492 * 2
def baseEnd_5756492 : Nat := 2955847279761596932276381

theorem tailTrace_5756492 : CollatzResearch.WordTrace tailWord_5756492 prefixEnd_5756492 2955847279761596932276381 := by
  unfold tailWord_5756492
  simp only [CollatzResearch.WordTrace]
  refine ⟨104978255930610044703843865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139971007907480059605125153 104978255930610044703843865)
  ·
    refine ⟨78733691947957533527882899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104978255930610044703843865 78733691947957533527882899)
    ·
      refine ⟨118100537921936300291824349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78733691947957533527882899 118100537921936300291824349)
      ·
        refine ⟨44287701720726112609434131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118100537921936300291824349 44287701720726112609434131)
        ·
          refine ⟨66431552581089168914151197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44287701720726112609434131 66431552581089168914151197)
          ·
            refine ⟨24911832217908438342806699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66431552581089168914151197 24911832217908438342806699)
            ·
              refine ⟨37367748326862657514210049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24911832217908438342806699 37367748326862657514210049)
              ·
                refine ⟨28025811245146993135657537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37367748326862657514210049 28025811245146993135657537)
                ·
                  refine ⟨21019358433860244851743153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28025811245146993135657537 21019358433860244851743153)
                  ·
                    refine ⟨15764518825395183638807365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21019358433860244851743153 15764518825395183638807365)
                    ·
                      refine ⟨2955847279761596932276381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15764518825395183638807365 2955847279761596932276381)
                      ·
                        rfl

theorem cell23_5756492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5756492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756492 prefixEnd_5756492 := by exact prefixLift 5756492
  have htrace : WordTrace (prefixWord ++ tailWord_5756492) baseStart_5756492 baseEnd_5756492 := by
    simpa [prefixWord, tailWord_5756492, baseEnd_5756492] using wordTrace_append hprefix tailTrace_5756492
  have hstable : (prefixWord ++ tailWord_5756492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756492).length < 2 ^ (prefixWord ++ tailWord_5756492).sum := by decide
  have hdescent : baseEnd_5756492 < baseStart_5756492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756513 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_5756513 : Nat := 118140960795 + 5756513 * 2 ^ 59
def prefixEnd_5756513 : Nat := 4983230072969 + 3 ^ 40 * 5756513 * 2
def baseEnd_5756513 : Nat := 2955858062855341350113785

theorem tailTrace_5756513 : CollatzResearch.WordTrace tailWord_5756513 prefixEnd_5756513 2955858062855341350113785 := by
  unfold tailWord_5756513
  simp only [CollatzResearch.WordTrace]
  refine ⟨209957277794144009994202193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139971518529429339996134795 209957277794144009994202193)
  ·
    refine ⟨157467958345608007495651645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209957277794144009994202193 157467958345608007495651645)
    ·
      refine ⟨59050484379603002810869367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157467958345608007495651645 59050484379603002810869367)
      ·
        refine ⟨88575726569404504216304051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59050484379603002810869367 88575726569404504216304051)
        ·
          refine ⟨132863589854106756324456077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88575726569404504216304051 132863589854106756324456077)
          ·
            refine ⟨49823846195290033621671029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132863589854106756324456077 49823846195290033621671029)
            ·
              refine ⟨4670985580808440652031659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49823846195290033621671029 4670985580808440652031659)
              ·
                refine ⟨7006478371212660978047489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670985580808440652031659 7006478371212660978047489)
                ·
                  refine ⟨5254858778409495733535617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006478371212660978047489 5254858778409495733535617)
                  ·
                    refine ⟨3941144083807121800151713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254858778409495733535617 3941144083807121800151713)
                    ·
                      refine ⟨2955858062855341350113785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941144083807121800151713 2955858062855341350113785)
                      ·
                        rfl

theorem cell23_5756513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_5756513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756513 prefixEnd_5756513 := by exact prefixLift 5756513
  have htrace : WordTrace (prefixWord ++ tailWord_5756513) baseStart_5756513 baseEnd_5756513 := by
    simpa [prefixWord, tailWord_5756513, baseEnd_5756513] using wordTrace_append hprefix tailTrace_5756513
  have hstable : (prefixWord ++ tailWord_5756513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756513).length < 2 ^ (prefixWord ++ tailWord_5756513).sum := by decide
  have hdescent : baseEnd_5756513 < baseStart_5756513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756564 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5756564 : Nat := 118140960795 + 5756564 * 2 ^ 59
def prefixEnd_5756564 : Nat := 4983230072969 + 3 ^ 40 * 5756564 * 2
def baseEnd_5756564 : Nat := 2955884250368720650576051

theorem tailTrace_5756564 : CollatzResearch.WordTrace tailWord_5756564 prefixEnd_5756564 2955884250368720650576051 := by
  unfold tailWord_5756564
  simp only [CollatzResearch.WordTrace]
  refine ⟨104979568958479622852154373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139972758611306163802872497 104979568958479622852154373)
  ·
    refine ⟨19683669179714929284778945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104979568958479622852154373 19683669179714929284778945)
    ·
      refine ⟨14762751884786196963584209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19683669179714929284778945 14762751884786196963584209)
      ·
        refine ⟨11072063913589647722688157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14762751884786196963584209 11072063913589647722688157)
        ·
          refine ⟨4152023967596117896008059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11072063913589647722688157 4152023967596117896008059)
          ·
            refine ⟨6228035951394176844012089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152023967596117896008059 6228035951394176844012089)
            ·
              refine ⟨4671026963545632633009067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228035951394176844012089 4671026963545632633009067)
              ·
                refine ⟨7006540445318448949513601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671026963545632633009067 7006540445318448949513601)
                ·
                  refine ⟨5254905333988836712135201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006540445318448949513601 5254905333988836712135201)
                  ·
                    refine ⟨3941179000491627534101401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254905333988836712135201 3941179000491627534101401)
                    ·
                      refine ⟨2955884250368720650576051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941179000491627534101401 2955884250368720650576051)
                      ·
                        rfl

theorem cell23_5756564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5756564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756564 prefixEnd_5756564 := by exact prefixLift 5756564
  have htrace : WordTrace (prefixWord ++ tailWord_5756564) baseStart_5756564 baseEnd_5756564 := by
    simpa [prefixWord, tailWord_5756564, baseEnd_5756564] using wordTrace_append hprefix tailTrace_5756564
  have hstable : (prefixWord ++ tailWord_5756564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756564).length < 2 ^ (prefixWord ++ tailWord_5756564).sum := by decide
  have hdescent : baseEnd_5756564 < baseStart_5756564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756606 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_5756606 : Nat := 118140960795 + 5756606 * 2 ^ 59
def prefixEnd_5756606 : Nat := 4983230072969 + 3 ^ 40 * 5756606 * 2
def baseEnd_5756606 : Nat := 2955905816556209486250857

theorem tailTrace_5756606 : CollatzResearch.WordTrace tailWord_5756606 prefixEnd_5756606 2955905816556209486250857 := by
  unfold tailWord_5756606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245083722850885859667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139973779855204724584891781 26245083722850885859667209)
  ·
    refine ⟨19683812792138164394750407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26245083722850885859667209 19683812792138164394750407)
    ·
      refine ⟨29525719188207246592125611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19683812792138164394750407 29525719188207246592125611)
      ·
        refine ⟨44288578782310869888188417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29525719188207246592125611 44288578782310869888188417)
        ·
          refine ⟨33216434086733152416141313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44288578782310869888188417 33216434086733152416141313)
          ·
            refine ⟨24912325565049864312105985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33216434086733152416141313 24912325565049864312105985)
            ·
              refine ⟨18684244173787398234079489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24912325565049864312105985 18684244173787398234079489)
              ·
                refine ⟨14013183130340548675559617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18684244173787398234079489 14013183130340548675559617)
                ·
                  refine ⟨10509887347755411506669713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14013183130340548675559617 10509887347755411506669713)
                  ·
                    refine ⟨7882415510816558630002285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10509887347755411506669713 7882415510816558630002285)
                    ·
                      refine ⟨2955905816556209486250857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882415510816558630002285 2955905816556209486250857)
                      ·
                        rfl

theorem cell23_5756606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_5756606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756606 prefixEnd_5756606 := by exact prefixLift 5756606
  have htrace : WordTrace (prefixWord ++ tailWord_5756606) baseStart_5756606 baseEnd_5756606 := by
    simpa [prefixWord, tailWord_5756606, baseEnd_5756606] using wordTrace_append hprefix tailTrace_5756606
  have hstable : (prefixWord ++ tailWord_5756606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756606).length < 2 ^ (prefixWord ++ tailWord_5756606).sum := by decide
  have hdescent : baseEnd_5756606 < baseStart_5756606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756619 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 3]
def baseStart_5756619 : Nat := 118140960795 + 5756619 * 2 ^ 59
def prefixEnd_5756619 : Nat := 4983230072969 + 3 ^ 40 * 5756619 * 2
def baseEnd_5756619 : Nat := 2955912491804717935388297

theorem tailTrace_5756619 : CollatzResearch.WordTrace tailWord_5756619 prefixEnd_5756619 2955912491804717935388297 := by
  unfold tailWord_5756619
  simp only [CollatzResearch.WordTrace]
  refine ⟨209961143931759990097560911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139974095954506660065040607 209961143931759990097560911)
  ·
    refine ⟨314941715897639985146341367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209961143931759990097560911 314941715897639985146341367)
    ·
      refine ⟨472412573846459977719512051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314941715897639985146341367 472412573846459977719512051)
      ·
        refine ⟨708618860769689966579268077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472412573846459977719512051 708618860769689966579268077)
        ·
          refine ⟨265732072788633737467225529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708618860769689966579268077 265732072788633737467225529)
          ·
            refine ⟨199299054591475303100419147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265732072788633737467225529 199299054591475303100419147)
            ·
              refine ⟨298948581887212954650628721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199299054591475303100419147 298948581887212954650628721)
              ·
                refine ⟨224211436415409715987971541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298948581887212954650628721 224211436415409715987971541)
                ·
                  refine ⟨5254955540986165218468083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224211436415409715987971541 5254955540986165218468083)
                  ·
                    refine ⟨7882433311479247827702125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254955540986165218468083 7882433311479247827702125)
                    ·
                      refine ⟨2955912491804717935388297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882433311479247827702125 2955912491804717935388297)
                      ·
                        rfl

theorem cell23_5756619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 3].length) (baseStart_5756619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756619 prefixEnd_5756619 := by exact prefixLift 5756619
  have htrace : WordTrace (prefixWord ++ tailWord_5756619) baseStart_5756619 baseEnd_5756619 := by
    simpa [prefixWord, tailWord_5756619, baseEnd_5756619] using wordTrace_append hprefix tailTrace_5756619
  have hstable : (prefixWord ++ tailWord_5756619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756619).length < 2 ^ (prefixWord ++ tailWord_5756619).sum := by decide
  have hdescent : baseEnd_5756619 < baseStart_5756619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756630 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5756630 : Nat := 118140960795 + 5756630 * 2 ^ 59
def prefixEnd_5756630 : Nat := 4983230072969 + 3 ^ 40 * 5756630 * 2
def baseEnd_5756630 : Nat := 985306046697305797450249

theorem tailTrace_5756630 : CollatzResearch.WordTrace tailWord_5756630 prefixEnd_5756630 985306046697305797450249 := by
  unfold tailWord_5756630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122596570920008686013209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139974363423146759317474229 13122596570920008686013209)
  ·
    refine ⟨9841947428190006514509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13122596570920008686013209 9841947428190006514509907)
    ·
      refine ⟨14762921142285009771764861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9841947428190006514509907 14762921142285009771764861)
      ·
        refine ⟨5536095428356878664411823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14762921142285009771764861 5536095428356878664411823)
        ·
          refine ⟨8304143142535317996617735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536095428356878664411823 8304143142535317996617735)
          ·
            refine ⟨12456214713802976994926603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304143142535317996617735 12456214713802976994926603)
            ·
              refine ⟨18684322070704465492389905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12456214713802976994926603 18684322070704465492389905)
              ·
                refine ⟨14013241553028349119292429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18684322070704465492389905 14013241553028349119292429)
                ·
                  refine ⟨5254965582385630919734661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14013241553028349119292429 5254965582385630919734661)
                  ·
                    refine ⟨985306046697305797450249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254965582385630919734661 985306046697305797450249)
                    ·
                      rfl

theorem cell23_5756630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5756630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756630 prefixEnd_5756630 := by exact prefixLift 5756630
  have htrace : WordTrace (prefixWord ++ tailWord_5756630) baseStart_5756630 baseEnd_5756630 := by
    simpa [prefixWord, tailWord_5756630, baseEnd_5756630] using wordTrace_append hprefix tailTrace_5756630
  have hstable : (prefixWord ++ tailWord_5756630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756630).length < 2 ^ (prefixWord ++ tailWord_5756630).sum := by decide
  have hdescent : baseEnd_5756630 < baseStart_5756630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756632 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5756632 : Nat := 118140960795 + 5756632 * 2 ^ 59
def prefixEnd_5756632 : Nat := 4983230072969 + 3 ^ 40 * 5756632 * 2
def baseEnd_5756632 : Nat := 2955919167053226384525737

theorem tailTrace_5756632 : CollatzResearch.WordTrace tailWord_5756632 prefixEnd_5756632 2955919167053226384525737 := by
  unfold tailWord_5756632
  simp only [CollatzResearch.WordTrace]
  refine ⟨104980809040356446658892075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139974412053808595545189433 104980809040356446658892075)
  ·
    refine ⟨157471213560534669988338113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104980809040356446658892075 157471213560534669988338113)
    ·
      refine ⟨118103410170401002491253585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157471213560534669988338113 118103410170401002491253585)
      ·
        refine ⟨88577557627800751868440189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118103410170401002491253585 88577557627800751868440189)
        ·
          refine ⟨33216584110425281950665071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88577557627800751868440189 33216584110425281950665071)
          ·
            refine ⟨49824876165637922925997607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33216584110425281950665071 49824876165637922925997607)
            ·
              refine ⟨74737314248456884388996411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49824876165637922925997607 74737314248456884388996411)
              ·
                refine ⟨112105971372685326583494617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74737314248456884388996411 112105971372685326583494617)
                ·
                  refine ⟨84079478529513994937620963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112105971372685326583494617 84079478529513994937620963)
                  ·
                    refine ⟨126119217794270992406431445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84079478529513994937620963 126119217794270992406431445)
                    ·
                      refine ⟨2955919167053226384525737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126119217794270992406431445 2955919167053226384525737)
                      ·
                        rfl

theorem cell23_5756632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5756632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756632 prefixEnd_5756632 := by exact prefixLift 5756632
  have htrace : WordTrace (prefixWord ++ tailWord_5756632) baseStart_5756632 baseEnd_5756632 := by
    simpa [prefixWord, tailWord_5756632, baseEnd_5756632] using wordTrace_append hprefix tailTrace_5756632
  have hstable : (prefixWord ++ tailWord_5756632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756632).length < 2 ^ (prefixWord ++ tailWord_5756632).sum := by decide
  have hdescent : baseEnd_5756632 < baseStart_5756632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756639 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 1, 5]
def baseStart_5756639 : Nat := 118140960795 + 5756639 * 2 ^ 59
def prefixEnd_5756639 : Nat := 4983230072969 + 3 ^ 40 * 5756639 * 2
def baseEnd_5756639 : Nat := 985307587139269285712735

theorem tailTrace_5756639 : CollatzResearch.WordTrace tailWord_5756639 prefixEnd_5756639 985307587139269285712735 := by
  unfold tailWord_5756639
  simp only [CollatzResearch.WordTrace]
  refine ⟨209961873391687533513288971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139974582261125022342192647 209961873391687533513288971)
  ·
    refine ⟨314942810087531300269933457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209961873391687533513288971 314942810087531300269933457)
    ·
      refine ⟨236207107565648475202450093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314942810087531300269933457 236207107565648475202450093)
      ·
        refine ⟨88577665337118178200918785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236207107565648475202450093 88577665337118178200918785)
        ·
          refine ⟨66433249002838633650689089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88577665337118178200918785 66433249002838633650689089)
          ·
            refine ⟨49824936752128975238016817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66433249002838633650689089 49824936752128975238016817)
            ·
              refine ⟨37368702564096731428512613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49824936752128975238016817 37368702564096731428512613)
              ·
                refine ⟨7006631730768137142846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37368702564096731428512613 7006631730768137142846115)
                ·
                  refine ⟨10509947596152205714269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006631730768137142846115 10509947596152205714269173)
                  ·
                    refine ⟨985307587139269285712735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10509947596152205714269173 985307587139269285712735)
                    ·
                      rfl

theorem cell23_5756639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_5756639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756639 prefixEnd_5756639 := by exact prefixLift 5756639
  have htrace : WordTrace (prefixWord ++ tailWord_5756639) baseStart_5756639 baseEnd_5756639 := by
    simpa [prefixWord, tailWord_5756639, baseEnd_5756639] using wordTrace_append hprefix tailTrace_5756639
  have hstable : (prefixWord ++ tailWord_5756639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756639).length < 2 ^ (prefixWord ++ tailWord_5756639).sum := by decide
  have hdescent : baseEnd_5756639 < baseStart_5756639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756660 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5756660 : Nat := 118140960795 + 5756660 * 2 ^ 59
def prefixEnd_5756660 : Nat := 4983230072969 + 3 ^ 40 * 5756660 * 2
def baseEnd_5756660 : Nat := 328437060501283586108401

theorem tailTrace_5756660 : CollatzResearch.WordTrace tailWord_5756660 prefixEnd_5756660 328437060501283586108401 := by
  unfold tailWord_5756660
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981319662305727049901717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139975092883074302733202289 104981319662305727049901717)
  ·
    refine ⟨4920999359170580955464143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104981319662305727049901717 4920999359170580955464143)
    ·
      refine ⟨7381499038755871433196215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920999359170580955464143 7381499038755871433196215)
      ·
        refine ⟨11072248558133807149794323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381499038755871433196215 11072248558133807149794323)
        ·
          refine ⟨16608372837200710724691485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11072248558133807149794323 16608372837200710724691485)
          ·
            refine ⟨6228139813950266521759307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16608372837200710724691485 6228139813950266521759307)
            ·
              refine ⟨9342209720925399782638961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228139813950266521759307 9342209720925399782638961)
              ·
                refine ⟨7006657290694049836979221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9342209720925399782638961 7006657290694049836979221)
                ·
                  refine ⟨328437060501283586108401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7006657290694049836979221 328437060501283586108401)
                  ·
                    rfl

theorem cell23_5756660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5756660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756660 prefixEnd_5756660 := by exact prefixLift 5756660
  have htrace : WordTrace (prefixWord ++ tailWord_5756660) baseStart_5756660 baseEnd_5756660 := by
    simpa [prefixWord, tailWord_5756660, baseEnd_5756660] using wordTrace_append hprefix tailTrace_5756660
  have hstable : (prefixWord ++ tailWord_5756660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756660).length < 2 ^ (prefixWord ++ tailWord_5756660).sum := by decide
  have hdescent : baseEnd_5756660 < baseStart_5756660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756670 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5756670 : Nat := 118140960795 + 5756670 * 2 ^ 59
def prefixEnd_5756670 : Nat := 4983230072969 + 3 ^ 40 * 5756670 * 2
def baseEnd_5756670 : Nat := 2955938679318097235850563

theorem tailTrace_5756670 : CollatzResearch.WordTrace tailWord_5756670 prefixEnd_5756670 2955938679318097235850563 := by
  unfold tailWord_5756670
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245375506821903225958433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139975336036383483871778309 26245375506821903225958433)
  ·
    refine ⟨19684031630116427419468825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26245375506821903225958433 19684031630116427419468825)
    ·
      refine ⟨14763023722587320564601619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19684031630116427419468825 14763023722587320564601619)
      ·
        refine ⟨22144535583880980846902429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14763023722587320564601619 22144535583880980846902429)
        ·
          refine ⟨8304200843955367817588411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22144535583880980846902429 8304200843955367817588411)
          ·
            refine ⟨12456301265933051726382617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304200843955367817588411 12456301265933051726382617)
            ·
              refine ⟨9342225949449788794786963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12456301265933051726382617 9342225949449788794786963)
              ·
                refine ⟨14013338924174683192180445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342225949449788794786963 14013338924174683192180445)
                ·
                  refine ⟨5255002096565506197067667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14013338924174683192180445 5255002096565506197067667)
                  ·
                    refine ⟨7882503144848259295601501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5255002096565506197067667 7882503144848259295601501)
                    ·
                      refine ⟨2955938679318097235850563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882503144848259295601501 2955938679318097235850563)
                      ·
                        rfl

theorem cell23_5756670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5756670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756670 prefixEnd_5756670 := by exact prefixLift 5756670
  have htrace : WordTrace (prefixWord ++ tailWord_5756670) baseStart_5756670 baseEnd_5756670 := by
    simpa [prefixWord, tailWord_5756670, baseEnd_5756670] using wordTrace_append hprefix tailTrace_5756670
  have hstable : (prefixWord ++ tailWord_5756670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756670).length < 2 ^ (prefixWord ++ tailWord_5756670).sum := by decide
  have hdescent : baseEnd_5756670 < baseStart_5756670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756672 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_5756672 : Nat := 118140960795 + 5756672 * 2 ^ 59
def prefixEnd_5756672 : Nat := 4983230072969 + 3 ^ 40 * 5756672 * 2
def baseEnd_5756672 : Nat := 2955939706279406228025553

theorem tailTrace_5756672 : CollatzResearch.WordTrace tailWord_5756672 prefixEnd_5756672 2955939706279406228025553 := by
  unfold tailWord_5756672
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981538500283990074620135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139975384667045320099493513 104981538500283990074620135)
  ·
    refine ⟨157472307750425985111930203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104981538500283990074620135 157472307750425985111930203)
    ·
      refine ⟨236208461625638977667895305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157472307750425985111930203 236208461625638977667895305)
      ·
        refine ⟨177156346219229233250921479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236208461625638977667895305 177156346219229233250921479)
        ·
          refine ⟨265734519328843849876382219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177156346219229233250921479 265734519328843849876382219)
          ·
            refine ⟨398601778993265774814573329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265734519328843849876382219 398601778993265774814573329)
            ·
              refine ⟨298951334244949331110929997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398601778993265774814573329 298951334244949331110929997)
              ·
                refine ⟨112106750341855999166598749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298951334244949331110929997 112106750341855999166598749)
                ·
                  refine ⟨42040031378195999687474531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112106750341855999166598749 42040031378195999687474531)
                  ·
                    refine ⟨63060047067293999531211797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42040031378195999687474531 63060047067293999531211797)
                    ·
                      refine ⟨2955939706279406228025553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63060047067293999531211797 2955939706279406228025553)
                      ·
                        rfl

theorem cell23_5756672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_5756672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756672 prefixEnd_5756672 := by exact prefixLift 5756672
  have htrace : WordTrace (prefixWord ++ tailWord_5756672) baseStart_5756672 baseEnd_5756672 := by
    simpa [prefixWord, tailWord_5756672, baseEnd_5756672] using wordTrace_append hprefix tailTrace_5756672
  have hstable : (prefixWord ++ tailWord_5756672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756672).length < 2 ^ (prefixWord ++ tailWord_5756672).sum := by decide
  have hdescent : baseEnd_5756672 < baseStart_5756672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756686 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_5756686 : Nat := 118140960795 + 5756686 * 2 ^ 59
def prefixEnd_5756686 : Nat := 4983230072969 + 3 ^ 40 * 5756686 * 2
def baseEnd_5756686 : Nat := 985315631669523057750163

theorem tailTrace_5756686 : CollatzResearch.WordTrace tailWord_5756686 prefixEnd_5756686 985315631669523057750163 := by
  unfold tailWord_5756686
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245448452814657567531239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139975725081678173693499941 26245448452814657567531239)
  ·
    refine ⟨39368172679221986351296859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26245448452814657567531239 39368172679221986351296859)
    ·
      refine ⟨59052259018832979526945289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39368172679221986351296859 59052259018832979526945289)
      ·
        refine ⟨44289194264124734645208967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59052259018832979526945289 44289194264124734645208967)
        ·
          refine ⟨66433791396187101967813451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44289194264124734645208967 66433791396187101967813451)
          ·
            refine ⟨99650687094280652951720177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66433791396187101967813451 99650687094280652951720177)
            ·
              refine ⟨74738015320710489713790133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99650687094280652951720177 74738015320710489713790133)
              ·
                refine ⟨7006688936316608410667825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74738015320710489713790133 7006688936316608410667825)
                ·
                  refine ⟨5255016702237456308000869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006688936316608410667825 5255016702237456308000869)
                  ·
                    refine ⟨985315631669523057750163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255016702237456308000869 985315631669523057750163)
                    ·
                      rfl

theorem cell23_5756686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_5756686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756686 prefixEnd_5756686 := by exact prefixLift 5756686
  have htrace : WordTrace (prefixWord ++ tailWord_5756686) baseStart_5756686 baseEnd_5756686 := by
    simpa [prefixWord, tailWord_5756686, baseEnd_5756686] using wordTrace_append hprefix tailTrace_5756686
  have hstable : (prefixWord ++ tailWord_5756686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756686).length < 2 ^ (prefixWord ++ tailWord_5756686).sum := by decide
  have hdescent : baseEnd_5756686 < baseStart_5756686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756693 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_5756693 : Nat := 118140960795 + 5756693 * 2 ^ 59
def prefixEnd_5756693 : Nat := 4983230072969 + 3 ^ 40 * 5756693 * 2
def baseEnd_5756693 : Nat := 2955950489373150645862957

theorem tailTrace_5756693 : CollatzResearch.WordTrace tailWord_5756693 prefixEnd_5756693 2955950489373150645862957 := by
  unfold tailWord_5756693
  simp only [CollatzResearch.WordTrace]
  refine ⟨209963842933491900735754733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139975895288994600490503155 209963842933491900735754733)
  ·
    refine ⟨78736441100059462775908025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209963842933491900735754733 78736441100059462775908025)
    ·
      refine ⟨59052330825044597081931019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78736441100059462775908025 59052330825044597081931019)
      ·
        refine ⟨88578496237566895622896529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59052330825044597081931019 88578496237566895622896529)
        ·
          refine ⟨66433872178175171717172397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88578496237566895622896529 66433872178175171717172397)
          ·
            refine ⟨24912702066815689393939649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66433872178175171717172397 24912702066815689393939649)
            ·
              refine ⟨18684526550111767045454737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24912702066815689393939649 18684526550111767045454737)
              ·
                refine ⟨14013394912583825284091053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18684526550111767045454737 14013394912583825284091053)
                ·
                  refine ⟨5255023092218934481534145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14013394912583825284091053 5255023092218934481534145)
                  ·
                    refine ⟨3941267319164200861150609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5255023092218934481534145 3941267319164200861150609)
                    ·
                      refine ⟨2955950489373150645862957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941267319164200861150609 2955950489373150645862957)
                      ·
                        rfl

theorem cell23_5756693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_5756693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756693 prefixEnd_5756693 := by exact prefixLift 5756693
  have htrace : WordTrace (prefixWord ++ tailWord_5756693) baseStart_5756693 baseEnd_5756693 := by
    simpa [prefixWord, tailWord_5756693, baseEnd_5756693] using wordTrace_append hprefix tailTrace_5756693
  have hstable : (prefixWord ++ tailWord_5756693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756693).length < 2 ^ (prefixWord ++ tailWord_5756693).sum := by decide
  have hdescent : baseEnd_5756693 < baseStart_5756693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756696 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5756696 : Nat := 118140960795 + 5756696 * 2 ^ 59
def prefixEnd_5756696 : Nat := 4983230072969 + 3 ^ 40 * 5756696 * 2
def baseEnd_5756696 : Nat := 2955952029815114134125443

theorem tailTrace_5756696 : CollatzResearch.WordTrace tailWord_5756696 prefixEnd_5756696 2955952029815114134125443 := by
  unfold tailWord_5756696
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981976176240516124056971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139975968234987354832075961 104981976176240516124056971)
  ·
    refine ⟨157472964264360774186085457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104981976176240516124056971 157472964264360774186085457)
    ·
      refine ⟨118104723198270580639564093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157472964264360774186085457 118104723198270580639564093)
      ·
        refine ⟨44289271199351467739836535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118104723198270580639564093 44289271199351467739836535)
        ·
          refine ⟨66433906799027201609754803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44289271199351467739836535 66433906799027201609754803)
          ·
            refine ⟨99650860198540802414632205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66433906799027201609754803 99650860198540802414632205)
            ·
              refine ⟨37369072574452800905487077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99650860198540802414632205 37369072574452800905487077)
              ·
                refine ⟨7006701107709900169778827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37369072574452800905487077 7006701107709900169778827)
                ·
                  refine ⟨10510051661564850254668241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006701107709900169778827 10510051661564850254668241)
                  ·
                    refine ⟨7882538746173637691001181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10510051661564850254668241 7882538746173637691001181)
                    ·
                      refine ⟨2955952029815114134125443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882538746173637691001181 2955952029815114134125443)
                      ·
                        rfl

theorem cell23_5756696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5756696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756696 prefixEnd_5756696 := by exact prefixLift 5756696
  have htrace : WordTrace (prefixWord ++ tailWord_5756696) baseStart_5756696 baseEnd_5756696 := by
    simpa [prefixWord, tailWord_5756696, baseEnd_5756696] using wordTrace_append hprefix tailTrace_5756696
  have hstable : (prefixWord ++ tailWord_5756696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756696).length < 2 ^ (prefixWord ++ tailWord_5756696).sum := by decide
  have hdescent : baseEnd_5756696 < baseStart_5756696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756753 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_5756753 : Nat := 118140960795 + 5756753 * 2 ^ 59
def prefixEnd_5756753 : Nat := 4983230072969 + 3 ^ 40 * 5756753 * 2
def baseEnd_5756753 : Nat := 2955981298212420411112681

theorem tailTrace_5756753 : CollatzResearch.WordTrace tailWord_5756753 prefixEnd_5756753 2955981298212420411112681 := by
  unfold tailWord_5756753
  simp only [CollatzResearch.WordTrace]
  refine ⟨209966031313274530982938913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139977354208849687321959275 209966031313274530982938913)
  ·
    refine ⟨157474523484955898237204185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209966031313274530982938913 157474523484955898237204185)
    ·
      refine ⟨118105892613716923677903139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157474523484955898237204185 118105892613716923677903139)
      ·
        refine ⟨177158838920575385516854709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118105892613716923677903139 177158838920575385516854709)
        ·
          refine ⟨16608641148803942392205129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177158838920575385516854709 16608641148803942392205129)
          ·
            refine ⟨12456480861602956794153847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16608641148803942392205129 12456480861602956794153847)
            ·
              refine ⟨18684721292404435191230771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12456480861602956794153847 18684721292404435191230771)
              ·
                refine ⟨28027081938606652786846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18684721292404435191230771 28027081938606652786846157)
                ·
                  refine ⟨10510155726977494795067309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28027081938606652786846157 10510155726977494795067309)
                  ·
                    refine ⟨3941308397616560548150241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10510155726977494795067309 3941308397616560548150241)
                    ·
                      refine ⟨2955981298212420411112681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941308397616560548150241 2955981298212420411112681)
                      ·
                        rfl

theorem cell23_5756753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_5756753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756753 prefixEnd_5756753 := by exact prefixLift 5756753
  have htrace : WordTrace (prefixWord ++ tailWord_5756753) baseStart_5756753 baseEnd_5756753 := by
    simpa [prefixWord, tailWord_5756753, baseEnd_5756753] using wordTrace_append hprefix tailTrace_5756753
  have hstable : (prefixWord ++ tailWord_5756753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756753).length < 2 ^ (prefixWord ++ tailWord_5756753).sum := by decide
  have hdescent : baseEnd_5756753 < baseStart_5756753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756769 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5756769 : Nat := 118140960795 + 5756769 * 2 ^ 59
def prefixEnd_5756769 : Nat := 4983230072969 + 3 ^ 40 * 5756769 * 2
def baseEnd_5756769 : Nat := 2955989513902892348512607

theorem tailTrace_5756769 : CollatzResearch.WordTrace tailWord_5756769 prefixEnd_5756769 2955989513902892348512607 := by
  unfold tailWord_5756769
  simp only [CollatzResearch.WordTrace]
  refine ⟨209966614881216565715521361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139977743254144377143680907 209966614881216565715521361)
  ·
    refine ⟨157474961160912424286641021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209966614881216565715521361 157474961160912424286641021)
    ·
      refine ⟨59053110435342159107490383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157474961160912424286641021 59053110435342159107490383)
      ·
        refine ⟨88579665653013238661235575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59053110435342159107490383 88579665653013238661235575)
        ·
          refine ⟨132869498479519857991853363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88579665653013238661235575 132869498479519857991853363)
          ·
            refine ⟨199304247719279786987780045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132869498479519857991853363 199304247719279786987780045)
            ·
              refine ⟨74739092894729920120417517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199304247719279786987780045 74739092894729920120417517)
              ·
                refine ⟨28027159835523720045156569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74739092894729920120417517 28027159835523720045156569)
                ·
                  refine ⟨21020369876642790033867427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28027159835523720045156569 21020369876642790033867427)
                  ·
                    refine ⟨31530554814964185050801141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21020369876642790033867427 31530554814964185050801141)
                    ·
                      refine ⟨2955989513902892348512607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31530554814964185050801141 2955989513902892348512607)
                      ·
                        rfl

theorem cell23_5756769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5756769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756769 prefixEnd_5756769 := by exact prefixLift 5756769
  have htrace : WordTrace (prefixWord ++ tailWord_5756769) baseStart_5756769 baseEnd_5756769 := by
    simpa [prefixWord, tailWord_5756769, baseEnd_5756769] using wordTrace_append hprefix tailTrace_5756769
  have hstable : (prefixWord ++ tailWord_5756769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756769).length < 2 ^ (prefixWord ++ tailWord_5756769).sum := by decide
  have hdescent : baseEnd_5756769 < baseStart_5756769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756778 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5756778 : Nat := 118140960795 + 5756778 * 2 ^ 59
def prefixEnd_5756778 : Nat := 4983230072969 + 3 ^ 40 * 5756778 * 2
def baseEnd_5756778 : Nat := 2955994135228782813300067

theorem tailTrace_5756778 : CollatzResearch.WordTrace tailWord_5756778 prefixEnd_5756778 2955994135228782813300067 := by
  unfold tailWord_5756778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52491735784545990063149747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139977962092122640168399325 52491735784545990063149747)
  ·
    refine ⟨78737603676818985094724621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52491735784545990063149747 78737603676818985094724621)
    ·
      refine ⟨29526601378807119410521733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78737603676818985094724621 29526601378807119410521733)
      ·
        refine ⟨5536237758526334889472825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29526601378807119410521733 5536237758526334889472825)
        ·
          refine ⟨4152178318894751167104619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536237758526334889472825 4152178318894751167104619)
          ·
            refine ⟨6228267478342126750656929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152178318894751167104619 6228267478342126750656929)
            ·
              refine ⟨4671200608756595062992697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228267478342126750656929 4671200608756595062992697)
              ·
                refine ⟨3503400456567446297244523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671200608756595062992697 3503400456567446297244523)
                ·
                  refine ⟨5255100684851169445866785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503400456567446297244523 5255100684851169445866785)
                  ·
                    refine ⟨3941325513638377084400089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5255100684851169445866785 3941325513638377084400089)
                    ·
                      refine ⟨2955994135228782813300067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941325513638377084400089 2955994135228782813300067)
                      ·
                        rfl

theorem cell23_5756778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5756778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756778 prefixEnd_5756778 := by exact prefixLift 5756778
  have htrace : WordTrace (prefixWord ++ tailWord_5756778) baseStart_5756778 baseEnd_5756778 := by
    simpa [prefixWord, tailWord_5756778, baseEnd_5756778] using wordTrace_append hprefix tailTrace_5756778
  have hstable : (prefixWord ++ tailWord_5756778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756778).length < 2 ^ (prefixWord ++ tailWord_5756778).sum := by decide
  have hdescent : baseEnd_5756778 < baseStart_5756778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756779 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_5756779 : Nat := 118140960795 + 5756779 * 2 ^ 59
def prefixEnd_5756779 : Nat := 4983230072969 + 3 ^ 40 * 5756779 * 2
def baseEnd_5756779 : Nat := 2955994648709437309387561

theorem tailTrace_5756779 : CollatzResearch.WordTrace tailWord_5756779 prefixEnd_5756779 2955994648709437309387561 := by
  unfold tailWord_5756779
  simp only [CollatzResearch.WordTrace]
  refine ⟨209966979611180337423385391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139977986407453558282256927 209966979611180337423385391)
  ·
    refine ⟨314950469416770506135078087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209966979611180337423385391 314950469416770506135078087)
    ·
      refine ⟨472425704125155759202617131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314950469416770506135078087 472425704125155759202617131)
      ·
        refine ⟨708638556187733638803925697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472425704125155759202617131 708638556187733638803925697)
        ·
          refine ⟨531478917140800229102944273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708638556187733638803925697 531478917140800229102944273)
          ·
            refine ⟨398609187855600171827208205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531478917140800229102944273 398609187855600171827208205)
            ·
              refine ⟨149478445445850064435203077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398609187855600171827208205 149478445445850064435203077)
              ·
                refine ⟨28027208521096887081600577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149478445445850064435203077 28027208521096887081600577)
                ·
                  refine ⟨21020406390822665311200433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28027208521096887081600577 21020406390822665311200433)
                  ·
                    refine ⟨15765304793116998983400325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21020406390822665311200433 15765304793116998983400325)
                    ·
                      refine ⟨2955994648709437309387561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15765304793116998983400325 2955994648709437309387561)
                      ·
                        rfl

theorem cell23_5756779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_5756779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756779 prefixEnd_5756779 := by exact prefixLift 5756779
  have htrace : WordTrace (prefixWord ++ tailWord_5756779) baseStart_5756779 baseEnd_5756779 := by
    simpa [prefixWord, tailWord_5756779, baseEnd_5756779] using wordTrace_append hprefix tailTrace_5756779
  have hstable : (prefixWord ++ tailWord_5756779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756779).length < 2 ^ (prefixWord ++ tailWord_5756779).sum := by decide
  have hdescent : baseEnd_5756779 < baseStart_5756779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756823 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 5]
def baseStart_5756823 : Nat := 118140960795 + 5756823 * 2 ^ 59
def prefixEnd_5756823 : Nat := 4983230072969 + 3 ^ 40 * 5756823 * 2
def baseEnd_5756823 : Nat := 328446360206470570804151

theorem tailTrace_5756823 : CollatzResearch.WordTrace tailWord_5756823 prefixEnd_5756823 328446360206470570804151 := by
  unfold tailWord_5756823
  simp only [CollatzResearch.WordTrace]
  refine ⟨209968584423020932937987123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139979056282013955291991415 209968584423020932937987123)
  ·
    refine ⟨314952876634531399406980685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209968584423020932937987123 314952876634531399406980685)
    ·
      refine ⟨118107328737949274777617757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314952876634531399406980685 118107328737949274777617757)
      ·
        refine ⟨44290248276730978041606659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118107328737949274777617757 44290248276730978041606659)
        ·
          refine ⟨66435372415096467062409989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44290248276730978041606659 66435372415096467062409989)
          ·
            refine ⟨12456632327830587574201873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66435372415096467062409989 12456632327830587574201873)
            ·
              refine ⟨9342474245872940680651405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12456632327830587574201873 9342474245872940680651405)
              ·
                refine ⟨3503427842202352755244277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9342474245872940680651405 3503427842202352755244277)
                ·
                  refine ⟨328446360206470570804151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3503427842202352755244277 328446360206470570804151)
                  ·
                    rfl

theorem cell23_5756823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 5].length) (baseStart_5756823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756823 prefixEnd_5756823 := by exact prefixLift 5756823
  have htrace : WordTrace (prefixWord ++ tailWord_5756823) baseStart_5756823 baseEnd_5756823 := by
    simpa [prefixWord, tailWord_5756823, baseEnd_5756823] using wordTrace_append hprefix tailTrace_5756823
  have hstable : (prefixWord ++ tailWord_5756823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756823).length < 2 ^ (prefixWord ++ tailWord_5756823).sum := by decide
  have hdescent : baseEnd_5756823 < baseStart_5756823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756834 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5756834 : Nat := 118140960795 + 5756834 * 2 ^ 59
def prefixEnd_5756834 : Nat := 4983230072969 + 3 ^ 40 * 5756834 * 2
def baseEnd_5756834 : Nat := 2956022890145434594199809

theorem tailTrace_5756834 : CollatzResearch.WordTrace tailWord_5756834 prefixEnd_5756834 2956022890145434594199809 := by
  unfold tailWord_5756834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52492246406495270454159389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139979323750654054544425037 52492246406495270454159389)
  ·
    refine ⟨19684592402435726420309771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52492246406495270454159389 19684592402435726420309771)
    ·
      refine ⟨29526888603653589630464657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19684592402435726420309771 29526888603653589630464657)
      ·
        refine ⟨22145166452740192222848493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29526888603653589630464657 22145166452740192222848493)
        ·
          refine ⟨8304437419777572083568185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22145166452740192222848493 8304437419777572083568185)
          ·
            refine ⟨6228328064833179062676139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304437419777572083568185 6228328064833179062676139)
            ·
              refine ⟨9342492097249768594014209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228328064833179062676139 9342492097249768594014209)
              ·
                refine ⟨7006869072937326445510657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9342492097249768594014209 7006869072937326445510657)
                ·
                  refine ⟨5255151804702994834132993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006869072937326445510657 5255151804702994834132993)
                  ·
                    refine ⟨3941363853527246125599745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5255151804702994834132993 3941363853527246125599745)
                    ·
                      refine ⟨2956022890145434594199809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941363853527246125599745 2956022890145434594199809)
                      ·
                        rfl

theorem cell23_5756834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5756834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756834 prefixEnd_5756834 := by exact prefixLift 5756834
  have htrace : WordTrace (prefixWord ++ tailWord_5756834) baseStart_5756834 baseEnd_5756834 := by
    simpa [prefixWord, tailWord_5756834, baseEnd_5756834] using wordTrace_append hprefix tailTrace_5756834
  have hstable : (prefixWord ++ tailWord_5756834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756834).length < 2 ^ (prefixWord ++ tailWord_5756834).sum := by decide
  have hdescent : baseEnd_5756834 < baseStart_5756834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756840 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 7]
def baseStart_5756840 : Nat := 118140960795 + 5756840 * 2 ^ 59
def prefixEnd_5756840 : Nat := 4983230072969 + 3 ^ 40 * 5756840 * 2
def baseEnd_5756840 : Nat := 328447330114373507858309

theorem tailTrace_5756840 : CollatzResearch.WordTrace tailWord_5756840 prefixEnd_5756840 328447330114373507858309 := by
  unfold tailWord_5756840
  simp only [CollatzResearch.WordTrace]
  refine ⟨104984602231979672420677987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139979469642639563227570649 104984602231979672420677987)
  ·
    refine ⟨157476903347969508631016981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104984602231979672420677987 157476903347969508631016981)
    ·
      refine ⟨7381729844436070717078921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157476903347969508631016981 7381729844436070717078921)
      ·
        refine ⟨5536297383327053037809191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381729844436070717078921 5536297383327053037809191)
        ·
          refine ⟨8304446074990579556713787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536297383327053037809191 8304446074990579556713787)
          ·
            refine ⟨12456669112485869335070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304446074990579556713787 12456669112485869335070681)
            ·
              refine ⟨9342501834364402001303011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12456669112485869335070681 9342501834364402001303011)
              ·
                refine ⟨14013752751546603001954517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342501834364402001303011 14013752751546603001954517)
                ·
                  refine ⟨328447330114373507858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14013752751546603001954517 328447330114373507858309)
                  ·
                    rfl

theorem cell23_5756840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_5756840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756840 prefixEnd_5756840 := by exact prefixLift 5756840
  have htrace : WordTrace (prefixWord ++ tailWord_5756840) baseStart_5756840 baseEnd_5756840 := by
    simpa [prefixWord, tailWord_5756840, baseEnd_5756840] using wordTrace_append hprefix tailTrace_5756840
  have hstable : (prefixWord ++ tailWord_5756840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756840).length < 2 ^ (prefixWord ++ tailWord_5756840).sum := by decide
  have hdescent : baseEnd_5756840 < baseStart_5756840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756869 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_5756869 : Nat := 118140960795 + 5756869 * 2 ^ 59
def prefixEnd_5756869 : Nat := 4983230072969 + 3 ^ 40 * 5756869 * 2
def baseEnd_5756869 : Nat := 2956040861968341957262147

theorem tailTrace_5756869 : CollatzResearch.WordTrace tailWord_5756869 prefixEnd_5756869 2956040861968341957262147 := by
  unfold tailWord_5756869
  simp only [CollatzResearch.WordTrace]
  refine ⟨209970262180854282794161661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139980174787236188529441107 209970262180854282794161661)
  ·
    refine ⟨78738848317820356047810623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209970262180854282794161661 78738848317820356047810623)
    ·
      refine ⟨118108272476730534071715935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78738848317820356047810623 118108272476730534071715935)
      ·
        refine ⟨177162408715095801107573903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118108272476730534071715935 177162408715095801107573903)
        ·
          refine ⟨265743613072643701661360855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177162408715095801107573903 265743613072643701661360855)
          ·
            refine ⟨398615419608965552492041283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265743613072643701661360855 398615419608965552492041283)
            ·
              refine ⟨597923129413448328738061925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398615419608965552492041283 597923129413448328738061925)
              ·
                refine ⟨112110586765021561638386611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597923129413448328738061925 112110586765021561638386611)
                ·
                  refine ⟨168165880147532342457579917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112110586765021561638386611 168165880147532342457579917)
                  ·
                    refine ⟨63062205055324628421592469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168165880147532342457579917 63062205055324628421592469)
                    ·
                      refine ⟨2956040861968341957262147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63062205055324628421592469 2956040861968341957262147)
                      ·
                        rfl

theorem cell23_5756869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_5756869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756869 prefixEnd_5756869 := by exact prefixLift 5756869
  have htrace : WordTrace (prefixWord ++ tailWord_5756869) baseStart_5756869 baseEnd_5756869 := by
    simpa [prefixWord, tailWord_5756869, baseEnd_5756869] using wordTrace_append hprefix tailTrace_5756869
  have hstable : (prefixWord ++ tailWord_5756869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756869).length < 2 ^ (prefixWord ++ tailWord_5756869).sum := by decide
  have hdescent : baseEnd_5756869 < baseStart_5756869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756879 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 10]
def baseStart_5756879 : Nat := 118140960795 + 5756879 * 2 ^ 59
def prefixEnd_5756879 : Nat := 4983230072969 + 3 ^ 40 * 5756879 * 2
def baseEnd_5756879 : Nat := 328449555197209657570789

theorem tailTrace_5756879 : CollatzResearch.WordTrace tailWord_5756879 prefixEnd_5756879 328449555197209657570789 := by
  unfold tailWord_5756879
  simp only [CollatzResearch.WordTrace]
  refine ⟨209970626910818054502025691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139980417940545369668017127 209970626910818054502025691)
  ·
    refine ⟨314955940366227081753038537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209970626910818054502025691 314955940366227081753038537)
    ·
      refine ⟨236216955274670311314778903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314955940366227081753038537 236216955274670311314778903)
      ·
        refine ⟨354325432912005466972168355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236216955274670311314778903 354325432912005466972168355)
        ·
          refine ⟨531488149368008200458252533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354325432912005466972168355 531488149368008200458252533)
          ·
            refine ⟨49827014003250768792961175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 531488149368008200458252533 49827014003250768792961175)
            ·
              refine ⟨74740521004876153189441763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49827014003250768792961175 74740521004876153189441763)
              ·
                refine ⟨112110781507314229784162645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74740521004876153189441763 112110781507314229784162645)
                ·
                  refine ⟨328449555197209657570789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112110781507314229784162645 328449555197209657570789)
                  ·
                    rfl

theorem cell23_5756879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 10].length) (baseStart_5756879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756879 prefixEnd_5756879 := by exact prefixLift 5756879
  have htrace : WordTrace (prefixWord ++ tailWord_5756879) baseStart_5756879 baseEnd_5756879 := by
    simpa [prefixWord, tailWord_5756879, baseEnd_5756879] using wordTrace_append hprefix tailTrace_5756879
  have hstable : (prefixWord ++ tailWord_5756879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756879).length < 2 ^ (prefixWord ++ tailWord_5756879).sum := by decide
  have hdescent : baseEnd_5756879 < baseStart_5756879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756913 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 6]
def baseStart_5756913 : Nat := 118140960795 + 5756913 * 2 ^ 59
def prefixEnd_5756913 : Nat := 4983230072969 + 3 ^ 40 * 5756913 * 2
def baseEnd_5756913 : Nat := 328451495013015531679105

theorem tailTrace_5756913 : CollatzResearch.WordTrace tailWord_5756913 prefixEnd_5756913 328451495013015531679105 := by
  unfold tailWord_5756913
  simp only [CollatzResearch.WordTrace]
  refine ⟨209971866992694878308763393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139981244661796585539175595 209971866992694878308763393)
  ·
    refine ⟨157478900244521158731572545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209971866992694878308763393 157478900244521158731572545)
    ·
      refine ⟨118109175183390869048679409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157478900244521158731572545 118109175183390869048679409)
      ·
        refine ⟨88581881387543151786509557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118109175183390869048679409 88581881387543151786509557)
        ·
          refine ⟨8304551380082170479985271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88581881387543151786509557 8304551380082170479985271)
          ·
            refine ⟨12456827070123255719977907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304551380082170479985271 12456827070123255719977907)
            ·
              refine ⟨18685240605184883579966861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12456827070123255719977907 18685240605184883579966861)
              ·
                refine ⟨7006965226944331342487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18685240605184883579966861 7006965226944331342487573)
                ·
                  refine ⟨328451495013015531679105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7006965226944331342487573 328451495013015531679105)
                  ·
                    rfl

theorem cell23_5756913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_5756913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756913 prefixEnd_5756913 := by exact prefixLift 5756913
  have htrace : WordTrace (prefixWord ++ tailWord_5756913) baseStart_5756913 baseEnd_5756913 := by
    simpa [prefixWord, tailWord_5756913, baseEnd_5756913] using wordTrace_append hprefix tailTrace_5756913
  have hstable : (prefixWord ++ tailWord_5756913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756913).length < 2 ^ (prefixWord ++ tailWord_5756913).sum := by decide
  have hdescent : baseEnd_5756913 < baseStart_5756913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756923 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 3]
def baseStart_5756923 : Nat := 118140960795 + 5756923 * 2 ^ 59
def prefixEnd_5756923 : Nat := 4983230072969 + 3 ^ 40 * 5756923 * 2
def baseEnd_5756923 : Nat := 2956068589923684745986899

theorem tailTrace_5756923 : CollatzResearch.WordTrace tailWord_5756923 prefixEnd_5756923 2956068589923684745986899 := by
  unfold tailWord_5756923
  simp only [CollatzResearch.WordTrace]
  refine ⟨209972231722658650016627423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139981487815105766677751615 209972231722658650016627423)
  ·
    refine ⟨314958347583987975024941135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209972231722658650016627423 314958347583987975024941135)
    ·
      refine ⟨472437521375981962537411703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314958347583987975024941135 472437521375981962537411703)
      ·
        refine ⟨708656282063972943806117555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472437521375981962537411703 708656282063972943806117555)
        ·
          refine ⟨1062984423095959415709176333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708656282063972943806117555 1062984423095959415709176333)
          ·
            refine ⟨398619158660984780890941125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1062984423095959415709176333 398619158660984780890941125)
            ·
              refine ⟨74741092248934646417051461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398619158660984780890941125 74741092248934646417051461)
              ·
                refine ⟨14013954796675246203197149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74741092248934646417051461 14013954796675246203197149)
                ·
                  refine ⟨5255233048753217326198931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14013954796675246203197149 5255233048753217326198931)
                  ·
                    refine ⟨7882849573129825989298397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5255233048753217326198931 7882849573129825989298397)
                    ·
                      refine ⟨2956068589923684745986899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882849573129825989298397 2956068589923684745986899)
                      ·
                        rfl

theorem cell23_5756923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 3].length) (baseStart_5756923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756923 prefixEnd_5756923 := by exact prefixLift 5756923
  have htrace : WordTrace (prefixWord ++ tailWord_5756923) baseStart_5756923 baseEnd_5756923 := by
    simpa [prefixWord, tailWord_5756923, baseEnd_5756923] using wordTrace_append hprefix tailTrace_5756923
  have hstable : (prefixWord ++ tailWord_5756923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756923).length < 2 ^ (prefixWord ++ tailWord_5756923).sum := by decide
  have hdescent : baseEnd_5756923 < baseStart_5756923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756951 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 1, 4]
def baseStart_5756951 : Nat := 118140960795 + 5756951 * 2 ^ 59
def prefixEnd_5756951 : Nat := 4983230072969 + 3 ^ 40 * 5756951 * 2
def baseEnd_5756951 : Nat := 985360989127336878812257

theorem tailTrace_5756951 : CollatzResearch.WordTrace tailWord_5756951 prefixEnd_5756951 985360989127336878812257 := by
  unfold tailWord_5756951
  simp only [CollatzResearch.WordTrace]
  refine ⟨209973252966557210798646707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139982168644371473865764471 209973252966557210798646707)
  ·
    refine ⟨314959879449835816197970061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209973252966557210798646707 314959879449835816197970061)
    ·
      refine ⟨118109954793688431074238773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314959879449835816197970061 118109954793688431074238773)
      ·
        refine ⟨11072808261908290413209885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118109954793688431074238773 11072808261908290413209885)
        ·
          refine ⟨4152303098215608904953707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11072808261908290413209885 4152303098215608904953707)
          ·
            refine ⟨6228454647323413357430561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152303098215608904953707 6228454647323413357430561)
            ·
              refine ⟨4671340985492560018072921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228454647323413357430561 4671340985492560018072921)
              ·
                refine ⟨3503505739119420013554691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671340985492560018072921 3503505739119420013554691)
                ·
                  refine ⟨5255258608679130020332037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503505739119420013554691 5255258608679130020332037)
                  ·
                    refine ⟨985360989127336878812257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255258608679130020332037 985360989127336878812257)
                    ·
                      rfl

theorem cell23_5756951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_5756951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756951 prefixEnd_5756951 := by exact prefixLift 5756951
  have htrace : WordTrace (prefixWord ++ tailWord_5756951) baseStart_5756951 baseEnd_5756951 := by
    simpa [prefixWord, tailWord_5756951, baseEnd_5756951] using wordTrace_append hprefix tailTrace_5756951
  have hstable : (prefixWord ++ tailWord_5756951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756951).length < 2 ^ (prefixWord ++ tailWord_5756951).sum := by decide
  have hdescent : baseEnd_5756951 < baseStart_5756951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756983 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_5756983 : Nat := 118140960795 + 5756983 * 2 ^ 59
def prefixEnd_5756983 : Nat := 4983230072969 + 3 ^ 40 * 5756983 * 2
def baseEnd_5756983 : Nat := 2956099398762954511236623

theorem tailTrace_5756983 : CollatzResearch.WordTrace tailWord_5756983 prefixEnd_5756983 2956099398762954511236623 := by
  unfold tailWord_5756983
  simp only [CollatzResearch.WordTrace]
  refine ⟨209974420102441280263811603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139982946734960853509207735 209974420102441280263811603)
  ·
    refine ⟨314961630153661920395717405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209974420102441280263811603 314961630153661920395717405)
    ·
      refine ⟨118110611307623220148394027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314961630153661920395717405 118110611307623220148394027)
      ·
        refine ⟨177165916961434830222591041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118110611307623220148394027 177165916961434830222591041)
        ·
          refine ⟨132874437721076122666943281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177165916961434830222591041 132874437721076122666943281)
          ·
            refine ⟨99655828290807092000207461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132874437721076122666943281 99655828290807092000207461)
            ·
              refine ⟨18685467804526329750038899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99655828290807092000207461 18685467804526329750038899)
              ·
                refine ⟨28028201706789494625058349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18685467804526329750038899 28028201706789494625058349)
                ·
                  refine ⟨10510575640046060484396881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28028201706789494625058349 10510575640046060484396881)
                  ·
                    refine ⟨7882931730034545363297661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10510575640046060484396881 7882931730034545363297661)
                    ·
                      refine ⟨2956099398762954511236623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7882931730034545363297661 2956099398762954511236623)
                      ·
                        rfl

theorem cell23_5756983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_5756983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756983 prefixEnd_5756983 := by exact prefixLift 5756983
  have htrace : WordTrace (prefixWord ++ tailWord_5756983) baseStart_5756983 baseEnd_5756983 := by
    simpa [prefixWord, tailWord_5756983, baseEnd_5756983] using wordTrace_append hprefix tailTrace_5756983
  have hstable : (prefixWord ++ tailWord_5756983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756983).length < 2 ^ (prefixWord ++ tailWord_5756983).sum := by decide
  have hdescent : baseEnd_5756983 < baseStart_5756983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5756984 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_5756984 : Nat := 118140960795 + 5756984 * 2 ^ 59
def prefixEnd_5756984 : Nat := 4983230072969 + 3 ^ 40 * 5756984 * 2
def baseEnd_5756984 : Nat := 2956099912243609007324119

theorem tailTrace_5756984 : CollatzResearch.WordTrace tailWord_5756984 prefixEnd_5756984 2956099912243609007324119 := by
  unfold tailWord_5756984
  simp only [CollatzResearch.WordTrace]
  refine ⟨104987228287718828717299003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139982971050291771623065337 104987228287718828717299003)
  ·
    refine ⟨157480842431578243075948505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104987228287718828717299003 157480842431578243075948505)
    ·
      refine ⟨118110631823683682306961379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157480842431578243075948505 118110631823683682306961379)
      ·
        refine ⟨177165947735525523460442069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118110631823683682306961379 177165947735525523460442069)
        ·
          refine ⟨4152326900051379456104111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177165947735525523460442069 4152326900051379456104111)
          ·
            refine ⟨6228490350077069184156167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152326900051379456104111 6228490350077069184156167)
            ·
              refine ⟨9342735525115603776234251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228490350077069184156167 9342735525115603776234251)
              ·
                refine ⟨14014103287673405664351377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342735525115603776234251 14014103287673405664351377)
                ·
                  refine ⟨10510577465755054248263533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14014103287673405664351377 10510577465755054248263533)
                  ·
                    refine ⟨3941466549658145343098825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10510577465755054248263533 3941466549658145343098825)
                    ·
                      refine ⟨2956099912243609007324119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941466549658145343098825 2956099912243609007324119)
                      ·
                        rfl

theorem cell23_5756984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_5756984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5756984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5756984 prefixEnd_5756984 := by exact prefixLift 5756984
  have htrace : WordTrace (prefixWord ++ tailWord_5756984) baseStart_5756984 baseEnd_5756984 := by
    simpa [prefixWord, tailWord_5756984, baseEnd_5756984] using wordTrace_append hprefix tailTrace_5756984
  have hstable : (prefixWord ++ tailWord_5756984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5756984).length < 2 ^ (prefixWord ++ tailWord_5756984).sum := by decide
  have hdescent : baseEnd_5756984 < baseStart_5756984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5756984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757023 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 7, 2]
def baseStart_5757023 : Nat := 118140960795 + 5757023 * 2 ^ 59
def prefixEnd_5757023 : Nat := 4983230072969 + 3 ^ 40 * 5757023 * 2
def baseEnd_5757023 : Nat := 2956119937989134354736439

theorem tailTrace_5757023 : CollatzResearch.WordTrace tailWord_5757023 prefixEnd_5757023 2956119937989134354736439 := by
  unfold tailWord_5757023
  simp only [CollatzResearch.WordTrace]
  refine ⟨209975879022296367095267723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139983919348197578063511815 209975879022296367095267723)
  ·
    refine ⟨314963818533444550642901585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209975879022296367095267723 314963818533444550642901585)
    ·
      refine ⟨236222863900083412982176189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314963818533444550642901585 236222863900083412982176189)
      ·
        refine ⟨88583573962531279868316071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236222863900083412982176189 88583573962531279868316071)
        ·
          refine ⟨132875360943796919802474107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88583573962531279868316071 132875360943796919802474107)
          ·
            refine ⟨199313041415695379703711161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132875360943796919802474107 199313041415695379703711161)
            ·
              refine ⟨149484781061771534777783371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199313041415695379703711161 149484781061771534777783371)
              ·
                refine ⟨224227171592657302166675057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149484781061771534777783371 224227171592657302166675057)
                ·
                  refine ⟨168170378694492976625006293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224227171592657302166675057 168170378694492976625006293)
                  ·
                    refine ⟨3941493250652179139648585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168170378694492976625006293 3941493250652179139648585)
                    ·
                      refine ⟨2956119937989134354736439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941493250652179139648585 2956119937989134354736439)
                      ·
                        rfl

theorem cell23_5757023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_5757023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757023 prefixEnd_5757023 := by exact prefixLift 5757023
  have htrace : WordTrace (prefixWord ++ tailWord_5757023) baseStart_5757023 baseEnd_5757023 := by
    simpa [prefixWord, tailWord_5757023, baseEnd_5757023] using wordTrace_append hprefix tailTrace_5757023
  have hstable : (prefixWord ++ tailWord_5757023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757023).length < 2 ^ (prefixWord ++ tailWord_5757023).sum := by decide
  have hdescent : baseEnd_5757023 < baseStart_5757023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757090 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5757090 : Nat := 118140960795 + 5757090 * 2 ^ 59
def prefixEnd_5757090 : Nat := 4983230072969 + 3 ^ 40 * 5757090 * 2
def baseEnd_5757090 : Nat := 2956154341192985592598631

theorem tailTrace_5757090 : CollatzResearch.WordTrace tailWord_5757090 prefixEnd_5757090 2956154341192985592598631 := by
  unfold tailWord_5757090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52494580678263409384489181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139985548475369091691971149 52494580678263409384489181)
  ·
    refine ⟨19685467754348778519183443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52494580678263409384489181 19685467754348778519183443)
    ·
      refine ⟨29528201631523167778775165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19685467754348778519183443 29528201631523167778775165)
      ·
        refine ⟨11073075611821187917040687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29528201631523167778775165 11073075611821187917040687)
        ·
          refine ⟨16609613417731781875561031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073075611821187917040687 16609613417731781875561031)
          ·
            refine ⟨24914420126597672813341547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16609613417731781875561031 24914420126597672813341547)
            ·
              refine ⟨37371630189896509220012321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24914420126597672813341547 37371630189896509220012321)
              ·
                refine ⟨28028722642422381915009241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37371630189896509220012321 28028722642422381915009241)
                ·
                  refine ⟨21021541981816786436256931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28028722642422381915009241 21021541981816786436256931)
                  ·
                    refine ⟨31532312972725179654385397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21021541981816786436256931 31532312972725179654385397)
                    ·
                      refine ⟨2956154341192985592598631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31532312972725179654385397 2956154341192985592598631)
                      ·
                        rfl

theorem cell23_5757090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5757090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757090 prefixEnd_5757090 := by exact prefixLift 5757090
  have htrace : WordTrace (prefixWord ++ tailWord_5757090) baseStart_5757090 baseEnd_5757090 := by
    simpa [prefixWord, tailWord_5757090, baseEnd_5757090] using wordTrace_append hprefix tailTrace_5757090
  have hstable : (prefixWord ++ tailWord_5757090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757090).length < 2 ^ (prefixWord ++ tailWord_5757090).sum := by decide
  have hdescent : baseEnd_5757090 < baseStart_5757090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757103 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_5757103 : Nat := 118140960795 + 5757103 * 2 ^ 59
def prefixEnd_5757103 : Nat := 4983230072969 + 3 ^ 40 * 5757103 * 2
def baseEnd_5757103 : Nat := 2956161016441494041736071

theorem tailTrace_5757103 : CollatzResearch.WordTrace tailWord_5757103 prefixEnd_5757103 2956161016441494041736071 := by
  unfold tailWord_5757103
  simp only [CollatzResearch.WordTrace]
  refine ⟨209978796862006540758179963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139985864574671027172119975 209978796862006540758179963)
  ·
    refine ⟨314968195293009811137269945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209978796862006540758179963 314968195293009811137269945)
    ·
      refine ⟨236226146469757358352952459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314968195293009811137269945 236226146469757358352952459)
      ·
        refine ⟨354339219704636037529428689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236226146469757358352952459 354339219704636037529428689)
        ·
          refine ⟨265754414778477028147071517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354339219704636037529428689 265754414778477028147071517)
          ·
            refine ⟨99657905541928885555151819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265754414778477028147071517 99657905541928885555151819)
            ·
              refine ⟨149486858312893328332727729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99657905541928885555151819 149486858312893328332727729)
              ·
                refine ⟨112115143734669996249545797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149486858312893328332727729 112115143734669996249545797)
                ·
                  refine ⟨21021589450250624296789837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112115143734669996249545797 21021589450250624296789837)
                  ·
                    refine ⟨7883096043843984111296189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21021589450250624296789837 7883096043843984111296189)
                    ·
                      refine ⟨2956161016441494041736071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883096043843984111296189 2956161016441494041736071)
                      ·
                        rfl

theorem cell23_5757103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_5757103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757103 prefixEnd_5757103 := by exact prefixLift 5757103
  have htrace : WordTrace (prefixWord ++ tailWord_5757103) baseStart_5757103 baseEnd_5757103 := by
    simpa [prefixWord, tailWord_5757103, baseEnd_5757103] using wordTrace_append hprefix tailTrace_5757103
  have hstable : (prefixWord ++ tailWord_5757103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757103).length < 2 ^ (prefixWord ++ tailWord_5757103).sum := by decide
  have hdescent : baseEnd_5757103 < baseStart_5757103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757130 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_5757130 : Nat := 118140960795 + 5757130 * 2 ^ 59
def prefixEnd_5757130 : Nat := 4983230072969 + 3 ^ 40 * 5757130 * 2
def baseEnd_5757130 : Nat := 2956174880419165436098447

theorem tailTrace_5757130 : CollatzResearch.WordTrace tailWord_5757130 prefixEnd_5757130 2956174880419165436098447 := by
  unfold tailWord_5757130
  simp only [CollatzResearch.WordTrace]
  refine ⟨52494945408227181092353211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139986521088605816246275229 52494945408227181092353211)
  ·
    refine ⟨78742418112340771638529817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52494945408227181092353211 78742418112340771638529817)
    ·
      refine ⟨59056813584255578728897363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78742418112340771638529817 59056813584255578728897363)
      ·
        refine ⟨88585220376383368093346045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59056813584255578728897363 88585220376383368093346045)
        ·
          refine ⟨33219457641143763035004767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88585220376383368093346045 33219457641143763035004767)
          ·
            refine ⟨49829186461715644552507151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33219457641143763035004767 49829186461715644552507151)
            ·
              refine ⟨74743779692573466828760727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49829186461715644552507151 74743779692573466828760727)
              ·
                refine ⟨112115669538860200243141091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74743779692573466828760727 112115669538860200243141091)
                ·
                  refine ⟨168173504308290300364711637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112115669538860200243141091 168173504308290300364711637)
                  ·
                    refine ⟨3941566507225553914797929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168173504308290300364711637 3941566507225553914797929)
                    ·
                      refine ⟨2956174880419165436098447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941566507225553914797929 2956174880419165436098447)
                      ·
                        rfl

theorem cell23_5757130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_5757130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757130 prefixEnd_5757130 := by exact prefixLift 5757130
  have htrace : WordTrace (prefixWord ++ tailWord_5757130) baseStart_5757130 baseEnd_5757130 := by
    simpa [prefixWord, tailWord_5757130, baseEnd_5757130] using wordTrace_append hprefix tailTrace_5757130
  have hstable : (prefixWord ++ tailWord_5757130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757130).length < 2 ^ (prefixWord ++ tailWord_5757130).sum := by decide
  have hdescent : baseEnd_5757130 < baseStart_5757130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757143 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_5757143 : Nat := 118140960795 + 5757143 * 2 ^ 59
def prefixEnd_5757143 : Nat := 4983230072969 + 3 ^ 40 * 5757143 * 2
def baseEnd_5757143 : Nat := 2956181555667673885235887

theorem tailTrace_5757143 : CollatzResearch.WordTrace tailWord_5757143 prefixEnd_5757143 2956181555667673885235887 := by
  unfold tailWord_5757143
  simp only [CollatzResearch.WordTrace]
  refine ⟨209980255781861627589636083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139986837187907751726424055 209980255781861627589636083)
  ·
    refine ⟨314970383672792441384454125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209980255781861627589636083 314970383672792441384454125)
    ·
      refine ⟨118113893877297165519170297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314970383672792441384454125 118113893877297165519170297)
      ·
        refine ⟨88585420407972874139377723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118113893877297165519170297 88585420407972874139377723)
        ·
          refine ⟨132878130611959311209066585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88585420407972874139377723 132878130611959311209066585)
          ·
            refine ⟨99658597958969483406799939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132878130611959311209066585 99658597958969483406799939)
            ·
              refine ⟨149487896938454225110199909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99658597958969483406799939 149487896938454225110199909)
              ·
                refine ⟨28028980675960167208162483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149487896938454225110199909 28028980675960167208162483)
                ·
                  refine ⟨42043471013940250812243725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28028980675960167208162483 42043471013940250812243725)
                  ·
                    refine ⟨15766301630227594054591397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42043471013940250812243725 15766301630227594054591397)
                    ·
                      refine ⟨2956181555667673885235887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15766301630227594054591397 2956181555667673885235887)
                      ·
                        rfl

theorem cell23_5757143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_5757143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757143 prefixEnd_5757143 := by exact prefixLift 5757143
  have htrace : WordTrace (prefixWord ++ tailWord_5757143) baseStart_5757143 baseEnd_5757143 := by
    simpa [prefixWord, tailWord_5757143, baseEnd_5757143] using wordTrace_append hprefix tailTrace_5757143
  have hstable : (prefixWord ++ tailWord_5757143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757143).length < 2 ^ (prefixWord ++ tailWord_5757143).sum := by decide
  have hdescent : baseEnd_5757143 < baseStart_5757143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757157 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_5757157 : Nat := 118140960795 + 5757157 * 2 ^ 59
def prefixEnd_5757157 : Nat := 4983230072969 + 3 ^ 40 * 5757157 * 2
def baseEnd_5757157 : Nat := 985396248132278943486941

theorem tailTrace_5757157 : CollatzResearch.WordTrace tailWord_5757157 prefixEnd_5757157 985396248132278943486941 := by
  unfold tailWord_5757157
  simp only [CollatzResearch.WordTrace]
  refine ⟨209980766403810907980645725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139987177602540605320430483 209980766403810907980645725)
  ·
    refine ⟨78742787401429090492742147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209980766403810907980645725 78742787401429090492742147)
    ·
      refine ⟨118114181102143635739113221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78742787401429090492742147 118114181102143635739113221)
      ·
        refine ⟨22146408956651931701083729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118114181102143635739113221 22146408956651931701083729)
        ·
          refine ⟨16609806717488948775812797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22146408956651931701083729 16609806717488948775812797)
          ·
            refine ⟨6228677519058355790929799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16609806717488948775812797 6228677519058355790929799)
            ·
              refine ⟨9343016278587533686394699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228677519058355790929799 9343016278587533686394699)
              ·
                refine ⟨14014524417881300529592049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9343016278587533686394699 14014524417881300529592049)
                ·
                  refine ⟨10510893313410975397194037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14014524417881300529592049 10510893313410975397194037)
                  ·
                    refine ⟨985396248132278943486941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10510893313410975397194037 985396248132278943486941)
                    ·
                      rfl

theorem cell23_5757157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_5757157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757157 prefixEnd_5757157 := by exact prefixLift 5757157
  have htrace : WordTrace (prefixWord ++ tailWord_5757157) baseStart_5757157 baseEnd_5757157 := by
    simpa [prefixWord, tailWord_5757157, baseEnd_5757157] using wordTrace_append hprefix tailTrace_5757157
  have hstable : (prefixWord ++ tailWord_5757157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757157).length < 2 ^ (prefixWord ++ tailWord_5757157).sum := by decide
  have hdescent : baseEnd_5757157 < baseStart_5757157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757160 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5757160 : Nat := 118140960795 + 5757160 * 2 ^ 59
def prefixEnd_5757160 : Nat := 4983230072969 + 3 ^ 40 * 5757160 * 2
def baseEnd_5757160 : Nat := 2956190284838800318723309

theorem tailTrace_5757160 : CollatzResearch.WordTrace tailWord_5757160 prefixEnd_5757160 2956190284838800318723309 := by
  unfold tailWord_5757160
  simp only [CollatzResearch.WordTrace]
  refine ⟨104990437911400019746502467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139987250548533359662003289 104990437911400019746502467)
  ·
    refine ⟨157485656867100029619753701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104990437911400019746502467 157485656867100029619753701)
    ·
      refine ⟨29528560662581255553703819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157485656867100029619753701 29528560662581255553703819)
      ·
        refine ⟨44292840993871883330555729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29528560662581255553703819 44292840993871883330555729)
        ·
          refine ⟨33219630745403912497916797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44292840993871883330555729 33219630745403912497916797)
          ·
            refine ⟨12457361529526467186718799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33219630745403912497916797 12457361529526467186718799)
            ·
              refine ⟨18686042294289700780078199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12457361529526467186718799 18686042294289700780078199)
              ·
                refine ⟨28029063441434551170117299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18686042294289700780078199 28029063441434551170117299)
                ·
                  refine ⟨42043595162151826755175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28029063441434551170117299 42043595162151826755175949)
                  ·
                    refine ⟨15766348185806935033190981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42043595162151826755175949 15766348185806935033190981)
                    ·
                      refine ⟨2956190284838800318723309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15766348185806935033190981 2956190284838800318723309)
                      ·
                        rfl

theorem cell23_5757160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5757160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757160 prefixEnd_5757160 := by exact prefixLift 5757160
  have htrace : WordTrace (prefixWord ++ tailWord_5757160) baseStart_5757160 baseEnd_5757160 := by
    simpa [prefixWord, tailWord_5757160, baseEnd_5757160] using wordTrace_append hprefix tailTrace_5757160
  have hstable : (prefixWord ++ tailWord_5757160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757160).length < 2 ^ (prefixWord ++ tailWord_5757160).sum := by decide
  have hdescent : baseEnd_5757160 < baseStart_5757160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757183 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 8]
def baseStart_5757183 : Nat := 118140960795 + 5757183 * 2 ^ 59
def prefixEnd_5757183 : Nat := 4983230072969 + 3 ^ 40 * 5757183 * 2
def baseEnd_5757183 : Nat := 328466899432650414303967

theorem tailTrace_5757183 : CollatzResearch.WordTrace tailWord_5757183 prefixEnd_5757183 328466899432650414303967 := by
  unfold tailWord_5757183
  simp only [CollatzResearch.WordTrace]
  refine ⟨209981714701716714421092203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139987809801144476280728135 209981714701716714421092203)
  ·
    refine ⟨314972572052575071631638305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209981714701716714421092203 314972572052575071631638305)
    ·
      refine ⟨236229429039431303723728729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314972572052575071631638305 236229429039431303723728729)
      ·
        refine ⟨177172071779573477792796547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236229429039431303723728729 177172071779573477792796547)
        ·
          refine ⟨265758107669360216689194821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177172071779573477792796547 265758107669360216689194821)
          ·
            refine ⟨49829645188005040629224029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265758107669360216689194821 49829645188005040629224029)
            ·
              refine ⟨18686116945501890235959011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49829645188005040629224029 18686116945501890235959011)
              ·
                refine ⟨28029175418252835353938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18686116945501890235959011 28029175418252835353938517)
                ·
                  refine ⟨328466899432650414303967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28029175418252835353938517 328466899432650414303967)
                  ·
                    rfl

theorem cell23_5757183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 8].length) (baseStart_5757183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757183 prefixEnd_5757183 := by exact prefixLift 5757183
  have htrace : WordTrace (prefixWord ++ tailWord_5757183) baseStart_5757183 baseEnd_5757183 := by
    simpa [prefixWord, tailWord_5757183, baseEnd_5757183] using wordTrace_append hprefix tailTrace_5757183
  have hstable : (prefixWord ++ tailWord_5757183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757183).length < 2 ^ (prefixWord ++ tailWord_5757183).sum := by decide
  have hdescent : baseEnd_5757183 < baseStart_5757183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757187 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 1, 4]
def baseStart_5757187 : Nat := 118140960795 + 5757187 * 2 ^ 59
def prefixEnd_5757187 : Nat := 4983230072969 + 3 ^ 40 * 5757187 * 2
def baseEnd_5757187 : Nat := 985401382938823904361895

theorem tailTrace_5757187 : CollatzResearch.WordTrace tailWord_5757187 prefixEnd_5757187 985401382938823904361895 := by
  unfold tailWord_5757187
  simp only [CollatzResearch.WordTrace]
  refine ⟨209981860593702223104237815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139987907062468148736158543 209981860593702223104237815)
  ·
    refine ⟨314972790890553334656356723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209981860593702223104237815 314972790890553334656356723)
    ·
      refine ⟨472459186335830001984535085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314972790890553334656356723 472459186335830001984535085)
      ·
        refine ⟨177172194875936250744200657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472459186335830001984535085 177172194875936250744200657)
        ·
          refine ⟨132879146156952188058150493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177172194875936250744200657 132879146156952188058150493)
          ·
            refine ⟨49829679808857070521806435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132879146156952188058150493 49829679808857070521806435)
            ·
              refine ⟨74744519713285605782709653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49829679808857070521806435 74744519713285605782709653)
              ·
                refine ⟨3503649361560262771064515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74744519713285605782709653 3503649361560262771064515)
                ·
                  refine ⟨5255474042340394156596773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503649361560262771064515 5255474042340394156596773)
                  ·
                    refine ⟨985401382938823904361895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255474042340394156596773 985401382938823904361895)
                    ·
                      rfl

theorem cell23_5757187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 4].length) (baseStart_5757187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757187 prefixEnd_5757187 := by exact prefixLift 5757187
  have htrace : WordTrace (prefixWord ++ tailWord_5757187) baseStart_5757187 baseEnd_5757187 := by
    simpa [prefixWord, tailWord_5757187, baseEnd_5757187] using wordTrace_append hprefix tailTrace_5757187
  have hstable : (prefixWord ++ tailWord_5757187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757187).length < 2 ^ (prefixWord ++ tailWord_5757187).sum := by decide
  have hdescent : baseEnd_5757187 < baseStart_5757187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757214 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5757214 : Nat := 118140960795 + 5757214 * 2 ^ 59
def prefixEnd_5757214 : Nat := 4983230072969 + 3 ^ 40 * 5757214 * 2
def baseEnd_5757214 : Nat := 2956218012794143107448061

theorem tailTrace_5757214 : CollatzResearch.WordTrace tailWord_5757214 prefixEnd_5757214 2956218012794143107448061 := by
  unfold tailWord_5757214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26247855670575550839433837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139988563576402937810313797 26247855670575550839433837)
  ·
    refine ⟨9842945876465831564787689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26247855670575550839433837 9842945876465831564787689)
    ·
      refine ⟨7382209407349373673590767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9842945876465831564787689 7382209407349373673590767)
      ·
        refine ⟨11073314111024060510386151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382209407349373673590767 11073314111024060510386151)
        ·
          refine ⟨16609971166536090765579227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073314111024060510386151 16609971166536090765579227)
          ·
            refine ⟨24914956749804136148368841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16609971166536090765579227 24914956749804136148368841)
            ·
              refine ⟨18686217562353102111276631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24914956749804136148368841 18686217562353102111276631)
              ·
                refine ⟨28029326343529653166914947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18686217562353102111276631 28029326343529653166914947)
                ·
                  refine ⟨42043989515294479750372421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28029326343529653166914947 42043989515294479750372421)
                  ·
                    refine ⟨7883248034117714953194829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42043989515294479750372421 7883248034117714953194829)
                    ·
                      refine ⟨2956218012794143107448061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883248034117714953194829 2956218012794143107448061)
                      ·
                        rfl

theorem cell23_5757214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5757214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757214 prefixEnd_5757214 := by exact prefixLift 5757214
  have htrace : WordTrace (prefixWord ++ tailWord_5757214) baseStart_5757214 baseEnd_5757214 := by
    simpa [prefixWord, tailWord_5757214, baseEnd_5757214] using wordTrace_append hprefix tailTrace_5757214
  have hstable : (prefixWord ++ tailWord_5757214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757214).length < 2 ^ (prefixWord ++ tailWord_5757214).sum := by decide
  have hdescent : baseEnd_5757214 < baseStart_5757214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757221 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_5757221 : Nat := 118140960795 + 5757221 * 2 ^ 59
def prefixEnd_5757221 : Nat := 4983230072969 + 3 ^ 40 * 5757221 * 2
def baseEnd_5757221 : Nat := 985407202386241526686843

theorem tailTrace_5757221 : CollatzResearch.WordTrace tailWord_5757221 prefixEnd_5757221 985407202386241526686843 := by
  unfold tailWord_5757221
  simp only [CollatzResearch.WordTrace]
  refine ⟨209983100675579046910975517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139988733783719364607317011 209983100675579046910975517)
  ·
    refine ⟨78743662753342142591615819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209983100675579046910975517 78743662753342142591615819)
    ·
      refine ⟨118115494130013213887423729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78743662753342142591615819 118115494130013213887423729)
      ·
        refine ⟨88586620597509910415567797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118115494130013213887423729 88586620597509910415567797)
        ·
          refine ⟨8304995681016554101459481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88586620597509910415567797 8304995681016554101459481)
          ·
            refine ⟨6228746760762415576094611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304995681016554101459481 6228746760762415576094611)
            ·
              refine ⟨9343120141143623364141917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228746760762415576094611 9343120141143623364141917)
              ·
                refine ⟨3503670052928858761553219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9343120141143623364141917 3503670052928858761553219)
                ·
                  refine ⟨5255505079393288142329829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503670052928858761553219 5255505079393288142329829)
                  ·
                    refine ⟨985407202386241526686843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255505079393288142329829 985407202386241526686843)
                    ·
                      rfl

theorem cell23_5757221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_5757221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757221 prefixEnd_5757221 := by exact prefixLift 5757221
  have htrace : WordTrace (prefixWord ++ tailWord_5757221) baseStart_5757221 baseEnd_5757221 := by
    simpa [prefixWord, tailWord_5757221, baseEnd_5757221] using wordTrace_append hprefix tailTrace_5757221
  have hstable : (prefixWord ++ tailWord_5757221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757221).length < 2 ^ (prefixWord ++ tailWord_5757221).sum := by decide
  have hdescent : baseEnd_5757221 < baseStart_5757221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757260 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_5757260 : Nat := 118140960795 + 5757260 * 2 ^ 59
def prefixEnd_5757260 : Nat := 4983230072969 + 3 ^ 40 * 5757260 * 2
def baseEnd_5757260 : Nat := 985413877634749975824283

theorem tailTrace_5757260 : CollatzResearch.WordTrace tailWord_5757260 prefixEnd_5757260 985413877634749975824283 := by
  unfold tailWord_5757260
  simp only [CollatzResearch.WordTrace]
  refine ⟨104992261561218878285822617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139989682081625171047763489 104992261561218878285822617)
  ·
    refine ⟨78744196170914158714366963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104992261561218878285822617 78744196170914158714366963)
    ·
      refine ⟨118116294256371238071550445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78744196170914158714366963 118116294256371238071550445)
      ·
        refine ⟨44293610346139214276831417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118116294256371238071550445 44293610346139214276831417)
        ·
          refine ⟨33220207759604410707623563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44293610346139214276831417 33220207759604410707623563)
          ·
            refine ⟨49830311639406616061435345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33220207759604410707623563 49830311639406616061435345)
            ·
              refine ⟨37372733729554962046076509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49830311639406616061435345 37372733729554962046076509)
              ·
                refine ⟨14014775148583110767278691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37372733729554962046076509 14014775148583110767278691)
                ·
                  refine ⟨21022162722874666150918037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14014775148583110767278691 21022162722874666150918037)
                  ·
                    refine ⟨985413877634749975824283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21022162722874666150918037 985413877634749975824283)
                    ·
                      rfl

theorem cell23_5757260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_5757260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757260 prefixEnd_5757260 := by exact prefixLift 5757260
  have htrace : WordTrace (prefixWord ++ tailWord_5757260) baseStart_5757260 baseEnd_5757260 := by
    simpa [prefixWord, tailWord_5757260, baseEnd_5757260] using wordTrace_append hprefix tailTrace_5757260
  have hstable : (prefixWord ++ tailWord_5757260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757260).length < 2 ^ (prefixWord ++ tailWord_5757260).sum := by decide
  have hdescent : baseEnd_5757260 < baseStart_5757260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757284 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_5757284 : Nat := 118140960795 + 5757284 * 2 ^ 59
def prefixEnd_5757284 : Nat := 4983230072969 + 3 ^ 40 * 5757284 * 2
def baseEnd_5757284 : Nat := 2956253956439957833572739

theorem tailTrace_5757284 : CollatzResearch.WordTrace tailWord_5757284 prefixEnd_5757284 2956253956439957833572739 := by
  unfold tailWord_5757284
  simp only [CollatzResearch.WordTrace]
  refine ⟨104992699237175404335259453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139990265649567205780345937 104992699237175404335259453)
  ·
    refine ⟨39372262213940776625722295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104992699237175404335259453 39372262213940776625722295)
    ·
      refine ⟨59058393320911164938583443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39372262213940776625722295 59058393320911164938583443)
      ·
        refine ⟨88587589981366747407875165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59058393320911164938583443 88587589981366747407875165)
        ·
          refine ⟨33220346243012530277953187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88587589981366747407875165 33220346243012530277953187)
          ·
            refine ⟨49830519364518795416929781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33220346243012530277953187 49830519364518795416929781)
            ·
              refine ⟨4671611190423637070337167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49830519364518795416929781 4671611190423637070337167)
              ·
                refine ⟨7007416785635455605505751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671611190423637070337167 7007416785635455605505751)
                ·
                  refine ⟨10511125178453183408258627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007416785635455605505751 10511125178453183408258627)
                  ·
                    refine ⟨15766687767679775112387941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10511125178453183408258627 15766687767679775112387941)
                    ·
                      refine ⟨2956253956439957833572739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15766687767679775112387941 2956253956439957833572739)
                      ·
                        rfl

theorem cell23_5757284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_5757284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757284 prefixEnd_5757284 := by exact prefixLift 5757284
  have htrace : WordTrace (prefixWord ++ tailWord_5757284) baseStart_5757284 baseEnd_5757284 := by
    simpa [prefixWord, tailWord_5757284, baseEnd_5757284] using wordTrace_append hprefix tailTrace_5757284
  have hstable : (prefixWord ++ tailWord_5757284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757284).length < 2 ^ (prefixWord ++ tailWord_5757284).sum := by decide
  have hdescent : baseEnd_5757284 < baseStart_5757284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757287 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_5757287 : Nat := 118140960795 + 5757287 * 2 ^ 59
def prefixEnd_5757287 : Nat := 4983230072969 + 3 ^ 40 * 5757287 * 2
def baseEnd_5757287 : Nat := 2956255496881921321835225

theorem tailTrace_5757287 : CollatzResearch.WordTrace tailWord_5757287 prefixEnd_5757287 2956255496881921321835225 := by
  unfold tailWord_5757287
  simp only [CollatzResearch.WordTrace]
  refine ⟨209985507893339940182878115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139990338595559960121918743 209985507893339940182878115)
  ·
    refine ⟨314978261840009910274317173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209985507893339940182878115 314978261840009910274317173)
    ·
      refine ⟨29529212047500929088217235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314978261840009910274317173 29529212047500929088217235)
      ·
        refine ⟨44293818071251393632325853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29529212047500929088217235 44293818071251393632325853)
        ·
          refine ⟨16610181776719272612122195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44293818071251393632325853 16610181776719272612122195)
          ·
            refine ⟨24915272665078908918183293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610181776719272612122195 24915272665078908918183293)
            ·
              refine ⟨9343227249404590844318735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24915272665078908918183293 9343227249404590844318735)
              ·
                refine ⟨14014840874106886266478103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9343227249404590844318735 14014840874106886266478103)
                ·
                  refine ⟨21022261311160329399717155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14014840874106886266478103 21022261311160329399717155)
                  ·
                    refine ⟨31533391966740494099575733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21022261311160329399717155 31533391966740494099575733)
                    ·
                      refine ⟨2956255496881921321835225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31533391966740494099575733 2956255496881921321835225)
                      ·
                        rfl

theorem cell23_5757287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_5757287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757287 prefixEnd_5757287 := by exact prefixLift 5757287
  have htrace : WordTrace (prefixWord ++ tailWord_5757287) baseStart_5757287 baseEnd_5757287 := by
    simpa [prefixWord, tailWord_5757287, baseEnd_5757287] using wordTrace_append hprefix tailTrace_5757287
  have hstable : (prefixWord ++ tailWord_5757287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757287).length < 2 ^ (prefixWord ++ tailWord_5757287).sum := by decide
  have hdescent : baseEnd_5757287 < baseStart_5757287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757290 : List Nat := [3, 1, 3, 3, 1, 12]
def baseStart_5757290 : Nat := 118140960795 + 5757290 * 2 ^ 59
def prefixEnd_5757290 : Nat := 4983230072969 + 3 ^ 40 * 5757290 * 2
def baseEnd_5757290 : Nat := 12165666820262900453077

theorem tailTrace_5757290 : CollatzResearch.WordTrace tailWord_5757290 prefixEnd_5757290 12165666820262900453077 := by
  unfold tailWord_5757290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52496404328082267923809331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139990411541552714463491549 52496404328082267923809331)
  ·
    refine ⟨78744606492123401885713997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52496404328082267923809331 78744606492123401885713997)
    ·
      refine ⟨29529227434546275707142749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78744606492123401885713997 29529227434546275707142749)
      ·
        refine ⟨11073460287954853390178531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29529227434546275707142749 11073460287954853390178531)
        ·
          refine ⟨16610190431932280085267797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073460287954853390178531 16610190431932280085267797)
          ·
            refine ⟨12165666820262900453077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16610190431932280085267797 12165666820262900453077)
            ·
              rfl

theorem cell23_5757290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 12].length) (baseStart_5757290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757290 prefixEnd_5757290 := by exact prefixLift 5757290
  have htrace : WordTrace (prefixWord ++ tailWord_5757290) baseStart_5757290 baseEnd_5757290 := by
    simpa [prefixWord, tailWord_5757290, baseEnd_5757290] using wordTrace_append hprefix tailTrace_5757290
  have hstable : (prefixWord ++ tailWord_5757290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757290).length < 2 ^ (prefixWord ++ tailWord_5757290).sum := by decide
  have hdescent : baseEnd_5757290 < baseStart_5757290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757317 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_5757317 : Nat := 118140960795 + 5757317 * 2 ^ 59
def prefixEnd_5757317 : Nat := 4983230072969 + 3 ^ 40 * 5757317 * 2
def baseEnd_5757317 : Nat := 2956270901301556204460087

theorem tailTrace_5757317 : CollatzResearch.WordTrace tailWord_5757317 prefixEnd_5757317 2956270901301556204460087 := by
  unfold tailWord_5757317
  simp only [CollatzResearch.WordTrace]
  refine ⟨209986602083231255306470205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139991068055487503537646803 209986602083231255306470205)
  ·
    refine ⟨78744975781211720739926327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209986602083231255306470205 78744975781211720739926327)
    ·
      refine ⟨118117463671817581109889491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78744975781211720739926327 118117463671817581109889491)
      ·
        refine ⟨177176195507726371664834237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118117463671817581109889491 177176195507726371664834237)
        ·
          refine ⟨66441073315397389374312839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177176195507726371664834237 66441073315397389374312839)
          ·
            refine ⟨99661609973096084061469259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66441073315397389374312839 99661609973096084061469259)
            ·
              refine ⟨149492414959644126092203889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99661609973096084061469259 149492414959644126092203889)
              ·
                refine ⟨112119311219733094569152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149492414959644126092203889 112119311219733094569152917)
                ·
                  refine ⟨5255592713424988807929043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112119311219733094569152917 5255592713424988807929043)
                  ·
                    refine ⟨7883389070137483211893565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5255592713424988807929043 7883389070137483211893565)
                    ·
                      refine ⟨2956270901301556204460087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883389070137483211893565 2956270901301556204460087)
                      ·
                        rfl

theorem cell23_5757317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_5757317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757317 prefixEnd_5757317 := by exact prefixLift 5757317
  have htrace : WordTrace (prefixWord ++ tailWord_5757317) baseStart_5757317 baseEnd_5757317 := by
    simpa [prefixWord, tailWord_5757317, baseEnd_5757317] using wordTrace_append hprefix tailTrace_5757317
  have hstable : (prefixWord ++ tailWord_5757317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757317).length < 2 ^ (prefixWord ++ tailWord_5757317).sum := by decide
  have hdescent : baseEnd_5757317 < baseStart_5757317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757320 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_5757320 : Nat := 118140960795 + 5757320 * 2 ^ 59
def prefixEnd_5757320 : Nat := 4983230072969 + 3 ^ 40 * 5757320 * 2
def baseEnd_5757320 : Nat := 985424147247839897574191

theorem tailTrace_5757320 : CollatzResearch.WordTrace tailWord_5757320 prefixEnd_5757320 985424147247839897574191 := by
  unfold tailWord_5757320
  simp only [CollatzResearch.WordTrace]
  refine ⟨104993355751110193409414707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139991141001480257879219609 104993355751110193409414707)
  ·
    refine ⟨157490033626665290114122061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104993355751110193409414707 157490033626665290114122061)
    ·
      refine ⟨59058762609999483792795773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157490033626665290114122061 59058762609999483792795773)
      ·
        refine ⟨22147035978749806422298415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59058762609999483792795773 22147035978749806422298415)
        ·
          refine ⟨33220553968124709633447623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22147035978749806422298415 33220553968124709633447623)
          ·
            refine ⟨49830830952187064450171435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33220553968124709633447623 49830830952187064450171435)
            ·
              refine ⟨74746246428280596675257153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49830830952187064450171435 74746246428280596675257153)
              ·
                refine ⟨56059684821210447506442865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74746246428280596675257153 56059684821210447506442865)
                ·
                  refine ⟨42044763615907835629832149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56059684821210447506442865 42044763615907835629832149)
                  ·
                    refine ⟨985424147247839897574191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42044763615907835629832149 985424147247839897574191)
                    ·
                      rfl

theorem cell23_5757320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_5757320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757320 prefixEnd_5757320 := by exact prefixLift 5757320
  have htrace : WordTrace (prefixWord ++ tailWord_5757320) baseStart_5757320 baseEnd_5757320 := by
    simpa [prefixWord, tailWord_5757320, baseEnd_5757320] using wordTrace_append hprefix tailTrace_5757320
  have hstable : (prefixWord ++ tailWord_5757320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757320).length < 2 ^ (prefixWord ++ tailWord_5757320).sum := by decide
  have hdescent : baseEnd_5757320 < baseStart_5757320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757351 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5757351 : Nat := 118140960795 + 5757351 * 2 ^ 59
def prefixEnd_5757351 : Nat := 4983230072969 + 3 ^ 40 * 5757351 * 2
def baseEnd_5757351 : Nat := 2956288359643809071434931

theorem tailTrace_5757351 : CollatzResearch.WordTrace tailWord_5757351 prefixEnd_5757351 2956288359643809071434931 := by
  unfold tailWord_5757351
  simp only [CollatzResearch.WordTrace]
  refine ⟨209987842165108079113207907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139991894776738719408805271 209987842165108079113207907)
  ·
    refine ⟨314981763247662118669811861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209987842165108079113207907 314981763247662118669811861)
    ·
      refine ⟨14764770152234161812647431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314981763247662118669811861 14764770152234161812647431)
      ·
        refine ⟨22147155228351242718971147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14764770152234161812647431 22147155228351242718971147)
        ·
          refine ⟨33220732842526864078456721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22147155228351242718971147 33220732842526864078456721)
          ·
            refine ⟨24915549631895148058842541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33220732842526864078456721 24915549631895148058842541)
            ·
              refine ⟨9343331111960680522065953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24915549631895148058842541 9343331111960680522065953)
              ·
                refine ⟨7007498333970510391549465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9343331111960680522065953 7007498333970510391549465)
                ·
                  refine ⟨5255623750477882793662099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7007498333970510391549465 5255623750477882793662099)
                  ·
                    refine ⟨7883435625716824190493149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5255623750477882793662099 7883435625716824190493149)
                    ·
                      refine ⟨2956288359643809071434931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883435625716824190493149 2956288359643809071434931)
                      ·
                        rfl

theorem cell23_5757351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5757351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757351 prefixEnd_5757351 := by exact prefixLift 5757351
  have htrace : WordTrace (prefixWord ++ tailWord_5757351) baseStart_5757351 baseEnd_5757351 := by
    simpa [prefixWord, tailWord_5757351, baseEnd_5757351] using wordTrace_append hprefix tailTrace_5757351
  have hstable : (prefixWord ++ tailWord_5757351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757351).length < 2 ^ (prefixWord ++ tailWord_5757351).sum := by decide
  have hdescent : baseEnd_5757351 < baseStart_5757351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757444 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_5757444 : Nat := 118140960795 + 5757444 * 2 ^ 59
def prefixEnd_5757444 : Nat := 4983230072969 + 3 ^ 40 * 5757444 * 2
def baseEnd_5757444 : Nat := 985445371114892402524001

theorem tailTrace_5757444 : CollatzResearch.WordTrace tailWord_5757444 prefixEnd_5757444 985445371114892402524001 := by
  unfold tailWord_5757444
  simp only [CollatzResearch.WordTrace]
  refine ⟨104995617076885577998171693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139994156102514103997562257 104995617076885577998171693)
  ·
    refine ⟨39373356403832091749314385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104995617076885577998171693 39373356403832091749314385)
    ·
      refine ⟨29530017302874068811985789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39373356403832091749314385 29530017302874068811985789)
      ·
        refine ⟨11073756488577775804494671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29530017302874068811985789 11073756488577775804494671)
        ·
          refine ⟨16610634732866663706742007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073756488577775804494671 16610634732866663706742007)
          ·
            refine ⟨24915952099299995560113011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610634732866663706742007 24915952099299995560113011)
            ·
              refine ⟨37373928148949993340169517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24915952099299995560113011 37373928148949993340169517)
              ·
                refine ⟨14015223055856247502563569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37373928148949993340169517 14015223055856247502563569)
                ·
                  refine ⟨10511417291892185626922677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015223055856247502563569 10511417291892185626922677)
                  ·
                    refine ⟨985445371114892402524001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10511417291892185626922677 985445371114892402524001)
                    ·
                      rfl

theorem cell23_5757444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_5757444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757444 prefixEnd_5757444 := by exact prefixLift 5757444
  have htrace : WordTrace (prefixWord ++ tailWord_5757444) baseStart_5757444 baseEnd_5757444 := by
    simpa [prefixWord, tailWord_5757444, baseEnd_5757444] using wordTrace_append hprefix tailTrace_5757444
  have hstable : (prefixWord ++ tailWord_5757444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757444).length < 2 ^ (prefixWord ++ tailWord_5757444).sum := by decide
  have hdescent : baseEnd_5757444 < baseStart_5757444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757457 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_5757457 : Nat := 118140960795 + 5757457 * 2 ^ 59
def prefixEnd_5757457 : Nat := 4983230072969 + 3 ^ 40 * 5757457 * 2
def baseEnd_5757457 : Nat := 985447596197728552236481

theorem tailTrace_5757457 : CollatzResearch.WordTrace tailWord_5757457 prefixEnd_5757457 985447596197728552236481 := by
  unfold tailWord_5757457
  simp only [CollatzResearch.WordTrace]
  refine ⟨209991708302724059216566625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139994472201816039477711083 209991708302724059216566625)
  ·
    refine ⟨157493781227043044412424969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209991708302724059216566625 157493781227043044412424969)
    ·
      refine ⟨118120335920282283309318727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157493781227043044412424969 118120335920282283309318727)
      ·
        refine ⟨177180503880423424963978091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118120335920282283309318727 177180503880423424963978091)
        ·
          refine ⟨265770755820635137445967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177180503880423424963978091 265770755820635137445967137)
          ·
            refine ⟨199328066865476353084475353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265770755820635137445967137 199328066865476353084475353)
            ·
              refine ⟨149496050149107264813356515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199328066865476353084475353 149496050149107264813356515)
              ·
                refine ⟨224244075223660897220034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149496050149107264813356515 224244075223660897220034773)
                ·
                  refine ⟨5255720513054552278594565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224244075223660897220034773 5255720513054552278594565)
                  ·
                    refine ⟨985447596197728552236481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255720513054552278594565 985447596197728552236481)
                    ·
                      rfl

theorem cell23_5757457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_5757457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757457 prefixEnd_5757457 := by exact prefixLift 5757457
  have htrace : WordTrace (prefixWord ++ tailWord_5757457) baseStart_5757457 baseEnd_5757457 := by
    simpa [prefixWord, tailWord_5757457, baseEnd_5757457] using wordTrace_append hprefix tailTrace_5757457
  have hstable : (prefixWord ++ tailWord_5757457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757457).length < 2 ^ (prefixWord ++ tailWord_5757457).sum := by decide
  have hdescent : baseEnd_5757457 < baseStart_5757457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757464 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5757464 : Nat := 118140960795 + 5757464 * 2 ^ 59
def prefixEnd_5757464 : Nat := 4983230072969 + 3 ^ 40 * 5757464 * 2
def baseEnd_5757464 : Nat := 2956346382957767129321911

theorem tailTrace_5757464 : CollatzResearch.WordTrace tailWord_5757464 prefixEnd_5757464 2956346382957767129321911 := by
  unfold tailWord_5757464
  simp only [CollatzResearch.WordTrace]
  refine ⟨104995981806849349706035723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139994642409132466274714297 104995981806849349706035723)
  ·
    refine ⟨157493972710274024559053585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104995981806849349706035723 157493972710274024559053585)
    ·
      refine ⟨118120479532705518419290189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157493972710274024559053585 118120479532705518419290189)
      ·
        refine ⟨44295179824764569407233821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118120479532705518419290189 44295179824764569407233821)
        ·
          refine ⟨16610692434286713527712683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44295179824764569407233821 16610692434286713527712683)
          ·
            refine ⟨24916038651430070291569025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610692434286713527712683 24916038651430070291569025)
            ·
              refine ⟨18687028988572552718676769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24916038651430070291569025 18687028988572552718676769)
              ·
                refine ⟨14015271741429414539007577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18687028988572552718676769 14015271741429414539007577)
                ·
                  refine ⟨10511453806072060904255683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015271741429414539007577 10511453806072060904255683)
                  ·
                    refine ⟨15767180709108091356383525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10511453806072060904255683 15767180709108091356383525)
                    ·
                      refine ⟨2956346382957767129321911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15767180709108091356383525 2956346382957767129321911)
                      ·
                        rfl

theorem cell23_5757464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5757464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757464 prefixEnd_5757464 := by exact prefixLift 5757464
  have htrace : WordTrace (prefixWord ++ tailWord_5757464) baseStart_5757464 baseEnd_5757464 := by
    simpa [prefixWord, tailWord_5757464, baseEnd_5757464] using wordTrace_append hprefix tailTrace_5757464
  have hstable : (prefixWord ++ tailWord_5757464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757464).length < 2 ^ (prefixWord ++ tailWord_5757464).sum := by decide
  have hdescent : baseEnd_5757464 < baseStart_5757464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757474 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5757474 : Nat := 118140960795 + 5757474 * 2 ^ 59
def prefixEnd_5757474 : Nat := 4983230072969 + 3 ^ 40 * 5757474 * 2
def baseEnd_5757474 : Nat := 985450505921437363398955

theorem tailTrace_5757474 : CollatzResearch.WordTrace tailWord_5757474 prefixEnd_5757474 985450505921437363398955 := by
  unfold tailWord_5757474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52498082085915617779983869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139994885562441647413290317 52498082085915617779983869)
  ·
    refine ⟨19686780782218356667493951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52498082085915617779983869 19686780782218356667493951)
    ·
      refine ⟨29530171173327535001240927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19686780782218356667493951 29530171173327535001240927)
      ·
        refine ⟨44295256759991302501861391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29530171173327535001240927 44295256759991302501861391)
        ·
          refine ⟨66442885139986953752792087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44295256759991302501861391 66442885139986953752792087)
          ·
            refine ⟨99664327709980430629188131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66442885139986953752792087 99664327709980430629188131)
            ·
              refine ⟨149496491564970645943782197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99664327709980430629188131 149496491564970645943782197)
              ·
                refine ⟨14015296084215998057229581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149496491564970645943782197 14015296084215998057229581)
                ·
                  refine ⟨5255736031580999271461093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14015296084215998057229581 5255736031580999271461093)
                  ·
                    refine ⟨985450505921437363398955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255736031580999271461093 985450505921437363398955)
                    ·
                      rfl

theorem cell23_5757474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5757474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757474 prefixEnd_5757474 := by exact prefixLift 5757474
  have htrace : WordTrace (prefixWord ++ tailWord_5757474) baseStart_5757474 baseEnd_5757474 := by
    simpa [prefixWord, tailWord_5757474, baseEnd_5757474] using wordTrace_append hprefix tailTrace_5757474
  have hstable : (prefixWord ++ tailWord_5757474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757474).length < 2 ^ (prefixWord ++ tailWord_5757474).sum := by decide
  have hdescent : baseEnd_5757474 < baseStart_5757474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757501 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5757501 : Nat := 118140960795 + 5757501 * 2 ^ 59
def prefixEnd_5757501 : Nat := 4983230072969 + 3 ^ 40 * 5757501 * 2
def baseEnd_5757501 : Nat := 2956365381741983484559241

theorem tailTrace_5757501 : CollatzResearch.WordTrace tailWord_5757501 prefixEnd_5757501 2956365381741983484559241 := by
  unfold tailWord_5757501
  simp only [CollatzResearch.WordTrace]
  refine ⟨209993313114564654731168357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139995542076376436487445571 209993313114564654731168357)
  ·
    refine ⟨39373746208980872762094067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209993313114564654731168357 39373746208980872762094067)
    ·
      refine ⟨59060619313471309143141101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39373746208980872762094067 59060619313471309143141101)
      ·
        refine ⟨22147732242551740928677913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59060619313471309143141101 22147732242551740928677913)
        ·
          refine ⟨16610799181913805696508435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22147732242551740928677913 16610799181913805696508435)
          ·
            refine ⟨24916198772870708544762653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610799181913805696508435 24916198772870708544762653)
            ·
              refine ⟨9343574539826515704285995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24916198772870708544762653 9343574539826515704285995)
              ·
                refine ⟨14015361809739773556428993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9343574539826515704285995 14015361809739773556428993)
                ·
                  refine ⟨10511521357304830167321745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015361809739773556428993 10511521357304830167321745)
                  ·
                    refine ⟨7883641017978622625491309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10511521357304830167321745 7883641017978622625491309)
                    ·
                      refine ⟨2956365381741983484559241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883641017978622625491309 2956365381741983484559241)
                      ·
                        rfl

theorem cell23_5757501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5757501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757501 prefixEnd_5757501 := by exact prefixLift 5757501
  have htrace : WordTrace (prefixWord ++ tailWord_5757501) baseStart_5757501 baseEnd_5757501 := by
    simpa [prefixWord, tailWord_5757501, baseEnd_5757501] using wordTrace_append hprefix tailTrace_5757501
  have hstable : (prefixWord ++ tailWord_5757501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757501).length < 2 ^ (prefixWord ++ tailWord_5757501).sum := by decide
  have hdescent : baseEnd_5757501 < baseStart_5757501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757547 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 6]
def baseStart_5757547 : Nat := 118140960795 + 5757547 * 2 ^ 59
def prefixEnd_5757547 : Nat := 4983230072969 + 3 ^ 40 * 5757547 * 2
def baseEnd_5757547 : Nat := 985463000617363434861343

theorem tailTrace_5757547 : CollatzResearch.WordTrace tailWord_5757547 prefixEnd_5757547 985463000617363434861343 := by
  unfold tailWord_5757547
  simp only [CollatzResearch.WordTrace]
  refine ⟨209994990872398004587342895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139996660581598669724895263 209994990872398004587342895)
  ·
    refine ⟨314992486308597006881014343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209994990872398004587342895 314992486308597006881014343)
    ·
      refine ⟨472488729462895510321521515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314992486308597006881014343 472488729462895510321521515)
      ·
        refine ⟨708733094194343265482282273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472488729462895510321521515 708733094194343265482282273)
        ·
          refine ⟨531549820645757449111711705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708733094194343265482282273 531549820645757449111711705)
          ·
            refine ⟨398662365484318086833783779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531549820645757449111711705 398662365484318086833783779)
            ·
              refine ⟨597993548226477130250675669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398662365484318086833783779 597993548226477130250675669)
              ·
                refine ⟨14015473786558057740250211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 597993548226477130250675669 14015473786558057740250211)
                ·
                  refine ⟨21023210679837086610375317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14015473786558057740250211 21023210679837086610375317)
                  ·
                    refine ⟨985463000617363434861343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21023210679837086610375317 985463000617363434861343)
                    ·
                      rfl

theorem cell23_5757547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_5757547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757547 prefixEnd_5757547 := by exact prefixLift 5757547
  have htrace : WordTrace (prefixWord ++ tailWord_5757547) baseStart_5757547 baseEnd_5757547 := by
    simpa [prefixWord, tailWord_5757547, baseEnd_5757547] using wordTrace_append hprefix tailTrace_5757547
  have hstable : (prefixWord ++ tailWord_5757547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757547).length < 2 ^ (prefixWord ++ tailWord_5757547).sum := by decide
  have hdescent : baseEnd_5757547 < baseStart_5757547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757564 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_5757564 : Nat := 118140960795 + 5757564 * 2 ^ 59
def prefixEnd_5757564 : Nat := 4983230072969 + 3 ^ 40 * 5757564 * 2
def baseEnd_5757564 : Nat := 985465910341072246023817

theorem tailTrace_5757564 : CollatzResearch.WordTrace tailWord_5757564 prefixEnd_5757564 985465910341072246023817 := by
  unfold tailWord_5757564
  simp only [CollatzResearch.WordTrace]
  refine ⟨104997805456668208245355873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139997073942224277660474497 104997805456668208245355873)
  ·
    refine ⟨78748354092501156184016905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104997805456668208245355873 78748354092501156184016905)
    ·
      refine ⟨59061265569375867138012679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78748354092501156184016905 59061265569375867138012679)
      ·
        refine ⟨88591898354063800707019019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59061265569375867138012679 88591898354063800707019019)
        ·
          refine ⟨132887847531095701060528529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88591898354063800707019019 132887847531095701060528529)
          ·
            refine ⟨99665885648321775795396397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132887847531095701060528529 99665885648321775795396397)
            ·
              refine ⟨37374707118120665923273649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99665885648321775795396397 37374707118120665923273649)
              ·
                refine ⟨28031030338590499442455237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37374707118120665923273649 28031030338590499442455237)
                ·
                  refine ⟨5255818188485718645460357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28031030338590499442455237 5255818188485718645460357)
                  ·
                    refine ⟨985465910341072246023817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255818188485718645460357 985465910341072246023817)
                    ·
                      rfl

theorem cell23_5757564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_5757564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757564 prefixEnd_5757564 := by exact prefixLift 5757564
  have htrace : WordTrace (prefixWord ++ tailWord_5757564) baseStart_5757564 baseEnd_5757564 := by
    simpa [prefixWord, tailWord_5757564, baseEnd_5757564] using wordTrace_append hprefix tailTrace_5757564
  have hstable : (prefixWord ++ tailWord_5757564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757564).length < 2 ^ (prefixWord ++ tailWord_5757564).sum := by decide
  have hdescent : baseEnd_5757564 < baseStart_5757564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757571 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 5, 2, 2]
def baseStart_5757571 : Nat := 118140960795 + 5757571 * 2 ^ 59
def prefixEnd_5757571 : Nat := 4983230072969 + 3 ^ 40 * 5757571 * 2
def baseEnd_5757571 : Nat := 2956401325387798210683919

theorem tailTrace_5757571 : CollatzResearch.WordTrace tailWord_5757571 prefixEnd_5757571 2956401325387798210683919 := by
  unfold tailWord_5757571
  simp only [CollatzResearch.WordTrace]
  refine ⟨209995866224311056686216567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139997244149540704457477711 209995866224311056686216567)
  ·
    refine ⟨314993799336466585029324851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209995866224311056686216567 314993799336466585029324851)
    ·
      refine ⟨472490699004699877543987277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314993799336466585029324851 472490699004699877543987277)
      ·
        refine ⟨177184012126762454078995229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472490699004699877543987277 177184012126762454078995229)
        ·
          refine ⟨66444004547535920279623211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177184012126762454078995229 66444004547535920279623211)
          ·
            refine ⟨99666006821303880419434817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66444004547535920279623211 99666006821303880419434817)
            ·
              refine ⟨74749505115977910314576113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99666006821303880419434817 74749505115977910314576113)
              ·
                refine ⟨56062128836983432735932085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74749505115977910314576113 56062128836983432735932085)
                ·
                  refine ⟨5255824578467196818993633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56062128836983432735932085 5255824578467196818993633)
                  ·
                    refine ⟨3941868433850397614245225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5255824578467196818993633 3941868433850397614245225)
                    ·
                      refine ⟨2956401325387798210683919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941868433850397614245225 2956401325387798210683919)
                      ·
                        rfl

theorem cell23_5757571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_5757571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757571 prefixEnd_5757571 := by exact prefixLift 5757571
  have htrace : WordTrace (prefixWord ++ tailWord_5757571) baseStart_5757571 baseEnd_5757571 := by
    simpa [prefixWord, tailWord_5757571, baseEnd_5757571] using wordTrace_append hprefix tailTrace_5757571
  have hstable : (prefixWord ++ tailWord_5757571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757571).length < 2 ^ (prefixWord ++ tailWord_5757571).sum := by decide
  have hdescent : baseEnd_5757571 < baseStart_5757571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757598 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5757598 : Nat := 118140960795 + 5757598 * 2 ^ 59
def prefixEnd_5757598 : Nat := 4983230072969 + 3 ^ 40 * 5757598 * 2
def baseEnd_5757598 : Nat := 985471729788489868348765

theorem tailTrace_5757598 : CollatzResearch.WordTrace tailWord_5757598 prefixEnd_5757598 985471729788489868348765 := by
  unfold tailWord_5757598
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249606374401655037181181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139997900663475493531632965 26249606374401655037181181)
  ·
    refine ⟨9843602390400620638942943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26249606374401655037181181 9843602390400620638942943)
    ·
      refine ⟨14765403585600930958414415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9843602390400620638942943 14765403585600930958414415)
      ·
        refine ⟨22148105378401396437621623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14765403585600930958414415 22148105378401396437621623)
        ·
          refine ⟨33222158067602094656432435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22148105378401396437621623 33222158067602094656432435)
          ·
            refine ⟨49833237101403141984648653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33222158067602094656432435 49833237101403141984648653)
            ·
              refine ⟨18687463913026178244243245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49833237101403141984648653 18687463913026178244243245)
              ·
                refine ⟨7007798967384816841591217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18687463913026178244243245 7007798967384816841591217)
                ·
                  refine ⟨5255849225538612631193413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7007798967384816841591217 5255849225538612631193413)
                  ·
                    refine ⟨985471729788489868348765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255849225538612631193413 985471729788489868348765)
                    ·
                      rfl

theorem cell23_5757598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5757598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757598 prefixEnd_5757598 := by exact prefixLift 5757598
  have htrace : WordTrace (prefixWord ++ tailWord_5757598) baseStart_5757598 baseEnd_5757598 := by
    simpa [prefixWord, tailWord_5757598, baseEnd_5757598] using wordTrace_append hprefix tailTrace_5757598
  have hstable : (prefixWord ++ tailWord_5757598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757598).length < 2 ^ (prefixWord ++ tailWord_5757598).sum := by decide
  have hdescent : baseEnd_5757598 < baseStart_5757598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757621 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5757621 : Nat := 118140960795 + 5757621 * 2 ^ 59
def prefixEnd_5757621 : Nat := 4983230072969 + 3 ^ 40 * 5757621 * 2
def baseEnd_5757621 : Nat := 2956426999420523015058689

theorem tailTrace_5757621 : CollatzResearch.WordTrace tailWord_5757621 prefixEnd_5757621 2956426999420523015058689 := by
  unfold tailWord_5757621
  simp only [CollatzResearch.WordTrace]
  refine ⟨209997689874129915225536717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139998459916086610150357811 209997689874129915225536717)
  ·
    refine ⟨78749133702798718209576269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209997689874129915225536717 78749133702798718209576269)
    ·
      refine ⟨29530925138549519328591101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78749133702798718209576269 29530925138549519328591101)
      ·
        refine ⟨11074096926956069748221663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29530925138549519328591101 11074096926956069748221663)
        ·
          refine ⟨16611145390434104622332495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074096926956069748221663 16611145390434104622332495)
          ·
            refine ⟨24916718085651156933498743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611145390434104622332495 24916718085651156933498743)
            ·
              refine ⟨37375077128476735400248115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24916718085651156933498743 37375077128476735400248115)
              ·
                refine ⟨56062615692715103100372173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37375077128476735400248115 56062615692715103100372173)
                ·
                  refine ⟨21023480884768163662639565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56062615692715103100372173 21023480884768163662639565)
                  ·
                    refine ⟨7883805331788061373489837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21023480884768163662639565 7883805331788061373489837)
                    ·
                      refine ⟨2956426999420523015058689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883805331788061373489837 2956426999420523015058689)
                      ·
                        rfl

theorem cell23_5757621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5757621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757621 prefixEnd_5757621 := by exact prefixLift 5757621
  have htrace : WordTrace (prefixWord ++ tailWord_5757621) baseStart_5757621 baseEnd_5757621 := by
    simpa [prefixWord, tailWord_5757621, baseEnd_5757621] using wordTrace_append hprefix tailTrace_5757621
  have hstable : (prefixWord ++ tailWord_5757621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757621).length < 2 ^ (prefixWord ++ tailWord_5757621).sum := by decide
  have hdescent : baseEnd_5757621 < baseStart_5757621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757622 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5757622 : Nat := 118140960795 + 5757622 * 2 ^ 59
def prefixEnd_5757622 : Nat := 4983230072969 + 3 ^ 40 * 5757622 * 2
def baseEnd_5757622 : Nat := 2956427512901177511146185

theorem tailTrace_5757622 : CollatzResearch.WordTrace tailWord_5757622 prefixEnd_5757622 2956427512901177511146185 := by
  unfold tailWord_5757622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124857896695393274770195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139998484231417528264215413 13124857896695393274770195)
  ·
    refine ⟨19687286845043089912155293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13124857896695393274770195 19687286845043089912155293)
    ·
      refine ⟨7382732566891158717058235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19687286845043089912155293 7382732566891158717058235)
      ·
        refine ⟨11074098850336738075587353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382732566891158717058235 11074098850336738075587353)
        ·
          refine ⟨8305574137752553556690515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11074098850336738075587353 8305574137752553556690515)
          ·
            refine ⟨12458361206628830335035773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305574137752553556690515 12458361206628830335035773)
            ·
              refine ⟨4671885452485811375638415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12458361206628830335035773 4671885452485811375638415)
              ·
                refine ⟨7007828178728717063457623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671885452485811375638415 7007828178728717063457623)
                ·
                  refine ⟨10511742268093075595186435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007828178728717063457623 10511742268093075595186435)
                  ·
                    refine ⟨15767613402139613392779653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10511742268093075595186435 15767613402139613392779653)
                    ·
                      refine ⟨2956427512901177511146185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15767613402139613392779653 2956427512901177511146185)
                      ·
                        rfl

theorem cell23_5757622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5757622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757622 prefixEnd_5757622 := by exact prefixLift 5757622
  have htrace : WordTrace (prefixWord ++ tailWord_5757622) baseStart_5757622 baseEnd_5757622 := by
    simpa [prefixWord, tailWord_5757622, baseEnd_5757622] using wordTrace_append hprefix tailTrace_5757622
  have hstable : (prefixWord ++ tailWord_5757622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757622).length < 2 ^ (prefixWord ++ tailWord_5757622).sum := by decide
  have hdescent : baseEnd_5757622 < baseStart_5757622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757645 : List Nat := [1, 6, 2, 1, 3, 1, 1, 8]
def baseStart_5757645 : Nat := 118140960795 + 5757645 * 2 ^ 59
def prefixEnd_5757645 : Nat := 4983230072969 + 3 ^ 40 * 5757645 * 2
def baseEnd_5757645 : Nat := 109497752702082626709577

theorem tailTrace_5757645 : CollatzResearch.WordTrace tailWord_5757645 prefixEnd_5757645 109497752702082626709577 := by
  unfold tailWord_5757645
  simp only [CollatzResearch.WordTrace]
  refine ⟨209998565226042967324410389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139999043484028644882940259 209998565226042967324410389)
  ·
    refine ⟨9843682744970764093331737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209998565226042967324410389 9843682744970764093331737)
    ·
      refine ⟨7382762058728073069998803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9843682744970764093331737 7382762058728073069998803)
      ·
        refine ⟨11074143088092109604998205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382762058728073069998803 11074143088092109604998205)
        ·
          refine ⟨4152803658034541101874327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11074143088092109604998205 4152803658034541101874327)
          ·
            refine ⟨6229205487051811652811491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152803658034541101874327 6229205487051811652811491)
            ·
              refine ⟨9343808230577717479217237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229205487051811652811491 9343808230577717479217237)
              ·
                refine ⟨109497752702082626709577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9343808230577717479217237 109497752702082626709577)
                ·
                  rfl

theorem cell23_5757645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 8].length) (baseStart_5757645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757645 prefixEnd_5757645 := by exact prefixLift 5757645
  have htrace : WordTrace (prefixWord ++ tailWord_5757645) baseStart_5757645 baseEnd_5757645 := by
    simpa [prefixWord, tailWord_5757645, baseEnd_5757645] using wordTrace_append hprefix tailTrace_5757645
  have hstable : (prefixWord ++ tailWord_5757645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757645).length < 2 ^ (prefixWord ++ tailWord_5757645).sum := by decide
  have hdescent : baseEnd_5757645 < baseStart_5757645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757664 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_5757664 : Nat := 118140960795 + 5757664 * 2 ^ 59
def prefixEnd_5757664 : Nat := 4983230072969 + 3 ^ 40 * 5757664 * 2
def baseEnd_5757664 : Nat := 2956449079088666346820991

theorem tailTrace_5757664 : CollatzResearch.WordTrace tailWord_5757664 prefixEnd_5757664 2956449079088666346820991 := by
  unfold tailWord_5757664
  simp only [CollatzResearch.WordTrace]
  refine ⟨104999629106487066784676023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139999505475316089046234697 104999629106487066784676023)
  ·
    refine ⟨157499443659730600177014035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104999629106487066784676023 157499443659730600177014035)
    ·
      refine ⟨236249165489595900265521053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157499443659730600177014035 236249165489595900265521053)
      ·
        refine ⟨88593437058598462599570395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236249165489595900265521053 88593437058598462599570395)
        ·
          refine ⟨132890155587897693899355593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88593437058598462599570395 132890155587897693899355593)
          ·
            refine ⟨99667616690923270424516695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132890155587897693899355593 99667616690923270424516695)
            ·
              refine ⟨149501425036384905636775043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99667616690923270424516695 149501425036384905636775043)
              ·
                refine ⟨224252137554577358455162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149501425036384905636775043 224252137554577358455162565)
                ·
                  refine ⟨42047275791483254710342981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224252137554577358455162565 42047275791483254710342981)
                  ·
                    refine ⟨7883864210903110258189309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42047275791483254710342981 7883864210903110258189309)
                    ·
                      refine ⟨2956449079088666346820991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7883864210903110258189309 2956449079088666346820991)
                      ·
                        rfl

theorem cell23_5757664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_5757664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757664 prefixEnd_5757664 := by exact prefixLift 5757664
  have htrace : WordTrace (prefixWord ++ tailWord_5757664) baseStart_5757664 baseEnd_5757664 := by
    simpa [prefixWord, tailWord_5757664, baseEnd_5757664] using wordTrace_append hprefix tailTrace_5757664
  have hstable : (prefixWord ++ tailWord_5757664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757664).length < 2 ^ (prefixWord ++ tailWord_5757664).sum := by decide
  have hdescent : baseEnd_5757664 < baseStart_5757664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757674 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_5757674 : Nat := 118140960795 + 5757674 * 2 ^ 59
def prefixEnd_5757674 : Nat := 4983230072969 + 3 ^ 40 * 5757674 * 2
def baseEnd_5757674 : Nat := 2956454213895211307695945

theorem tailTrace_5757674 : CollatzResearch.WordTrace tailWord_5757674 prefixEnd_5757674 2956454213895211307695945 := by
  unfold tailWord_5757674
  simp only [CollatzResearch.WordTrace]
  refine ⟨52499905735734476319304019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139999748628625270184810717 52499905735734476319304019)
  ·
    refine ⟨78749858603601714478956029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52499905735734476319304019 78749858603601714478956029)
    ·
      refine ⟨29531196976350642929608511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78749858603601714478956029 29531196976350642929608511)
      ·
        refine ⟨44296795464525964394412767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531196976350642929608511 44296795464525964394412767)
        ·
          refine ⟨66445193196788946591619151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44296795464525964394412767 66445193196788946591619151)
          ·
            refine ⟨99667789795183419887428727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66445193196788946591619151 99667789795183419887428727)
            ·
              refine ⟨149501684692775129831143091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99667789795183419887428727 149501684692775129831143091)
              ·
                refine ⟨224252527039162694746714637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149501684692775129831143091 224252527039162694746714637)
                ·
                  refine ⟨84094697639686010530017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224252527039162694746714637 84094697639686010530017989)
                  ·
                    refine ⟨15767755807441126974378373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84094697639686010530017989 15767755807441126974378373)
                    ·
                      refine ⟨2956454213895211307695945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15767755807441126974378373 2956454213895211307695945)
                      ·
                        rfl

theorem cell23_5757674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_5757674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757674 prefixEnd_5757674 := by exact prefixLift 5757674
  have htrace : WordTrace (prefixWord ++ tailWord_5757674) baseStart_5757674 baseEnd_5757674 := by
    simpa [prefixWord, tailWord_5757674, baseEnd_5757674] using wordTrace_append hprefix tailTrace_5757674
  have hstable : (prefixWord ++ tailWord_5757674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757674).length < 2 ^ (prefixWord ++ tailWord_5757674).sum := by decide
  have hdescent : baseEnd_5757674 < baseStart_5757674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757678 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_5757678 : Nat := 118140960795 + 5757678 * 2 ^ 59
def prefixEnd_5757678 : Nat := 4983230072969 + 3 ^ 40 * 5757678 * 2
def baseEnd_5757678 : Nat := 2956456267817829292045927

theorem tailTrace_5757678 : CollatzResearch.WordTrace tailWord_5757678 prefixEnd_5757678 2956456267817829292045927 := by
  unfold tailWord_5757678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249971104365426745045211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139999845889948942640241125 26249971104365426745045211)
  ·
    refine ⟨39374956656548140117567817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26249971104365426745045211 39374956656548140117567817)
    ·
      refine ⟨29531217492411105088175863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39374956656548140117567817 29531217492411105088175863)
      ·
        refine ⟨44296826238616657632263795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531217492411105088175863 44296826238616657632263795)
        ·
          refine ⟨66445239357924986448395693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44296826238616657632263795 66445239357924986448395693)
          ·
            refine ⟨24916964759221869918148385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66445239357924986448395693 24916964759221869918148385)
            ·
              refine ⟨18687723569416402438611289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24916964759221869918148385 18687723569416402438611289)
              ·
                refine ⟨14015792677062301828958467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18687723569416402438611289 14015792677062301828958467)
                ·
                  refine ⟨21023689015593452743437701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14015792677062301828958467 21023689015593452743437701)
                  ·
                    refine ⟨3941941690423772389394569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21023689015593452743437701 3941941690423772389394569)
                    ·
                      refine ⟨2956456267817829292045927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941941690423772389394569 2956456267817829292045927)
                      ·
                        rfl

theorem cell23_5757678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_5757678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757678 prefixEnd_5757678 := by exact prefixLift 5757678
  have htrace : WordTrace (prefixWord ++ tailWord_5757678) baseStart_5757678 baseEnd_5757678 := by
    simpa [prefixWord, tailWord_5757678, baseEnd_5757678] using wordTrace_append hprefix tailTrace_5757678
  have hstable : (prefixWord ++ tailWord_5757678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757678).length < 2 ^ (prefixWord ++ tailWord_5757678).sum := by decide
  have hdescent : baseEnd_5757678 < baseStart_5757678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757682 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5757682 : Nat := 118140960795 + 5757682 * 2 ^ 59
def prefixEnd_5757682 : Nat := 4983230072969 + 3 ^ 40 * 5757682 * 2
def baseEnd_5757682 : Nat := 2956458321740447276395909

theorem tailTrace_5757682 : CollatzResearch.WordTrace tailWord_5757682 prefixEnd_5757682 2956458321740447276395909 := by
  unfold tailWord_5757682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52499978681727230660876825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139999943151272615095671533 52499978681727230660876825)
  ·
    refine ⟨39374984011295422995657619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52499978681727230660876825 39374984011295422995657619)
    ·
      refine ⟨59062476016943134493486429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39374984011295422995657619 59062476016943134493486429)
      ·
        refine ⟨22148428506353675435057411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59062476016943134493486429 22148428506353675435057411)
        ·
          refine ⟨33222642759530513152586117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22148428506353675435057411 33222642759530513152586117)
          ·
            refine ⟨6229245517411971216109897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33222642759530513152586117 6229245517411971216109897)
            ·
              refine ⟨4671934138058978412082423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229245517411971216109897 4671934138058978412082423)
              ·
                refine ⟨7007901207088467618123635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671934138058978412082423 7007901207088467618123635)
                ·
                  refine ⟨10511851810632701427185453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007901207088467618123635 10511851810632701427185453)
                  ·
                    refine ⟨3941944428987263035194545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10511851810632701427185453 3941944428987263035194545)
                    ·
                      refine ⟨2956458321740447276395909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3941944428987263035194545 2956458321740447276395909)
                      ·
                        rfl

theorem cell23_5757682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5757682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757682 prefixEnd_5757682 := by exact prefixLift 5757682
  have htrace : WordTrace (prefixWord ++ tailWord_5757682) baseStart_5757682 baseEnd_5757682 := by
    simpa [prefixWord, tailWord_5757682, baseEnd_5757682] using wordTrace_append hprefix tailTrace_5757682
  have hstable : (prefixWord ++ tailWord_5757682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757682).length < 2 ^ (prefixWord ++ tailWord_5757682).sum := by decide
  have hdescent : baseEnd_5757682 < baseStart_5757682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757751 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_5757751 : Nat := 118140960795 + 5757751 * 2 ^ 59
def prefixEnd_5757751 : Nat := 4983230072969 + 3 ^ 40 * 5757751 * 2
def baseEnd_5757751 : Nat := 2956493751905607506433091

theorem tailTrace_5757751 : CollatzResearch.WordTrace tailWord_5757751 prefixEnd_5757751 2956493751905607506433091 := by
  unfold tailWord_5757751
  simp only [CollatzResearch.WordTrace]
  refine ⟨210002431363658947427769107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140001620909105964951846071 210002431363658947427769107)
  ·
    refine ⟨315003647045488421141653661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210002431363658947427769107 315003647045488421141653661)
    ·
      refine ⟨118126367642058157928120123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315003647045488421141653661 118126367642058157928120123)
      ·
        refine ⟨177189551463087236892180185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118126367642058157928120123 177189551463087236892180185)
        ·
          refine ⟨132892163597315427669135139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177189551463087236892180185 132892163597315427669135139)
          ·
            refine ⟨199338245395973141503702709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132892163597315427669135139 199338245395973141503702709)
            ·
              refine ⟨18687960505872482015972129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199338245395973141503702709 18687960505872482015972129)
              ·
                refine ⟨14015970379404361511979097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18687960505872482015972129 14015970379404361511979097)
                ·
                  refine ⟨10511977784553271133984323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015970379404361511979097 10511977784553271133984323)
                  ·
                    refine ⟨15767966676829906700976485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10511977784553271133984323 15767966676829906700976485)
                    ·
                      refine ⟨2956493751905607506433091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15767966676829906700976485 2956493751905607506433091)
                      ·
                        rfl

theorem cell23_5757751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_5757751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757751 prefixEnd_5757751 := by exact prefixLift 5757751
  have htrace : WordTrace (prefixWord ++ tailWord_5757751) baseStart_5757751 baseEnd_5757751 := by
    simpa [prefixWord, tailWord_5757751, baseEnd_5757751] using wordTrace_append hprefix tailTrace_5757751
  have hstable : (prefixWord ++ tailWord_5757751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757751).length < 2 ^ (prefixWord ++ tailWord_5757751).sum := by decide
  have hdescent : baseEnd_5757751 < baseStart_5757751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757758 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_5757758 : Nat := 118140960795 + 5757758 * 2 ^ 59
def prefixEnd_5757758 : Nat := 4983230072969 + 3 ^ 40 * 5757758 * 2
def baseEnd_5757758 : Nat := 2956497346270188979045559

theorem tailTrace_5757758 : CollatzResearch.WordTrace tailWord_5757758 prefixEnd_5757758 2956497346270188979045559 := by
  unfold tailWord_5757758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250335834329198452909241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140001791116422391748849285 26250335834329198452909241)
  ·
    refine ⟨19687751875746898839681931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26250335834329198452909241 19687751875746898839681931)
    ·
      refine ⟨29531627813620348259522897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687751875746898839681931 29531627813620348259522897)
      ·
        refine ⟨22148720860215261194642173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29531627813620348259522897 22148720860215261194642173)
        ·
          refine ⟨8305770322580722947990815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22148720860215261194642173 8305770322580722947990815)
          ·
            refine ⟨12458655483871084421986223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305770322580722947990815 12458655483871084421986223)
            ·
              refine ⟨18687983225806626632979335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12458655483871084421986223 18687983225806626632979335)
              ·
                refine ⟨28031974838709939949469003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18687983225806626632979335 28031974838709939949469003)
                ·
                  refine ⟨42047962258064909924203505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28031974838709939949469003 42047962258064909924203505)
                  ·
                    refine ⟨31535971693548682443152629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42047962258064909924203505 31535971693548682443152629)
                    ·
                      refine ⟨2956497346270188979045559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31535971693548682443152629 2956497346270188979045559)
                      ·
                        rfl

theorem cell23_5757758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_5757758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757758 prefixEnd_5757758 := by exact prefixLift 5757758
  have htrace : WordTrace (prefixWord ++ tailWord_5757758) baseStart_5757758 baseEnd_5757758 := by
    simpa [prefixWord, tailWord_5757758, baseEnd_5757758] using wordTrace_append hprefix tailTrace_5757758
  have hstable : (prefixWord ++ tailWord_5757758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757758).length < 2 ^ (prefixWord ++ tailWord_5757758).sum := by decide
  have hdescent : baseEnd_5757758 < baseStart_5757758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757818 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_5757818 : Nat := 118140960795 + 5757818 * 2 ^ 59
def prefixEnd_5757818 : Nat := 4983230072969 + 3 ^ 40 * 5757818 * 2
def baseEnd_5757818 : Nat := 2956528155109458744295283

theorem tailTrace_5757818 : CollatzResearch.WordTrace tailWord_5757818 prefixEnd_5757818 2956528155109458744295283 := by
  unfold tailWord_5757818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52501218763604054467614527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140003250036277478580305405 52501218763604054467614527)
  ·
    refine ⟨78751828145406081701421791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52501218763604054467614527 78751828145406081701421791)
    ·
      refine ⟨118127742218109122552132687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78751828145406081701421791 118127742218109122552132687)
      ·
        refine ⟨177191613327163683828199031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118127742218109122552132687 177191613327163683828199031)
        ·
          refine ⟨265787419990745525742298547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177191613327163683828199031 265787419990745525742298547)
          ·
            refine ⟨398681129986118288613447821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265787419990745525742298547 398681129986118288613447821)
            ·
              refine ⟨149505423744794358230042933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398681129986118288613447821 149505423744794358230042933)
              ·
                refine ⟨14016133476074471084066525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149505423744794358230042933 14016133476074471084066525)
                ·
                  refine ⟨5256050053527926656524947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14016133476074471084066525 5256050053527926656524947)
                  ·
                    refine ⟨7884075080291889984787421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256050053527926656524947 7884075080291889984787421)
                    ·
                      refine ⟨2956528155109458744295283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7884075080291889984787421 2956528155109458744295283)
                      ·
                        rfl

theorem cell23_5757818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_5757818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757818 prefixEnd_5757818 := by exact prefixLift 5757818
  have htrace : WordTrace (prefixWord ++ tailWord_5757818) baseStart_5757818 baseEnd_5757818 := by
    simpa [prefixWord, tailWord_5757818, baseEnd_5757818] using wordTrace_append hprefix tailTrace_5757818
  have hstable : (prefixWord ++ tailWord_5757818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757818).length < 2 ^ (prefixWord ++ tailWord_5757818).sum := by decide
  have hdescent : baseEnd_5757818 < baseStart_5757818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757821 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_5757821 : Nat := 118140960795 + 5757821 * 2 ^ 59
def prefixEnd_5757821 : Nat := 4983230072969 + 3 ^ 40 * 5757821 * 2
def baseEnd_5757821 : Nat := 985509898517140744185923

theorem tailTrace_5757821 : CollatzResearch.WordTrace tailWord_5757821 prefixEnd_5757821 985509898517140744185923 := by
  unfold tailWord_5757821
  simp only [CollatzResearch.WordTrace]
  refine ⟨210004984473405349382817317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140003322982270232921878211 210004984473405349382817317)
  ·
    refine ⟨39375934588763503009278247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210004984473405349382817317 39375934588763503009278247)
    ·
      refine ⟨59063901883145254513917371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39375934588763503009278247 59063901883145254513917371)
      ·
        refine ⟨88595852824717881770876057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59063901883145254513917371 88595852824717881770876057)
        ·
          refine ⟨66446889618538411328157043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88595852824717881770876057 66446889618538411328157043)
          ·
            refine ⟨99670334427807616992235565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66446889618538411328157043 99670334427807616992235565)
            ·
              refine ⟨37376375410427856372088337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99670334427807616992235565 37376375410427856372088337)
              ·
                refine ⟨28032281557820892279066253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37376375410427856372088337 28032281557820892279066253)
                ·
                  refine ⟨10512105584182834604649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28032281557820892279066253 10512105584182834604649845)
                  ·
                    refine ⟨985509898517140744185923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10512105584182834604649845 985509898517140744185923)
                    ·
                      rfl

theorem cell23_5757821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_5757821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757821 prefixEnd_5757821 := by exact prefixLift 5757821
  have htrace : WordTrace (prefixWord ++ tailWord_5757821) baseStart_5757821 baseEnd_5757821 := by
    simpa [prefixWord, tailWord_5757821, baseEnd_5757821] using wordTrace_append hprefix tailTrace_5757821
  have hstable : (prefixWord ++ tailWord_5757821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757821).length < 2 ^ (prefixWord ++ tailWord_5757821).sum := by decide
  have hdescent : baseEnd_5757821 < baseStart_5757821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757828 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5757828 : Nat := 118140960795 + 5757828 * 2 ^ 59
def prefixEnd_5757828 : Nat := 4983230072969 + 3 ^ 40 * 5757828 * 2
def baseEnd_5757828 : Nat := 2956533289916003705170237

theorem tailTrace_5757828 : CollatzResearch.WordTrace tailWord_5757828 prefixEnd_5757828 2956533289916003705170237 := by
  unfold tailWord_5757828
  simp only [CollatzResearch.WordTrace]
  refine ⟨105002619892189994789161069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140003493189586659718881425 105002619892189994789161069)
  ·
    refine ⟨39375982459571248045935401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105002619892189994789161069 39375982459571248045935401)
    ·
      refine ⟨29531986844678436034451551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39375982459571248045935401 29531986844678436034451551)
      ·
        refine ⟨44297980267017654051677327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531986844678436034451551 44297980267017654051677327)
        ·
          refine ⟨66446970400526481077515991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44297980267017654051677327 66446970400526481077515991)
          ·
            refine ⟨99670455600789721616273987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66446970400526481077515991 99670455600789721616273987)
            ·
              refine ⟨149505683401184582424410981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99670455600789721616273987 149505683401184582424410981)
              ·
                refine ⟨28032315637722109204577059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149505683401184582424410981 28032315637722109204577059)
                ·
                  refine ⟨42048473456583163806865589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28032315637722109204577059 42048473456583163806865589)
                  ·
                    refine ⟨3942044386554671606893649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42048473456583163806865589 3942044386554671606893649)
                    ·
                      refine ⟨2956533289916003705170237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942044386554671606893649 2956533289916003705170237)
                      ·
                        rfl

theorem cell23_5757828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5757828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757828 prefixEnd_5757828 := by exact prefixLift 5757828
  have htrace : WordTrace (prefixWord ++ tailWord_5757828) baseStart_5757828 baseEnd_5757828 := by
    simpa [prefixWord, tailWord_5757828, baseEnd_5757828] using wordTrace_append hprefix tailTrace_5757828
  have hstable : (prefixWord ++ tailWord_5757828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757828).length < 2 ^ (prefixWord ++ tailWord_5757828).sum := by decide
  have hdescent : baseEnd_5757828 < baseStart_5757828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757845 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_5757845 : Nat := 118140960795 + 5757845 * 2 ^ 59
def prefixEnd_5757845 : Nat := 4983230072969 + 3 ^ 40 * 5757845 * 2
def baseEnd_5757845 : Nat := 2956542019087130138657659

theorem tailTrace_5757845 : CollatzResearch.WordTrace tailWord_5757845 prefixEnd_5757845 2956542019087130138657659 := by
  unfold tailWord_5757845
  simp only [CollatzResearch.WordTrace]
  refine ⟨210005859825318401481690989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140003906550212267654460659 210005859825318401481690989)
  ·
    refine ⟨78752197434494400555634121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210005859825318401481690989 78752197434494400555634121)
    ·
      refine ⟨59064148075870800416725591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78752197434494400555634121 59064148075870800416725591)
      ·
        refine ⟨88596222113806200625088387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59064148075870800416725591 88596222113806200625088387)
        ·
          refine ⟨132894333170709300937632581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88596222113806200625088387 132894333170709300937632581)
          ·
            refine ⟨24917687469507993925806109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132894333170709300937632581 24917687469507993925806109)
            ·
              refine ⟨9344132801065497722177291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24917687469507993925806109 9344132801065497722177291)
              ·
                refine ⟨14016199201598246583265937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344132801065497722177291 14016199201598246583265937)
                ·
                  refine ⟨10512149401198684937449453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14016199201598246583265937 10512149401198684937449453)
                  ·
                    refine ⟨3942056025449506851543545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10512149401198684937449453 3942056025449506851543545)
                    ·
                      refine ⟨2956542019087130138657659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942056025449506851543545 2956542019087130138657659)
                      ·
                        rfl

theorem cell23_5757845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_5757845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757845 prefixEnd_5757845 := by exact prefixLift 5757845
  have htrace : WordTrace (prefixWord ++ tailWord_5757845) baseStart_5757845 baseEnd_5757845 := by
    simpa [prefixWord, tailWord_5757845, baseEnd_5757845] using wordTrace_append hprefix tailTrace_5757845
  have hstable : (prefixWord ++ tailWord_5757845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757845).length < 2 ^ (prefixWord ++ tailWord_5757845).sum := by decide
  have hdescent : baseEnd_5757845 < baseStart_5757845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757846 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5757846 : Nat := 118140960795 + 5757846 * 2 ^ 59
def prefixEnd_5757846 : Nat := 4983230072969 + 3 ^ 40 * 5757846 * 2
def baseEnd_5757846 : Nat := 985514177522594878248385

theorem tailTrace_5757846 : CollatzResearch.WordTrace tailWord_5757846 prefixEnd_5757846 985514177522594878248385 := by
  unfold tailWord_5757846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125368518644673665779837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140003930865543185768318261 13125368518644673665779837)
  ·
    refine ⟨4922013194491752624667439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13125368518644673665779837 4922013194491752624667439)
    ·
      refine ⟨7383019791737628937001159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922013194491752624667439 7383019791737628937001159)
      ·
        refine ⟨11074529687606443405501739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383019791737628937001159 11074529687606443405501739)
        ·
          refine ⟨16611794531409665108252609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074529687606443405501739 16611794531409665108252609)
          ·
            refine ⟨12458845898557248831189457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16611794531409665108252609 12458845898557248831189457)
            ·
              refine ⟨9344134423917936623392093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12458845898557248831189457 9344134423917936623392093)
              ·
                refine ⟨3504050408969226233772035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9344134423917936623392093 3504050408969226233772035)
                ·
                  refine ⟨5256075613453839350658053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504050408969226233772035 5256075613453839350658053)
                  ·
                    refine ⟨985514177522594878248385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256075613453839350658053 985514177522594878248385)
                    ·
                      rfl

theorem cell23_5757846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5757846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757846 prefixEnd_5757846 := by exact prefixLift 5757846
  have htrace : WordTrace (prefixWord ++ tailWord_5757846) baseStart_5757846 baseEnd_5757846 := by
    simpa [prefixWord, tailWord_5757846, baseEnd_5757846] using wordTrace_append hprefix tailTrace_5757846
  have hstable : (prefixWord ++ tailWord_5757846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757846).length < 2 ^ (prefixWord ++ tailWord_5757846).sum := by decide
  have hdescent : baseEnd_5757846 < baseStart_5757846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757855 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 1, 5]
def baseStart_5757855 : Nat := 118140960795 + 5757855 * 2 ^ 59
def prefixEnd_5757855 : Nat := 4983230072969 + 3 ^ 40 * 5757855 * 2
def baseEnd_5757855 : Nat := 985515717964558366510871

theorem tailTrace_5757855 : CollatzResearch.WordTrace tailWord_5757855 prefixEnd_5757855 985515717964558366510871 := by
  unfold tailWord_5757855
  simp only [CollatzResearch.WordTrace]
  refine ⟨210006224555282173189555019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140004149703521448793036679 210006224555282173189555019)
  ·
    refine ⟨315009336832923259784332529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210006224555282173189555019 315009336832923259784332529)
    ·
      refine ⟨236257002624692444838249397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315009336832923259784332529 236257002624692444838249397)
      ·
        refine ⟨22149093996064916703585881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236257002624692444838249397 22149093996064916703585881)
        ·
          refine ⟨16611820497048687527689411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22149093996064916703585881 16611820497048687527689411)
          ·
            refine ⟨24917730745573031291534117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611820497048687527689411 24917730745573031291534117)
            ·
              refine ⟨4672074514794943367162647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24917730745573031291534117 4672074514794943367162647)
              ·
                refine ⟨7008111772192415050743971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672074514794943367162647 7008111772192415050743971)
                ·
                  refine ⟨10512167658288622576115957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7008111772192415050743971 10512167658288622576115957)
                  ·
                    refine ⟨985515717964558366510871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10512167658288622576115957 985515717964558366510871)
                    ·
                      rfl

theorem cell23_5757855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_5757855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757855 prefixEnd_5757855 := by exact prefixLift 5757855
  have htrace : WordTrace (prefixWord ++ tailWord_5757855) baseStart_5757855 baseEnd_5757855 := by
    simpa [prefixWord, tailWord_5757855, baseEnd_5757855] using wordTrace_append hprefix tailTrace_5757855
  have hstable : (prefixWord ++ tailWord_5757855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757855).length < 2 ^ (prefixWord ++ tailWord_5757855).sum := by decide
  have hdescent : baseEnd_5757855 < baseStart_5757855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757869 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5757869 : Nat := 118140960795 + 5757869 * 2 ^ 59
def prefixEnd_5757869 : Nat := 4983230072969 + 3 ^ 40 * 5757869 * 2
def baseEnd_5757869 : Nat := 2956554342622838044757549

theorem tailTrace_5757869 : CollatzResearch.WordTrace tailWord_5757869 prefixEnd_5757869 2956554342622838044757549 := by
  unfold tailWord_5757869
  simp only [CollatzResearch.WordTrace]
  refine ⟨210006735177231453580564661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140004490118154302387043107 210006735177231453580564661)
  ·
    refine ⟨19688131422865448773177937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210006735177231453580564661 19688131422865448773177937)
    ·
      refine ⟨14766098567149086579883453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19688131422865448773177937 14766098567149086579883453)
      ·
        refine ⟨5537286962680907467456295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14766098567149086579883453 5537286962680907467456295)
        ·
          refine ⟨8305930444021361201184443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537286962680907467456295 8305930444021361201184443)
          ·
            refine ⟨12458895666032041801776665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305930444021361201184443 12458895666032041801776665)
            ·
              refine ⟨9344171749524031351332499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12458895666032041801776665 9344171749524031351332499)
              ·
                refine ⟨14016257624286047026998749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344171749524031351332499 14016257624286047026998749)
                ·
                  refine ⟨5256096609107267635124531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14016257624286047026998749 5256096609107267635124531)
                  ·
                    refine ⟨7884144913660901452686797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256096609107267635124531 7884144913660901452686797)
                    ·
                      refine ⟨2956554342622838044757549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7884144913660901452686797 2956554342622838044757549)
                      ·
                        rfl

theorem cell23_5757869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5757869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757869 prefixEnd_5757869 := by exact prefixLift 5757869
  have htrace : WordTrace (prefixWord ++ tailWord_5757869) baseStart_5757869 baseEnd_5757869 := by
    simpa [prefixWord, tailWord_5757869, baseEnd_5757869] using wordTrace_append hprefix tailTrace_5757869
  have hstable : (prefixWord ++ tailWord_5757869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757869).length < 2 ^ (prefixWord ++ tailWord_5757869).sum := by decide
  have hdescent : baseEnd_5757869 < baseStart_5757869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757885 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_5757885 : Nat := 118140960795 + 5757885 * 2 ^ 59
def prefixEnd_5757885 : Nat := 4983230072969 + 3 ^ 40 * 5757885 * 2
def baseEnd_5757885 : Nat := 985520852771103327385825

theorem tailTrace_5757885 : CollatzResearch.WordTrace tailWord_5757885 prefixEnd_5757885 985520852771103327385825 := by
  unfold tailWord_5757885
  simp only [CollatzResearch.WordTrace]
  refine ⟨210007318745173488313147109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140004879163448992208764739 210007318745173488313147109)
  ·
    refine ⟨39376372264720029058715083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210007318745173488313147109 39376372264720029058715083)
    ·
      refine ⟨59064558397080043588072625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39376372264720029058715083 59064558397080043588072625)
      ·
        refine ⟨44298418797810032691054469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59064558397080043588072625 44298418797810032691054469)
        ·
          refine ⟨8305953524589381129572713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44298418797810032691054469 8305953524589381129572713)
          ·
            refine ⟨6229465143442035847179535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8305953524589381129572713 6229465143442035847179535)
            ·
              refine ⟨9344197715163053770769303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229465143442035847179535 9344197715163053770769303)
              ·
                refine ⟨14016296572744580656153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344197715163053770769303 14016296572744580656153955)
                ·
                  refine ⟨21024444859116870984230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14016296572744580656153955 21024444859116870984230933)
                  ·
                    refine ⟨985520852771103327385825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21024444859116870984230933 985520852771103327385825)
                    ·
                      rfl

theorem cell23_5757885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_5757885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757885 prefixEnd_5757885 := by exact prefixLift 5757885
  have htrace : WordTrace (prefixWord ++ tailWord_5757885) baseStart_5757885 baseEnd_5757885 := by
    simpa [prefixWord, tailWord_5757885, baseEnd_5757885] using wordTrace_append hprefix tailTrace_5757885
  have hstable : (prefixWord ++ tailWord_5757885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757885).length < 2 ^ (prefixWord ++ tailWord_5757885).sum := by decide
  have hdescent : baseEnd_5757885 < baseStart_5757885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757888 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_5757888 : Nat := 118140960795 + 5757888 * 2 ^ 59
def prefixEnd_5757888 : Nat := 4983230072969 + 3 ^ 40 * 5757888 * 2
def baseEnd_5757888 : Nat := 2956564098755273470419961

theorem tailTrace_5757888 : CollatzResearch.WordTrace tailWord_5757888 prefixEnd_5757888 2956564098755273470419961 := by
  unfold tailWord_5757888
  simp only [CollatzResearch.WordTrace]
  refine ⟨105003714082081309912753159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140004952109441746550337545 105003714082081309912753159)
  ·
    refine ⟨157505571123121964869129739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105003714082081309912753159 157505571123121964869129739)
    ·
      refine ⟨236258356684682947303694609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157505571123121964869129739 236258356684682947303694609)
      ·
        refine ⟨177193767513512210477770957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236258356684682947303694609 177193767513512210477770957)
        ·
          refine ⟨66447662817567078929164109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177193767513512210477770957 66447662817567078929164109)
          ·
            refine ⟨24917873556587654598436541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66447662817567078929164109 24917873556587654598436541)
            ·
              refine ⟨9344202583720370474413703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24917873556587654598436541 9344202583720370474413703)
              ·
                refine ⟨14016303875580555711620555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344202583720370474413703 14016303875580555711620555)
                ·
                  refine ⟨21024455813370833567430833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14016303875580555711620555 21024455813370833567430833)
                  ·
                    refine ⟨15768341860028125175573125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21024455813370833567430833 15768341860028125175573125)
                    ·
                      refine ⟨2956564098755273470419961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15768341860028125175573125 2956564098755273470419961)
                      ·
                        rfl

theorem cell23_5757888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_5757888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757888 prefixEnd_5757888 := by exact prefixLift 5757888
  have htrace : WordTrace (prefixWord ++ tailWord_5757888) baseStart_5757888 baseEnd_5757888 := by
    simpa [prefixWord, tailWord_5757888, baseEnd_5757888] using wordTrace_append hprefix tailTrace_5757888
  have hstable : (prefixWord ++ tailWord_5757888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757888).length < 2 ^ (prefixWord ++ tailWord_5757888).sum := by decide
  have hdescent : baseEnd_5757888 < baseStart_5757888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757921 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5757921 : Nat := 118140960795 + 5757921 * 2 ^ 59
def prefixEnd_5757921 : Nat := 4983230072969 + 3 ^ 40 * 5757921 * 2
def baseEnd_5757921 : Nat := 2956581043616871841307309

theorem tailTrace_5757921 : CollatzResearch.WordTrace tailWord_5757921 prefixEnd_5757921 2956581043616871841307309 := by
  unfold tailWord_5757921
  simp only [CollatzResearch.WordTrace]
  refine ⟨210008631773043066461457617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140005754515362044307638411 210008631773043066461457617)
  ·
    refine ⟨157506473829782299846093213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210008631773043066461457617 157506473829782299846093213)
    ·
      refine ⟨59064927686168362442284955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157506473829782299846093213 59064927686168362442284955)
      ·
        refine ⟨88597391529252543663427433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59064927686168362442284955 88597391529252543663427433)
        ·
          refine ⟨66448043646939407747570575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88597391529252543663427433 66448043646939407747570575)
          ·
            refine ⟨99672065470409111621355863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66448043646939407747570575 99672065470409111621355863)
            ·
              refine ⟨149508098205613667432033795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99672065470409111621355863 149508098205613667432033795)
              ·
                refine ⟨224262147308420501148050693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149508098205613667432033795 224262147308420501148050693)
                ·
                  refine ⟨42049152620328843965259505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224262147308420501148050693 42049152620328843965259505)
                  ·
                    refine ⟨31536864465246632973944629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42049152620328843965259505 31536864465246632973944629)
                    ·
                      refine ⟨2956581043616871841307309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31536864465246632973944629 2956581043616871841307309)
                      ·
                        rfl

theorem cell23_5757921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5757921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757921 prefixEnd_5757921 := by exact prefixLift 5757921
  have htrace : WordTrace (prefixWord ++ tailWord_5757921) baseStart_5757921 baseEnd_5757921 := by
    simpa [prefixWord, tailWord_5757921, baseEnd_5757921] using wordTrace_append hprefix tailTrace_5757921
  have hstable : (prefixWord ++ tailWord_5757921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757921).length < 2 ^ (prefixWord ++ tailWord_5757921).sum := by decide
  have hdescent : baseEnd_5757921 < baseStart_5757921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5757978 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_5757978 : Nat := 118140960795 + 5757978 * 2 ^ 59
def prefixEnd_5757978 : Nat := 4983230072969 + 3 ^ 40 * 5757978 * 2
def baseEnd_5757978 : Nat := 2956610312014178118294547

theorem tailTrace_5757978 : CollatzResearch.WordTrace tailWord_5757978 prefixEnd_5757978 2956610312014178118294547 := by
  unfold tailWord_5757978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52502677683459141299070647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140007140489224376797521725 52502677683459141299070647)
  ·
    refine ⟨78754016525188711948605971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52502677683459141299070647 78754016525188711948605971)
    ·
      refine ⟨118131024787783067922908957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78754016525188711948605971 118131024787783067922908957)
      ·
        refine ⟨44299134295418650471090859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118131024787783067922908957 44299134295418650471090859)
        ·
          refine ⟨66448701443127975706636289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44299134295418650471090859 66448701443127975706636289)
          ·
            refine ⟨49836526082345981779977217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66448701443127975706636289 49836526082345981779977217)
            ·
              refine ⟨37377394561759486334982913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49836526082345981779977217 37377394561759486334982913)
              ·
                refine ⟨28033045921319614751237185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37377394561759486334982913 28033045921319614751237185)
                ·
                  refine ⟨21024784440989711063427889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28033045921319614751237185 21024784440989711063427889)
                  ·
                    refine ⟨15768588330742283297570917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21024784440989711063427889 15768588330742283297570917)
                    ·
                      refine ⟨2956610312014178118294547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15768588330742283297570917 2956610312014178118294547)
                      ·
                        rfl

theorem cell23_5757978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_5757978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5757978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5757978 prefixEnd_5757978 := by exact prefixLift 5757978
  have htrace : WordTrace (prefixWord ++ tailWord_5757978) baseStart_5757978 baseEnd_5757978 := by
    simpa [prefixWord, tailWord_5757978, baseEnd_5757978] using wordTrace_append hprefix tailTrace_5757978
  have hstable : (prefixWord ++ tailWord_5757978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5757978).length < 2 ^ (prefixWord ++ tailWord_5757978).sum := by decide
  have hdescent : baseEnd_5757978 < baseStart_5757978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5757978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758115 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 5, 2]
def baseStart_5758115 : Nat := 118140960795 + 5758115 * 2 ^ 59
def prefixEnd_5758115 : Nat := 4983230072969 + 3 ^ 40 * 5758115 * 2
def baseEnd_5758115 : Nat := 2956680658863844082281417

theorem tailTrace_5758115 : CollatzResearch.WordTrace tailWord_5758115 prefixEnd_5758115 2956680658863844082281417 := by
  unfold tailWord_5758115
  simp only [CollatzResearch.WordTrace]
  refine ⟨210015707534340237594019799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140010471689560158396013199 210015707534340237594019799)
  ·
    refine ⟨315023561301510356391029699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210015707534340237594019799 315023561301510356391029699)
    ·
      refine ⟨472535341952265534586544549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315023561301510356391029699 472535341952265534586544549)
      ·
        refine ⟨88600376616049787734977103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 472535341952265534586544549 88600376616049787734977103)
        ·
          refine ⟨132900564924074681602465655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88600376616049787734977103 132900564924074681602465655)
          ·
            refine ⟨199350847386112022403698483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132900564924074681602465655 199350847386112022403698483)
            ·
              refine ⟨299026271079168033605547725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199350847386112022403698483 299026271079168033605547725)
              ·
                refine ⟨112134851654688012602080397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299026271079168033605547725 112134851654688012602080397)
                ·
                  refine ⟨42050569370508004725780149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112134851654688012602080397 42050569370508004725780149)
                  ·
                    refine ⟨3942240878485125443041889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42050569370508004725780149 3942240878485125443041889)
                    ·
                      refine ⟨2956680658863844082281417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942240878485125443041889 2956680658863844082281417)
                      ·
                        rfl

theorem cell23_5758115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_5758115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758115 prefixEnd_5758115 := by exact prefixLift 5758115
  have htrace : WordTrace (prefixWord ++ tailWord_5758115) baseStart_5758115 baseEnd_5758115 := by
    simpa [prefixWord, tailWord_5758115, baseEnd_5758115] using wordTrace_append hprefix tailTrace_5758115
  have hstable : (prefixWord ++ tailWord_5758115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758115).length < 2 ^ (prefixWord ++ tailWord_5758115).sum := by decide
  have hdescent : baseEnd_5758115 < baseStart_5758115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758128 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_5758128 : Nat := 118140960795 + 5758128 * 2 ^ 59
def prefixEnd_5758128 : Nat := 4983230072969 + 3 ^ 40 * 5758128 * 2
def baseEnd_5758128 : Nat := 2956687334112352531418857

theorem tailTrace_5758128 : CollatzResearch.WordTrace tailWord_5758128 prefixEnd_5758128 2956687334112352531418857 := by
  unfold tailWord_5758128
  simp only [CollatzResearch.WordTrace]
  refine ⟨105008090841646570407121519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140010787788862093876162025 105008090841646570407121519)
  ·
    refine ⟨157512136262469855610682279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105008090841646570407121519 157512136262469855610682279)
    ·
      refine ⟨236268204393704783416023419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157512136262469855610682279 236268204393704783416023419)
      ·
        refine ⟨354402306590557175124035129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236268204393704783416023419 354402306590557175124035129)
        ·
          refine ⟨265801729942917881343026347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354402306590557175124035129 265801729942917881343026347)
          ·
            refine ⟨398702594914376822014539521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265801729942917881343026347 398702594914376822014539521)
            ·
              refine ⟨299026946185782616510904641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398702594914376822014539521 299026946185782616510904641)
              ·
                refine ⟨224270209639336962383178481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299026946185782616510904641 224270209639336962383178481)
                ·
                  refine ⟨168202657229502721787383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224270209639336962383178481 168202657229502721787383861)
                  ·
                    refine ⟨15768999115265880167567237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168202657229502721787383861 15768999115265880167567237)
                    ·
                      refine ⟨2956687334112352531418857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15768999115265880167567237 2956687334112352531418857)
                      ·
                        rfl

theorem cell23_5758128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_5758128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758128 prefixEnd_5758128 := by exact prefixLift 5758128
  have htrace : WordTrace (prefixWord ++ tailWord_5758128) baseStart_5758128 baseEnd_5758128 := by
    simpa [prefixWord, tailWord_5758128, baseEnd_5758128] using wordTrace_append hprefix tailTrace_5758128
  have hstable : (prefixWord ++ tailWord_5758128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758128).length < 2 ^ (prefixWord ++ tailWord_5758128).sum := by decide
  have hdescent : baseEnd_5758128 < baseStart_5758128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758146 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5758146 : Nat := 118140960795 + 5758146 * 2 ^ 59
def prefixEnd_5758146 : Nat := 4983230072969 + 3 ^ 40 * 5758146 * 2
def baseEnd_5758146 : Nat := 328521841862681495665975

theorem tailTrace_5758146 : CollatzResearch.WordTrace tailWord_5758146 prefixEnd_5758146 328521841862681495665975 := by
  unfold tailWord_5758146
  simp only [CollatzResearch.WordTrace]
  refine ⟨52504209549306982472099573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140011225464818619925598861 52504209549306982472099573)
  ·
    refine ⟨4922269645247529606759335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52504209549306982472099573 4922269645247529606759335)
    ·
      refine ⟨7383404467871294410139003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922269645247529606759335 7383404467871294410139003)
      ·
        refine ⟨11075106701806941615208505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383404467871294410139003 11075106701806941615208505)
        ·
          refine ⟨8306330026355206211406379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11075106701806941615208505 8306330026355206211406379)
          ·
            refine ⟨12459495039532809317109569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306330026355206211406379 12459495039532809317109569)
            ·
              refine ⟨9344621279649606987832177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459495039532809317109569 9344621279649606987832177)
              ·
                refine ⟨7008465959737205240874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9344621279649606987832177 7008465959737205240874133)
                ·
                  refine ⟨328521841862681495665975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7008465959737205240874133 328521841862681495665975)
                  ·
                    rfl

theorem cell23_5758146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5758146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758146 prefixEnd_5758146 := by exact prefixLift 5758146
  have htrace : WordTrace (prefixWord ++ tailWord_5758146) baseStart_5758146 baseEnd_5758146 := by
    simpa [prefixWord, tailWord_5758146, baseEnd_5758146] using wordTrace_append hprefix tailTrace_5758146
  have hstable : (prefixWord ++ tailWord_5758146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758146).length < 2 ^ (prefixWord ++ tailWord_5758146).sum := by decide
  have hdescent : baseEnd_5758146 < baseStart_5758146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758150 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5758150 : Nat := 118140960795 + 5758150 * 2 ^ 59
def prefixEnd_5758150 : Nat := 4983230072969 + 3 ^ 40 * 5758150 * 2
def baseEnd_5758150 : Nat := 985566210228917148447919

theorem tailTrace_5758150 : CollatzResearch.WordTrace tailWord_5758150 prefixEnd_5758150 985566210228917148447919 := by
  unfold tailWord_5758150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563030752787919955360747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140011322726142292381029269 6563030752787919955360747)
  ·
    refine ⟨9844546129181879933041121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563030752787919955360747 9844546129181879933041121)
    ·
      refine ⟨7383409596886409949780841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9844546129181879933041121 7383409596886409949780841)
      ·
        refine ⟨5537557197664807462335631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7383409596886409949780841 5537557197664807462335631)
        ·
          refine ⟨8306335796497211193503447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537557197664807462335631 8306335796497211193503447)
          ·
            refine ⟨12459503694745816790255171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306335796497211193503447 12459503694745816790255171)
            ·
              refine ⟨18689255542118725185382757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12459503694745816790255171 18689255542118725185382757)
              ·
                refine ⟨3504235414147260972259267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18689255542118725185382757 3504235414147260972259267)
                ·
                  refine ⟨5256353121220891458388901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504235414147260972259267 5256353121220891458388901)
                  ·
                    refine ⟨985566210228917148447919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256353121220891458388901 985566210228917148447919)
                    ·
                      rfl

theorem cell23_5758150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5758150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758150 prefixEnd_5758150 := by exact prefixLift 5758150
  have htrace : WordTrace (prefixWord ++ tailWord_5758150) baseStart_5758150 baseEnd_5758150 := by
    simpa [prefixWord, tailWord_5758150, baseEnd_5758150] using wordTrace_append hprefix tailTrace_5758150
  have hstable : (prefixWord ++ tailWord_5758150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758150).length < 2 ^ (prefixWord ++ tailWord_5758150).sum := by decide
  have hdescent : baseEnd_5758150 < baseStart_5758150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758175 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_5758175 : Nat := 118140960795 + 5758175 * 2 ^ 59
def prefixEnd_5758175 : Nat := 4983230072969 + 3 ^ 40 * 5758175 * 2
def baseEnd_5758175 : Nat := 2956711467703113847531141

theorem tailTrace_5758175 : CollatzResearch.WordTrace tailWord_5758175 prefixEnd_5758175 2956711467703113847531141 := by
  unfold tailWord_5758175
  simp only [CollatzResearch.WordTrace]
  refine ⟨210017895914122867841203979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140011930609415245227469319 210017895914122867841203979)
  ·
    refine ⟨315026843871184301761805969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210017895914122867841203979 315026843871184301761805969)
    ·
      refine ⟨236270132903388226321354477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315026843871184301761805969 236270132903388226321354477)
      ·
        refine ⟨88601299838770584870507929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236270132903388226321354477 88601299838770584870507929)
        ·
          refine ⟨66450974879077938652880947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88601299838770584870507929 66450974879077938652880947)
          ·
            refine ⟨99676462318616907979321421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66450974879077938652880947 99676462318616907979321421)
            ·
              refine ⟨37378673369481340492245533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99676462318616907979321421 37378673369481340492245533)
              ·
                refine ⟨14017002513555502684592075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37378673369481340492245533 14017002513555502684592075)
                ·
                  refine ⟨21025503770333254026888113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14017002513555502684592075 21025503770333254026888113)
                  ·
                    refine ⟨15769127827749940520166085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21025503770333254026888113 15769127827749940520166085)
                    ·
                      refine ⟨2956711467703113847531141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15769127827749940520166085 2956711467703113847531141)
                      ·
                        rfl

theorem cell23_5758175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_5758175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758175 prefixEnd_5758175 := by exact prefixLift 5758175
  have htrace : WordTrace (prefixWord ++ tailWord_5758175) baseStart_5758175 baseEnd_5758175 := by
    simpa [prefixWord, tailWord_5758175, baseEnd_5758175] using wordTrace_append hprefix tailTrace_5758175
  have hstable : (prefixWord ++ tailWord_5758175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758175).length < 2 ^ (prefixWord ++ tailWord_5758175).sum := by decide
  have hdescent : baseEnd_5758175 < baseStart_5758175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758183 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5758183 : Nat := 118140960795 + 5758183 * 2 ^ 59
def prefixEnd_5758183 : Nat := 4983230072969 + 3 ^ 40 * 5758183 * 2
def baseEnd_5758183 : Nat := 2956715575548349816231105

theorem tailTrace_5758183 : CollatzResearch.WordTrace tailWord_5758183 prefixEnd_5758183 2956715575548349816231105 := by
  unfold tailWord_5758183
  simp only [CollatzResearch.WordTrace]
  refine ⟨210018187698093885207495203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140012125132062590138330135 210018187698093885207495203)
  ·
    refine ⟨315027281547140827811242805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210018187698093885207495203 315027281547140827811242805)
    ·
      refine ⟨29533807645044452607304013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315027281547140827811242805 29533807645044452607304013)
      ·
        refine ⟨11075177866891669727739005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29533807645044452607304013 11075177866891669727739005)
        ·
          refine ⟨4153191700084376147902127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11075177866891669727739005 4153191700084376147902127)
          ·
            refine ⟨6229787550126564221853191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153191700084376147902127 6229787550126564221853191)
            ·
              refine ⟨9344681325189846332779787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229787550126564221853191 9344681325189846332779787)
              ·
                refine ⟨14017021987784769499169681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344681325189846332779787 14017021987784769499169681)
                ·
                  refine ⟨10512766490838577124377261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14017021987784769499169681 10512766490838577124377261)
                  ·
                    refine ⟨3942287434064466421641473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10512766490838577124377261 3942287434064466421641473)
                    ·
                      refine ⟨2956715575548349816231105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942287434064466421641473 2956715575548349816231105)
                      ·
                        rfl

theorem cell23_5758183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5758183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758183 prefixEnd_5758183 := by exact prefixLift 5758183
  have htrace : WordTrace (prefixWord ++ tailWord_5758183) baseStart_5758183 baseEnd_5758183 := by
    simpa [prefixWord, tailWord_5758183, baseEnd_5758183] using wordTrace_append hprefix tailTrace_5758183
  have hstable : (prefixWord ++ tailWord_5758183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758183).length < 2 ^ (prefixWord ++ tailWord_5758183).sum := by decide
  have hdescent : baseEnd_5758183 < baseStart_5758183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758206 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5758206 : Nat := 118140960795 + 5758206 * 2 ^ 59
def prefixEnd_5758206 : Nat := 4983230072969 + 3 ^ 40 * 5758206 * 2
def baseEnd_5758206 : Nat := 985575795201134408747833

theorem tailTrace_5758206 : CollatzResearch.WordTrace tailWord_5758206 prefixEnd_5758206 985575795201134408747833 := by
  unfold tailWord_5758206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26252378322126320016947809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140012684384673706757054981 26252378322126320016947809)
  ·
    refine ⟨19689283741594740012710857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26252378322126320016947809 19689283741594740012710857)
    ·
      refine ⟨14766962806196055009533143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19689283741594740012710857 14766962806196055009533143)
      ·
        refine ⟨22150444209294082514299715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766962806196055009533143 22150444209294082514299715)
        ·
          refine ⟨33225666313941123771449573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22150444209294082514299715 33225666313941123771449573)
          ·
            refine ⟨6229812433863960707146795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33225666313941123771449573 6229812433863960707146795)
            ·
              refine ⟨9344718650795941060720193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229812433863960707146795 9344718650795941060720193)
              ·
                refine ⟨7008538988096955795540145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9344718650795941060720193 7008538988096955795540145)
                ·
                  refine ⟨5256404241072716846655109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7008538988096955795540145 5256404241072716846655109)
                  ·
                    refine ⟨985575795201134408747833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256404241072716846655109 985575795201134408747833)
                    ·
                      rfl

theorem cell23_5758206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5758206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758206 prefixEnd_5758206 := by exact prefixLift 5758206
  have htrace : WordTrace (prefixWord ++ tailWord_5758206) baseStart_5758206 baseEnd_5758206 := by
    simpa [prefixWord, tailWord_5758206, baseEnd_5758206] using wordTrace_append hprefix tailTrace_5758206
  have hstable : (prefixWord ++ tailWord_5758206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758206).length < 2 ^ (prefixWord ++ tailWord_5758206).sum := by decide
  have hdescent : baseEnd_5758206 < baseStart_5758206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758252 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_5758252 : Nat := 118140960795 + 5758252 * 2 ^ 59
def prefixEnd_5758252 : Nat := 4983230072969 + 3 ^ 40 * 5758252 * 2
def baseEnd_5758252 : Nat := 2956751005713510046268287

theorem tailTrace_5758252 : CollatzResearch.WordTrace tailWord_5758252 prefixEnd_5758252 2956751005713510046268287 := by
  unfold tailWord_5758252
  simp only [CollatzResearch.WordTrace]
  refine ⟨105010352167421954995878505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140013802889895939994504673 105010352167421954995878505)
  ·
    refine ⟨78757764125566466246908879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105010352167421954995878505 78757764125566466246908879)
    ·
      refine ⟨118136646188349699370363319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78757764125566466246908879 118136646188349699370363319)
      ·
        refine ⟨177204969282524549055544979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118136646188349699370363319 177204969282524549055544979)
        ·
          refine ⟨265807453923786823583317469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177204969282524549055544979 265807453923786823583317469)
          ·
            refine ⟨99677795221420058843744051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265807453923786823583317469 99677795221420058843744051)
            ·
              refine ⟨149516692832130088265616077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99677795221420058843744051 149516692832130088265616077)
              ·
                refine ⟨56068759812048783099606029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149516692832130088265616077 56068759812048783099606029)
                ·
                  refine ⟨21025784929518293662352261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56068759812048783099606029 21025784929518293662352261)
                  ·
                    refine ⟨3942334674284680061691049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21025784929518293662352261 3942334674284680061691049)
                    ·
                      refine ⟨2956751005713510046268287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942334674284680061691049 2956751005713510046268287)
                      ·
                        rfl

theorem cell23_5758252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_5758252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758252 prefixEnd_5758252 := by exact prefixLift 5758252
  have htrace : WordTrace (prefixWord ++ tailWord_5758252) baseStart_5758252 baseEnd_5758252 := by
    simpa [prefixWord, tailWord_5758252, baseEnd_5758252] using wordTrace_append hprefix tailTrace_5758252
  have hstable : (prefixWord ++ tailWord_5758252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758252).length < 2 ^ (prefixWord ++ tailWord_5758252).sum := by decide
  have hdescent : baseEnd_5758252 < baseStart_5758252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758255 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_5758255 : Nat := 118140960795 + 5758255 * 2 ^ 59
def prefixEnd_5758255 : Nat := 4983230072969 + 3 ^ 40 * 5758255 * 2
def baseEnd_5758255 : Nat := 2956752546155473534530773

theorem tailTrace_5758255 : CollatzResearch.WordTrace tailWord_5758255 prefixEnd_5758255 2956752546155473534530773 := by
  unfold tailWord_5758255
  simp only [CollatzResearch.WordTrace]
  refine ⟨210020813753833041504116219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140013875835888694336077479 210020813753833041504116219)
  ·
    refine ⟨315031220630749562256174329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210020813753833041504116219 315031220630749562256174329)
    ·
      refine ⟨236273415473062171692130747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315031220630749562256174329 236273415473062171692130747)
      ·
        refine ⟨354410123209593257538196121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236273415473062171692130747 354410123209593257538196121)
        ·
          refine ⟨265807592407194943153647091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354410123209593257538196121 265807592407194943153647091)
          ·
            refine ⟨398711388610792414730470637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265807592407194943153647091 398711388610792414730470637)
            ·
              refine ⟨149516770729047155523926489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398711388610792414730470637 149516770729047155523926489)
              ·
                refine ⟨112137578046785366642944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149516770729047155523926489 112137578046785366642944867)
                ·
                  refine ⟨168206367070178049964417301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112137578046785366642944867 168206367070178049964417301)
                  ·
                    refine ⟨7884673456414596092082061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168206367070178049964417301 7884673456414596092082061)
                    ·
                      refine ⟨2956752546155473534530773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7884673456414596092082061 2956752546155473534530773)
                      ·
                        rfl

theorem cell23_5758255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_5758255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758255 prefixEnd_5758255 := by exact prefixLift 5758255
  have htrace : WordTrace (prefixWord ++ tailWord_5758255) baseStart_5758255 baseEnd_5758255 := by
    simpa [prefixWord, tailWord_5758255, baseEnd_5758255] using wordTrace_append hprefix tailTrace_5758255
  have hstable : (prefixWord ++ tailWord_5758255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758255).length < 2 ^ (prefixWord ++ tailWord_5758255).sum := by decide
  have hdescent : baseEnd_5758255 < baseStart_5758255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758286 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_5758286 : Nat := 118140960795 + 5758286 * 2 ^ 59
def prefixEnd_5758286 : Nat := 4983230072969 + 3 ^ 40 * 5758286 * 2
def baseEnd_5758286 : Nat := 2956768464055762913243131

theorem tailTrace_5758286 : CollatzResearch.WordTrace tailWord_5758286 prefixEnd_5758286 2956768464055762913243131 := by
  unfold tailWord_5758286
  simp only [CollatzResearch.WordTrace]
  refine ⟨26252743052090091724811839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140014629611147155865663141 26252743052090091724811839)
  ·
    refine ⟨39379114578135137587217759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26252743052090091724811839 39379114578135137587217759)
    ·
      refine ⟨59068671867202706380826639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39379114578135137587217759 59068671867202706380826639)
      ·
        refine ⟨88603007800804059571239959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59068671867202706380826639 88603007800804059571239959)
        ·
          refine ⟨132904511701206089356859939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88603007800804059571239959 132904511701206089356859939)
          ·
            refine ⟨199356767551809134035289909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132904511701206089356859939 199356767551809134035289909)
            ·
              refine ⟨18689696957982106315808429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199356767551809134035289909 18689696957982106315808429)
              ·
                refine ⟨7008636359243289868428161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18689696957982106315808429 7008636359243289868428161)
                ·
                  refine ⟨5256477269432467401321121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7008636359243289868428161 5256477269432467401321121)
                  ·
                    refine ⟨3942357952074350550990841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5256477269432467401321121 3942357952074350550990841)
                    ·
                      refine ⟨2956768464055762913243131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942357952074350550990841 2956768464055762913243131)
                      ·
                        rfl

theorem cell23_5758286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_5758286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758286 prefixEnd_5758286 := by exact prefixLift 5758286
  have htrace : WordTrace (prefixWord ++ tailWord_5758286) baseStart_5758286 baseEnd_5758286 := by
    simpa [prefixWord, tailWord_5758286, baseEnd_5758286] using wordTrace_append hprefix tailTrace_5758286
  have hstable : (prefixWord ++ tailWord_5758286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758286).length < 2 ^ (prefixWord ++ tailWord_5758286).sum := by decide
  have hdescent : baseEnd_5758286 < baseStart_5758286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758305 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_5758305 : Nat := 118140960795 + 5758305 * 2 ^ 59
def prefixEnd_5758305 : Nat := 4983230072969 + 3 ^ 40 * 5758305 * 2
def baseEnd_5758305 : Nat := 985592740062732779635181

theorem tailTrace_5758305 : CollatzResearch.WordTrace tailWord_5758305 prefixEnd_5758305 985592740062732779635181 := by
  unfold tailWord_5758305
  simp only [CollatzResearch.WordTrace]
  refine ⟨210022637403651900043436369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140015091602434600028957579 210022637403651900043436369)
  ·
    refine ⟨157516978052738925032577277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210022637403651900043436369 157516978052738925032577277)
    ·
      refine ⟨59068866769777096887216479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157516978052738925032577277 59068866769777096887216479)
      ·
        refine ⟨88603300154665645330824719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59068866769777096887216479 88603300154665645330824719)
        ·
          refine ⟨132904950231998467996237079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88603300154665645330824719 132904950231998467996237079)
          ·
            refine ⟨199357425347997701994355619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132904950231998467996237079 199357425347997701994355619)
            ·
              refine ⟨299036138021996552991533429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199357425347997701994355619 299036138021996552991533429)
              ·
                refine ⟨28034637939562176842956259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299036138021996552991533429 28034637939562176842956259)
                ·
                  refine ⟨42051956909343265264434389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28034637939562176842956259 42051956909343265264434389)
                  ·
                    refine ⟨985592740062732779635181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42051956909343265264434389 985592740062732779635181)
                    ·
                      rfl

theorem cell23_5758305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_5758305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758305 prefixEnd_5758305 := by exact prefixLift 5758305
  have htrace : WordTrace (prefixWord ++ tailWord_5758305) baseStart_5758305 baseEnd_5758305 := by
    simpa [prefixWord, tailWord_5758305, baseEnd_5758305] using wordTrace_append hprefix tailTrace_5758305
  have hstable : (prefixWord ++ tailWord_5758305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758305).length < 2 ^ (prefixWord ++ tailWord_5758305).sum := by decide
  have hdescent : baseEnd_5758305 < baseStart_5758305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758322 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_5758322 : Nat := 118140960795 + 5758322 * 2 ^ 59
def prefixEnd_5758322 : Nat := 4983230072969 + 3 ^ 40 * 5758322 * 2
def baseEnd_5758322 : Nat := 985595649786441590797655

theorem tailTrace_5758322 : CollatzResearch.WordTrace tailWord_5758322 prefixEnd_5758322 985595649786441590797655 := by
  unfold tailWord_5758322
  simp only [CollatzResearch.WordTrace]
  refine ⟨52505814361147577986701305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140015504963060207964536813 52505814361147577986701305)
  ·
    refine ⟨39379360770860683490025979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52505814361147577986701305 39379360770860683490025979)
    ·
      refine ⟨59069041156291025235038969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39379360770860683490025979 59069041156291025235038969)
      ·
        refine ⟨44301780867218268926279227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59069041156291025235038969 44301780867218268926279227)
        ·
          refine ⟨66452671300827403389418841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44301780867218268926279227 66452671300827403389418841)
          ·
            refine ⟨49839503475620552542064131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66452671300827403389418841 49839503475620552542064131)
            ·
              refine ⟨74759255213430828813096197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49839503475620552542064131 74759255213430828813096197)
              ·
                refine ⟨14017360352518280402455537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74759255213430828813096197 14017360352518280402455537)
                ·
                  refine ⟨10513020264388710301841653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14017360352518280402455537 10513020264388710301841653)
                  ·
                    refine ⟨985595649786441590797655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10513020264388710301841653 985595649786441590797655)
                    ·
                      rfl

theorem cell23_5758322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_5758322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758322 prefixEnd_5758322 := by exact prefixLift 5758322
  have htrace : WordTrace (prefixWord ++ tailWord_5758322) baseStart_5758322 baseEnd_5758322 := by
    simpa [prefixWord, tailWord_5758322, baseEnd_5758322] using wordTrace_append hprefix tailTrace_5758322
  have hstable : (prefixWord ++ tailWord_5758322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758322).length < 2 ^ (prefixWord ++ tailWord_5758322).sum := by decide
  have hdescent : baseEnd_5758322 < baseStart_5758322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758355 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_5758355 : Nat := 118140960795 + 5758355 * 2 ^ 59
def prefixEnd_5758355 : Nat := 4983230072969 + 3 ^ 40 * 5758355 * 2
def baseEnd_5758355 : Nat := 2956803894220923143280313

theorem tailTrace_5758355 : CollatzResearch.WordTrace tailWord_5758355 prefixEnd_5758355 2956803894220923143280313 := by
  unfold tailWord_5758355
  simp only [CollatzResearch.WordTrace]
  refine ⟨210024461053470758582756519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140016307368980505721837679 210024461053470758582756519)
  ·
    refine ⟨315036691580206137874134779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210024461053470758582756519 315036691580206137874134779)
    ·
      refine ⟨472555037370309206811202169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315036691580206137874134779 472555037370309206811202169)
      ·
        refine ⟨354416278027731905108401627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472555037370309206811202169 354416278027731905108401627)
        ·
          refine ⟨531624417041597857662602441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354416278027731905108401627 531624417041597857662602441)
          ·
            refine ⟨398718312781198393246951831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531624417041597857662602441 398718312781198393246951831)
            ·
              refine ⟨598077469171797589870427747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398718312781198393246951831 598077469171797589870427747)
              ·
                refine ⟨897116203757696384805641621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598077469171797589870427747 897116203757696384805641621)
                ·
                  refine ⟨42052322051142018037764451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 897116203757696384805641621 42052322051142018037764451)
                  ·
                    refine ⟨63078483076713027056646677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42052322051142018037764451 63078483076713027056646677)
                    ·
                      refine ⟨2956803894220923143280313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63078483076713027056646677 2956803894220923143280313)
                      ·
                        rfl

theorem cell23_5758355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_5758355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758355 prefixEnd_5758355 := by exact prefixLift 5758355
  have htrace : WordTrace (prefixWord ++ tailWord_5758355) baseStart_5758355 baseEnd_5758355 := by
    simpa [prefixWord, tailWord_5758355, baseEnd_5758355] using wordTrace_append hprefix tailTrace_5758355
  have hstable : (prefixWord ++ tailWord_5758355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758355).length < 2 ^ (prefixWord ++ tailWord_5758355).sum := by decide
  have hdescent : baseEnd_5758355 < baseStart_5758355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758356 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5758356 : Nat := 118140960795 + 5758356 * 2 ^ 59
def prefixEnd_5758356 : Nat := 4983230072969 + 3 ^ 40 * 5758356 * 2
def baseEnd_5758356 : Nat := 985601469233859213122603

theorem tailTrace_5758356 : CollatzResearch.WordTrace tailWord_5758356 prefixEnd_5758356 985601469233859213122603 := by
  unfold tailWord_5758356
  simp only [CollatzResearch.WordTrace]
  refine ⟨105012248763233567876771461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140016331684311423835695281 105012248763233567876771461)
  ·
    refine ⟨19689796643106293976894649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105012248763233567876771461 19689796643106293976894649)
    ·
      refine ⟨14767347482329720482670987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19689796643106293976894649 14767347482329720482670987)
      ·
        refine ⟨22151021223494580724006481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767347482329720482670987 22151021223494580724006481)
        ·
          refine ⟨16613265917620935543004861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22151021223494580724006481 16613265917620935543004861)
          ·
            refine ⟨6229974719107850828626823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16613265917620935543004861 6229974719107850828626823)
            ·
              refine ⟨9344962078661776242940235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229974719107850828626823 9344962078661776242940235)
              ·
                refine ⟨14017443117992664364410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344962078661776242940235 14017443117992664364410353)
                ·
                  refine ⟨10513082338494498273307765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14017443117992664364410353 10513082338494498273307765)
                  ·
                    refine ⟨985601469233859213122603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10513082338494498273307765 985601469233859213122603)
                    ·
                      rfl

theorem cell23_5758356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5758356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758356 prefixEnd_5758356 := by exact prefixLift 5758356
  have htrace : WordTrace (prefixWord ++ tailWord_5758356) baseStart_5758356 baseEnd_5758356 := by
    simpa [prefixWord, tailWord_5758356, baseEnd_5758356] using wordTrace_append hprefix tailTrace_5758356
  have hstable : (prefixWord ++ tailWord_5758356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758356).length < 2 ^ (prefixWord ++ tailWord_5758356).sum := by decide
  have hdescent : baseEnd_5758356 < baseStart_5758356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758420 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_5758420 : Nat := 118140960795 + 5758420 * 2 ^ 59
def prefixEnd_5758420 : Nat := 4983230072969 + 3 ^ 40 * 5758420 * 2
def baseEnd_5758420 : Nat := 985612423487821796322505

theorem tailTrace_5758420 : CollatzResearch.WordTrace tailWord_5758420 prefixEnd_5758420 985612423487821796322505 := by
  unfold tailWord_5758420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105013415899117637341936357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140017887865490183122581809 105013415899117637341936357)
  ·
    refine ⟨19690015481084557001613067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105013415899117637341936357 19690015481084557001613067)
    ·
      refine ⟨29535023221626835502419601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19690015481084557001613067 29535023221626835502419601)
      ·
        refine ⟨22151267416220126626814701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29535023221626835502419601 22151267416220126626814701)
        ·
          refine ⟨8306725281082547485055513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22151267416220126626814701 8306725281082547485055513)
          ·
            refine ⟨6230043960811910613791635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8306725281082547485055513 6230043960811910613791635)
            ·
              refine ⟨9345065941217865920687453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230043960811910613791635 9345065941217865920687453)
              ·
                refine ⟨3504399727956699720257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9345065941217865920687453 3504399727956699720257795)
                ·
                  refine ⟨5256599591935049580386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504399727956699720257795 5256599591935049580386693)
                  ·
                    refine ⟨985612423487821796322505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256599591935049580386693 985612423487821796322505)
                    ·
                      rfl

theorem cell23_5758420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_5758420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758420 prefixEnd_5758420 := by exact prefixLift 5758420
  have htrace : WordTrace (prefixWord ++ tailWord_5758420) baseStart_5758420 baseEnd_5758420 := by
    simpa [prefixWord, tailWord_5758420, baseEnd_5758420] using wordTrace_append hprefix tailTrace_5758420
  have hstable : (prefixWord ++ tailWord_5758420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758420).length < 2 ^ (prefixWord ++ tailWord_5758420).sum := by decide
  have hdescent : baseEnd_5758420 < baseStart_5758420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758459 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 2, 4]
def baseStart_5758459 : Nat := 118140960795 + 5758459 * 2 ^ 59
def prefixEnd_5758459 : Nat := 4983230072969 + 3 ^ 40 * 5758459 * 2
def baseEnd_5758459 : Nat := 985619098736330245459945

theorem tailTrace_5758459 : CollatzResearch.WordTrace tailWord_5758459 prefixEnd_5758459 985619098736330245459945 := by
  unfold tailWord_5758459
  simp only [CollatzResearch.WordTrace]
  refine ⟨210028254245093984344542431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140018836163395989563028287 210028254245093984344542431)
  ·
    refine ⟨315042381367640976516813647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210028254245093984344542431 315042381367640976516813647)
    ·
      refine ⟨472563572051461464775220471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315042381367640976516813647 472563572051461464775220471)
      ·
        refine ⟨708845358077192197162830707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472563572051461464775220471 708845358077192197162830707)
        ·
          refine ⟨1063268037115788295744246061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708845358077192197162830707 1063268037115788295744246061)
          ·
            refine ⟨398725513918420610904092273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1063268037115788295744246061 398725513918420610904092273)
            ·
              refine ⟨299044135438815458178069205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398725513918420610904092273 299044135438815458178069205)
              ·
                refine ⟨7008846924347237301048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 299044135438815458178069205 7008846924347237301048497)
                ·
                  refine ⟨5256635193260427975786373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7008846924347237301048497 5256635193260427975786373)
                  ·
                    refine ⟨985619098736330245459945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256635193260427975786373 985619098736330245459945)
                    ·
                      rfl

theorem cell23_5758459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 4].length) (baseStart_5758459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758459 prefixEnd_5758459 := by exact prefixLift 5758459
  have htrace : WordTrace (prefixWord ++ tailWord_5758459) baseStart_5758459 baseEnd_5758459 := by
    simpa [prefixWord, tailWord_5758459, baseEnd_5758459] using wordTrace_append hprefix tailTrace_5758459
  have hstable : (prefixWord ++ tailWord_5758459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758459).length < 2 ^ (prefixWord ++ tailWord_5758459).sum := by decide
  have hdescent : baseEnd_5758459 < baseStart_5758459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758472 : List Nat := [2, 1, 3, 2, 1, 1, 4, 9]
def baseStart_5758472 : Nat := 118140960795 + 5758472 * 2 ^ 59
def prefixEnd_5758472 : Nat := 4983230072969 + 3 ^ 40 * 5758472 * 2
def baseEnd_5758472 : Nat := 109513480424351821685825

theorem tailTrace_5758472 : CollatzResearch.WordTrace tailWord_5758472 prefixEnd_5758472 109513480424351821685825 := by
  unfold tailWord_5758472
  simp only [CollatzResearch.WordTrace]
  refine ⟨105014364197023443782382835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140019152262697925043177113 105014364197023443782382835)
  ·
    refine ⟨157521546295535165673574253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105014364197023443782382835 157521546295535165673574253)
    ·
      refine ⟨59070579860825687127590345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157521546295535165673574253 59070579860825687127590345)
      ·
        refine ⟨44302934895619265345692759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59070579860825687127590345 44302934895619265345692759)
        ·
          refine ⟨66454402343428898018539139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44302934895619265345692759 66454402343428898018539139)
          ·
            refine ⟨99681603515143347027808709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66454402343428898018539139 99681603515143347027808709)
            ·
              refine ⟨18690300659089377567714133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99681603515143347027808709 18690300659089377567714133)
              ·
                refine ⟨109513480424351821685825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18690300659089377567714133 109513480424351821685825)
                ·
                  rfl

theorem cell23_5758472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 9].length) (baseStart_5758472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758472 prefixEnd_5758472 := by exact prefixLift 5758472
  have htrace : WordTrace (prefixWord ++ tailWord_5758472) baseStart_5758472 baseEnd_5758472 := by
    simpa [prefixWord, tailWord_5758472, baseEnd_5758472] using wordTrace_append hprefix tailTrace_5758472
  have hstable : (prefixWord ++ tailWord_5758472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758472).length < 2 ^ (prefixWord ++ tailWord_5758472).sum := by decide
  have hdescent : baseEnd_5758472 < baseStart_5758472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758512 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_5758512 : Nat := 118140960795 + 5758512 * 2 ^ 59
def prefixEnd_5758512 : Nat := 4983230072969 + 3 ^ 40 * 5758512 * 2
def baseEnd_5758512 : Nat := 2956884510683679029017091

theorem tailTrace_5758512 : CollatzResearch.WordTrace tailWord_5758512 prefixEnd_5758512 2956884510683679029017091 := by
  unfold tailWord_5758512
  simp only [CollatzResearch.WordTrace]
  refine ⟨105015093656950987198110895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140020124875934649597481193 105015093656950987198110895)
  ·
    refine ⟨157522640485426480797166343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105015093656950987198110895 157522640485426480797166343)
    ·
      refine ⟨236283960728139721195749515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157522640485426480797166343 236283960728139721195749515)
      ·
        refine ⟨354425941092209581793624273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236283960728139721195749515 354425941092209581793624273)
        ·
          refine ⟨265819455819157186345218205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354425941092209581793624273 265819455819157186345218205)
          ·
            refine ⟨99682295932183944879456827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265819455819157186345218205 99682295932183944879456827)
            ·
              refine ⟨149523443898275917319185241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99682295932183944879456827 149523443898275917319185241)
              ·
                refine ⟨112142582923706937989388931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149523443898275917319185241 112142582923706937989388931)
                ·
                  refine ⟨168213874385560406984083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112142582923706937989388931 168213874385560406984083397)
                  ·
                    refine ⟨31540101447292576309515637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168213874385560406984083397 31540101447292576309515637)
                    ·
                      refine ⟨2956884510683679029017091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31540101447292576309515637 2956884510683679029017091)
                      ·
                        rfl

theorem cell23_5758512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_5758512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758512 prefixEnd_5758512 := by exact prefixLift 5758512
  have htrace : WordTrace (prefixWord ++ tailWord_5758512) baseStart_5758512 baseEnd_5758512 := by
    simpa [prefixWord, tailWord_5758512, baseEnd_5758512] using wordTrace_append hprefix tailTrace_5758512
  have hstable : (prefixWord ++ tailWord_5758512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758512).length < 2 ^ (prefixWord ++ tailWord_5758512).sum := by decide
  have hdescent : baseEnd_5758512 < baseStart_5758512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758529 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5758529 : Nat := 118140960795 + 5758529 * 2 ^ 59
def prefixEnd_5758529 : Nat := 4983230072969 + 3 ^ 40 * 5758529 * 2
def baseEnd_5758529 : Nat := 2956893239854805462504513

theorem tailTrace_5758529 : CollatzResearch.WordTrace tailWord_5758529 prefixEnd_5758529 2956893239854805462504513 := by
  unfold tailWord_5758529
  simp only [CollatzResearch.WordTrace]
  refine ⟨210030807354840386299590641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140020538236560257533060427 210030807354840386299590641)
  ·
    refine ⟨157523105516130289724692981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210030807354840386299590641 157523105516130289724692981)
    ·
      refine ⟨14767791142137214661689967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157523105516130289724692981 14767791142137214661689967)
      ·
        refine ⟨22151686713205821992534951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767791142137214661689967 22151686713205821992534951)
        ·
          refine ⟨33227530069808732988802427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22151686713205821992534951 33227530069808732988802427)
          ·
            refine ⟨49841295104713099483203641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33227530069808732988802427 49841295104713099483203641)
            ·
              refine ⟨37380971328534824612402731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49841295104713099483203641 37380971328534824612402731)
              ·
                refine ⟨56071456992802236918604097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37380971328534824612402731 56071456992802236918604097)
                ·
                  refine ⟨42053592744601677688953073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56071456992802236918604097 42053592744601677688953073)
                  ·
                    refine ⟨31540194558451258266714805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42053592744601677688953073 31540194558451258266714805)
                    ·
                      refine ⟨2956893239854805462504513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31540194558451258266714805 2956893239854805462504513)
                      ·
                        rfl

theorem cell23_5758529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5758529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758529 prefixEnd_5758529 := by exact prefixLift 5758529
  have htrace : WordTrace (prefixWord ++ tailWord_5758529) baseStart_5758529 baseEnd_5758529 := by
    simpa [prefixWord, tailWord_5758529, baseEnd_5758529] using wordTrace_append hprefix tailTrace_5758529
  have hstable : (prefixWord ++ tailWord_5758529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758529).length < 2 ^ (prefixWord ++ tailWord_5758529).sum := by decide
  have hdescent : baseEnd_5758529 < baseStart_5758529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758534 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5758534 : Nat := 118140960795 + 5758534 * 2 ^ 59
def prefixEnd_5758534 : Nat := 4983230072969 + 3 ^ 40 * 5758534 * 2
def baseEnd_5758534 : Nat := 2956895807258077942941991

theorem tailTrace_5758534 : CollatzResearch.WordTrace tailWord_5758534 prefixEnd_5758534 2956895807258077942941991 := by
  unfold tailWord_5758534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563468428744446004797583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140020659813214848102348437 6563468428744446004797583)
  ·
    refine ⟨9845202643116669007196375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563468428744446004797583 9845202643116669007196375)
    ·
      refine ⟨14767803964675003510794563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845202643116669007196375 14767803964675003510794563)
      ·
        refine ⟨22151705947012505266191845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767803964675003510794563 22151705947012505266191845)
        ·
          refine ⟨4153444865064844737410971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22151705947012505266191845 4153444865064844737410971)
          ·
            refine ⟨6230167297597267106116457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153444865064844737410971 6230167297597267106116457)
            ·
              refine ⟨4672625473197950329587343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230167297597267106116457 4672625473197950329587343)
              ·
                refine ⟨7008938209796925494381015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672625473197950329587343 7008938209796925494381015)
                ·
                  refine ⟨10513407314695388241571523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7008938209796925494381015 10513407314695388241571523)
                  ·
                    refine ⟨15770110972043082362357285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10513407314695388241571523 15770110972043082362357285)
                    ·
                      refine ⟨2956895807258077942941991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15770110972043082362357285 2956895807258077942941991)
                      ·
                        rfl

theorem cell23_5758534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5758534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758534 prefixEnd_5758534 := by exact prefixLift 5758534
  have htrace : WordTrace (prefixWord ++ tailWord_5758534) baseStart_5758534 baseEnd_5758534 := by
    simpa [prefixWord, tailWord_5758534, baseEnd_5758534] using wordTrace_append hprefix tailTrace_5758534
  have hstable : (prefixWord ++ tailWord_5758534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758534).length < 2 ^ (prefixWord ++ tailWord_5758534).sum := by decide
  have hdescent : baseEnd_5758534 < baseStart_5758534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758569 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_5758569 : Nat := 118140960795 + 5758569 * 2 ^ 59
def prefixEnd_5758569 : Nat := 4983230072969 + 3 ^ 40 * 5758569 * 2
def baseEnd_5758569 : Nat := 2956913779080985306004329

theorem tailTrace_5758569 : CollatzResearch.WordTrace tailWord_5758569 prefixEnd_5758569 2956913779080985306004329 := by
  unfold tailWord_5758569
  simp only [CollatzResearch.WordTrace]
  refine ⟨210032266274695473131046761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140021510849796982087364507 210032266274695473131046761)
  ·
    refine ⟨157524199706021604848285071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210032266274695473131046761 157524199706021604848285071)
    ·
      refine ⟨236286299559032407272427607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157524199706021604848285071 236286299559032407272427607)
      ·
        refine ⟨354429449338548610908641411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236286299559032407272427607 354429449338548610908641411)
        ·
          refine ⟨531644174007822916362962117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354429449338548610908641411 531644174007822916362962117)
          ·
            refine ⟨99683282626466796818055397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 531644174007822916362962117 99683282626466796818055397)
            ·
              refine ⟨18690615492462524403385387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99683282626466796818055397 18690615492462524403385387)
              ·
                refine ⟨28035923238693786605078081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18690615492462524403385387 28035923238693786605078081)
                ·
                  refine ⟨21026942429020339953808561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28035923238693786605078081 21026942429020339953808561)
                  ·
                    refine ⟨15770206821765254965356421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21026942429020339953808561 15770206821765254965356421)
                    ·
                      refine ⟨2956913779080985306004329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15770206821765254965356421 2956913779080985306004329)
                      ·
                        rfl

theorem cell23_5758569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_5758569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758569 prefixEnd_5758569 := by exact prefixLift 5758569
  have htrace : WordTrace (prefixWord ++ tailWord_5758569) baseStart_5758569 baseEnd_5758569 := by
    simpa [prefixWord, tailWord_5758569, baseEnd_5758569] using wordTrace_append hprefix tailTrace_5758569
  have hstable : (prefixWord ++ tailWord_5758569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758569).length < 2 ^ (prefixWord ++ tailWord_5758569).sum := by decide
  have hdescent : baseEnd_5758569 < baseStart_5758569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758629 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_5758629 : Nat := 118140960795 + 5758629 * 2 ^ 59
def prefixEnd_5758629 : Nat := 4983230072969 + 3 ^ 40 * 5758629 * 2
def baseEnd_5758629 : Nat := 2956944587920255071254053

theorem tailTrace_5758629 : CollatzResearch.WordTrace tailWord_5758629 prefixEnd_5758629 2956944587920255071254053 := by
  unfold tailWord_5758629
  simp only [CollatzResearch.WordTrace]
  refine ⟨210034454654478103378230941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140022969769652068918820627 210034454654478103378230941)
  ·
    refine ⟨78762920495429288766836603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210034454654478103378230941 78762920495429288766836603)
    ·
      refine ⟨118144380743143933150254905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78762920495429288766836603 118144380743143933150254905)
      ·
        refine ⟨88608285557357949862691179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118144380743143933150254905 88608285557357949862691179)
        ·
          refine ⟨132912428336036924794036769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88608285557357949862691179 132912428336036924794036769)
          ·
            refine ⟨99684321252027693595527577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132912428336036924794036769 99684321252027693595527577)
            ·
              refine ⟨74763240939020770196645683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99684321252027693595527577 74763240939020770196645683)
              ·
                refine ⟨112144861408531155294968525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74763240939020770196645683 112144861408531155294968525)
                ·
                  refine ⟨42054323028199183235613197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112144861408531155294968525 42054323028199183235613197)
                  ·
                    refine ⟨15770371135574693713354949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42054323028199183235613197 15770371135574693713354949)
                    ·
                      refine ⟨2956944587920255071254053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15770371135574693713354949 2956944587920255071254053)
                      ·
                        rfl

theorem cell23_5758629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_5758629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758629 prefixEnd_5758629 := by exact prefixLift 5758629
  have htrace : WordTrace (prefixWord ++ tailWord_5758629) baseStart_5758629 baseEnd_5758629 := by
    simpa [prefixWord, tailWord_5758629, baseEnd_5758629] using wordTrace_append hprefix tailTrace_5758629
  have hstable : (prefixWord ++ tailWord_5758629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758629).length < 2 ^ (prefixWord ++ tailWord_5758629).sum := by decide
  have hdescent : baseEnd_5758629 < baseStart_5758629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758723 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 2, 3, 2]
def baseStart_5758723 : Nat := 118140960795 + 5758723 * 2 ^ 59
def prefixEnd_5758723 : Nat := 4983230072969 + 3 ^ 40 * 5758723 * 2
def baseEnd_5758723 : Nat := 2956992855101777703478621

theorem tailTrace_5758723 : CollatzResearch.WordTrace tailWord_5758723 prefixEnd_5758723 2956992855101777703478621 := by
  unfold tailWord_5758723
  simp only [CollatzResearch.WordTrace]
  refine ⟨210037883116137557432152823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140025255410758371621435215 210037883116137557432152823)
  ·
    refine ⟨315056824674206336148229235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210037883116137557432152823 315056824674206336148229235)
    ·
      refine ⟨472585237011309504222343853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315056824674206336148229235 472585237011309504222343853)
      ·
        refine ⟨177219463879241064083378945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472585237011309504222343853 177219463879241064083378945)
        ·
          refine ⟨132914597909430798062534209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177219463879241064083378945 132914597909430798062534209)
          ·
            refine ⟨99685948432073098546900657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132914597909430798062534209 99685948432073098546900657)
            ·
              refine ⟨74764461324054823910175493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99685948432073098546900657 74764461324054823910175493)
              ·
                refine ⟨14018336498260279483157905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74764461324054823910175493 14018336498260279483157905)
                ·
                  refine ⟨10513752373695209612368429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14018336498260279483157905 10513752373695209612368429)
                  ·
                    refine ⟨3942657140135703604638161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10513752373695209612368429 3942657140135703604638161)
                    ·
                      refine ⟨2956992855101777703478621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942657140135703604638161 2956992855101777703478621)
                      ·
                        rfl

theorem cell23_5758723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_5758723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758723 prefixEnd_5758723 := by exact prefixLift 5758723
  have htrace : WordTrace (prefixWord ++ tailWord_5758723) baseStart_5758723 baseEnd_5758723 := by
    simpa [prefixWord, tailWord_5758723, baseEnd_5758723] using wordTrace_append hprefix tailTrace_5758723
  have hstable : (prefixWord ++ tailWord_5758723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758723).length < 2 ^ (prefixWord ++ tailWord_5758723).sum := by decide
  have hdescent : baseEnd_5758723 < baseStart_5758723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758730 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_5758730 : Nat := 118140960795 + 5758730 * 2 ^ 59
def prefixEnd_5758730 : Nat := 4983230072969 + 3 ^ 40 * 5758730 * 2
def baseEnd_5758730 : Nat := 2956996449466359176091089

theorem tailTrace_5758730 : CollatzResearch.WordTrace tailWord_5758730 prefixEnd_5758730 2956996449466359176091089 := by
  unfold tailWord_5758730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52509534606778049406914411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140025425618074798418438429 52509534606778049406914411)
  ·
    refine ⟨78764301910167074110371617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52509534606778049406914411 78764301910167074110371617)
    ·
      refine ⟨59073226432625305582778713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78764301910167074110371617 59073226432625305582778713)
      ·
        refine ⟨44304919824468979187084035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59073226432625305582778713 44304919824468979187084035)
        ·
          refine ⟨66457379736703468780626053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44304919824468979187084035 66457379736703468780626053)
          ·
            refine ⟨12460758700631900396367385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66457379736703468780626053 12460758700631900396367385)
            ·
              refine ⟨9345569025473925297275539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12460758700631900396367385 9345569025473925297275539)
              ·
                refine ⟨14018353538210887945913309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345569025473925297275539 14018353538210887945913309)
                ·
                  refine ⟨5256882576829082979717491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14018353538210887945913309 5256882576829082979717491)
                  ·
                    refine ⟨7885323865243624469576237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256882576829082979717491 7885323865243624469576237)
                    ·
                      refine ⟨2956996449466359176091089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885323865243624469576237 2956996449466359176091089)
                      ·
                        rfl

theorem cell23_5758730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_5758730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758730 prefixEnd_5758730 := by exact prefixLift 5758730
  have htrace : WordTrace (prefixWord ++ tailWord_5758730) baseStart_5758730 baseEnd_5758730 := by
    simpa [prefixWord, tailWord_5758730, baseEnd_5758730] using wordTrace_append hprefix tailTrace_5758730
  have hstable : (prefixWord ++ tailWord_5758730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758730).length < 2 ^ (prefixWord ++ tailWord_5758730).sum := by decide
  have hdescent : baseEnd_5758730 < baseStart_5758730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758753 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5758753 : Nat := 118140960795 + 5758753 * 2 ^ 59
def prefixEnd_5758753 : Nat := 4983230072969 + 3 ^ 40 * 5758753 * 2
def baseEnd_5758753 : Nat := 2957008259521412586103483

theorem tailTrace_5758753 : CollatzResearch.WordTrace tailWord_5758753 prefixEnd_5758753 2957008259521412586103483 := by
  unfold tailWord_5758753
  simp only [CollatzResearch.WordTrace]
  refine ⟨210038977306028872555744913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140025984870685915037163275 210038977306028872555744913)
  ·
    refine ⟨157529232979521654416808685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210038977306028872555744913 157529232979521654416808685)
    ·
      refine ⟨59073462367320620406303257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157529232979521654416808685 59073462367320620406303257)
      ·
        refine ⟨44305096775490465304727443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59073462367320620406303257 44305096775490465304727443)
        ·
          refine ⟨66457645163235697957091165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44305096775490465304727443 66457645163235697957091165)
          ·
            refine ⟨24921616936213386733909187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66457645163235697957091165 24921616936213386733909187)
            ·
              refine ⟨37382425404320080100863781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24921616936213386733909187 37382425404320080100863781)
              ·
                refine ⟨7009204763310015018911959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37382425404320080100863781 7009204763310015018911959)
                ·
                  refine ⟨10513807144965022528367939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009204763310015018911959 10513807144965022528367939)
                  ·
                    refine ⟨15770710717447533792551909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10513807144965022528367939 15770710717447533792551909)
                    ·
                      refine ⟨2957008259521412586103483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15770710717447533792551909 2957008259521412586103483)
                      ·
                        rfl

theorem cell23_5758753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5758753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758753 prefixEnd_5758753 := by exact prefixLift 5758753
  have htrace : WordTrace (prefixWord ++ tailWord_5758753) baseStart_5758753 baseEnd_5758753 := by
    simpa [prefixWord, tailWord_5758753, baseEnd_5758753] using wordTrace_append hprefix tailTrace_5758753
  have hstable : (prefixWord ++ tailWord_5758753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758753).length < 2 ^ (prefixWord ++ tailWord_5758753).sum := by decide
  have hdescent : baseEnd_5758753 < baseStart_5758753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758776 : List Nat := [2, 1, 2, 1, 3, 5, 9]
def baseStart_5758776 : Nat := 118140960795 + 5758776 * 2 ^ 59
def prefixEnd_5758776 : Nat := 4983230072969 + 3 ^ 40 * 5758776 * 2
def baseEnd_5758776 : Nat := 36506420612055135754517

theorem tailTrace_5758776 : CollatzResearch.WordTrace tailWord_5758776 prefixEnd_5758776 36506420612055135754517 := by
  unfold tailWord_5758776
  simp only [CollatzResearch.WordTrace]
  refine ⟨105019908092472773741916091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140026544123297031655888121 105019908092472773741916091)
  ·
    refine ⟨157529862138709160612874137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105019908092472773741916091 157529862138709160612874137)
    ·
      refine ⟨118147396604031870459655603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157529862138709160612874137 118147396604031870459655603)
      ·
        refine ⟨177221094906047805689483405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118147396604031870459655603 177221094906047805689483405)
        ·
          refine ⟨66457910589767927133556277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177221094906047805689483405 66457910589767927133556277)
          ·
            refine ⟨6230429117790743168770901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66457910589767927133556277 6230429117790743168770901)
            ·
              refine ⟨36506420612055135754517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6230429117790743168770901 36506420612055135754517)
              ·
                rfl

theorem cell23_5758776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 9].length) (baseStart_5758776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758776 prefixEnd_5758776 := by exact prefixLift 5758776
  have htrace : WordTrace (prefixWord ++ tailWord_5758776) baseStart_5758776 baseEnd_5758776 := by
    simpa [prefixWord, tailWord_5758776, baseEnd_5758776] using wordTrace_append hprefix tailTrace_5758776
  have hstable : (prefixWord ++ tailWord_5758776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758776).length < 2 ^ (prefixWord ++ tailWord_5758776).sum := by decide
  have hdescent : baseEnd_5758776 < baseStart_5758776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758787 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 3, 2, 2]
def baseStart_5758787 : Nat := 118140960795 + 5758787 * 2 ^ 59
def prefixEnd_5758787 : Nat := 4983230072969 + 3 ^ 40 * 5758787 * 2
def baseEnd_5758787 : Nat := 2957025717863665453078327

theorem tailTrace_5758787 : CollatzResearch.WordTrace tailWord_5758787 prefixEnd_5758787 2957025717863665453078327 := by
  unfold tailWord_5758787
  simp only [CollatzResearch.WordTrace]
  refine ⟨210040217387905696362482615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140026811591937130908321743 210040217387905696362482615)
  ·
    refine ⟨315060326081858544543723923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210040217387905696362482615 315060326081858544543723923)
    ·
      refine ⟨472590489122787816815585885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315060326081858544543723923 472590489122787816815585885)
      ·
        refine ⟨177221433421045431305844707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472590489122787816815585885 177221433421045431305844707)
        ·
          refine ⟨265832150131568146958767061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177221433421045431305844707 265832150131568146958767061)
          ·
            refine ⟨6230441018708628444346103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265832150131568146958767061 6230441018708628444346103)
            ·
              refine ⟨9345661528062942666519155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230441018708628444346103 9345661528062942666519155)
              ·
                refine ⟨14018492292094413999778733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345661528062942666519155 14018492292094413999778733)
                ·
                  refine ⟨5256934609535405249917025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14018492292094413999778733 5256934609535405249917025)
                  ·
                    refine ⟨3942700957151553937437769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5256934609535405249917025 3942700957151553937437769)
                    ·
                      refine ⟨2957025717863665453078327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942700957151553937437769 2957025717863665453078327)
                      ·
                        rfl

theorem cell23_5758787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_5758787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758787 prefixEnd_5758787 := by exact prefixLift 5758787
  have htrace : WordTrace (prefixWord ++ tailWord_5758787) baseStart_5758787 baseEnd_5758787 := by
    simpa [prefixWord, tailWord_5758787, baseEnd_5758787] using wordTrace_append hprefix tailTrace_5758787
  have hstable : (prefixWord ++ tailWord_5758787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758787).length < 2 ^ (prefixWord ++ tailWord_5758787).sum := by decide
  have hdescent : baseEnd_5758787 < baseStart_5758787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758797 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5758797 : Nat := 118140960795 + 5758797 * 2 ^ 59
def prefixEnd_5758797 : Nat := 4983230072969 + 3 ^ 40 * 5758797 * 2
def baseEnd_5758797 : Nat := 985676950890070137984427

theorem tailTrace_5758797 : CollatzResearch.WordTrace tailWord_5758797 prefixEnd_5758797 985676950890070137984427 := by
  unfold tailWord_5758797
  simp only [CollatzResearch.WordTrace]
  refine ⟨210040582117869468070346645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140027054745246312046897763 210040582117869468070346645)
  ·
    refine ⟨9845652286775131315797499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 210040582117869468070346645 9845652286775131315797499)
    ·
      refine ⟨14768478430162696973696249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845652286775131315797499 14768478430162696973696249)
      ·
        refine ⟨11076358822622022730272187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14768478430162696973696249 11076358822622022730272187)
        ·
          refine ⟨16614538233933034095408281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11076358822622022730272187 16614538233933034095408281)
          ·
            refine ⟨12460903675449775571556211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16614538233933034095408281 12460903675449775571556211)
            ·
              refine ⟨18691355513174663357334317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460903675449775571556211 18691355513174663357334317)
              ·
                refine ⟨7009258317440498759000369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18691355513174663357334317 7009258317440498759000369)
                ·
                  refine ⟨5256943738080374069250277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009258317440498759000369 5256943738080374069250277)
                  ·
                    refine ⟨985676950890070137984427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256943738080374069250277 985676950890070137984427)
                    ·
                      rfl

theorem cell23_5758797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5758797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758797 prefixEnd_5758797 := by exact prefixLift 5758797
  have htrace : WordTrace (prefixWord ++ tailWord_5758797) baseStart_5758797 baseEnd_5758797 := by
    simpa [prefixWord, tailWord_5758797, baseEnd_5758797] using wordTrace_append hprefix tailTrace_5758797
  have hstable : (prefixWord ++ tailWord_5758797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758797).length < 2 ^ (prefixWord ++ tailWord_5758797).sum := by decide
  have hdescent : baseEnd_5758797 < baseStart_5758797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758807 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_5758807 : Nat := 118140960795 + 5758807 * 2 ^ 59
def prefixEnd_5758807 : Nat := 4983230072969 + 3 ^ 40 * 5758807 * 2
def baseEnd_5758807 : Nat := 2957035987476755374828235

theorem tailTrace_5758807 : CollatzResearch.WordTrace tailWord_5758807 prefixEnd_5758807 2957035987476755374828235 := by
  unfold tailWord_5758807
  simp only [CollatzResearch.WordTrace]
  refine ⟨210040946847833239778210675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140027297898555493185473783 210040946847833239778210675)
  ·
    refine ⟨315061420271749859667316013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210040946847833239778210675 315061420271749859667316013)
    ·
      refine ⟨118148032601906197375243505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315061420271749859667316013 118148032601906197375243505)
      ·
        refine ⟨88611024451429648031432629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118148032601906197375243505 88611024451429648031432629)
        ·
          refine ⟨8307283542321529502946809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88611024451429648031432629 8307283542321529502946809)
          ·
            refine ⟨6230462656741147127210107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8307283542321529502946809 6230462656741147127210107)
            ·
              refine ⟨9345693985111720690815161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230462656741147127210107 9345693985111720690815161)
              ·
                refine ⟨7009270488833790518111371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345693985111720690815161 7009270488833790518111371)
                ·
                  refine ⟨10513905733250685777167057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009270488833790518111371 10513905733250685777167057)
                  ·
                    refine ⟨7885429299938014332875293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10513905733250685777167057 7885429299938014332875293)
                    ·
                      refine ⟨2957035987476755374828235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885429299938014332875293 2957035987476755374828235)
                      ·
                        rfl

theorem cell23_5758807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_5758807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758807 prefixEnd_5758807 := by exact prefixLift 5758807
  have htrace : WordTrace (prefixWord ++ tailWord_5758807) baseStart_5758807 baseEnd_5758807 := by
    simpa [prefixWord, tailWord_5758807, baseEnd_5758807] using wordTrace_append hprefix tailTrace_5758807
  have hstable : (prefixWord ++ tailWord_5758807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758807).length < 2 ^ (prefixWord ++ tailWord_5758807).sum := by decide
  have hdescent : baseEnd_5758807 < baseStart_5758807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758820 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_5758820 : Nat := 118140960795 + 5758820 * 2 ^ 59
def prefixEnd_5758820 : Nat := 4983230072969 + 3 ^ 40 * 5758820 * 2
def baseEnd_5758820 : Nat := 2957042662725263823965675

theorem tailTrace_5758820 : CollatzResearch.WordTrace tailWord_5758820 prefixEnd_5758820 2957042662725263823965675 := by
  unfold tailWord_5758820
  simp only [CollatzResearch.WordTrace]
  refine ⟨105020710498393071499216957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140027613997857428665622609 105020710498393071499216957)
  ·
    refine ⟨39382766436897401812206359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105020710498393071499216957 39382766436897401812206359)
    ·
      refine ⟨59074149655346102718309539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39382766436897401812206359 59074149655346102718309539)
      ·
        refine ⟨88611224483019154077464309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59074149655346102718309539 88611224483019154077464309)
        ·
          refine ⟨8307302295283045694762279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88611224483019154077464309 8307302295283045694762279)
          ·
            refine ⟨12460953442924568542143419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307302295283045694762279 12460953442924568542143419)
            ·
              refine ⟨18691430164386852813215129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460953442924568542143419 18691430164386852813215129)
              ·
                refine ⟨14018572623290139609911347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18691430164386852813215129 14018572623290139609911347)
                ·
                  refine ⟨21027858934935209414867021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14018572623290139609911347 21027858934935209414867021)
                  ·
                    refine ⟨7885447100600703530575133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21027858934935209414867021 7885447100600703530575133)
                    ·
                      refine ⟨2957042662725263823965675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885447100600703530575133 2957042662725263823965675)
                      ·
                        rfl

theorem cell23_5758820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_5758820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758820 prefixEnd_5758820 := by exact prefixLift 5758820
  have htrace : WordTrace (prefixWord ++ tailWord_5758820) baseStart_5758820 baseEnd_5758820 := by
    simpa [prefixWord, tailWord_5758820, baseEnd_5758820] using wordTrace_append hprefix tailTrace_5758820
  have hstable : (prefixWord ++ tailWord_5758820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758820).length < 2 ^ (prefixWord ++ tailWord_5758820).sum := by decide
  have hdescent : baseEnd_5758820 < baseStart_5758820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758837 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5758837 : Nat := 118140960795 + 5758837 * 2 ^ 59
def prefixEnd_5758837 : Nat := 4983230072969 + 3 ^ 40 * 5758837 * 2
def baseEnd_5758837 : Nat := 2957051391896390257453097

theorem tailTrace_5758837 : CollatzResearch.WordTrace tailWord_5758837 prefixEnd_5758837 2957051391896390257453097 := by
  unfold tailWord_5758837
  simp only [CollatzResearch.WordTrace]
  refine ⟨210042041037724554901802765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140028027358483036601201843 210042041037724554901802765)
  ·
    refine ⟨78765765389146708088176037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210042041037724554901802765 78765765389146708088176037)
    ·
      refine ⟨14768581010465007766533007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78765765389146708088176037 14768581010465007766533007)
      ·
        refine ⟨22152871515697511649799511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768581010465007766533007 22152871515697511649799511)
        ·
          refine ⟨33229307273546267474699267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22152871515697511649799511 33229307273546267474699267)
          ·
            refine ⟨49843960910319401212048901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33229307273546267474699267 49843960910319401212048901)
            ·
              refine ⟨9345742670684887727259169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49843960910319401212048901 9345742670684887727259169)
              ·
                refine ⟨7009307003013665795444377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345742670684887727259169 7009307003013665795444377)
                ·
                  refine ⟨5256980252260249346583283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009307003013665795444377 5256980252260249346583283)
                  ·
                    refine ⟨7885470378390374019874925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256980252260249346583283 7885470378390374019874925)
                    ·
                      refine ⟨2957051391896390257453097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885470378390374019874925 2957051391896390257453097)
                      ·
                        rfl

theorem cell23_5758837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5758837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758837 prefixEnd_5758837 := by exact prefixLift 5758837
  have htrace : WordTrace (prefixWord ++ tailWord_5758837) baseStart_5758837 baseEnd_5758837 := by
    simpa [prefixWord, tailWord_5758837, baseEnd_5758837] using wordTrace_append hprefix tailTrace_5758837
  have hstable : (prefixWord ++ tailWord_5758837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758837).length < 2 ^ (prefixWord ++ tailWord_5758837).sum := by decide
  have hdescent : baseEnd_5758837 < baseStart_5758837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 4, 2]
def baseStart_5758843 : Nat := 118140960795 + 5758843 * 2 ^ 59
def prefixEnd_5758843 : Nat := 4983230072969 + 3 ^ 40 * 5758843 * 2
def baseEnd_5758843 : Nat := 2957054472780317233978069

theorem tailTrace_5758843 : CollatzResearch.WordTrace tailWord_5758843 prefixEnd_5758843 2957054472780317233978069 := by
  unfold tailWord_5758843
  simp only [CollatzResearch.WordTrace]
  refine ⟨210042259875702817926521183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140028173250468545284347455 210042259875702817926521183)
  ·
    refine ⟨315063389813554226889781775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210042259875702817926521183 315063389813554226889781775)
    ·
      refine ⟨472595084720331340334672663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315063389813554226889781775 472595084720331340334672663)
      ·
        refine ⟨708892627080497010502008995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472595084720331340334672663 708892627080497010502008995)
        ·
          refine ⟨1063338940620745515753013493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708892627080497010502008995 1063338940620745515753013493)
          ·
            refine ⟨99688025683194892101845015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1063338940620745515753013493 99688025683194892101845015)
            ·
              refine ⟨149532038524792338152767523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99688025683194892101845015 149532038524792338152767523)
              ·
                refine ⟨224298057787188507229151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149532038524792338152767523 224298057787188507229151285)
                ·
                  refine ⟨21027942917548922552732933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224298057787188507229151285 21027942917548922552732933)
                  ·
                    refine ⟨3942739297040422978637425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21027942917548922552732933 3942739297040422978637425)
                    ·
                      refine ⟨2957054472780317233978069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942739297040422978637425 2957054472780317233978069)
                      ·
                        rfl

theorem cell23_5758843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4, 2].length) (baseStart_5758843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758843 prefixEnd_5758843 := by exact prefixLift 5758843
  have htrace : WordTrace (prefixWord ++ tailWord_5758843) baseStart_5758843 baseEnd_5758843 := by
    simpa [prefixWord, tailWord_5758843, baseEnd_5758843] using wordTrace_append hprefix tailTrace_5758843
  have hstable : (prefixWord ++ tailWord_5758843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758843).length < 2 ^ (prefixWord ++ tailWord_5758843).sum := by decide
  have hdescent : baseEnd_5758843 < baseStart_5758843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758860 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_5758860 : Nat := 118140960795 + 5758860 * 2 ^ 59
def prefixEnd_5758860 : Nat := 4983230072969 + 3 ^ 40 * 5758860 * 2
def baseEnd_5758860 : Nat := 2957063201951443667465491

theorem tailTrace_5758860 : CollatzResearch.WordTrace tailWord_5758860 prefixEnd_5758860 2957063201951443667465491 := by
  unfold tailWord_5758860
  simp only [CollatzResearch.WordTrace]
  refine ⟨105021439958320614914945017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140028586611094153219926689 105021439958320614914945017)
  ·
    refine ⟨78766079968740461186208763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105021439958320614914945017 78766079968740461186208763)
    ·
      refine ⟨118149119953110691779313145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78766079968740461186208763 118149119953110691779313145)
      ·
        refine ⟨88611839964833018834484859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118149119953110691779313145 88611839964833018834484859)
        ·
          refine ⟨132917759947249528251727289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88611839964833018834484859 132917759947249528251727289)
          ·
            refine ⟨99688319960437146188795467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132917759947249528251727289 99688319960437146188795467)
            ·
              refine ⟨149532479940655719283193201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99688319960437146188795467 149532479940655719283193201)
              ·
                refine ⟨112149359955491789462394901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149532479940655719283193201 112149359955491789462394901)
                ·
                  refine ⟨5257001247913677631049761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112149359955491789462394901 5257001247913677631049761)
                  ·
                    refine ⟨3942750935935258223287321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5257001247913677631049761 3942750935935258223287321)
                    ·
                      refine ⟨2957063201951443667465491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942750935935258223287321 2957063201951443667465491)
                      ·
                        rfl

theorem cell23_5758860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_5758860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758860 prefixEnd_5758860 := by exact prefixLift 5758860
  have htrace : WordTrace (prefixWord ++ tailWord_5758860) baseStart_5758860 baseEnd_5758860 := by
    simpa [prefixWord, tailWord_5758860, baseEnd_5758860] using wordTrace_append hprefix tailTrace_5758860
  have hstable : (prefixWord ++ tailWord_5758860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758860).length < 2 ^ (prefixWord ++ tailWord_5758860).sum := by decide
  have hdescent : baseEnd_5758860 < baseStart_5758860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758881 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5758881 : Nat := 118140960795 + 5758881 * 2 ^ 59
def prefixEnd_5758881 : Nat := 4983230072969 + 3 ^ 40 * 5758881 * 2
def baseEnd_5758881 : Nat := 2957073985045188085302895

theorem tailTrace_5758881 : CollatzResearch.WordTrace tailWord_5758881 prefixEnd_5758881 2957073985045188085302895 := by
  unfold tailWord_5758881
  simp only [CollatzResearch.WordTrace]
  refine ⟨210043645849565150416404497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140029097233043433610936331 210043645849565150416404497)
  ·
    refine ⟨157532734387173862812303373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210043645849565150416404497 157532734387173862812303373)
    ·
      refine ⟨59074775395190198554613765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157532734387173862812303373 59074775395190198554613765)
      ·
        refine ⟨11076520386598162228990081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59074775395190198554613765 11076520386598162228990081)
        ·
          refine ⟨8307390289948621671742561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11076520386598162228990081 8307390289948621671742561)
          ·
            refine ⟨6230542717461466253806921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8307390289948621671742561 6230542717461466253806921)
            ·
              refine ⟨4672907038096099690355191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230542717461466253806921 4672907038096099690355191)
              ·
                refine ⟨7009360557144149535532787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672907038096099690355191 7009360557144149535532787)
                ·
                  refine ⟨10514040835716224303299181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009360557144149535532787 10514040835716224303299181)
                  ·
                    refine ⟨3942765313393584113737193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10514040835716224303299181 3942765313393584113737193)
                    ·
                      refine ⟨2957073985045188085302895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942765313393584113737193 2957073985045188085302895)
                      ·
                        rfl

theorem cell23_5758881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5758881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758881 prefixEnd_5758881 := by exact prefixLift 5758881
  have htrace : WordTrace (prefixWord ++ tailWord_5758881) baseStart_5758881 baseEnd_5758881 := by
    simpa [prefixWord, tailWord_5758881, baseEnd_5758881] using wordTrace_append hprefix tailTrace_5758881
  have hstable : (prefixWord ++ tailWord_5758881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758881).length < 2 ^ (prefixWord ++ tailWord_5758881).sum := by decide
  have hdescent : baseEnd_5758881 < baseStart_5758881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758888 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5758888 : Nat := 118140960795 + 5758888 * 2 ^ 59
def prefixEnd_5758888 : Nat := 4983230072969 + 3 ^ 40 * 5758888 * 2
def baseEnd_5758888 : Nat := 2957077579409769557915363

theorem tailTrace_5758888 : CollatzResearch.WordTrace tailWord_5758888 prefixEnd_5758888 2957077579409769557915363 := by
  unfold tailWord_5758888
  simp only [CollatzResearch.WordTrace]
  refine ⟨105021950580269895305954659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140029267440359860407939545 105021950580269895305954659)
  ·
    refine ⟨157532925870404842958931989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105021950580269895305954659 157532925870404842958931989)
    ·
      refine ⟨7384355900175227013699937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157532925870404842958931989 7384355900175227013699937)
      ·
        refine ⟨5538266925131420260274953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7384355900175227013699937 5538266925131420260274953)
        ·
          refine ⟨4153700193848565195206215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5538266925131420260274953 4153700193848565195206215)
          ·
            refine ⟨6230550290772847792809323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153700193848565195206215 6230550290772847792809323)
            ·
              refine ⟨9345825436159271689213985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230550290772847792809323 9345825436159271689213985)
              ·
                refine ⟨7009369077119453766910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345825436159271689213985 7009369077119453766910489)
                ·
                  refine ⟨5257026807839590325182867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009369077119453766910489 5257026807839590325182867)
                  ·
                    refine ⟨7885540211759385487774301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257026807839590325182867 7885540211759385487774301)
                    ·
                      refine ⟨2957077579409769557915363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885540211759385487774301 2957077579409769557915363)
                      ·
                        rfl

theorem cell23_5758888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5758888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758888 prefixEnd_5758888 := by exact prefixLift 5758888
  have htrace : WordTrace (prefixWord ++ tailWord_5758888) baseStart_5758888 baseEnd_5758888 := by
    simpa [prefixWord, tailWord_5758888, baseEnd_5758888] using wordTrace_append hprefix tailTrace_5758888
  have hstable : (prefixWord ++ tailWord_5758888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758888).length < 2 ^ (prefixWord ++ tailWord_5758888).sum := by decide
  have hdescent : baseEnd_5758888 < baseStart_5758888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758910 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_5758910 : Nat := 118140960795 + 5758910 * 2 ^ 59
def prefixEnd_5758910 : Nat := 4983230072969 + 3 ^ 40 * 5758910 * 2
def baseEnd_5758910 : Nat := 2957088875984168471840261

theorem tailTrace_5758910 : CollatzResearch.WordTrace tailWord_5758910 prefixEnd_5758910 2957088875984168471840261 := by
  unfold tailWord_5758910
  simp only [CollatzResearch.WordTrace]
  refine ⟨26255587945807511046151273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140029802377640058912806789 26255587945807511046151273)
  ·
    refine ⟨19691690959355633284613455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26255587945807511046151273 19691690959355633284613455)
    ·
      refine ⟨29537536439033449926920183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19691690959355633284613455 29537536439033449926920183)
      ·
        refine ⟨44306304658550174890380275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29537536439033449926920183 44306304658550174890380275)
        ·
          refine ⟨66459456987825262335570413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44306304658550174890380275 66459456987825262335570413)
          ·
            refine ⟨24922296370434473375838905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66459456987825262335570413 24922296370434473375838905)
            ·
              refine ⟨18691722277825855031879179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24922296370434473375838905 18691722277825855031879179)
              ·
                refine ⟨28037583416738782547818769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18691722277825855031879179 28037583416738782547818769)
                ·
                  refine ⟨21028187562554086910864077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28037583416738782547818769 21028187562554086910864077)
                  ·
                    refine ⟨7885570335957782591574029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21028187562554086910864077 7885570335957782591574029)
                    ·
                      refine ⟨2957088875984168471840261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885570335957782591574029 2957088875984168471840261)
                      ·
                        rfl

theorem cell23_5758910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_5758910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758910 prefixEnd_5758910 := by exact prefixLift 5758910
  have htrace : WordTrace (prefixWord ++ tailWord_5758910) baseStart_5758910 baseEnd_5758910 := by
    simpa [prefixWord, tailWord_5758910, baseEnd_5758910] using wordTrace_append hprefix tailTrace_5758910
  have hstable : (prefixWord ++ tailWord_5758910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758910).length < 2 ^ (prefixWord ++ tailWord_5758910).sum := by decide
  have hdescent : baseEnd_5758910 < baseStart_5758910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758957 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5758957 : Nat := 118140960795 + 5758957 * 2 ^ 59
def prefixEnd_5758957 : Nat := 4983230072969 + 3 ^ 40 * 5758957 * 2
def baseEnd_5758957 : Nat := 2957113009574929787952545

theorem tailTrace_5758957 : CollatzResearch.WordTrace tailWord_5758957 prefixEnd_5758957 2957113009574929787952545 := by
  unfold tailWord_5758957
  simp only [CollatzResearch.WordTrace]
  refine ⟨210046417797289815396171125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140030945198193210264114083 210046417797289815396171125)
  ·
    refine ⟨19691851668495920193391043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210046417797289815396171125 19691851668495920193391043)
    ·
      refine ⟨29537777502743880290086565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19691851668495920193391043 29537777502743880290086565)
      ·
        refine ⟨5538333281764477554391231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29537777502743880290086565 5538333281764477554391231)
        ·
          refine ⟨8307499922646716331586847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538333281764477554391231 8307499922646716331586847)
          ·
            refine ⟨12461249883970074497380271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307499922646716331586847 12461249883970074497380271)
            ·
              refine ⟨18691874825955111746070407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12461249883970074497380271 18691874825955111746070407)
              ·
                refine ⟨28037812238932667619105611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18691874825955111746070407 28037812238932667619105611)
                ·
                  refine ⟨42056718358399001428658417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28037812238932667619105611 42056718358399001428658417)
                  ·
                    refine ⟨31542538768799251071493813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42056718358399001428658417 31542538768799251071493813)
                    ·
                      refine ⟨2957113009574929787952545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31542538768799251071493813 2957113009574929787952545)
                      ·
                        rfl

theorem cell23_5758957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5758957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758957 prefixEnd_5758957 := by exact prefixLift 5758957
  have htrace : WordTrace (prefixWord ++ tailWord_5758957) baseStart_5758957 baseEnd_5758957 := by
    simpa [prefixWord, tailWord_5758957, baseEnd_5758957] using wordTrace_append hprefix tailTrace_5758957
  have hstable : (prefixWord ++ tailWord_5758957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758957).length < 2 ^ (prefixWord ++ tailWord_5758957).sum := by decide
  have hdescent : baseEnd_5758957 < baseStart_5758957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5758960 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_5758960 : Nat := 118140960795 + 5758960 * 2 ^ 59
def prefixEnd_5758960 : Nat := 4983230072969 + 3 ^ 40 * 5758960 * 2
def baseEnd_5758960 : Nat := 985704850005631092071677

theorem tailTrace_5758960 : CollatzResearch.WordTrace tailWord_5758960 prefixEnd_5758960 985704850005631092071677 := by
  unfold tailWord_5758960
  simp only [CollatzResearch.WordTrace]
  refine ⟨105023263608139473454265167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140031018144185964605686889 105023263608139473454265167)
  ·
    refine ⟨157534895412209210181397751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105023263608139473454265167 157534895412209210181397751)
    ·
      refine ⟨236302343118313815272096627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157534895412209210181397751 236302343118313815272096627)
      ·
        refine ⟨354453514677470722908144941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236302343118313815272096627 354453514677470722908144941)
        ·
          refine ⟨132920068004051521090554353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354453514677470722908144941 132920068004051521090554353)
          ·
            refine ⟨99690051003038640817915765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132920068004051521090554353 99690051003038640817915765)
            ·
              refine ⟨9345942281534872576679603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99690051003038640817915765 9345942281534872576679603)
              ·
                refine ⟨14018913422302308865019405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345942281534872576679603 14018913422302308865019405)
                ·
                  refine ⟨5257092533363365824382277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14018913422302308865019405 5257092533363365824382277)
                  ·
                    refine ⟨985704850005631092071677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257092533363365824382277 985704850005631092071677)
                    ·
                      rfl

theorem cell23_5758960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_5758960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5758960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5758960 prefixEnd_5758960 := by exact prefixLift 5758960
  have htrace : WordTrace (prefixWord ++ tailWord_5758960) baseStart_5758960 baseEnd_5758960 := by
    simpa [prefixWord, tailWord_5758960, baseEnd_5758960] using wordTrace_append hprefix tailTrace_5758960
  have hstable : (prefixWord ++ tailWord_5758960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5758960).length < 2 ^ (prefixWord ++ tailWord_5758960).sum := by decide
  have hdescent : baseEnd_5758960 < baseStart_5758960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5758960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759030 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5759030 : Nat := 118140960795 + 5759030 * 2 ^ 59
def prefixEnd_5759030 : Nat := 4983230072969 + 3 ^ 40 * 5759030 * 2
def baseEnd_5759030 : Nat := 2957150493662708002339709

theorem tailTrace_5759030 : CollatzResearch.WordTrace tailWord_5759030 prefixEnd_5759030 2957150493662708002339709 := by
  unfold tailWord_5759030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128067520376584303973659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140032720217350232575719029 13128067520376584303973659)
  ·
    refine ⟨19692101280564876455960489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128067520376584303973659 19692101280564876455960489)
    ·
      refine ⟨14769075960423657341970367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19692101280564876455960489 14769075960423657341970367)
      ·
        refine ⟨22153613940635486012955551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14769075960423657341970367 22153613940635486012955551)
        ·
          refine ⟨33230420910953229019433327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22153613940635486012955551 33230420910953229019433327)
          ·
            refine ⟨49845631366429843529149991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33230420910953229019433327 49845631366429843529149991)
            ·
              refine ⟨74768447049644765293724987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49845631366429843529149991 74768447049644765293724987)
              ·
                refine ⟨112152670574467147940587481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74768447049644765293724987 112152670574467147940587481)
                ·
                  refine ⟨84114502930850360955440611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112152670574467147940587481 84114502930850360955440611)
                  ·
                    refine ⟨126171754396275541433160917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84114502930850360955440611 126171754396275541433160917)
                    ·
                      refine ⟨2957150493662708002339709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126171754396275541433160917 2957150493662708002339709)
                      ·
                        rfl

theorem cell23_5759030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5759030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759030 prefixEnd_5759030 := by exact prefixLift 5759030
  have htrace : WordTrace (prefixWord ++ tailWord_5759030) baseStart_5759030 baseEnd_5759030 := by
    simpa [prefixWord, tailWord_5759030, baseEnd_5759030] using wordTrace_append hprefix tailTrace_5759030
  have hstable : (prefixWord ++ tailWord_5759030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759030).length < 2 ^ (prefixWord ++ tailWord_5759030).sum := by decide
  have hdescent : baseEnd_5759030 < baseStart_5759030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759040 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_5759040 : Nat := 118140960795 + 5759040 * 2 ^ 59
def prefixEnd_5759040 : Nat := 4983230072969 + 3 ^ 40 * 5759040 * 2
def baseEnd_5759040 : Nat := 2957155628469252963214663

theorem tailTrace_5759040 : CollatzResearch.WordTrace tailWord_5759040 prefixEnd_5759040 2957155628469252963214663 := by
  unfold tailWord_5759040
  simp only [CollatzResearch.WordTrace]
  refine ⟨105024722527994560285721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140032963370659413714295049 105024722527994560285721287)
  ·
    refine ⟨157537083791991840428581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105024722527994560285721287 157537083791991840428581931)
    ·
      refine ⟨236305625687987760642872897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157537083791991840428581931 236305625687987760642872897)
      ·
        refine ⟨177229219265990820482154673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236305625687987760642872897 177229219265990820482154673)
        ·
          refine ⟨132921914449493115361616005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177229219265990820482154673 132921914449493115361616005)
          ·
            refine ⟨24922858959279959130303001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132921914449493115361616005 24922858959279959130303001)
            ·
              refine ⟨18692144219459969347727251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24922858959279959130303001 18692144219459969347727251)
              ·
                refine ⟨28038216329189954021590877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18692144219459969347727251 28038216329189954021590877)
                ·
                  refine ⟨10514331123446232758096579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28038216329189954021590877 10514331123446232758096579)
                  ·
                    refine ⟨15771496685169349137144869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10514331123446232758096579 15771496685169349137144869)
                    ·
                      refine ⟨2957155628469252963214663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15771496685169349137144869 2957155628469252963214663)
                      ·
                        rfl

theorem cell23_5759040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_5759040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759040 prefixEnd_5759040 := by exact prefixLift 5759040
  have htrace : WordTrace (prefixWord ++ tailWord_5759040) baseStart_5759040 baseEnd_5759040 := by
    simpa [prefixWord, tailWord_5759040, baseEnd_5759040] using wordTrace_append hprefix tailTrace_5759040
  have hstable : (prefixWord ++ tailWord_5759040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759040).length < 2 ^ (prefixWord ++ tailWord_5759040).sum := by decide
  have hdescent : baseEnd_5759040 < baseStart_5759040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_5759043 : Nat := 118140960795 + 5759043 * 2 ^ 59
def prefixEnd_5759043 : Nat := 4983230072969 + 3 ^ 40 * 5759043 * 2
def baseEnd_5759043 : Nat := 2957157168911216451477149

theorem tailTrace_5759043 : CollatzResearch.WordTrace tailWord_5759043 prefixEnd_5759043 2957157168911216451477149 := by
  unfold tailWord_5759043
  simp only [CollatzResearch.WordTrace]
  refine ⟨210049554474978252083801783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140033036316652168055867855 210049554474978252083801783)
  ·
    refine ⟨315074331712467378125702675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210049554474978252083801783 315074331712467378125702675)
    ·
      refine ⟨472611497568701067188554013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315074331712467378125702675 472611497568701067188554013)
      ·
        refine ⟨177229311588262900195707755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472611497568701067188554013 177229311588262900195707755)
        ·
          refine ⟨265843967382394350293561633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177229311588262900195707755 265843967382394350293561633)
          ·
            refine ⟨199382975536795762720171225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265843967382394350293561633 199382975536795762720171225)
            ·
              refine ⟨149537231652596822040128419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199382975536795762720171225 149537231652596822040128419)
              ·
                refine ⟨224305847478895233060192629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149537231652596822040128419 224305847478895233060192629)
                ·
                  refine ⟨21028673201146428099393059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224305847478895233060192629 21028673201146428099393059)
                  ·
                    refine ⟨31543009801719642149089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21028673201146428099393059 31543009801719642149089589)
                    ·
                      refine ⟨2957157168911216451477149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31543009801719642149089589 2957157168911216451477149)
                      ·
                        rfl

theorem cell23_5759043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_5759043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759043 prefixEnd_5759043 := by exact prefixLift 5759043
  have htrace : WordTrace (prefixWord ++ tailWord_5759043) baseStart_5759043 baseEnd_5759043 := by
    simpa [prefixWord, tailWord_5759043, baseEnd_5759043] using wordTrace_append hprefix tailTrace_5759043
  have hstable : (prefixWord ++ tailWord_5759043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759043).length < 2 ^ (prefixWord ++ tailWord_5759043).sum := by decide
  have hdescent : baseEnd_5759043 < baseStart_5759043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759050 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_5759050 : Nat := 118140960795 + 5759050 * 2 ^ 59
def prefixEnd_5759050 : Nat := 4983230072969 + 3 ^ 40 * 5759050 * 2
def baseEnd_5759050 : Nat := 985720254425265974696539

theorem tailTrace_5759050 : CollatzResearch.WordTrace tailWord_5759050 prefixEnd_5759050 985720254425265974696539 := by
  unfold tailWord_5759050
  simp only [CollatzResearch.WordTrace]
  refine ⟨52512452446488223069826651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140033206523968594852871069 52512452446488223069826651)
  ·
    refine ⟨78768678669732334604739977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52512452446488223069826651 78768678669732334604739977)
    ·
      refine ⟨59076509002299250953554983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78768678669732334604739977 59076509002299250953554983)
      ·
        refine ⟨88614763503448876430332475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59076509002299250953554983 88614763503448876430332475)
        ·
          refine ⟨132922145255173314645498713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88614763503448876430332475 132922145255173314645498713)
          ·
            refine ⟨99691608941379985984124035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132922145255173314645498713 99691608941379985984124035)
            ·
              refine ⟨149537413412069978976186053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99691608941379985984124035 149537413412069978976186053)
              ·
                refine ⟨28038265014763121058034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149537413412069978976186053 28038265014763121058034885)
                ·
                  refine ⟨5257174690268085198381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28038265014763121058034885 5257174690268085198381541)
                  ·
                    refine ⟨985720254425265974696539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257174690268085198381541 985720254425265974696539)
                    ·
                      rfl

theorem cell23_5759050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_5759050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759050 prefixEnd_5759050 := by exact prefixLift 5759050
  have htrace : WordTrace (prefixWord ++ tailWord_5759050) baseStart_5759050 baseEnd_5759050 := by
    simpa [prefixWord, tailWord_5759050, baseEnd_5759050] using wordTrace_append hprefix tailTrace_5759050
  have hstable : (prefixWord ++ tailWord_5759050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759050).length < 2 ^ (prefixWord ++ tailWord_5759050).sum := by decide
  have hdescent : baseEnd_5759050 < baseStart_5759050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759054 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_5759054 : Nat := 118140960795 + 5759054 * 2 ^ 59
def prefixEnd_5759054 : Nat := 4983230072969 + 3 ^ 40 * 5759054 * 2
def baseEnd_5759054 : Nat := 985720939066138636146533

theorem tailTrace_5759054 : CollatzResearch.WordTrace tailWord_5759054 prefixEnd_5759054 985720939066138636146533 := by
  unfold tailWord_5759054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26256244459742300120306527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140033303785292267308301477 26256244459742300120306527)
  ·
    refine ⟨39384366689613450180459791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26256244459742300120306527 39384366689613450180459791)
    ·
      refine ⟨59076550034420175270689687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39384366689613450180459791 59076550034420175270689687)
      ·
        refine ⟨88614825051630262906034531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59076550034420175270689687 88614825051630262906034531)
        ·
          refine ⟨132922237577445394359051797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88614825051630262906034531 132922237577445394359051797)
          ·
            refine ⟨6230729886442752860580553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132922237577445394359051797 6230729886442752860580553)
            ·
              refine ⟨4673047414832064645435415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230729886442752860580553 4673047414832064645435415)
              ·
                refine ⟨7009571122248096968153123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673047414832064645435415 7009571122248096968153123)
                ·
                  refine ⟨10514356683372145452229685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009571122248096968153123 10514356683372145452229685)
                  ·
                    refine ⟨985720939066138636146533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10514356683372145452229685 985720939066138636146533)
                    ·
                      rfl

theorem cell23_5759054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_5759054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759054 prefixEnd_5759054 := by exact prefixLift 5759054
  have htrace : WordTrace (prefixWord ++ tailWord_5759054) baseStart_5759054 baseEnd_5759054 := by
    simpa [prefixWord, tailWord_5759054, baseEnd_5759054] using wordTrace_append hprefix tailTrace_5759054
  have hstable : (prefixWord ++ tailWord_5759054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759054).length < 2 ^ (prefixWord ++ tailWord_5759054).sum := by decide
  have hdescent : baseEnd_5759054 < baseStart_5759054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759057 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_5759057 : Nat := 118140960795 + 5759057 * 2 ^ 59
def prefixEnd_5759057 : Nat := 4983230072969 + 3 ^ 40 * 5759057 * 2
def baseEnd_5759057 : Nat := 2957164357640379396702085

theorem tailTrace_5759057 : CollatzResearch.WordTrace tailWord_5759057 prefixEnd_5759057 2957164357640379396702085 := by
  unfold tailWord_5759057
  simp only [CollatzResearch.WordTrace]
  refine ⟨210050065096927532474811425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140033376731285021649874283 210050065096927532474811425)
  ·
    refine ⟨157537548822695649356108569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210050065096927532474811425 157537548822695649356108569)
    ·
      refine ⟨118153161617021737017081427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157537548822695649356108569 118153161617021737017081427)
      ·
        refine ⟨177229742425532605525622141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118153161617021737017081427 177229742425532605525622141)
        ·
          refine ⟨66461153409574727072108303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177229742425532605525622141 66461153409574727072108303)
          ·
            refine ⟨99691730114362090608162455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66461153409574727072108303 99691730114362090608162455)
            ·
              refine ⟨149537595171543135912243683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99691730114362090608162455 149537595171543135912243683)
              ·
                refine ⟨224306392757314703868365525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149537595171543135912243683 224306392757314703868365525)
                ·
                  refine ⟨5257181080249563371914817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224306392757314703868365525 5257181080249563371914817)
                  ·
                    refine ⟨3942885810187172528936113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5257181080249563371914817 3942885810187172528936113)
                    ·
                      refine ⟨2957164357640379396702085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3942885810187172528936113 2957164357640379396702085)
                      ·
                        rfl

theorem cell23_5759057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_5759057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759057 prefixEnd_5759057 := by exact prefixLift 5759057
  have htrace : WordTrace (prefixWord ++ tailWord_5759057) baseStart_5759057 baseEnd_5759057 := by
    simpa [prefixWord, tailWord_5759057, baseEnd_5759057] using wordTrace_append hprefix tailTrace_5759057
  have hstable : (prefixWord ++ tailWord_5759057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759057).length < 2 ^ (prefixWord ++ tailWord_5759057).sum := by decide
  have hdescent : baseEnd_5759057 < baseStart_5759057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759060 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5759060 : Nat := 118140960795 + 5759060 * 2 ^ 59
def prefixEnd_5759060 : Nat := 4983230072969 + 3 ^ 40 * 5759060 * 2
def baseEnd_5759060 : Nat := 2957165898082342884964571

theorem tailTrace_5759060 : CollatzResearch.WordTrace tailWord_5759060 prefixEnd_5759060 2957165898082342884964571 := by
  unfold tailWord_5759060
  simp only [CollatzResearch.WordTrace]
  refine ⟨105025087257958331993585317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140033449677277775991447089 105025087257958331993585317)
  ·
    refine ⟨19692203860867187248797247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105025087257958331993585317 19692203860867187248797247)
    ·
      refine ⟨29538305791300780873195871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692203860867187248797247 29538305791300780873195871)
      ·
        refine ⟨44307458686951171309793807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29538305791300780873195871 44307458686951171309793807)
        ·
          refine ⟨66461188030426756964690711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44307458686951171309793807 66461188030426756964690711)
          ·
            refine ⟨99691782045640135447036067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66461188030426756964690711 99691782045640135447036067)
            ·
              refine ⟨149537673068460203170554101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99691782045640135447036067 149537673068460203170554101)
              ·
                refine ⟨14019156850168144047239447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149537673068460203170554101 14019156850168144047239447)
                ·
                  refine ⟨21028735275252216070859171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14019156850168144047239447 21028735275252216070859171)
                  ·
                    refine ⟨31543102912878324106288757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21028735275252216070859171 31543102912878324106288757)
                    ·
                      refine ⟨2957165898082342884964571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31543102912878324106288757 2957165898082342884964571)
                      ·
                        rfl

theorem cell23_5759060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5759060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759060 prefixEnd_5759060 := by exact prefixLift 5759060
  have htrace : WordTrace (prefixWord ++ tailWord_5759060) baseStart_5759060 baseEnd_5759060 := by
    simpa [prefixWord, tailWord_5759060, baseEnd_5759060] using wordTrace_append hprefix tailTrace_5759060
  have hstable : (prefixWord ++ tailWord_5759060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759060).length < 2 ^ (prefixWord ++ tailWord_5759060).sum := by decide
  have hdescent : baseEnd_5759060 < baseStart_5759060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5759073 : Nat := 118140960795 + 5759073 * 2 ^ 59
def prefixEnd_5759073 : Nat := 4983230072969 + 3 ^ 40 * 5759073 * 2
def baseEnd_5759073 : Nat := 2957172573330851334102011

theorem tailTrace_5759073 : CollatzResearch.WordTrace tailWord_5759073 prefixEnd_5759073 2957172573330851334102011 := by
  unfold tailWord_5759073
  simp only [CollatzResearch.WordTrace]
  refine ⟨210050648664869567207393873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140033765776579711471595915 210050648664869567207393873)
  ·
    refine ⟨157537986498652175405545405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210050648664869567207393873 157537986498652175405545405)
    ·
      refine ⟨59076744936994565777079527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157537986498652175405545405 59076744936994565777079527)
      ·
        refine ⟨88615117405491848665619291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59076744936994565777079527 88615117405491848665619291)
        ·
          refine ⟨132922676108237772998428937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88615117405491848665619291 132922676108237772998428937)
          ·
            refine ⟨99692007081178329748821703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132922676108237772998428937 99692007081178329748821703)
            ·
              refine ⟨149538010621767494623232555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99692007081178329748821703 149538010621767494623232555)
              ·
                refine ⟨224307015932651241934848833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149538010621767494623232555 224307015932651241934848833)
                ·
                  refine ⟨168230261949488431451136625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224307015932651241934848833 168230261949488431451136625)
                  ·
                    refine ⟨126172696462116323588352469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168230261949488431451136625 126172696462116323588352469)
                    ·
                      refine ⟨2957172573330851334102011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126172696462116323588352469 2957172573330851334102011)
                      ·
                        rfl

theorem cell23_5759073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5759073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759073 prefixEnd_5759073 := by exact prefixLift 5759073
  have htrace : WordTrace (prefixWord ++ tailWord_5759073) baseStart_5759073 baseEnd_5759073 := by
    simpa [prefixWord, tailWord_5759073, baseEnd_5759073] using wordTrace_append hprefix tailTrace_5759073
  have hstable : (prefixWord ++ tailWord_5759073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759073).length < 2 ^ (prefixWord ++ tailWord_5759073).sum := by decide
  have hdescent : baseEnd_5759073 < baseStart_5759073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759084 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_5759084 : Nat := 118140960795 + 5759084 * 2 ^ 59
def prefixEnd_5759084 : Nat := 4983230072969 + 3 ^ 40 * 5759084 * 2
def baseEnd_5759084 : Nat := 985726073872683597021487

theorem tailTrace_5759084 : CollatzResearch.WordTrace tailWord_5759084 prefixEnd_5759084 985726073872683597021487 := by
  unfold tailWord_5759084
  simp only [CollatzResearch.WordTrace]
  refine ⟨105025524933914858043022153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140034033245219810724029537 105025524933914858043022153)
  ·
    refine ⟨78769143700436143532266615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105025524933914858043022153 78769143700436143532266615)
    ·
      refine ⟨118153715550654215298399923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78769143700436143532266615 118153715550654215298399923)
      ·
        refine ⟨177230573325981322947599885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118153715550654215298399923 177230573325981322947599885)
        ·
          refine ⟨66461464997242996105349957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177230573325981322947599885 66461464997242996105349957)
          ·
            refine ⟨12461524686983061769753117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66461464997242996105349957 12461524686983061769753117)
            ·
              refine ⟨4673071757618648163657419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12461524686983061769753117 4673071757618648163657419)
              ·
                refine ⟨7009607636427972245486129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673071757618648163657419 7009607636427972245486129)
                ·
                  refine ⟨5257205727320979184114597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009607636427972245486129 5257205727320979184114597)
                  ·
                    refine ⟨985726073872683597021487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257205727320979184114597 985726073872683597021487)
                    ·
                      rfl

theorem cell23_5759084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_5759084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759084 prefixEnd_5759084 := by exact prefixLift 5759084
  have htrace : WordTrace (prefixWord ++ tailWord_5759084) baseStart_5759084 baseEnd_5759084 := by
    simpa [prefixWord, tailWord_5759084, baseEnd_5759084] using wordTrace_append hprefix tailTrace_5759084
  have hstable : (prefixWord ++ tailWord_5759084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759084).length < 2 ^ (prefixWord ++ tailWord_5759084).sum := by decide
  have hdescent : baseEnd_5759084 < baseStart_5759084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759087 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_5759087 : Nat := 118140960795 + 5759087 * 2 ^ 59
def prefixEnd_5759087 : Nat := 4983230072969 + 3 ^ 40 * 5759087 * 2
def baseEnd_5759087 : Nat := 2957179762060014279326947

theorem tailTrace_5759087 : CollatzResearch.WordTrace tailWord_5759087 prefixEnd_5759087 2957179762060014279326947 := by
  unfold tailWord_5759087
  simp only [CollatzResearch.WordTrace]
  refine ⟨210051159286818847598403515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140034106191212565065602343 210051159286818847598403515)
  ·
    refine ⟨315076738930228271397605273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210051159286818847598403515 315076738930228271397605273)
    ·
      refine ⟨236307554197671203548203955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315076738930228271397605273 236307554197671203548203955)
      ·
        refine ⟨354461331296506805322305933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236307554197671203548203955 354461331296506805322305933)
        ·
          refine ⟨132922999236190051995864725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354461331296506805322305933 132922999236190051995864725)
          ·
            refine ⟨6230765589196408687306159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132922999236190051995864725 6230765589196408687306159)
            ·
              refine ⟨9346148383794613030959239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230765589196408687306159 9346148383794613030959239)
              ·
                refine ⟨14019222575691919546438859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9346148383794613030959239 14019222575691919546438859)
                ·
                  refine ⟨21028833863537879319658289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14019222575691919546438859 21028833863537879319658289)
                  ·
                    refine ⟨15771625397653409489743717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21028833863537879319658289 15771625397653409489743717)
                    ·
                      refine ⟨2957179762060014279326947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15771625397653409489743717 2957179762060014279326947)
                      ·
                        rfl

theorem cell23_5759087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_5759087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759087 prefixEnd_5759087 := by exact prefixLift 5759087
  have htrace : WordTrace (prefixWord ++ tailWord_5759087) baseStart_5759087 baseEnd_5759087 := by
    simpa [prefixWord, tailWord_5759087, baseEnd_5759087] using wordTrace_append hprefix tailTrace_5759087
  have hstable : (prefixWord ++ tailWord_5759087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759087).length < 2 ^ (prefixWord ++ tailWord_5759087).sum := by decide
  have hdescent : baseEnd_5759087 < baseStart_5759087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759094 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5759094 : Nat := 118140960795 + 5759094 * 2 ^ 59
def prefixEnd_5759094 : Nat := 4983230072969 + 3 ^ 40 * 5759094 * 2
def baseEnd_5759094 : Nat := 2957183356424595751939415

theorem tailTrace_5759094 : CollatzResearch.WordTrace tailWord_5759094 prefixEnd_5759094 2957183356424595751939415 := by
  unfold tailWord_5759094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128213412362092987119271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140034276398528991862605557 13128213412362092987119271)
  ·
    refine ⟨19692320118543139480678907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128213412362092987119271 19692320118543139480678907)
    ·
      refine ⟨29538480177814709221018361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692320118543139480678907 29538480177814709221018361)
      ·
        refine ⟨22153860133361031915763771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29538480177814709221018361 22153860133361031915763771)
        ·
          refine ⟨33230790200041547873645657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22153860133361031915763771 33230790200041547873645657)
          ·
            refine ⟨24923092650031160905234243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33230790200041547873645657 24923092650031160905234243)
            ·
              refine ⟨37384638975046741357851365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24923092650031160905234243 37384638975046741357851365)
              ·
                refine ⟨7009619807821264004597131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37384638975046741357851365 7009619807821264004597131)
                ·
                  refine ⟨10514429711731896006895697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009619807821264004597131 10514429711731896006895697)
                  ·
                    refine ⟨7885822283798922005171773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10514429711731896006895697 7885822283798922005171773)
                    ·
                      refine ⟨2957183356424595751939415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885822283798922005171773 2957183356424595751939415)
                      ·
                        rfl

theorem cell23_5759094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5759094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759094 prefixEnd_5759094 := by exact prefixLift 5759094
  have htrace : WordTrace (prefixWord ++ tailWord_5759094) baseStart_5759094 baseEnd_5759094 := by
    simpa [prefixWord, tailWord_5759094, baseEnd_5759094] using wordTrace_append hprefix tailTrace_5759094
  have hstable : (prefixWord ++ tailWord_5759094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759094).length < 2 ^ (prefixWord ++ tailWord_5759094).sum := by decide
  have hdescent : baseEnd_5759094 < baseStart_5759094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759097 : List Nat := [1, 2, 1, 3, 4, 3, 2, 7]
def baseStart_5759097 : Nat := 118140960795 + 5759097 * 2 ^ 59
def prefixEnd_5759097 : Nat := 4983230072969 + 3 ^ 40 * 5759097 * 2
def baseEnd_5759097 : Nat := 109525366550613305192663

theorem tailTrace_5759097 : CollatzResearch.WordTrace tailWord_5759097 prefixEnd_5759097 109525366550613305192663 := by
  unfold tailWord_5759097
  simp only [CollatzResearch.WordTrace]
  refine ⟨210051524016782619306267545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140034349344521746204178363 210051524016782619306267545)
  ·
    refine ⟨157538643012586964479700659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210051524016782619306267545 157538643012586964479700659)
    ·
      refine ⟨236307964518880446719550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157538643012586964479700659 236307964518880446719550989)
      ·
        refine ⟨88615486694580167519831621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236307964518880446719550989 88615486694580167519831621)
        ·
          refine ⟨16615403755233781409968429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88615486694580167519831621 16615403755233781409968429)
          ·
            refine ⟨6230776408212668028738161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16615403755233781409968429 6230776408212668028738161)
            ·
              refine ⟨4673082306159501021553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230776408212668028738161 4673082306159501021553621)
              ·
                refine ⟨109525366550613305192663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4673082306159501021553621 109525366550613305192663)
                ·
                  rfl

theorem cell23_5759097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 7].length) (baseStart_5759097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759097 prefixEnd_5759097 := by exact prefixLift 5759097
  have htrace : WordTrace (prefixWord ++ tailWord_5759097) baseStart_5759097 baseEnd_5759097 := by
    simpa [prefixWord, tailWord_5759097, baseEnd_5759097] using wordTrace_append hprefix tailTrace_5759097
  have hstable : (prefixWord ++ tailWord_5759097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759097).length < 2 ^ (prefixWord ++ tailWord_5759097).sum := by decide
  have hdescent : baseEnd_5759097 < baseStart_5759097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759107 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 3]
def baseStart_5759107 : Nat := 118140960795 + 5759107 * 2 ^ 59
def prefixEnd_5759107 : Nat := 4983230072969 + 3 ^ 40 * 5759107 * 2
def baseEnd_5759107 : Nat := 2957190031673104201076855

theorem tailTrace_5759107 : CollatzResearch.WordTrace tailWord_5759107 prefixEnd_5759107 2957190031673104201076855 := by
  unfold tailWord_5759107
  simp only [CollatzResearch.WordTrace]
  refine ⟨210051888746746391014131575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140034592497830927342754383 210051888746746391014131575)
  ·
    refine ⟨315077833120119586521197363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210051888746746391014131575 315077833120119586521197363)
    ·
      refine ⟨472616749680179379781796045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315077833120119586521197363 472616749680179379781796045)
      ·
        refine ⟨177231281130067267418173517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472616749680179379781796045 177231281130067267418173517)
        ·
          refine ⟨66461730423775225281815069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177231281130067267418173517 66461730423775225281815069)
          ·
            refine ⟨24923148908915709480680651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66461730423775225281815069 24923148908915709480680651)
            ·
              refine ⟨37384723363373564221020977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24923148908915709480680651 37384723363373564221020977)
              ·
                refine ⟨28038542522530173165765733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37384723363373564221020977 28038542522530173165765733)
                ·
                  refine ⟨5257226722974407468581075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28038542522530173165765733 5257226722974407468581075)
                  ·
                    refine ⟨7885840084461611202871613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257226722974407468581075 7885840084461611202871613)
                    ·
                      refine ⟨2957190031673104201076855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7885840084461611202871613 2957190031673104201076855)
                      ·
                        rfl

theorem cell23_5759107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_5759107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759107 prefixEnd_5759107 := by exact prefixLift 5759107
  have htrace : WordTrace (prefixWord ++ tailWord_5759107) baseStart_5759107 baseEnd_5759107 := by
    simpa [prefixWord, tailWord_5759107, baseEnd_5759107] using wordTrace_append hprefix tailTrace_5759107
  have hstable : (prefixWord ++ tailWord_5759107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759107).length < 2 ^ (prefixWord ++ tailWord_5759107).sum := by decide
  have hdescent : baseEnd_5759107 < baseStart_5759107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759200 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_5759200 : Nat := 118140960795 + 5759200 * 2 ^ 59
def prefixEnd_5759200 : Nat := 4983230072969 + 3 ^ 40 * 5759200 * 2
def baseEnd_5759200 : Nat := 985745928457990779071309

theorem tailTrace_5759200 : CollatzResearch.WordTrace tailWord_5759200 prefixEnd_5759200 985745928457990779071309 := by
  unfold tailWord_5759200
  simp only [CollatzResearch.WordTrace]
  refine ⟨105027640367704733948633527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140036853823606311931511369 105027640367704733948633527)
  ·
    refine ⟨157541460551557100922950291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105027640367704733948633527 157541460551557100922950291)
    ·
      refine ⟨236312190827335651384425437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157541460551557100922950291 236312190827335651384425437)
      ·
        refine ⟨88617071560250869269159539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236312190827335651384425437 88617071560250869269159539)
        ·
          refine ⟨132925607340376303903739309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88617071560250869269159539 132925607340376303903739309)
          ·
            refine ⟨49847102752641113963902241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132925607340376303903739309 49847102752641113963902241)
            ·
              refine ⟨37385327064480835472926681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49847102752641113963902241 37385327064480835472926681)
              ·
                refine ⟨28038995298360626604695011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37385327064480835472926681 28038995298360626604695011)
                ·
                  refine ⟨42058492947540939907042517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28038995298360626604695011 42058492947540939907042517)
                  ·
                    refine ⟨985745928457990779071309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42058492947540939907042517 985745928457990779071309)
                    ·
                      rfl

theorem cell23_5759200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_5759200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759200 prefixEnd_5759200 := by exact prefixLift 5759200
  have htrace : WordTrace (prefixWord ++ tailWord_5759200) baseStart_5759200 baseEnd_5759200 := by
    simpa [prefixWord, tailWord_5759200, baseEnd_5759200] using wordTrace_append hprefix tailTrace_5759200
  have hstable : (prefixWord ++ tailWord_5759200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759200).length < 2 ^ (prefixWord ++ tailWord_5759200).sum := by decide
  have hdescent : baseEnd_5759200 < baseStart_5759200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759217 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_5759217 : Nat := 118140960795 + 5759217 * 2 ^ 59
def prefixEnd_5759217 : Nat := 4983230072969 + 3 ^ 40 * 5759217 * 2
def baseEnd_5759217 : Nat := 985748838181699590233783

theorem tailTrace_5759217 : CollatzResearch.WordTrace tailWord_5759217 prefixEnd_5759217 985748838181699590233783 := by
  unfold tailWord_5759217
  simp only [CollatzResearch.WordTrace]
  refine ⟨210055900776347879800635905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140037267184231919867090603 210055900776347879800635905)
  ·
    refine ⟨157541925582260909850476929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210055900776347879800635905 157541925582260909850476929)
    ·
      refine ⟨118156444186695682387857697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157541925582260909850476929 118156444186695682387857697)
      ·
        refine ⟨88617333140021761790893273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118156444186695682387857697 88617333140021761790893273)
        ·
          refine ⟨66462999855016321343169955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88617333140021761790893273 66462999855016321343169955)
          ·
            refine ⟨99694499782524482014754933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66462999855016321343169955 99694499782524482014754933)
            ·
              refine ⟨9346359354611670188883275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99694499782524482014754933 9346359354611670188883275)
              ·
                refine ⟨14019539031917505283324913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9346359354611670188883275 14019539031917505283324913)
                ·
                  refine ⟨10514654273938128962493685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14019539031917505283324913 10514654273938128962493685)
                  ·
                    refine ⟨985748838181699590233783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10514654273938128962493685 985748838181699590233783)
                    ·
                      rfl

theorem cell23_5759217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_5759217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759217 prefixEnd_5759217 := by exact prefixLift 5759217
  have htrace : WordTrace (prefixWord ++ tailWord_5759217) baseStart_5759217 baseEnd_5759217 := by
    simpa [prefixWord, tailWord_5759217, baseEnd_5759217] using wordTrace_append hprefix tailTrace_5759217
  have hstable : (prefixWord ++ tailWord_5759217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759217).length < 2 ^ (prefixWord ++ tailWord_5759217).sum := by decide
  have hdescent : baseEnd_5759217 < baseStart_5759217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759264 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_5759264 : Nat := 118140960795 + 5759264 * 2 ^ 59
def prefixEnd_5759264 : Nat := 4983230072969 + 3 ^ 40 * 5759264 * 2
def baseEnd_5759264 : Nat := 985756882711953362271211

theorem tailTrace_5759264 : CollatzResearch.WordTrace tailWord_5759264 prefixEnd_5759264 985756882711953362271211 := by
  unfold tailWord_5759264
  simp only [CollatzResearch.WordTrace]
  refine ⟨105028807503588803413798423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140038410004785071218397897 105028807503588803413798423)
  ·
    refine ⟨157543211255383205120697635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105028807503588803413798423 157543211255383205120697635)
    ·
      refine ⟨236314816883074807681046453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157543211255383205120697635 236314816883074807681046453)
      ·
        refine ⟨22154514082788263220098105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236314816883074807681046453 22154514082788263220098105)
        ·
          refine ⟨16615885562091197415073579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22154514082788263220098105 16615885562091197415073579)
          ·
            refine ⟨24923828343136796122610369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16615885562091197415073579 24923828343136796122610369)
            ·
              refine ⟨18692871257352597091957777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24923828343136796122610369 18692871257352597091957777)
              ·
                refine ⟨14019653443014447818968333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18692871257352597091957777 14019653443014447818968333)
                ·
                  refine ⟨5257370041130417932113125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14019653443014447818968333 5257370041130417932113125)
                  ·
                    refine ⟨985756882711953362271211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257370041130417932113125 985756882711953362271211)
                    ·
                      rfl

theorem cell23_5759264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_5759264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759264 prefixEnd_5759264 := by exact prefixLift 5759264
  have htrace : WordTrace (prefixWord ++ tailWord_5759264) baseStart_5759264 baseEnd_5759264 := by
    simpa [prefixWord, tailWord_5759264, baseEnd_5759264] using wordTrace_append hprefix tailTrace_5759264
  have hstable : (prefixWord ++ tailWord_5759264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759264).length < 2 ^ (prefixWord ++ tailWord_5759264).sum := by decide
  have hdescent : baseEnd_5759264 < baseStart_5759264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_5759280 : Nat := 118140960795 + 5759280 * 2 ^ 59
def prefixEnd_5759280 : Nat := 4983230072969 + 3 ^ 40 * 5759280 * 2
def baseEnd_5759280 : Nat := 2957278863826332024213559

theorem tailTrace_5759280 : CollatzResearch.WordTrace tailWord_5759280 prefixEnd_5759280 2957278863826332024213559 := by
  unfold tailWord_5759280
  simp only [CollatzResearch.WordTrace]
  refine ⟨105029099287559820780089647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140038799050079761040119529 105029099287559820780089647)
  ·
    refine ⟨157543648931339731170134471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105029099287559820780089647 157543648931339731170134471)
    ·
      refine ⟨236315473397009596755201707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157543648931339731170134471 236315473397009596755201707)
      ·
        refine ⟨354473210095514395132802561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236315473397009596755201707 354473210095514395132802561)
        ·
          refine ⟨265854907571635796349601921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354473210095514395132802561 265854907571635796349601921)
          ·
            refine ⟨199391180678726847262201441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265854907571635796349601921 199391180678726847262201441)
            ·
              refine ⟨149543385509045135446651081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199391180678726847262201441 149543385509045135446651081)
              ·
                refine ⟨112157539131783851584988311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149543385509045135446651081 112157539131783851584988311)
                ·
                  refine ⟨168236308697675777377482467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112157539131783851584988311 168236308697675777377482467)
                  ·
                    refine ⟨252354463046513666066223701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168236308697675777377482467 252354463046513666066223701)
                    ·
                      refine ⟨2957278863826332024213559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 252354463046513666066223701 2957278863826332024213559)
                      ·
                        rfl

theorem cell23_5759280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_5759280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759280 prefixEnd_5759280 := by exact prefixLift 5759280
  have htrace : WordTrace (prefixWord ++ tailWord_5759280) baseStart_5759280 baseEnd_5759280 := by
    simpa [prefixWord, tailWord_5759280, baseEnd_5759280] using wordTrace_append hprefix tailTrace_5759280
  have hstable : (prefixWord ++ tailWord_5759280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759280).length < 2 ^ (prefixWord ++ tailWord_5759280).sum := by decide
  have hdescent : baseEnd_5759280 < baseStart_5759280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759314 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_5759314 : Nat := 118140960795 + 5759314 * 2 ^ 59
def prefixEnd_5759314 : Nat := 4983230072969 + 3 ^ 40 * 5759314 * 2
def baseEnd_5759314 : Nat := 2957296322168584891188403

theorem tailTrace_5759314 : CollatzResearch.WordTrace tailWord_5759314 prefixEnd_5759314 2957296322168584891188403 := by
  unfold tailWord_5759314
  simp only [CollatzResearch.WordTrace]
  refine ⟨52514859664249116341729249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140039625771330976911277997 52514859664249116341729249)
  ·
    refine ⟨39386144748186837256296937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52514859664249116341729249 39386144748186837256296937)
    ·
      refine ⟨29539608561140127942222703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39386144748186837256296937 29539608561140127942222703)
      ·
        refine ⟨44309412841710191913334055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29539608561140127942222703 44309412841710191913334055)
        ·
          refine ⟨66464119262565287870001083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44309412841710191913334055 66464119262565287870001083)
          ·
            refine ⟨99696178893847931805001625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66464119262565287870001083 99696178893847931805001625)
            ·
              refine ⟨74772134170385948853751219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99696178893847931805001625 74772134170385948853751219)
              ·
                refine ⟨112158201255578923280626829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74772134170385948853751219 112158201255578923280626829)
                ·
                  refine ⟨42059325470842096230235061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112158201255578923280626829 42059325470842096230235061)
                  ·
                    refine ⟨3943061762891446521584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42059325470842096230235061 3943061762891446521584537)
                    ·
                      refine ⟨2957296322168584891188403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943061762891446521584537 2957296322168584891188403)
                      ·
                        rfl

theorem cell23_5759314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_5759314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759314 prefixEnd_5759314 := by exact prefixLift 5759314
  have htrace : WordTrace (prefixWord ++ tailWord_5759314) baseStart_5759314 baseEnd_5759314 := by
    simpa [prefixWord, tailWord_5759314, baseEnd_5759314] using wordTrace_append hprefix tailTrace_5759314
  have hstable : (prefixWord ++ tailWord_5759314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759314).length < 2 ^ (prefixWord ++ tailWord_5759314).sum := by decide
  have hdescent : baseEnd_5759314 < baseStart_5759314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759331 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5759331 : Nat := 118140960795 + 5759331 * 2 ^ 59
def prefixEnd_5759331 : Nat := 4983230072969 + 3 ^ 40 * 5759331 * 2
def baseEnd_5759331 : Nat := 2957305051339711324675825

theorem tailTrace_5759331 : CollatzResearch.WordTrace tailWord_5759331 prefixEnd_5759331 2957305051339711324675825 := by
  unfold tailWord_5759331
  simp only [CollatzResearch.WordTrace]
  refine ⟨210060058697934877270285847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140040039131956584846857231 210060058697934877270285847)
  ·
    refine ⟨315090088046902315905428771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210060058697934877270285847 315090088046902315905428771)
    ·
      refine ⟨472635132070353473858143157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315090088046902315905428771 472635132070353473858143157)
      ·
        refine ⟨44309543631595638174200921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 472635132070353473858143157 44309543631595638174200921)
        ·
          refine ⟨33232157723696728630650691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44309543631595638174200921 33232157723696728630650691)
          ·
            refine ⟨49848236585545092945976037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33232157723696728630650691 49848236585545092945976037)
            ·
              refine ⟨9346544359789704927370507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49848236585545092945976037 9346544359789704927370507)
              ·
                refine ⟨14019816539684557391055761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9346544359789704927370507 14019816539684557391055761)
                ·
                  refine ⟨10514862404763418043291821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14019816539684557391055761 10514862404763418043291821)
                  ·
                    refine ⟨3943073401786281766234433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10514862404763418043291821 3943073401786281766234433)
                    ·
                      refine ⟨2957305051339711324675825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943073401786281766234433 2957305051339711324675825)
                      ·
                        rfl

theorem cell23_5759331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5759331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759331 prefixEnd_5759331 := by exact prefixLift 5759331
  have htrace : WordTrace (prefixWord ++ tailWord_5759331) baseStart_5759331 baseEnd_5759331 := by
    simpa [prefixWord, tailWord_5759331, baseEnd_5759331] using wordTrace_append hprefix tailTrace_5759331
  have hstable : (prefixWord ++ tailWord_5759331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759331).length < 2 ^ (prefixWord ++ tailWord_5759331).sum := by decide
  have hdescent : baseEnd_5759331 < baseStart_5759331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759337 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_5759337 : Nat := 118140960795 + 5759337 * 2 ^ 59
def prefixEnd_5759337 : Nat := 4983230072969 + 3 ^ 40 * 5759337 * 2
def baseEnd_5759337 : Nat := 985769377407879433733599

theorem tailTrace_5759337 : CollatzResearch.WordTrace tailWord_5759337 prefixEnd_5759337 985769377407879433733599 := by
  unfold tailWord_5759337
  simp only [CollatzResearch.WordTrace]
  refine ⟨210060277535913140295004265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140040185023942093530002843 210060277535913140295004265)
  ·
    refine ⟨157545208151934855221253199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210060277535913140295004265 157545208151934855221253199)
    ·
      refine ⟨236317812227902282831879799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157545208151934855221253199 236317812227902282831879799)
      ·
        refine ⟨354476718341853424247819699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236317812227902282831879799 354476718341853424247819699)
        ·
          refine ⟨531715077512780136371729549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354476718341853424247819699 531715077512780136371729549)
          ·
            refine ⟨199393154067292551139398581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531715077512780136371729549 199393154067292551139398581)
            ·
              refine ⟨18693108193808676669318617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199393154067292551139398581 18693108193808676669318617)
              ·
                refine ⟨14019831145356507501988963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18693108193808676669318617 14019831145356507501988963)
                ·
                  refine ⟨21029746718034761252983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14019831145356507501988963 21029746718034761252983445)
                  ·
                    refine ⟨985769377407879433733599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21029746718034761252983445 985769377407879433733599)
                    ·
                      rfl

theorem cell23_5759337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_5759337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759337 prefixEnd_5759337 := by exact prefixLift 5759337
  have htrace : WordTrace (prefixWord ++ tailWord_5759337) baseStart_5759337 baseEnd_5759337 := by
    simpa [prefixWord, tailWord_5759337, baseEnd_5759337] using wordTrace_append hprefix tailTrace_5759337
  have hstable : (prefixWord ++ tailWord_5759337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759337).length < 2 ^ (prefixWord ++ tailWord_5759337).sum := by decide
  have hdescent : baseEnd_5759337 < baseStart_5759337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
