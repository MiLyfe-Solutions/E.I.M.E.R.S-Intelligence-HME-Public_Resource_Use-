import V185TrunkScan23Chunk1147

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6799570 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_6799570 : Nat := 118140960795 + 6799570 * 2 ^ 59
def prefixEnd_6799570 : Nat := 4983230072969 + 3 ^ 40 * 6799570 * 2
def baseEnd_6799570 : Nat := 1163815884630688961601451

theorem tailTrace_6799570 : CollatzResearch.WordTrace tailWord_6799570 prefixEnd_6799570 1163815884630688961601451 := by
  unfold tailWord_6799570
  simp only [CollatzResearch.WordTrace]
  refine ⟨62000172994081659736839041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165333794650884425964904109 62000172994081659736839041)
  ·
    refine ⟨46500129745561244802629281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62000172994081659736839041 46500129745561244802629281)
    ·
      refine ⟨34875097309170933601971961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46500129745561244802629281 34875097309170933601971961)
      ·
        refine ⟨26156322981878200201478971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34875097309170933601971961 26156322981878200201478971)
        ·
          refine ⟨39234484472817300302218457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26156322981878200201478971 39234484472817300302218457)
          ·
            refine ⟨29425863354612975226663843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39234484472817300302218457 29425863354612975226663843)
            ·
              refine ⟨44138795031919462839995765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29425863354612975226663843 44138795031919462839995765)
              ·
                refine ⟨4138012034242449641249603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44138795031919462839995765 4138012034242449641249603)
                ·
                  refine ⟨6207018051363674461874405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138012034242449641249603 6207018051363674461874405)
                  ·
                    refine ⟨1163815884630688961601451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207018051363674461874405 1163815884630688961601451)
                    ·
                      rfl

theorem cell23_6799570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_6799570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799570 prefixEnd_6799570 := by exact prefixLift 6799570
  have htrace : WordTrace (prefixWord ++ tailWord_6799570) baseStart_6799570 baseEnd_6799570 := by
    simpa [prefixWord, tailWord_6799570, baseEnd_6799570] using wordTrace_append hprefix tailTrace_6799570
  have hstable : (prefixWord ++ tailWord_6799570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799570).length < 2 ^ (prefixWord ++ tailWord_6799570).sum := by decide
  have hdescent : baseEnd_6799570 < baseStart_6799570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799606 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6799606 : Nat := 118140960795 + 6799606 * 2 ^ 59
def prefixEnd_6799606 : Nat := 4983230072969 + 3 ^ 40 * 6799606 * 2
def baseEnd_6799606 : Nat := 3491466139195628743954187

theorem tailTrace_6799606 : CollatzResearch.WordTrace tailWord_6799606 prefixEnd_6799606 3491466139195628743954187 := by
  unfold tailWord_6799606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500125312762263568479167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165334670002797478063777781 15500125312762263568479167)
  ·
    refine ⟨23250187969143395352718751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15500125312762263568479167 23250187969143395352718751)
    ·
      refine ⟨34875281953715093029078127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23250187969143395352718751 34875281953715093029078127)
      ·
        refine ⟨52312922930572639543617191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34875281953715093029078127 52312922930572639543617191)
        ·
          refine ⟨78469384395858959315425787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52312922930572639543617191 78469384395858959315425787)
          ·
            refine ⟨117704076593788438973138681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78469384395858959315425787 117704076593788438973138681)
            ·
              refine ⟨88278057445341329229854011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117704076593788438973138681 88278057445341329229854011)
              ·
                refine ⟨132417086168011993844781017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88278057445341329229854011 132417086168011993844781017)
                ·
                  refine ⟨99312814626008995383585763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132417086168011993844781017 99312814626008995383585763)
                  ·
                    refine ⟨148969221939013493075378645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99312814626008995383585763 148969221939013493075378645)
                    ·
                      refine ⟨3491466139195628743954187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148969221939013493075378645 3491466139195628743954187)
                      ·
                        rfl

theorem cell23_6799606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6799606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799606 prefixEnd_6799606 := by exact prefixLift 6799606
  have htrace : WordTrace (prefixWord ++ tailWord_6799606) baseStart_6799606 baseEnd_6799606 := by
    simpa [prefixWord, tailWord_6799606, baseEnd_6799606] using wordTrace_append hprefix tailTrace_6799606
  have hstable : (prefixWord ++ tailWord_6799606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799606).length < 2 ^ (prefixWord ++ tailWord_6799606).sum := by decide
  have hdescent : baseEnd_6799606 < baseStart_6799606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799616 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_6799616 : Nat := 118140960795 + 6799616 * 2 ^ 59
def prefixEnd_6799616 : Nat := 4983230072969 + 3 ^ 40 * 6799616 * 2
def baseEnd_6799616 : Nat := 3491471274002173704829141

theorem tailTrace_6799616 : CollatzResearch.WordTrace tailWord_6799616 prefixEnd_6799616 3491471274002173704829141 := by
  unfold tailWord_6799616
  simp only [CollatzResearch.WordTrace]
  refine ⟨124001184867079994401765351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165334913156106659202353801 124001184867079994401765351)
  ·
    refine ⟨186001777300619991602648027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124001184867079994401765351 186001777300619991602648027)
    ·
      refine ⟨279002665950929987403972041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186001777300619991602648027 279002665950929987403972041)
      ·
        refine ⟨209251999463197490552979031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279002665950929987403972041 209251999463197490552979031)
        ·
          refine ⟨313877999194796235829468547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209251999463197490552979031 313877999194796235829468547)
          ·
            refine ⟨470816998792194353744202821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313877999194796235829468547 470816998792194353744202821)
            ·
              refine ⟨88278187273536441327038029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 470816998792194353744202821 88278187273536441327038029)
              ·
                refine ⟨33104320227576165497639261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88278187273536441327038029 33104320227576165497639261)
                ·
                  refine ⟨12414120085341062061614723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33104320227576165497639261 12414120085341062061614723)
                  ·
                    refine ⟨18621180128011593092422085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414120085341062061614723 18621180128011593092422085)
                    ·
                      refine ⟨3491471274002173704829141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18621180128011593092422085 3491471274002173704829141)
                      ·
                        rfl

theorem cell23_6799616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_6799616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799616 prefixEnd_6799616 := by exact prefixLift 6799616
  have htrace : WordTrace (prefixWord ++ tailWord_6799616) baseStart_6799616 baseEnd_6799616 := by
    simpa [prefixWord, tailWord_6799616, baseEnd_6799616] using wordTrace_append hprefix tailTrace_6799616
  have hstable : (prefixWord ++ tailWord_6799616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799616).length < 2 ^ (prefixWord ++ tailWord_6799616).sum := by decide
  have hdescent : baseEnd_6799616 < baseStart_6799616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799626 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_6799626 : Nat := 118140960795 + 6799626 * 2 ^ 59
def prefixEnd_6799626 : Nat := 4983230072969 + 3 ^ 40 * 6799626 * 2
def baseEnd_6799626 : Nat := 1163825469602906221901365

theorem tailTrace_6799626 : CollatzResearch.WordTrace tailWord_6799626 prefixEnd_6799626 1163825469602906221901365 := by
  unfold tailWord_6799626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62000683616030940127848683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165335156309415840340929821 62000683616030940127848683)
  ·
    refine ⟨93001025424046410191773025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62000683616030940127848683 93001025424046410191773025)
    ·
      refine ⟨69750769068034807643829769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93001025424046410191773025 69750769068034807643829769)
      ·
        refine ⟨52313076801026105732872327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69750769068034807643829769 52313076801026105732872327)
        ·
          refine ⟨78469615201539158599308491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52313076801026105732872327 78469615201539158599308491)
          ·
            refine ⟨117704422802308737898962737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78469615201539158599308491 117704422802308737898962737)
            ·
              refine ⟨88278317101731553424222053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117704422802308737898962737 88278317101731553424222053)
              ·
                refine ⟨16552184456574666267041635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88278317101731553424222053 16552184456574666267041635)
                ·
                  refine ⟨24828276684861999400562453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16552184456574666267041635 24828276684861999400562453)
                  ·
                    refine ⟨1163825469602906221901365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24828276684861999400562453 1163825469602906221901365)
                    ·
                      rfl

theorem cell23_6799626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_6799626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799626 prefixEnd_6799626 := by exact prefixLift 6799626
  have htrace : WordTrace (prefixWord ++ tailWord_6799626) baseStart_6799626 baseEnd_6799626 := by
    simpa [prefixWord, tailWord_6799626, baseEnd_6799626] using wordTrace_append hprefix tailTrace_6799626
  have hstable : (prefixWord ++ tailWord_6799626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799626).length < 2 ^ (prefixWord ++ tailWord_6799626).sum := by decide
  have hdescent : baseEnd_6799626 < baseStart_6799626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799633 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_6799633 : Nat := 118140960795 + 6799633 * 2 ^ 59
def prefixEnd_6799633 : Nat := 4983230072969 + 3 ^ 40 * 6799633 * 2
def baseEnd_6799633 : Nat := 3491480003173300138316563

theorem tailTrace_6799633 : CollatzResearch.WordTrace tailWord_6799633 prefixEnd_6799633 3491480003173300138316563 := by
  unfold tailWord_6799633
  simp only [CollatzResearch.WordTrace]
  refine ⟨248002989775098400706899553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165335326516732267137933035 248002989775098400706899553)
  ·
    refine ⟨186002242331323800530174665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248002989775098400706899553 186002242331323800530174665)
    ·
      refine ⟨139501681748492850397630999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186002242331323800530174665 139501681748492850397630999)
      ·
        refine ⟨209252522622739275596446499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139501681748492850397630999 209252522622739275596446499)
        ·
          refine ⟨313878783934108913394669749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209252522622739275596446499 313878783934108913394669749)
          ·
            refine ⟨29426135993822710630750289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313878783934108913394669749 29426135993822710630750289)
            ·
              refine ⟨22069601995367032973062717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29426135993822710630750289 22069601995367032973062717)
              ·
                refine ⟨8276100748262637364898519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22069601995367032973062717 8276100748262637364898519)
                ·
                  refine ⟨12414151122393956047347779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276100748262637364898519 12414151122393956047347779)
                  ·
                    refine ⟨18621226683590934071021669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414151122393956047347779 18621226683590934071021669)
                    ·
                      refine ⟨3491480003173300138316563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18621226683590934071021669 3491480003173300138316563)
                      ·
                        rfl

theorem cell23_6799633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_6799633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799633 prefixEnd_6799633 := by exact prefixLift 6799633
  have htrace : WordTrace (prefixWord ++ tailWord_6799633) baseStart_6799633 baseEnd_6799633 := by
    simpa [prefixWord, tailWord_6799633, baseEnd_6799633] using wordTrace_append hprefix tailTrace_6799633
  have hstable : (prefixWord ++ tailWord_6799633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799633).length < 2 ^ (prefixWord ++ tailWord_6799633).sum := by decide
  have hdescent : baseEnd_6799633 < baseStart_6799633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799660 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_6799660 : Nat := 118140960795 + 6799660 * 2 ^ 59
def prefixEnd_6799660 : Nat := 4983230072969 + 3 ^ 40 * 6799660 * 2
def baseEnd_6799660 : Nat := 1163831289050323844226313

theorem tailTrace_6799660 : CollatzResearch.WordTrace tailWord_6799660 prefixEnd_6799660 1163831289050323844226313 := by
  unfold tailWord_6799660
  simp only [CollatzResearch.WordTrace]
  refine ⟨124001987273000292159066217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165335983030667056212088289 124001987273000292159066217)
  ·
    refine ⟨93001490454750219119299663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124001987273000292159066217 93001490454750219119299663)
    ·
      refine ⟨139502235682125328678949495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93001490454750219119299663 139502235682125328678949495)
      ·
        refine ⟨209253353523187993018424243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139502235682125328678949495 209253353523187993018424243)
        ·
          refine ⟨313880030284781989527636365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209253353523187993018424243 313880030284781989527636365)
          ·
            refine ⟨117705011356793246072863637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313880030284781989527636365 117705011356793246072863637)
            ·
              refine ⟨5517422407349683409665483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117705011356793246072863637 5517422407349683409665483)
              ·
                refine ⟨8276133611024525114498225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517422407349683409665483 8276133611024525114498225)
                ·
                  refine ⟨6207100208268393835873669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276133611024525114498225 6207100208268393835873669)
                  ·
                    refine ⟨1163831289050323844226313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207100208268393835873669 1163831289050323844226313)
                    ·
                      rfl

theorem cell23_6799660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_6799660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799660 prefixEnd_6799660 := by exact prefixLift 6799660
  have htrace : WordTrace (prefixWord ++ tailWord_6799660) baseStart_6799660 baseEnd_6799660 := by
    simpa [prefixWord, tailWord_6799660, baseEnd_6799660] using wordTrace_append hprefix tailTrace_6799660
  have hstable : (prefixWord ++ tailWord_6799660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799660).length < 2 ^ (prefixWord ++ tailWord_6799660).sum := by decide
  have hdescent : baseEnd_6799660 < baseStart_6799660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799683 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 3]
def baseStart_6799683 : Nat := 118140960795 + 6799683 * 2 ^ 59
def prefixEnd_6799683 : Nat := 4983230072969 + 3 ^ 40 * 6799683 * 2
def baseEnd_6799683 : Nat := 3491505677206024942691333

theorem tailTrace_6799683 : CollatzResearch.WordTrace tailWord_6799683 prefixEnd_6799683 3491505677206024942691333 := by
  unfold tailWord_6799683
  simp only [CollatzResearch.WordTrace]
  refine ⟨248004813424917259246219703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165336542283278172830813135 248004813424917259246219703)
  ·
    refine ⟨372007220137375888869329555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248004813424917259246219703 372007220137375888869329555)
    ·
      refine ⟨558010830206063833303994333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372007220137375888869329555 558010830206063833303994333)
      ·
        refine ⟨209254061327273937488997875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558010830206063833303994333 209254061327273937488997875)
        ·
          refine ⟨313881091990910906233496813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209254061327273937488997875 313881091990910906233496813)
          ·
            refine ⟨117705409496591589837561305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313881091990910906233496813 117705409496591589837561305)
            ·
              refine ⟨88279057122443692378170979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117705409496591589837561305 88279057122443692378170979)
              ·
                refine ⟨132418585683665538567256469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88279057122443692378170979 132418585683665538567256469)
                ·
                  refine ⟨6207121203921822120340147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132418585683665538567256469 6207121203921822120340147)
                  ·
                    refine ⟨9310681805882733180510221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207121203921822120340147 9310681805882733180510221)
                    ·
                      refine ⟨3491505677206024942691333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310681805882733180510221 3491505677206024942691333)
                      ·
                        rfl

theorem cell23_6799683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_6799683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799683 prefixEnd_6799683 := by exact prefixLift 6799683
  have htrace : WordTrace (prefixWord ++ tailWord_6799683) baseStart_6799683 baseEnd_6799683 := by
    simpa [prefixWord, tailWord_6799683, baseEnd_6799683] using wordTrace_append hprefix tailTrace_6799683
  have hstable : (prefixWord ++ tailWord_6799683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799683).length < 2 ^ (prefixWord ++ tailWord_6799683).sum := by decide
  have hdescent : baseEnd_6799683 < baseStart_6799683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799684 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6799684 : Nat := 118140960795 + 6799684 * 2 ^ 59
def prefixEnd_6799684 : Nat := 4983230072969 + 3 ^ 40 * 6799684 * 2
def baseEnd_6799684 : Nat := 3491506190686679438778829

theorem tailTrace_6799684 : CollatzResearch.WordTrace tailWord_6799684 prefixEnd_6799684 3491506190686679438778829 := by
  unfold tailWord_6799684
  simp only [CollatzResearch.WordTrace]
  refine ⟨124002424948956818208503053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165336566598609090944670737 124002424948956818208503053)
  ·
    refine ⟨46500909355858806828188645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124002424948956818208503053 46500909355858806828188645)
    ·
      refine ⟨8718920504223526280285371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46500909355858806828188645 8718920504223526280285371)
      ·
        refine ⟨13078380756335289420428057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718920504223526280285371 13078380756335289420428057)
        ·
          refine ⟨9808785567251467065321043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13078380756335289420428057 9808785567251467065321043)
          ·
            refine ⟨14713178350877200597981565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808785567251467065321043 14713178350877200597981565)
            ·
              refine ⟨5517441881578950224243087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14713178350877200597981565 5517441881578950224243087)
              ·
                refine ⟨8276162822368425336364631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517441881578950224243087 8276162822368425336364631)
                ·
                  refine ⟨12414244233552638004546947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276162822368425336364631 12414244233552638004546947)
                  ·
                    refine ⟨18621366350328957006820421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414244233552638004546947 18621366350328957006820421)
                    ·
                      refine ⟨3491506190686679438778829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18621366350328957006820421 3491506190686679438778829)
                      ·
                        rfl

theorem cell23_6799684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6799684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799684 prefixEnd_6799684 := by exact prefixLift 6799684
  have htrace : WordTrace (prefixWord ++ tailWord_6799684) baseStart_6799684 baseEnd_6799684 := by
    simpa [prefixWord, tailWord_6799684, baseEnd_6799684] using wordTrace_append hprefix tailTrace_6799684
  have hstable : (prefixWord ++ tailWord_6799684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799684).length < 2 ^ (prefixWord ++ tailWord_6799684).sum := by decide
  have hdescent : baseEnd_6799684 < baseStart_6799684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 4, 2]
def baseStart_6799723 : Nat := 118140960795 + 6799723 * 2 ^ 59
def prefixEnd_6799723 : Nat := 4983230072969 + 3 ^ 40 * 6799723 * 2
def baseEnd_6799723 : Nat := 3491526216432204786191149

theorem tailTrace_6799723 : CollatzResearch.WordTrace tailWord_6799723 prefixEnd_6799723 3491526216432204786191149 := by
  unfold tailWord_6799723
  simp only [CollatzResearch.WordTrace]
  refine ⟨248006272344772346077675823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165337514896514897385117215 248006272344772346077675823)
  ·
    refine ⟨372009408517158519116513735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248006272344772346077675823 372009408517158519116513735)
    ·
      refine ⟨558014112775737778674770603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372009408517158519116513735 558014112775737778674770603)
      ·
        refine ⟨837021169163606668012155905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558014112775737778674770603 837021169163606668012155905)
        ·
          refine ⟨627765876872705001009116929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837021169163606668012155905 627765876872705001009116929)
          ·
            refine ⟨470824407654528750756837697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627765876872705001009116929 470824407654528750756837697)
            ·
              refine ⟨353118305740896563067628273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470824407654528750756837697 353118305740896563067628273)
              ·
                refine ⟨264838729305672422300721205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353118305740896563067628273 264838729305672422300721205)
                ·
                  refine ⟨24828630872406789590692613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264838729305672422300721205 24828630872406789590692613)
                  ·
                    refine ⟨4655368288576273048254865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24828630872406789590692613 4655368288576273048254865)
                    ·
                      refine ⟨3491526216432204786191149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655368288576273048254865 3491526216432204786191149)
                      ·
                        rfl

theorem cell23_6799723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4, 2].length) (baseStart_6799723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799723 prefixEnd_6799723 := by exact prefixLift 6799723
  have htrace : WordTrace (prefixWord ++ tailWord_6799723) baseStart_6799723 baseEnd_6799723 := by
    simpa [prefixWord, tailWord_6799723, baseEnd_6799723] using wordTrace_append hprefix tailTrace_6799723
  have hstable : (prefixWord ++ tailWord_6799723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799723).length < 2 ^ (prefixWord ++ tailWord_6799723).sum := by decide
  have hdescent : baseEnd_6799723 < baseStart_6799723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799753 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_6799753 : Nat := 118140960795 + 6799753 * 2 ^ 59
def prefixEnd_6799753 : Nat := 4983230072969 + 3 ^ 40 * 6799753 * 2
def baseEnd_6799753 : Nat := 3491541620851839668816011

theorem tailTrace_6799753 : CollatzResearch.WordTrace tailWord_6799753 prefixEnd_6799753 3491541620851839668816011 := by
  unfold tailWord_6799753
  simp only [CollatzResearch.WordTrace]
  refine ⟨248007366534663661201267913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165338244356442440800845275 248007366534663661201267913)
  ·
    refine ⟨186005524900997745900950935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248007366534663661201267913 186005524900997745900950935)
    ·
      refine ⟨279008287351496618851426403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186005524900997745900950935 279008287351496618851426403)
      ·
        refine ⟨418512431027244928277139605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279008287351496618851426403 418512431027244928277139605)
        ·
          refine ⟨19617770204402106012990919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 418512431027244928277139605 19617770204402106012990919)
          ·
            refine ⟨29426655306603159019486379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617770204402106012990919 29426655306603159019486379)
            ·
              refine ⟨44139982959904738529229569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29426655306603159019486379 44139982959904738529229569)
              ·
                refine ⟨33104987219928553896922177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44139982959904738529229569 33104987219928553896922177)
                ·
                  refine ⟨24828740414946415422691633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33104987219928553896922177 24828740414946415422691633)
                  ·
                    refine ⟨18621555311209811567018725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24828740414946415422691633 18621555311209811567018725)
                    ·
                      refine ⟨3491541620851839668816011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18621555311209811567018725 3491541620851839668816011)
                      ·
                        rfl

theorem cell23_6799753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_6799753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799753 prefixEnd_6799753 := by exact prefixLift 6799753
  have htrace : WordTrace (prefixWord ++ tailWord_6799753) baseStart_6799753 baseEnd_6799753 := by
    simpa [prefixWord, tailWord_6799753, baseEnd_6799753] using wordTrace_append hprefix tailTrace_6799753
  have hstable : (prefixWord ++ tailWord_6799753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799753).length < 2 ^ (prefixWord ++ tailWord_6799753).sum := by decide
  have hdescent : baseEnd_6799753 < baseStart_6799753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799774 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6799774 : Nat := 118140960795 + 6799774 * 2 ^ 59
def prefixEnd_6799774 : Nat := 4983230072969 + 3 ^ 40 * 6799774 * 2
def baseEnd_6799774 : Nat := 3491552403945584086653415

theorem tailTrace_6799774 : CollatzResearch.WordTrace tailWord_6799774 prefixEnd_6799774 3491552403945584086653415 := by
  unfold tailWord_6799774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001016558448447723472797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165338754978391721191854917 31001016558448447723472797)
  ·
    refine ⟨11625381209418167896302299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31001016558448447723472797 11625381209418167896302299)
    ·
      refine ⟨17438071814127251844453449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625381209418167896302299 17438071814127251844453449)
      ·
        refine ⟨13078553860595438883340087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17438071814127251844453449 13078553860595438883340087)
        ·
          refine ⟨19617830790893158325010131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078553860595438883340087 19617830790893158325010131)
          ·
            refine ⟨29426746186339737487515197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617830790893158325010131 29426746186339737487515197)
            ·
              refine ⟨11035029819877401557818199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29426746186339737487515197 11035029819877401557818199)
              ·
                refine ⟨16552544729816102336727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11035029819877401557818199 16552544729816102336727299)
                ·
                  refine ⟨24828817094724153505090949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16552544729816102336727299 24828817094724153505090949)
                  ·
                    refine ⟨4655403205260778782204553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24828817094724153505090949 4655403205260778782204553)
                    ·
                      refine ⟨3491552403945584086653415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655403205260778782204553 3491552403945584086653415)
                      ·
                        rfl

theorem cell23_6799774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6799774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799774 prefixEnd_6799774 := by exact prefixLift 6799774
  have htrace : WordTrace (prefixWord ++ tailWord_6799774) baseStart_6799774 baseEnd_6799774 := by
    simpa [prefixWord, tailWord_6799774, baseEnd_6799774] using wordTrace_append hprefix tailTrace_6799774
  have hstable : (prefixWord ++ tailWord_6799774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799774).length < 2 ^ (prefixWord ++ tailWord_6799774).sum := by decide
  have hdescent : baseEnd_6799774 < baseStart_6799774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799793 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_6799793 : Nat := 118140960795 + 6799793 * 2 ^ 59
def prefixEnd_6799793 : Nat := 4983230072969 + 3 ^ 40 * 6799793 * 2
def baseEnd_6799793 : Nat := 1163854053359339837438609

theorem tailTrace_6799793 : CollatzResearch.WordTrace tailWord_6799793 prefixEnd_6799793 1163854053359339837438609 := by
  unfold tailWord_6799793
  simp only [CollatzResearch.WordTrace]
  refine ⟨248008825454518748032724033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165339216969679165355149355 248008825454518748032724033)
  ·
    refine ⟨186006619090889061024543025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248008825454518748032724033 186006619090889061024543025)
    ·
      refine ⟨139504964318166795768407269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186006619090889061024543025 139504964318166795768407269)
      ·
        refine ⟨26157180809656274206576363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139504964318166795768407269 26157180809656274206576363)
        ·
          refine ⟨39235771214484411309864545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26157180809656274206576363 39235771214484411309864545)
          ·
            refine ⟨29426828410863308482398409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39235771214484411309864545 29426828410863308482398409)
            ·
              refine ⟨22070121308147481361798807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29426828410863308482398409 22070121308147481361798807)
              ·
                refine ⟨33105181962221222042698211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22070121308147481361798807 33105181962221222042698211)
                ·
                  refine ⟨49657772943331833064047317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33105181962221222042698211 49657772943331833064047317)
                  ·
                    refine ⟨1163854053359339837438609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49657772943331833064047317 1163854053359339837438609)
                    ·
                      rfl

theorem cell23_6799793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_6799793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799793 prefixEnd_6799793 := by exact prefixLift 6799793
  have htrace : WordTrace (prefixWord ++ tailWord_6799793) baseStart_6799793 baseEnd_6799793 := by
    simpa [prefixWord, tailWord_6799793, baseEnd_6799793] using wordTrace_append hprefix tailTrace_6799793
  have hstable : (prefixWord ++ tailWord_6799793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799793).length < 2 ^ (prefixWord ++ tailWord_6799793).sum := by decide
  have hdescent : baseEnd_6799793 < baseStart_6799793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799820 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6799820 : Nat := 118140960795 + 6799820 * 2 ^ 59
def prefixEnd_6799820 : Nat := 4983230072969 + 3 ^ 40 * 6799820 * 2
def baseEnd_6799820 : Nat := 3491576024055690906678203

theorem tailTrace_6799820 : CollatzResearch.WordTrace tailWord_6799820 prefixEnd_6799820 3491576024055690906678203 := by
  unfold tailWord_6799820
  simp only [CollatzResearch.WordTrace]
  refine ⟨124004905112710465821978457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165339873483613954429304609 124004905112710465821978457)
  ·
    refine ⟨93003678834532849366483843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124004905112710465821978457 93003678834532849366483843)
    ·
      refine ⟨139505518251799274049725765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93003678834532849366483843 139505518251799274049725765)
      ·
        refine ⟨26157284672212363884323581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139505518251799274049725765 26157284672212363884323581)
        ·
          refine ⟨9808981752079636456621343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26157284672212363884323581 9808981752079636456621343)
          ·
            refine ⟨14713472628119454684932015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808981752079636456621343 14713472628119454684932015)
            ·
              refine ⟨22070208942179182027398023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14713472628119454684932015 22070208942179182027398023)
              ·
                refine ⟨33105313413268773041097035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22070208942179182027398023 33105313413268773041097035)
                ·
                  refine ⟨49657970119903159561645553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33105313413268773041097035 49657970119903159561645553)
                  ·
                    refine ⟨37243477589927369671234165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49657970119903159561645553 37243477589927369671234165)
                    ·
                      refine ⟨3491576024055690906678203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37243477589927369671234165 3491576024055690906678203)
                      ·
                        rfl

theorem cell23_6799820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6799820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799820 prefixEnd_6799820 := by exact prefixLift 6799820
  have htrace : WordTrace (prefixWord ++ tailWord_6799820) baseStart_6799820 baseEnd_6799820 := by
    simpa [prefixWord, tailWord_6799820, baseEnd_6799820] using wordTrace_append hprefix tailTrace_6799820
  have hstable : (prefixWord ++ tailWord_6799820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799820).length < 2 ^ (prefixWord ++ tailWord_6799820).sum := by decide
  have hdescent : baseEnd_6799820 < baseStart_6799820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799857 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 1, 4]
def baseStart_6799857 : Nat := 118140960795 + 6799857 * 2 ^ 59
def prefixEnd_6799857 : Nat := 4983230072969 + 3 ^ 40 * 6799857 * 2
def baseEnd_6799857 : Nat := 1163865007613302420638511

theorem tailTrace_6799857 : CollatzResearch.WordTrace tailWord_6799857 prefixEnd_6799857 1163865007613302420638511 := by
  unfold tailWord_6799857
  simp only [CollatzResearch.WordTrace]
  refine ⟨248011159726286886963053825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165340773150857924642035883 248011159726286886963053825)
  ·
    refine ⟨186008369794715165222290369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248011159726286886963053825 186008369794715165222290369)
    ·
      refine ⟨139506277346036373916717777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186008369794715165222290369 139506277346036373916717777)
      ·
        refine ⟨104629708009527280437538333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139506277346036373916717777 104629708009527280437538333)
        ·
          refine ⟨39236140503572730164076875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104629708009527280437538333 39236140503572730164076875)
          ·
            refine ⟨58854210755359095246115313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39236140503572730164076875 58854210755359095246115313)
            ·
              refine ⟨44140658066519321434586485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58854210755359095246115313 44140658066519321434586485)
              ·
                refine ⟨4138186693736186384492483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44140658066519321434586485 4138186693736186384492483)
                ·
                  refine ⟨6207280040604279576738725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138186693736186384492483 6207280040604279576738725)
                  ·
                    refine ⟨1163865007613302420638511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207280040604279576738725 1163865007613302420638511)
                    ·
                      rfl

theorem cell23_6799857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_6799857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799857 prefixEnd_6799857 := by exact prefixLift 6799857
  have htrace : WordTrace (prefixWord ++ tailWord_6799857) baseStart_6799857 baseEnd_6799857 := by
    simpa [prefixWord, tailWord_6799857, baseEnd_6799857] using wordTrace_append hprefix tailTrace_6799857
  have hstable : (prefixWord ++ tailWord_6799857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799857).length < 2 ^ (prefixWord ++ tailWord_6799857).sum := by decide
  have hdescent : baseEnd_6799857 < baseStart_6799857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799863 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_6799863 : Nat := 118140960795 + 6799863 * 2 ^ 59
def prefixEnd_6799863 : Nat := 4983230072969 + 3 ^ 40 * 6799863 * 2
def baseEnd_6799863 : Nat := 3491598103723834238440505

theorem tailTrace_6799863 : CollatzResearch.WordTrace tailWord_6799863 prefixEnd_6799863 3491598103723834238440505 := by
  unfold tailWord_6799863
  simp only [CollatzResearch.WordTrace]
  refine ⟨248011378564265149987772243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165340919042843433325181495 248011378564265149987772243)
  ·
    refine ⟨372017067846397724981658365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248011378564265149987772243 372017067846397724981658365)
    ·
      refine ⟨139506400442399146868121887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372017067846397724981658365 139506400442399146868121887)
      ·
        refine ⟨209259600663598720302182831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139506400442399146868121887 209259600663598720302182831)
        ·
          refine ⟨313889400995398080453274247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209259600663598720302182831 313889400995398080453274247)
          ·
            refine ⟨470834101493097120679911371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313889400995398080453274247 470834101493097120679911371)
            ·
              refine ⟨706251152239645681019867057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470834101493097120679911371 706251152239645681019867057)
              ·
                refine ⟨529688364179734260764900293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706251152239645681019867057 529688364179734260764900293)
                ·
                  refine ⟨99316568283700173893418805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529688364179734260764900293 99316568283700173893418805)
                  ·
                    refine ⟨9310928276596891302508013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99316568283700173893418805 9310928276596891302508013)
                    ·
                      refine ⟨3491598103723834238440505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310928276596891302508013 3491598103723834238440505)
                      ·
                        rfl

theorem cell23_6799863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_6799863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799863 prefixEnd_6799863 := by exact prefixLift 6799863
  have htrace : WordTrace (prefixWord ++ tailWord_6799863) baseStart_6799863 baseEnd_6799863 := by
    simpa [prefixWord, tailWord_6799863, baseEnd_6799863] using wordTrace_append hprefix tailTrace_6799863
  have hstable : (prefixWord ++ tailWord_6799863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799863).length < 2 ^ (prefixWord ++ tailWord_6799863).sum := by decide
  have hdescent : baseEnd_6799863 < baseStart_6799863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799893 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6799893 : Nat := 118140960795 + 6799893 * 2 ^ 59
def prefixEnd_6799893 : Nat := 4983230072969 + 3 ^ 40 * 6799893 * 2
def baseEnd_6799893 : Nat := 3491613508143469121065367

theorem tailTrace_6799893 : CollatzResearch.WordTrace tailWord_6799893 prefixEnd_6799893 3491613508143469121065367 := by
  unfold tailWord_6799893
  simp only [CollatzResearch.WordTrace]
  refine ⟨248012472754156465111364333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165341648502770976740909555 248012472754156465111364333)
  ·
    refine ⟨93004677282808674416761625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248012472754156465111364333 93004677282808674416761625)
    ·
      refine ⟨69753507962106505812571219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93004677282808674416761625 69753507962106505812571219)
      ·
        refine ⟨104630261943159758718856829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69753507962106505812571219 104630261943159758718856829)
        ·
          refine ⟨39236348228684909519571311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104630261943159758718856829 39236348228684909519571311)
          ·
            refine ⟨58854522343027364279356967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39236348228684909519571311 58854522343027364279356967)
            ·
              refine ⟨88281783514541046419035451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58854522343027364279356967 88281783514541046419035451)
              ·
                refine ⟨132422675271811569628553177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88281783514541046419035451 132422675271811569628553177)
                ·
                  refine ⟨99317006453858677221414883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132422675271811569628553177 99317006453858677221414883)
                  ·
                    refine ⟨148975509680788015832122325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99317006453858677221414883 148975509680788015832122325)
                    ·
                      refine ⟨3491613508143469121065367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148975509680788015832122325 3491613508143469121065367)
                      ·
                        rfl

theorem cell23_6799893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6799893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799893 prefixEnd_6799893 := by exact prefixLift 6799893
  have htrace : WordTrace (prefixWord ++ tailWord_6799893) baseStart_6799893 baseEnd_6799893 := by
    simpa [prefixWord, tailWord_6799893, baseEnd_6799893] using wordTrace_append hprefix tailTrace_6799893
  have hstable : (prefixWord ++ tailWord_6799893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799893).length < 2 ^ (prefixWord ++ tailWord_6799893).sum := by decide
  have hdescent : baseEnd_6799893 < baseStart_6799893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799900 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6799900 : Nat := 118140960795 + 6799900 * 2 ^ 59
def prefixEnd_6799900 : Nat := 4983230072969 + 3 ^ 40 * 6799900 * 2
def baseEnd_6799900 : Nat := 1163872367502683531225945

theorem tailTrace_6799900 : CollatzResearch.WordTrace tailWord_6799900 prefixEnd_6799900 1163872367502683531225945 := by
  unfold tailWord_6799900
  simp only [CollatzResearch.WordTrace]
  refine ⟨124006364032565552653434577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165341818710087403537912769 124006364032565552653434577)
  ·
    refine ⟨93004773024424164490075933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124006364032565552653434577 93004773024424164490075933)
    ·
      refine ⟨34876789884159061683778475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93004773024424164490075933 34876789884159061683778475)
      ·
        refine ⟨52315184826238592525667713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34876789884159061683778475 52315184826238592525667713)
        ·
          refine ⟨39236388619678944394250785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52315184826238592525667713 39236388619678944394250785)
          ·
            refine ⟨29427291464759208295688089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39236388619678944394250785 29427291464759208295688089)
            ·
              refine ⟨22070468598569406221766067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29427291464759208295688089 22070468598569406221766067)
              ·
                refine ⟨33105702897854109332649101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22070468598569406221766067 33105702897854109332649101)
                ·
                  refine ⟨12414638586695290999743413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33105702897854109332649101 12414638586695290999743413)
                  ·
                    refine ⟨1163872367502683531225945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12414638586695290999743413 1163872367502683531225945)
                    ·
                      rfl

theorem cell23_6799900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6799900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799900 prefixEnd_6799900 := by exact prefixLift 6799900
  have htrace : WordTrace (prefixWord ++ tailWord_6799900) baseStart_6799900 baseEnd_6799900 := by
    simpa [prefixWord, tailWord_6799900, baseEnd_6799900] using wordTrace_append hprefix tailTrace_6799900
  have hstable : (prefixWord ++ tailWord_6799900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799900).length < 2 ^ (prefixWord ++ tailWord_6799900).sum := by decide
  have hdescent : baseEnd_6799900 < baseStart_6799900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799907 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 5, 2]
def baseStart_6799907 : Nat := 118140960795 + 6799907 * 2 ^ 59
def prefixEnd_6799907 : Nat := 4983230072969 + 3 ^ 40 * 6799907 * 2
def baseEnd_6799907 : Nat := 3491620696872632066290303

theorem tailTrace_6799907 : CollatzResearch.WordTrace tailWord_6799907 prefixEnd_6799907 3491620696872632066290303 := by
  unfold tailWord_6799907
  simp only [CollatzResearch.WordTrace]
  refine ⟨248012983376105745502373975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165341988917403830334915983 248012983376105745502373975)
  ·
    refine ⟨372019475064158618253560963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248012983376105745502373975 372019475064158618253560963)
    ·
      refine ⟨558029212596237927380341445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372019475064158618253560963 558029212596237927380341445)
      ·
        refine ⟨104630477361794611383814021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558029212596237927380341445 104630477361794611383814021)
        ·
          refine ⟨19618214505336489634465129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104630477361794611383814021 19618214505336489634465129)
          ·
            refine ⟨14713660879002367225848847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19618214505336489634465129 14713660879002367225848847)
            ·
              refine ⟨22070491318503550838773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14713660879002367225848847 22070491318503550838773271)
              ·
                refine ⟨33105736977755326258159907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22070491318503550838773271 33105736977755326258159907)
                ·
                  refine ⟨49658605466632989387239861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33105736977755326258159907 49658605466632989387239861)
                  ·
                    refine ⟨4655494262496842755053737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49658605466632989387239861 4655494262496842755053737)
                    ·
                      refine ⟨3491620696872632066290303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655494262496842755053737 3491620696872632066290303)
                      ·
                        rfl

theorem cell23_6799907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_6799907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799907 prefixEnd_6799907 := by exact prefixLift 6799907
  have htrace : WordTrace (prefixWord ++ tailWord_6799907) baseStart_6799907 baseEnd_6799907 := by
    simpa [prefixWord, tailWord_6799907, baseEnd_6799907] using wordTrace_append hprefix tailTrace_6799907
  have hstable : (prefixWord ++ tailWord_6799907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799907).length < 2 ^ (prefixWord ++ tailWord_6799907).sum := by decide
  have hdescent : baseEnd_6799907 < baseStart_6799907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799954 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_6799954 : Nat := 118140960795 + 6799954 * 2 ^ 59
def prefixEnd_6799954 : Nat := 4983230072969 + 3 ^ 40 * 6799954 * 2
def baseEnd_6799954 : Nat := 3491644830463393382402587

theorem tailTrace_6799954 : CollatzResearch.WordTrace tailWord_6799954 prefixEnd_6799954 3491644830463393382402587 := by
  unfold tailWord_6799954
  simp only [CollatzResearch.WordTrace]
  refine ⟨62003674401733868132333729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165343131737956981686223277 62003674401733868132333729)
  ·
    refine ⟨46502755801300401099250297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62003674401733868132333729 46502755801300401099250297)
    ·
      refine ⟨34877066850975300824437723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46502755801300401099250297 34877066850975300824437723)
      ·
        refine ⟨52315600276462951236656585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34877066850975300824437723 52315600276462951236656585)
        ·
          refine ⟨39236700207347213427492439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52315600276462951236656585 39236700207347213427492439)
          ·
            refine ⟨58855050311020820141238659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39236700207347213427492439 58855050311020820141238659)
            ·
              refine ⟨88282575466531230211857989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58855050311020820141238659 88282575466531230211857989)
              ·
                refine ⟨16552982899974605664723373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88282575466531230211857989 16552982899974605664723373)
                ·
                  refine ⟨6207368587490477124271265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16552982899974605664723373 6207368587490477124271265)
                  ·
                    refine ⟨4655526440617857843203449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207368587490477124271265 4655526440617857843203449)
                    ·
                      refine ⟨3491644830463393382402587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655526440617857843203449 3491644830463393382402587)
                      ·
                        rfl

theorem cell23_6799954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_6799954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799954 prefixEnd_6799954 := by exact prefixLift 6799954
  have htrace : WordTrace (prefixWord ++ tailWord_6799954) baseStart_6799954 baseEnd_6799954 := by
    simpa [prefixWord, tailWord_6799954, baseEnd_6799954] using wordTrace_append hprefix tailTrace_6799954
  have hstable : (prefixWord ++ tailWord_6799954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799954).length < 2 ^ (prefixWord ++ tailWord_6799954).sum := by decide
  have hdescent : baseEnd_6799954 < baseStart_6799954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799957 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6799957 : Nat := 118140960795 + 6799957 * 2 ^ 59
def prefixEnd_6799957 : Nat := 4983230072969 + 3 ^ 40 * 6799957 * 2
def baseEnd_6799957 : Nat := 3491646370905356870665073

theorem tailTrace_6799957 : CollatzResearch.WordTrace tailWord_6799957 prefixEnd_6799957 3491646370905356870665073 := by
  unfold tailWord_6799957
  simp only [CollatzResearch.WordTrace]
  refine ⟨248014807025924604041694125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165343204683949736027796083 248014807025924604041694125)
  ·
    refine ⟨93005552634721726515635297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248014807025924604041694125 93005552634721726515635297)
    ·
      refine ⟨69754164476041294886726473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93005552634721726515635297 69754164476041294886726473)
      ·
        refine ⟨52315623357030971165044855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69754164476041294886726473 52315623357030971165044855)
        ·
          refine ⟨78473435035546456747567283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52315623357030971165044855 78473435035546456747567283)
          ·
            refine ⟨117710152553319685121350925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78473435035546456747567283 117710152553319685121350925)
            ·
              refine ⟨44141307207494881920506597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117710152553319685121350925 44141307207494881920506597)
              ·
                refine ⟨8276495101405290360094987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44141307207494881920506597 8276495101405290360094987)
                ·
                  refine ⟨12414742652107935540142481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276495101405290360094987 12414742652107935540142481)
                  ·
                    refine ⟨9311056989080951655106861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12414742652107935540142481 9311056989080951655106861)
                    ·
                      refine ⟨3491646370905356870665073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311056989080951655106861 3491646370905356870665073)
                      ·
                        rfl

theorem cell23_6799957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6799957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799957 prefixEnd_6799957 := by exact prefixLift 6799957
  have htrace : WordTrace (prefixWord ++ tailWord_6799957) baseStart_6799957 baseEnd_6799957 := by
    simpa [prefixWord, tailWord_6799957, baseEnd_6799957] using wordTrace_append hprefix tailTrace_6799957
  have hstable : (prefixWord ++ tailWord_6799957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799957).length < 2 ^ (prefixWord ++ tailWord_6799957).sum := by decide
  have hdescent : baseEnd_6799957 < baseStart_6799957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799960 : List Nat := [2, 1, 2, 2, 1, 2, 6, 7]
def baseStart_6799960 : Nat := 118140960795 + 6799960 * 2 ^ 59
def prefixEnd_6799960 : Nat := 4983230072969 + 3 ^ 40 * 6799960 * 2
def baseEnd_6799960 : Nat := 129320293012863716997317

theorem tailTrace_6799960 : CollatzResearch.WordTrace tailWord_6799960 prefixEnd_6799960 129320293012863716997317 := by
  unfold tailWord_6799960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124007458222456867777026667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165343277629942490369368889 124007458222456867777026667)
  ·
    refine ⟨186011187333685301665540001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124007458222456867777026667 186011187333685301665540001)
    ·
      refine ⟨139508390500263976249155001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186011187333685301665540001 139508390500263976249155001)
      ·
        refine ⟨104631292875197982186866251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139508390500263976249155001 104631292875197982186866251)
        ·
          refine ⟨156946939312796973280299377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104631292875197982186866251 156946939312796973280299377)
          ·
            refine ⟨117710204484597729960224533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156946939312796973280299377 117710204484597729960224533)
            ·
              refine ⟨5517665835215518591885525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117710204484597729960224533 5517665835215518591885525)
              ·
                refine ⟨129320293012863716997317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5517665835215518591885525 129320293012863716997317)
                ·
                  rfl

theorem cell23_6799960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 7].length) (baseStart_6799960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799960 prefixEnd_6799960 := by exact prefixLift 6799960
  have htrace : WordTrace (prefixWord ++ tailWord_6799960) baseStart_6799960 baseEnd_6799960 := by
    simpa [prefixWord, tailWord_6799960, baseEnd_6799960] using wordTrace_append hprefix tailTrace_6799960
  have hstable : (prefixWord ++ tailWord_6799960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799960).length < 2 ^ (prefixWord ++ tailWord_6799960).sum := by decide
  have hdescent : baseEnd_6799960 < baseStart_6799960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800014 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6800014 : Nat := 118140960795 + 6800014 * 2 ^ 59
def prefixEnd_6800014 : Nat := 4983230072969 + 3 ^ 40 * 6800014 * 2
def baseEnd_6800014 : Nat := 3491675639302663147652311

theorem tailTrace_6800014 : CollatzResearch.WordTrace tailWord_6800014 prefixEnd_6800014 3491675639302663147652311 := by
  unfold tailWord_6800014
  simp only [CollatzResearch.WordTrace]
  refine ⟨31002110748339762847064887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165344590657812068517679397 31002110748339762847064887)
  ·
    refine ⟨46503166122509644270597331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31002110748339762847064887 46503166122509644270597331)
    ·
      refine ⟨69754749183764466405895997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503166122509644270597331 69754749183764466405895997)
      ·
        refine ⟨26158030943911674902210999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69754749183764466405895997 26158030943911674902210999)
        ·
          refine ⟨39237046415867512353316499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26158030943911674902210999 39237046415867512353316499)
          ·
            refine ⟨58855569623801268529974749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39237046415867512353316499 58855569623801268529974749)
            ·
              refine ⟨22070838608925475698740531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58855569623801268529974749 22070838608925475698740531)
              ·
                refine ⟨33106257913388213548110797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22070838608925475698740531 33106257913388213548110797)
                ·
                  refine ⟨12414846717520580080541549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33106257913388213548110797 12414846717520580080541549)
                  ·
                    refine ⟨4655567519070217530203081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12414846717520580080541549 4655567519070217530203081)
                    ·
                      refine ⟨3491675639302663147652311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655567519070217530203081 3491675639302663147652311)
                      ·
                        rfl

theorem cell23_6800014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6800014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800014 prefixEnd_6800014 := by exact prefixLift 6800014
  have htrace : WordTrace (prefixWord ++ tailWord_6800014) baseStart_6800014 baseEnd_6800014 := by
    simpa [prefixWord, tailWord_6800014, baseEnd_6800014] using wordTrace_append hprefix tailTrace_6800014
  have hstable : (prefixWord ++ tailWord_6800014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800014).length < 2 ^ (prefixWord ++ tailWord_6800014).sum := by decide
  have hdescent : baseEnd_6800014 < baseStart_6800014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800039 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6800039 : Nat := 118140960795 + 6800039 * 2 ^ 59
def prefixEnd_6800039 : Nat := 4983230072969 + 3 ^ 40 * 6800039 * 2
def baseEnd_6800039 : Nat := 3491688476319025549839697

theorem tailTrace_6800039 : CollatzResearch.WordTrace tailWord_6800039 prefixEnd_6800039 3491688476319025549839697 := by
  unfold tailWord_6800039
  simp only [CollatzResearch.WordTrace]
  refine ⟨248017797811627532046179171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165345198541085021364119447 248017797811627532046179171)
  ·
    refine ⟨372026696717441298069268757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248017797811627532046179171 372026696717441298069268757)
    ·
      refine ⟨17438751408630060846996973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 372026696717441298069268757 17438751408630060846996973)
      ·
        refine ⟨6539531778236272817623865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17438751408630060846996973 6539531778236272817623865)
        ·
          refine ⟨4904648833677204613217899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539531778236272817623865 4904648833677204613217899)
          ·
            refine ⟨7356973250515806919826849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904648833677204613217899 7356973250515806919826849)
            ·
              refine ⟨5517729937886855189870137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356973250515806919826849 5517729937886855189870137)
              ·
                refine ⟨4138297453415141392402603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517729937886855189870137 4138297453415141392402603)
                ·
                  refine ⟨6207446180122712088603905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138297453415141392402603 6207446180122712088603905)
                  ·
                    refine ⟨4655584635092034066452929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207446180122712088603905 4655584635092034066452929)
                    ·
                      refine ⟨3491688476319025549839697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655584635092034066452929 3491688476319025549839697)
                      ·
                        rfl

theorem cell23_6800039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6800039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800039 prefixEnd_6800039 := by exact prefixLift 6800039
  have htrace : WordTrace (prefixWord ++ tailWord_6800039) baseStart_6800039 baseEnd_6800039 := by
    simpa [prefixWord, tailWord_6800039, baseEnd_6800039] using wordTrace_append hprefix tailTrace_6800039
  have hstable : (prefixWord ++ tailWord_6800039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800039).length < 2 ^ (prefixWord ++ tailWord_6800039).sum := by decide
  have hdescent : baseEnd_6800039 < baseStart_6800039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800050 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_6800050 : Nat := 118140960795 + 6800050 * 2 ^ 59
def prefixEnd_6800050 : Nat := 4983230072969 + 3 ^ 40 * 6800050 * 2
def baseEnd_6800050 : Nat := 387966013845136111866905

theorem tailTrace_6800050 : CollatzResearch.WordTrace tailWord_6800050 prefixEnd_6800050 387966013845136111866905 := by
  unfold tailWord_6800050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004549753646920231207401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165345466009725120616553069 62004549753646920231207401)
  ·
    refine ⟨46503412315235190173405551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62004549753646920231207401 46503412315235190173405551)
    ·
      refine ⟨69755118472852785260108327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503412315235190173405551 69755118472852785260108327)
      ·
        refine ⟨104632677709279177890162491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69755118472852785260108327 104632677709279177890162491)
        ·
          refine ⟨156949016563918766835243737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104632677709279177890162491 156949016563918766835243737)
          ·
            refine ⟨117711762422939075126432803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156949016563918766835243737 117711762422939075126432803)
            ·
              refine ⟨176567643634408612689649205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117711762422939075126432803 176567643634408612689649205)
              ·
                refine ⟨16553216590725807439654613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176567643634408612689649205 16553216590725807439654613)
                ·
                  refine ⟨387966013845136111866905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16553216590725807439654613 387966013845136111866905)
                  ·
                    rfl

theorem cell23_6800050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_6800050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800050 prefixEnd_6800050 := by exact prefixLift 6800050
  have htrace : WordTrace (prefixWord ++ tailWord_6800050) baseStart_6800050 baseEnd_6800050 := by
    simpa [prefixWord, tailWord_6800050, baseEnd_6800050] using wordTrace_append hprefix tailTrace_6800050
  have hstable : (prefixWord ++ tailWord_6800050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800050).length < 2 ^ (prefixWord ++ tailWord_6800050).sum := by decide
  have hdescent : baseEnd_6800050 < baseStart_6800050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800061 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6800061 : Nat := 118140960795 + 6800061 * 2 ^ 59
def prefixEnd_6800061 : Nat := 4983230072969 + 3 ^ 40 * 6800061 * 2
def baseEnd_6800061 : Nat := 3491699772893424463764595

theorem tailTrace_6800061 : CollatzResearch.WordTrace tailWord_6800061 prefixEnd_6800061 3491699772893424463764595 := by
  unfold tailWord_6800061
  simp only [CollatzResearch.WordTrace]
  refine ⟨248018600217547829803480037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165345733478365219868986691 248018600217547829803480037)
  ·
    refine ⟨46503487540790218088152507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248018600217547829803480037 46503487540790218088152507)
    ·
      refine ⟨69755231311185327132228761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503487540790218088152507 69755231311185327132228761)
      ·
        refine ⟨52316423483388995349171571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69755231311185327132228761 52316423483388995349171571)
        ·
          refine ⟨78474635225083493023757357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52316423483388995349171571 78474635225083493023757357)
          ·
            refine ⟨29427988209406309883909009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78474635225083493023757357 29427988209406309883909009)
            ·
              refine ⟨22070991157054732412931757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29427988209406309883909009 22070991157054732412931757)
              ·
                refine ⟨8276621683895524654849409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22070991157054732412931757 8276621683895524654849409)
                ·
                  refine ⟨6207466262921643491137057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276621683895524654849409 6207466262921643491137057)
                  ·
                    refine ⟨4655599697191232618352793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207466262921643491137057 4655599697191232618352793)
                    ·
                      refine ⟨3491699772893424463764595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655599697191232618352793 3491699772893424463764595)
                      ·
                        rfl

theorem cell23_6800061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6800061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800061 prefixEnd_6800061 := by exact prefixLift 6800061
  have htrace : WordTrace (prefixWord ++ tailWord_6800061) baseStart_6800061 baseEnd_6800061 := by
    simpa [prefixWord, tailWord_6800061, baseEnd_6800061] using wordTrace_append hprefix tailTrace_6800061
  have hstable : (prefixWord ++ tailWord_6800061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800061).length < 2 ^ (prefixWord ++ tailWord_6800061).sum := by decide
  have hdescent : baseEnd_6800061 < baseStart_6800061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800137 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_6800137 : Nat := 118140960795 + 6800137 * 2 ^ 59
def prefixEnd_6800137 : Nat := 4983230072969 + 3 ^ 40 * 6800137 * 2
def baseEnd_6800137 : Nat := 3491738797423166166414245

theorem tailTrace_6800137 : CollatzResearch.WordTrace tailWord_6800137 prefixEnd_6800137 3491738797423166166414245 := by
  unfold tailWord_6800137
  simp only [CollatzResearch.WordTrace]
  refine ⟨248021372165272494783246665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165347581443514996522164443 248021372165272494783246665)
  ·
    refine ⟨186016029123954371087434999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248021372165272494783246665 186016029123954371087434999)
    ·
      refine ⟨279024043685931556631152499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186016029123954371087434999 279024043685931556631152499)
      ·
        refine ⟨418536065528897334946728749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279024043685931556631152499 418536065528897334946728749)
        ·
          refine ⟨156951024573336500605023281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418536065528897334946728749 156951024573336500605023281)
          ·
            refine ⟨117713268430002375453767461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156951024573336500605023281 117713268430002375453767461)
            ·
              refine ⟨22071237830625445397581399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117713268430002375453767461 22071237830625445397581399)
              ·
                refine ⟨33106856745938168096372099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22071237830625445397581399 33106856745938168096372099)
                ·
                  refine ⟨49660285118907252144558149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33106856745938168096372099 49660285118907252144558149)
                  ·
                    refine ⟨9311303459795109777104653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49660285118907252144558149 9311303459795109777104653)
                    ·
                      refine ⟨3491738797423166166414245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311303459795109777104653 3491738797423166166414245)
                      ·
                        rfl

theorem cell23_6800137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_6800137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800137 prefixEnd_6800137 := by exact prefixLift 6800137
  have htrace : WordTrace (prefixWord ++ tailWord_6800137) baseStart_6800137 baseEnd_6800137 := by
    simpa [prefixWord, tailWord_6800137, baseEnd_6800137] using wordTrace_append hprefix tailTrace_6800137
  have hstable : (prefixWord ++ tailWord_6800137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800137).length < 2 ^ (prefixWord ++ tailWord_6800137).sum := by decide
  have hdescent : baseEnd_6800137 < baseStart_6800137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800154 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_6800154 : Nat := 118140960795 + 6800154 * 2 ^ 59
def prefixEnd_6800154 : Nat := 4983230072969 + 3 ^ 40 * 6800154 * 2
def baseEnd_6800154 : Nat := 3491747526594292599901667

theorem tailTrace_6800154 : CollatzResearch.WordTrace tailWord_6800154 prefixEnd_6800154 3491747526594292599901667 := by
  unfold tailWord_6800154
  simp only [CollatzResearch.WordTrace]
  refine ⟨62005498051552726671653879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165347994804140604457743677 62005498051552726671653879)
  ·
    refine ⟨93008247077329090007480819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62005498051552726671653879 93008247077329090007480819)
    ·
      refine ⟨139512370615993635011221229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93008247077329090007480819 139512370615993635011221229)
      ·
        refine ⟨52317138980997613129207961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139512370615993635011221229 52317138980997613129207961)
        ·
          refine ⟨39237854235748209846905971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52317138980997613129207961 39237854235748209846905971)
          ·
            refine ⟨58856781353622314770358957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39237854235748209846905971 58856781353622314770358957)
            ·
              refine ⟨22071293007608368038884609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58856781353622314770358957 22071293007608368038884609)
              ·
                refine ⟨16553469755706276029163457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22071293007608368038884609 16553469755706276029163457)
                ·
                  refine ⟨12415102316779707021872593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16553469755706276029163457 12415102316779707021872593)
                  ·
                    refine ⟨9311326737584780266404445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12415102316779707021872593 9311326737584780266404445)
                    ·
                      refine ⟨3491747526594292599901667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311326737584780266404445 3491747526594292599901667)
                      ·
                        rfl

theorem cell23_6800154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_6800154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800154 prefixEnd_6800154 := by exact prefixLift 6800154
  have htrace : WordTrace (prefixWord ++ tailWord_6800154) baseStart_6800154 baseEnd_6800154 := by
    simpa [prefixWord, tailWord_6800154, baseEnd_6800154] using wordTrace_append hprefix tailTrace_6800154
  have hstable : (prefixWord ++ tailWord_6800154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800154).length < 2 ^ (prefixWord ++ tailWord_6800154).sum := by decide
  have hdescent : baseEnd_6800154 < baseStart_6800154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800184 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_6800184 : Nat := 118140960795 + 6800184 * 2 ^ 59
def prefixEnd_6800184 : Nat := 4983230072969 + 3 ^ 40 * 6800184 * 2
def baseEnd_6800184 : Nat := 3491762931013927482526529

theorem tailTrace_6800184 : CollatzResearch.WordTrace tailWord_6800184 prefixEnd_6800184 3491762931013927482526529 := by
  unfold tailWord_6800184
  simp only [CollatzResearch.WordTrace]
  refine ⟨124011543198051110905103803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165348724264068147873471737 124011543198051110905103803)
  ·
    refine ⟨186017314797076666357655705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124011543198051110905103803 186017314797076666357655705)
    ·
      refine ⟨139512986097807499768241779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186017314797076666357655705 139512986097807499768241779)
      ·
        refine ⟨209269479146711249652362669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139512986097807499768241779 209269479146711249652362669)
        ·
          refine ⟨78476054680016718619636001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209269479146711249652362669 78476054680016718619636001)
          ·
            refine ⟨58857041010012538964727001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78476054680016718619636001 58857041010012538964727001)
            ·
              refine ⟨44142780757509404223545251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58857041010012538964727001 44142780757509404223545251)
              ·
                refine ⟨66214171136264106335317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44142780757509404223545251 66214171136264106335317877)
                ·
                  refine ⟨6207578544024759968936051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66214171136264106335317877 6207578544024759968936051)
                  ·
                    refine ⟨9311367816037139953404077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207578544024759968936051 9311367816037139953404077)
                    ·
                      refine ⟨3491762931013927482526529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311367816037139953404077 3491762931013927482526529)
                      ·
                        rfl

theorem cell23_6800184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_6800184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800184 prefixEnd_6800184 := by exact prefixLift 6800184
  have htrace : WordTrace (prefixWord ++ tailWord_6800184) baseStart_6800184 baseEnd_6800184 := by
    simpa [prefixWord, tailWord_6800184, baseEnd_6800184] using wordTrace_append hprefix tailTrace_6800184
  have hstable : (prefixWord ++ tailWord_6800184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800184).length < 2 ^ (prefixWord ++ tailWord_6800184).sum := by decide
  have hdescent : baseEnd_6800184 < baseStart_6800184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800212 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_6800212 : Nat := 118140960795 + 6800212 * 2 ^ 59
def prefixEnd_6800212 : Nat := 4983230072969 + 3 ^ 40 * 6800212 * 2
def baseEnd_6800212 : Nat := 1163925769490751124325467

theorem tailTrace_6800212 : CollatzResearch.WordTrace tailWord_6800212 prefixEnd_6800212 1163925769490751124325467 := by
  unfold tailWord_6800212
  simp only [CollatzResearch.WordTrace]
  refine ⟨124012053820000391296113445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165349405093333855061484593 124012053820000391296113445)
  ·
    refine ⟨23252260091250073368021271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124012053820000391296113445 23252260091250073368021271)
    ·
      refine ⟨34878390136875110052031907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23252260091250073368021271 34878390136875110052031907)
      ·
        refine ⟨52317585205312665078047861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34878390136875110052031907 52317585205312665078047861)
        ·
          refine ⟨4904773612998062351066987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52317585205312665078047861 4904773612998062351066987)
          ·
            refine ⟨7357160419497093526600481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904773612998062351066987 7357160419497093526600481)
            ·
              refine ⟨5517870314622820144950361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357160419497093526600481 5517870314622820144950361)
              ·
                refine ⟨4138402735967115108712771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517870314622820144950361 4138402735967115108712771)
                ·
                  refine ⟨6207604103950672663069157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138402735967115108712771 6207604103950672663069157)
                  ·
                    refine ⟨1163925769490751124325467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207604103950672663069157 1163925769490751124325467)
                    ·
                      rfl

theorem cell23_6800212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_6800212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800212 prefixEnd_6800212 := by exact prefixLift 6800212
  have htrace : WordTrace (prefixWord ++ tailWord_6800212) baseStart_6800212 baseEnd_6800212 := by
    simpa [prefixWord, tailWord_6800212, baseEnd_6800212] using wordTrace_append hprefix tailTrace_6800212
  have hstable : (prefixWord ++ tailWord_6800212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800212).length < 2 ^ (prefixWord ++ tailWord_6800212).sum := by decide
  have hdescent : baseEnd_6800212 < baseStart_6800212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800218 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_6800218 : Nat := 118140960795 + 6800218 * 2 ^ 59
def prefixEnd_6800218 : Nat := 4983230072969 + 3 ^ 40 * 6800218 * 2
def baseEnd_6800218 : Nat := 3491780389356180349501373

theorem tailTrace_6800218 : CollatzResearch.WordTrace tailWord_6800218 prefixEnd_6800218 3491780389356180349501373 := by
  unfold tailWord_6800218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62006081619494761404236327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165349550985319363744630205 62006081619494761404236327)
  ·
    refine ⟨93009122429242142106354491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62006081619494761404236327 93009122429242142106354491)
    ·
      refine ⟨139513683643863213159531737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93009122429242142106354491 139513683643863213159531737)
      ·
        refine ⟨104635262732897409869648803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139513683643863213159531737 104635262732897409869648803)
        ·
          refine ⟨156952894099346114804473205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104635262732897409869648803 156952894099346114804473205)
          ·
            refine ⟨14714333821813698262919363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156952894099346114804473205 14714333821813698262919363)
            ·
              refine ⟨22071500732720547394379045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14714333821813698262919363 22071500732720547394379045)
              ·
                refine ⟨4138406387385102636446071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22071500732720547394379045 4138406387385102636446071)
                ·
                  refine ⟨6207609581077653954669107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138406387385102636446071 6207609581077653954669107)
                  ·
                    refine ⟨9311414371616480932003661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207609581077653954669107 9311414371616480932003661)
                    ·
                      refine ⟨3491780389356180349501373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311414371616480932003661 3491780389356180349501373)
                      ·
                        rfl

theorem cell23_6800218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_6800218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800218 prefixEnd_6800218 := by exact prefixLift 6800218
  have htrace : WordTrace (prefixWord ++ tailWord_6800218) baseStart_6800218 baseEnd_6800218 := by
    simpa [prefixWord, tailWord_6800218, baseEnd_6800218] using wordTrace_append hprefix tailTrace_6800218
  have hstable : (prefixWord ++ tailWord_6800218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800218).length < 2 ^ (prefixWord ++ tailWord_6800218).sum := by decide
  have hdescent : baseEnd_6800218 < baseStart_6800218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800241 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_6800241 : Nat := 118140960795 + 6800241 * 2 ^ 59
def prefixEnd_6800241 : Nat := 4983230072969 + 3 ^ 40 * 6800241 * 2
def baseEnd_6800241 : Nat := 3491792199411233759513767

theorem tailTrace_6800241 : CollatzResearch.WordTrace tailWord_6800241 prefixEnd_6800241 3491792199411233759513767 := by
  unfold tailWord_6800241
  simp only [CollatzResearch.WordTrace]
  refine ⟨248025165356895720545032577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165350110237930480363355051 248025165356895720545032577)
  ·
    refine ⟨186018874017671790408774433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248025165356895720545032577 186018874017671790408774433)
    ·
      refine ⟨139514155513253842806580825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186018874017671790408774433 139514155513253842806580825)
      ·
        refine ⟨104635616634940382104935619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139514155513253842806580825 104635616634940382104935619)
        ·
          refine ⟨156953424952410573157403429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104635616634940382104935619 156953424952410573157403429)
          ·
            refine ⟨29428767178576982467013143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156953424952410573157403429 29428767178576982467013143)
            ·
              refine ⟨44143150767865473700519715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29428767178576982467013143 44143150767865473700519715)
              ·
                refine ⟨66214726151798210550779573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44143150767865473700519715 66214726151798210550779573)
                ·
                  refine ⟨6207630576731082239135585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66214726151798210550779573 6207630576731082239135585)
                  ·
                    refine ⟨4655722932548311679351689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207630576731082239135585 4655722932548311679351689)
                    ·
                      refine ⟨3491792199411233759513767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655722932548311679351689 3491792199411233759513767)
                      ·
                        rfl

theorem cell23_6800241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_6800241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800241 prefixEnd_6800241 := by exact prefixLift 6800241
  have htrace : WordTrace (prefixWord ++ tailWord_6800241) baseStart_6800241 baseEnd_6800241 := by
    simpa [prefixWord, tailWord_6800241, baseEnd_6800241] using wordTrace_append hprefix tailTrace_6800241
  have hstable : (prefixWord ++ tailWord_6800241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800241).length < 2 ^ (prefixWord ++ tailWord_6800241).sum := by decide
  have hdescent : baseEnd_6800241 < baseStart_6800241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800261 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_6800261 : Nat := 118140960795 + 6800261 * 2 ^ 59
def prefixEnd_6800261 : Nat := 4983230072969 + 3 ^ 40 * 6800261 * 2
def baseEnd_6800261 : Nat := 3491802469024323681263675

theorem tailTrace_6800261 : CollatzResearch.WordTrace tailWord_6800261 prefixEnd_6800261 3491802469024323681263675 := by
  unfold tailWord_6800261
  simp only [CollatzResearch.WordTrace]
  refine ⟨248025894816823263960760637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165350596544548842640507091 248025894816823263960760637)
  ·
    refine ⟨93009710556308723985285239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248025894816823263960760637 93009710556308723985285239)
    ·
      refine ⟨139514565834463085977927859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93009710556308723985285239 139514565834463085977927859)
      ·
        refine ⟨209271848751694628966891789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139514565834463085977927859 209271848751694628966891789)
        ·
          refine ⟨78476943281885485862584421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209271848751694628966891789 78476943281885485862584421)
          ·
            refine ⟨14714426865353528599234579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78476943281885485862584421 14714426865353528599234579)
            ·
              refine ⟨22071640298030292898851869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14714426865353528599234579 22071640298030292898851869)
              ·
                refine ⟨8276865111761359837069451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22071640298030292898851869 8276865111761359837069451)
                ·
                  refine ⟨12415297667642039755604177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276865111761359837069451 12415297667642039755604177)
                  ·
                    refine ⟨9311473250731529816703133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12415297667642039755604177 9311473250731529816703133)
                    ·
                      refine ⟨3491802469024323681263675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311473250731529816703133 3491802469024323681263675)
                      ·
                        rfl

theorem cell23_6800261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_6800261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800261 prefixEnd_6800261 := by exact prefixLift 6800261
  have htrace : WordTrace (prefixWord ++ tailWord_6800261) baseStart_6800261 baseEnd_6800261 := by
    simpa [prefixWord, tailWord_6800261, baseEnd_6800261] using wordTrace_append hprefix tailTrace_6800261
  have hstable : (prefixWord ++ tailWord_6800261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800261).length < 2 ^ (prefixWord ++ tailWord_6800261).sum := by decide
  have hdescent : baseEnd_6800261 < baseStart_6800261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800278 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6800278 : Nat := 118140960795 + 6800278 * 2 ^ 59
def prefixEnd_6800278 : Nat := 4983230072969 + 3 ^ 40 * 6800278 * 2
def baseEnd_6800278 : Nat := 3491811198195450114751097

theorem tailTrace_6800278 : CollatzResearch.WordTrace tailWord_6800278 prefixEnd_6800278 3491811198195450114751097 := by
  unfold tailWord_6800278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501657178610104741508093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165351009905174450576086325 15501657178610104741508093)
  ·
    refine ⟨5813121441978789278065535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15501657178610104741508093 5813121441978789278065535)
    ·
      refine ⟨8719682162968183917098303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813121441978789278065535 8719682162968183917098303)
      ·
        refine ⟨13079523244452275875647455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719682162968183917098303 13079523244452275875647455)
        ·
          refine ⟨19619284866678413813471183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079523244452275875647455 19619284866678413813471183)
          ·
            refine ⟨29428927300017620720206775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19619284866678413813471183 29428927300017620720206775)
            ·
              refine ⟨44143390950026431080310163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29428927300017620720206775 44143390950026431080310163)
              ·
                refine ⟨66215086425039646620465245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44143390950026431080310163 66215086425039646620465245)
                ·
                  refine ⟨24830657409389867482674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66215086425039646620465245 24830657409389867482674467)
                  ·
                    refine ⟨37245986114084801224011701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24830657409389867482674467 37245986114084801224011701)
                    ·
                      refine ⟨3491811198195450114751097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37245986114084801224011701 3491811198195450114751097)
                      ·
                        rfl

theorem cell23_6800278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6800278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800278 prefixEnd_6800278 := by exact prefixLift 6800278
  have htrace : WordTrace (prefixWord ++ tailWord_6800278) baseStart_6800278 baseEnd_6800278 := by
    simpa [prefixWord, tailWord_6800278, baseEnd_6800278] using wordTrace_append hprefix tailTrace_6800278
  have hstable : (prefixWord ++ tailWord_6800278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800278).length < 2 ^ (prefixWord ++ tailWord_6800278).sum := by decide
  have hdescent : baseEnd_6800278 < baseStart_6800278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800291 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 3]
def baseStart_6800291 : Nat := 118140960795 + 6800291 * 2 ^ 59
def prefixEnd_6800291 : Nat := 4983230072969 + 3 ^ 40 * 6800291 * 2
def baseEnd_6800291 : Nat := 3491817873443958563888537

theorem tailTrace_6800291 : CollatzResearch.WordTrace tailWord_6800291 prefixEnd_6800291 3491817873443958563888537 := by
  unfold tailWord_6800291
  simp only [CollatzResearch.WordTrace]
  refine ⟨248026989006714579084352727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165351326004476386056235151 248026989006714579084352727)
  ·
    refine ⟨372040483510071868626529091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248026989006714579084352727 372040483510071868626529091)
    ·
      refine ⟨558060725265107802939793637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372040483510071868626529091 558060725265107802939793637)
      ·
        refine ⟨104636385987207713051211307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558060725265107802939793637 104636385987207713051211307)
        ·
          refine ⟨156954578980811569576816961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104636385987207713051211307 156954578980811569576816961)
          ·
            refine ⟨117715934235608677182612721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156954578980811569576816961 117715934235608677182612721)
            ·
              refine ⟨88286950676706507886959541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117715934235608677182612721 88286950676706507886959541)
              ·
                refine ⟨8276901625941235114402457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88286950676706507886959541 8276901625941235114402457)
                ·
                  refine ⟨6207676219455926335801843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276901625941235114402457 6207676219455926335801843)
                  ·
                    refine ⟨9311514329183889503702765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207676219455926335801843 9311514329183889503702765)
                    ·
                      refine ⟨3491817873443958563888537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311514329183889503702765 3491817873443958563888537)
                      ·
                        rfl

theorem cell23_6800291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_6800291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800291 prefixEnd_6800291 := by exact prefixLift 6800291
  have htrace : WordTrace (prefixWord ++ tailWord_6800291) baseStart_6800291 baseEnd_6800291 := by
    simpa [prefixWord, tailWord_6800291, baseEnd_6800291] using wordTrace_append hprefix tailTrace_6800291
  have hstable : (prefixWord ++ tailWord_6800291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800291).length < 2 ^ (prefixWord ++ tailWord_6800291).sum := by decide
  have hdescent : baseEnd_6800291 < baseStart_6800291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800307 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 6]
def baseStart_6800307 : Nat := 118140960795 + 6800307 * 2 ^ 59
def prefixEnd_6800307 : Nat := 4983230072969 + 3 ^ 40 * 6800307 * 2
def baseEnd_6800307 : Nat := 1163942029711476833762821

theorem tailTrace_6800307 : CollatzResearch.WordTrace tailWord_6800307 prefixEnd_6800307 1163942029711476833762821 := by
  unfold tailWord_6800307
  simp only [CollatzResearch.WordTrace]
  refine ⟨248027572574656613816935175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165351715049771075877956783 248027572574656613816935175)
  ·
    refine ⟨372041358861984920725402763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248027572574656613816935175 372041358861984920725402763)
    ·
      refine ⟨558062038292977381088104145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372041358861984920725402763 558062038292977381088104145)
      ·
        refine ⟨418546528719733035816078109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558062038292977381088104145 418546528719733035816078109)
        ·
          refine ⟨156954948269899888431029291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418546528719733035816078109 156954948269899888431029291)
          ·
            refine ⟨235432422404849832646543937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156954948269899888431029291 235432422404849832646543937)
            ·
              refine ⟨176574316803637374484907953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235432422404849832646543937 176574316803637374484907953)
              ·
                refine ⟨132430737602728030863680965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176574316803637374484907953 132430737602728030863680965)
                ·
                  refine ⟨24830763300511505786940181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132430737602728030863680965 24830763300511505786940181)
                  ·
                    refine ⟨1163942029711476833762821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24830763300511505786940181 1163942029711476833762821)
                    ·
                      rfl

theorem cell23_6800307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_6800307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800307 prefixEnd_6800307 := by exact prefixLift 6800307
  have htrace : WordTrace (prefixWord ++ tailWord_6800307) baseStart_6800307 baseEnd_6800307 := by
    simpa [prefixWord, tailWord_6800307, baseEnd_6800307] using wordTrace_append hprefix tailTrace_6800307
  have hstable : (prefixWord ++ tailWord_6800307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800307).length < 2 ^ (prefixWord ++ tailWord_6800307).sum := by decide
  have hdescent : baseEnd_6800307 < baseStart_6800307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800318 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_6800318 : Nat := 118140960795 + 6800318 * 2 ^ 59
def prefixEnd_6800318 : Nat := 4983230072969 + 3 ^ 40 * 6800318 * 2
def baseEnd_6800318 : Nat := 3491831737421629958250913

theorem tailTrace_6800318 : CollatzResearch.WordTrace tailWord_6800318 prefixEnd_6800318 3491831737421629958250913 := by
  unfold tailWord_6800318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31003496722202095336948201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165351982518411175130390405 31003496722202095336948201)
  ·
    refine ⟨23252622541651571502711151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31003496722202095336948201 23252622541651571502711151)
    ·
      refine ⟨34878933812477357254066727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23252622541651571502711151 34878933812477357254066727)
      ·
        refine ⟨52318400718716035881100091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34878933812477357254066727 52318400718716035881100091)
        ·
          refine ⟨78477601078074053821650137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52318400718716035881100091 78477601078074053821650137)
          ·
            refine ⟨58858200808555540366237603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78477601078074053821650137 58858200808555540366237603)
            ·
              refine ⟨88287301212833310549356405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58858200808555540366237603 88287301212833310549356405)
              ·
                refine ⟨8276934488703122864002163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88287301212833310549356405 8276934488703122864002163)
                ·
                  refine ⟨12415401733054684296003245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276934488703122864002163 12415401733054684296003245)
                  ·
                    refine ⟨4655775649895506611001217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12415401733054684296003245 4655775649895506611001217)
                    ·
                      refine ⟨3491831737421629958250913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655775649895506611001217 3491831737421629958250913)
                      ·
                        rfl

theorem cell23_6800318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_6800318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800318 prefixEnd_6800318 := by exact prefixLift 6800318
  have htrace : WordTrace (prefixWord ++ tailWord_6800318) baseStart_6800318 baseEnd_6800318 := by
    simpa [prefixWord, tailWord_6800318, baseEnd_6800318] using wordTrace_append hprefix tailTrace_6800318
  have hstable : (prefixWord ++ tailWord_6800318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800318).length < 2 ^ (prefixWord ++ tailWord_6800318).sum := by decide
  have hdescent : baseEnd_6800318 < baseStart_6800318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800342 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6800342 : Nat := 118140960795 + 6800342 * 2 ^ 59
def prefixEnd_6800342 : Nat := 4983230072969 + 3 ^ 40 * 6800342 * 2
def baseEnd_6800342 : Nat := 3491844060957337864350803

theorem tailTrace_6800342 : CollatzResearch.WordTrace tailWord_6800342 prefixEnd_6800342 3491844060957337864350803 := by
  unfold tailWord_6800342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501803070595613424653705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165352566086353209862972853 15501803070595613424653705)
  ·
    refine ⟨11626352302946710068490279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501803070595613424653705 11626352302946710068490279)
    ·
      refine ⟨17439528454420065102735419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626352302946710068490279 17439528454420065102735419)
      ·
        refine ⟨26159292681630097654103129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17439528454420065102735419 26159292681630097654103129)
        ·
          refine ⟨19619469511222573240577347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26159292681630097654103129 19619469511222573240577347)
          ·
            refine ⟨29429204266833859860866021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19619469511222573240577347 29429204266833859860866021)
            ·
              refine ⟨5517975800031348723912379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29429204266833859860866021 5517975800031348723912379)
              ·
                refine ⟨8276963700047023085868569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517975800031348723912379 8276963700047023085868569)
                ·
                  refine ⟨6207722775035267314401427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276963700047023085868569 6207722775035267314401427)
                  ·
                    refine ⟨9311584162552900971602141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207722775035267314401427 9311584162552900971602141)
                    ·
                      refine ⟨3491844060957337864350803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311584162552900971602141 3491844060957337864350803)
                      ·
                        rfl

theorem cell23_6800342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6800342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800342 prefixEnd_6800342 := by exact prefixLift 6800342
  have htrace : WordTrace (prefixWord ++ tailWord_6800342) baseStart_6800342 baseEnd_6800342 := by
    simpa [prefixWord, tailWord_6800342, baseEnd_6800342] using wordTrace_append hprefix tailTrace_6800342
  have hstable : (prefixWord ++ tailWord_6800342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800342).length < 2 ^ (prefixWord ++ tailWord_6800342).sum := by decide
  have hdescent : baseEnd_6800342 < baseStart_6800342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800364 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_6800364 : Nat := 118140960795 + 6800364 * 2 ^ 59
def prefixEnd_6800364 : Nat := 4983230072969 + 3 ^ 40 * 6800364 * 2
def baseEnd_6800364 : Nat := 3491855357531736778275701

theorem tailTrace_6800364 : CollatzResearch.WordTrace tailWord_6800364 prefixEnd_6800364 3491855357531736778275701 := by
  unfold tailWord_6800364
  simp only [CollatzResearch.WordTrace]
  refine ⟨124014825767725056275880073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165353101023633408367840097 124014825767725056275880073)
  ·
    refine ⟨93011119325793792206910055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124014825767725056275880073 93011119325793792206910055)
    ·
      refine ⟨139516678988690688310365083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93011119325793792206910055 139516678988690688310365083)
      ·
        refine ⟨209275018483036032465547625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139516678988690688310365083 209275018483036032465547625)
        ·
          refine ⟨156956263862277024349160719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209275018483036032465547625 156956263862277024349160719)
          ·
            refine ⟨235434395793415536523741079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156956263862277024349160719 235434395793415536523741079)
            ·
              refine ⟨353151593690123304785611619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235434395793415536523741079 353151593690123304785611619)
              ·
                refine ⟨529727390535184957178417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353151593690123304785611619 529727390535184957178417429)
                ·
                  refine ⟨24830971431336794867738317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 529727390535184957178417429 24830971431336794867738317)
                  ·
                    refine ⟨9311614286751298075401869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24830971431336794867738317 9311614286751298075401869)
                    ·
                      refine ⟨3491855357531736778275701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9311614286751298075401869 3491855357531736778275701)
                      ·
                        rfl

theorem cell23_6800364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_6800364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800364 prefixEnd_6800364 := by exact prefixLift 6800364
  have htrace : WordTrace (prefixWord ++ tailWord_6800364) baseStart_6800364 baseEnd_6800364 := by
    simpa [prefixWord, tailWord_6800364, baseEnd_6800364] using wordTrace_append hprefix tailTrace_6800364
  have hstable : (prefixWord ++ tailWord_6800364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800364).length < 2 ^ (prefixWord ++ tailWord_6800364).sum := by decide
  have hdescent : baseEnd_6800364 < baseStart_6800364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800391 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6800391 : Nat := 118140960795 + 6800391 * 2 ^ 59
def prefixEnd_6800391 : Nat := 4983230072969 + 3 ^ 40 * 6800391 * 2
def baseEnd_6800391 : Nat := 3491869221509408172638077

theorem tailTrace_6800391 : CollatzResearch.WordTrace tailWord_6800391 prefixEnd_6800391 3491869221509408172638077 := by
  unfold tailWord_6800391
  simp only [CollatzResearch.WordTrace]
  refine ⟨248030636306352296162993027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165353757537568197441995351 248030636306352296162993027)
  ·
    refine ⟨372045954459528444244489541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248030636306352296162993027 372045954459528444244489541)
    ·
      refine ⟨69758616461161583295841789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372045954459528444244489541 69758616461161583295841789)
      ·
        refine ⟨26159481172935593735940671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69758616461161583295841789 26159481172935593735940671)
        ·
          refine ⟨39239221759403390603911007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26159481172935593735940671 39239221759403390603911007)
          ·
            refine ⟨58858832639105085905866511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39239221759403390603911007 58858832639105085905866511)
            ·
              refine ⟨88288248958657628858799767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58858832639105085905866511 88288248958657628858799767)
              ·
                refine ⟨132432373437986443288199651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88288248958657628858799767 132432373437986443288199651)
                ·
                  refine ⟨198648560156979664932299477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132432373437986443288199651 198648560156979664932299477)
                  ·
                    refine ⟨4655825628679210896850769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198648560156979664932299477 4655825628679210896850769)
                    ·
                      refine ⟨3491869221509408172638077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655825628679210896850769 3491869221509408172638077)
                      ·
                        rfl

theorem cell23_6800391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6800391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800391 prefixEnd_6800391 := by exact prefixLift 6800391
  have htrace : WordTrace (prefixWord ++ tailWord_6800391) baseStart_6800391 baseEnd_6800391 := by
    simpa [prefixWord, tailWord_6800391, baseEnd_6800391] using wordTrace_append hprefix tailTrace_6800391
  have hstable : (prefixWord ++ tailWord_6800391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800391).length < 2 ^ (prefixWord ++ tailWord_6800391).sum := by decide
  have hdescent : baseEnd_6800391 < baseStart_6800391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800418 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_6800418 : Nat := 118140960795 + 6800418 * 2 ^ 59
def prefixEnd_6800418 : Nat := 4983230072969 + 3 ^ 40 * 6800418 * 2
def baseEnd_6800418 : Nat := 1163961028495693189000151

theorem tailTrace_6800418 : CollatzResearch.WordTrace tailWord_6800418 prefixEnd_6800418 1163961028495693189000151 := by
  unfold tailWord_6800418
  simp only [CollatzResearch.WordTrace]
  refine ⟨62007905269313619943556477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165354414051502986516150605 62007905269313619943556477)
  ·
    refine ⟨23252964475992607478833679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62007905269313619943556477 23252964475992607478833679)
    ·
      refine ⟨34879446713988911218250519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23252964475992607478833679 34879446713988911218250519)
      ·
        refine ⟨52319170070983366827375779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34879446713988911218250519 52319170070983366827375779)
        ·
          refine ⟨78478755106475050241063669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52319170070983366827375779 78478755106475050241063669)
          ·
            refine ⟨7357383291232035960099719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78478755106475050241063669 7357383291232035960099719)
            ·
              refine ⟨11036074936848053940149579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357383291232035960099719 11036074936848053940149579)
              ·
                refine ⟨16554112405272080910224369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036074936848053940149579 16554112405272080910224369)
                ·
                  refine ⟨12415584303954060682668277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16554112405272080910224369 12415584303954060682668277)
                  ·
                    refine ⟨1163961028495693189000151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12415584303954060682668277 1163961028495693189000151)
                    ·
                      rfl

theorem cell23_6800418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_6800418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800418 prefixEnd_6800418 := by exact prefixLift 6800418
  have htrace : WordTrace (prefixWord ++ tailWord_6800418) baseStart_6800418 baseEnd_6800418 := by
    simpa [prefixWord, tailWord_6800418, baseEnd_6800418] using wordTrace_append hprefix tailTrace_6800418
  have hstable : (prefixWord ++ tailWord_6800418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800418).length < 2 ^ (prefixWord ++ tailWord_6800418).sum := by decide
  have hdescent : baseEnd_6800418 < baseStart_6800418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800421 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_6800421 : Nat := 118140960795 + 6800421 * 2 ^ 59
def prefixEnd_6800421 : Nat := 4983230072969 + 3 ^ 40 * 6800421 * 2
def baseEnd_6800421 : Nat := 3491884625929043055262939

theorem tailTrace_6800421 : CollatzResearch.WordTrace tailWord_6800421 prefixEnd_6800421 3491884625929043055262939 := by
  unfold tailWord_6800421
  simp only [CollatzResearch.WordTrace]
  refine ⟨248031730496243611286585117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165354486997495740857723411 248031730496243611286585117)
  ·
    refine ⟨93011898936091354232469419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248031730496243611286585117 93011898936091354232469419)
    ·
      refine ⟨139517848404137031348704129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93011898936091354232469419 139517848404137031348704129)
      ·
        refine ⟨104638386303102773511528097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139517848404137031348704129 104638386303102773511528097)
        ·
          refine ⟨78478789727327080133646073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104638386303102773511528097 78478789727327080133646073)
          ·
            refine ⟨58859092295495310100234555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78478789727327080133646073 58859092295495310100234555)
            ·
              refine ⟨88288638443242965150351833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58859092295495310100234555 88288638443242965150351833)
              ·
                refine ⟨66216478832432223862763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88288638443242965150351833 66216478832432223862763875)
                ·
                  refine ⟨99324718248648335794145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66216478832432223862763875 99324718248648335794145813)
                  ·
                    refine ⟨4655846167905390740350585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99324718248648335794145813 4655846167905390740350585)
                    ·
                      refine ⟨3491884625929043055262939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655846167905390740350585 3491884625929043055262939)
                      ·
                        rfl

theorem cell23_6800421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_6800421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800421 prefixEnd_6800421 := by exact prefixLift 6800421
  have htrace : WordTrace (prefixWord ++ tailWord_6800421) baseStart_6800421 baseEnd_6800421 := by
    simpa [prefixWord, tailWord_6800421, baseEnd_6800421] using wordTrace_append hprefix tailTrace_6800421
  have hstable : (prefixWord ++ tailWord_6800421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800421).length < 2 ^ (prefixWord ++ tailWord_6800421).sum := by decide
  have hdescent : baseEnd_6800421 < baseStart_6800421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800434 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6800434 : Nat := 118140960795 + 6800434 * 2 ^ 59
def prefixEnd_6800434 : Nat := 4983230072969 + 3 ^ 40 * 6800434 * 2
def baseEnd_6800434 : Nat := 3491891301177551504400379

theorem tailTrace_6800434 : CollatzResearch.WordTrace tailWord_6800434 prefixEnd_6800434 3491891301177551504400379 := by
  unfold tailWord_6800434
  simp only [CollatzResearch.WordTrace]
  refine ⟨62008051161299128626702089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165354803096797676337872237 62008051161299128626702089)
  ·
    refine ⟨46506038370974346470026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62008051161299128626702089 46506038370974346470026567)
    ·
      refine ⟨69759057556461519705039851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46506038370974346470026567 69759057556461519705039851)
      ·
        refine ⟨104638586334692279557559777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69759057556461519705039851 104638586334692279557559777)
        ·
          refine ⟨78478939751019209668169833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104638586334692279557559777 78478939751019209668169833)
          ·
            refine ⟨58859204813264407251127375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78478939751019209668169833 58859204813264407251127375)
            ·
              refine ⟨88288807219896610876691063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58859204813264407251127375 88288807219896610876691063)
              ·
                refine ⟨132433210829844916315036595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88288807219896610876691063 132433210829844916315036595)
                ·
                  refine ⟨198649816244767374472554893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132433210829844916315036595 198649816244767374472554893)
                  ·
                    refine ⟨74493681091787765427208085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198649816244767374472554893 74493681091787765427208085)
                    ·
                      refine ⟨3491891301177551504400379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74493681091787765427208085 3491891301177551504400379)
                      ·
                        rfl

theorem cell23_6800434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6800434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800434 prefixEnd_6800434 := by exact prefixLift 6800434
  have htrace : WordTrace (prefixWord ++ tailWord_6800434) baseStart_6800434 baseEnd_6800434 := by
    simpa [prefixWord, tailWord_6800434, baseEnd_6800434] using wordTrace_append hprefix tailTrace_6800434
  have hstable : (prefixWord ++ tailWord_6800434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800434).length < 2 ^ (prefixWord ++ tailWord_6800434).sum := by decide
  have hdescent : baseEnd_6800434 < baseStart_6800434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800448 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 1, 4]
def baseStart_6800448 : Nat := 118140960795 + 6800448 * 2 ^ 59
def prefixEnd_6800448 : Nat := 4983230072969 + 3 ^ 40 * 6800448 * 2
def baseEnd_6800448 : Nat := 1163966163302238149875105

theorem tailTrace_6800448 : CollatzResearch.WordTrace tailWord_6800448 prefixEnd_6800448 1163966163302238149875105 := by
  unfold tailWord_6800448
  simp only [CollatzResearch.WordTrace]
  refine ⟨124016357633572897448908999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165355143511430529931878665 124016357633572897448908999)
  ·
    refine ⟨186024536450359346173363499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124016357633572897448908999 186024536450359346173363499)
    ·
      refine ⟨279036804675539019260045249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186024536450359346173363499 279036804675539019260045249)
      ·
        refine ⟨209277603506654264445033937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279036804675539019260045249 209277603506654264445033937)
        ·
          refine ⟨156958202629990698333775453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209277603506654264445033937 156958202629990698333775453)
          ·
            refine ⟨58859325986246511875165795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156958202629990698333775453 58859325986246511875165795)
            ·
              refine ⟨88288988979369767812748693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58859325986246511875165795 88288988979369767812748693)
              ·
                refine ⟨4138546358407957866222595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88288988979369767812748693 4138546358407957866222595)
                ·
                  refine ⟨6207819537611936799333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138546358407957866222595 6207819537611936799333893)
                  ·
                    refine ⟨1163966163302238149875105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207819537611936799333893 1163966163302238149875105)
                    ·
                      rfl

theorem cell23_6800448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_6800448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800448 prefixEnd_6800448 := by exact prefixLift 6800448
  have htrace : WordTrace (prefixWord ++ tailWord_6800448) baseStart_6800448 baseEnd_6800448 := by
    simpa [prefixWord, tailWord_6800448, baseEnd_6800448] using wordTrace_append hprefix tailTrace_6800448
  have hstable : (prefixWord ++ tailWord_6800448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800448).length < 2 ^ (prefixWord ++ tailWord_6800448).sum := by decide
  have hdescent : baseEnd_6800448 < baseStart_6800448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800482 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6800482 : Nat := 118140960795 + 6800482 * 2 ^ 59
def prefixEnd_6800482 : Nat := 4983230072969 + 3 ^ 40 * 6800482 * 2
def baseEnd_6800482 : Nat := 1163971982749655772200053

theorem tailTrace_6800482 : CollatzResearch.WordTrace tailWord_6800482 prefixEnd_6800482 1163971982749655772200053 := by
  unfold tailWord_6800482
  simp only [CollatzResearch.WordTrace]
  refine ⟨62008488837255654676138925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165355970232681745803037133 62008488837255654676138925)
  ·
    refine ⟨23253183313970870503552097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62008488837255654676138925 23253183313970870503552097)
    ·
      refine ⟨17439887485478152877664073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23253183313970870503552097 17439887485478152877664073)
      ·
        refine ⟨13079915614108614658248055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17439887485478152877664073 13079915614108614658248055)
        ·
          refine ⟨19619873421162921987372083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079915614108614658248055 19619873421162921987372083)
          ·
            refine ⟨29429810131744382981058125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19619873421162921987372083 29429810131744382981058125)
            ·
              refine ⟨11036178799404143617896797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29429810131744382981058125 11036178799404143617896797)
              ·
                refine ⟨4138567049776553856711299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11036178799404143617896797 4138567049776553856711299)
                ·
                  refine ⟨6207850574664830785066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138567049776553856711299 6207850574664830785066949)
                  ·
                    refine ⟨1163971982749655772200053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207850574664830785066949 1163971982749655772200053)
                    ·
                      rfl

theorem cell23_6800482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6800482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800482 prefixEnd_6800482 := by exact prefixLift 6800482
  have htrace : WordTrace (prefixWord ++ tailWord_6800482) baseStart_6800482 baseEnd_6800482 := by
    simpa [prefixWord, tailWord_6800482, baseEnd_6800482] using wordTrace_append hprefix tailTrace_6800482
  have hstable : (prefixWord ++ tailWord_6800482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800482).length < 2 ^ (prefixWord ++ tailWord_6800482).sum := by decide
  have hdescent : baseEnd_6800482 < baseStart_6800482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800538 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_6800538 : Nat := 118140960795 + 6800538 * 2 ^ 59
def prefixEnd_6800538 : Nat := 4983230072969 + 3 ^ 40 * 6800538 * 2
def baseEnd_6800538 : Nat := 1163981567721873032499967

theorem tailTrace_6800538 : CollatzResearch.WordTrace tailWord_6800538 prefixEnd_6800538 1163981567721873032499967 := by
  unfold tailWord_6800538
  simp only [CollatzResearch.WordTrace]
  refine ⟨62008999459204935067148567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165357331891213160179062845 62008999459204935067148567)
  ·
    refine ⟨93013499188807402600722851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62008999459204935067148567 93013499188807402600722851)
    ·
      refine ⟨139520248783211103901084277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93013499188807402600722851 139520248783211103901084277)
      ·
        refine ⟨13080023323426040990726651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139520248783211103901084277 13080023323426040990726651)
        ·
          refine ⟨19620034985139061486089977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080023323426040990726651 19620034985139061486089977)
          ·
            refine ⟨14715026238854296114567483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19620034985139061486089977 14715026238854296114567483)
            ·
              refine ⟨22072539358281444171851225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715026238854296114567483 22072539358281444171851225)
              ·
                refine ⟨16554404518711083128888419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22072539358281444171851225 16554404518711083128888419)
                ·
                  refine ⟨24831606778066624693332629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16554404518711083128888419 24831606778066624693332629)
                  ·
                    refine ⟨1163981567721873032499967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24831606778066624693332629 1163981567721873032499967)
                    ·
                      rfl

theorem cell23_6800538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_6800538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800538 prefixEnd_6800538 := by exact prefixLift 6800538
  have htrace : WordTrace (prefixWord ++ tailWord_6800538) baseStart_6800538 baseEnd_6800538 := by
    simpa [prefixWord, tailWord_6800538, baseEnd_6800538] using wordTrace_append hprefix tailTrace_6800538
  have hstable : (prefixWord ++ tailWord_6800538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800538).length < 2 ^ (prefixWord ++ tailWord_6800538).sum := by decide
  have hdescent : baseEnd_6800538 < baseStart_6800538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800542 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6800542 : Nat := 118140960795 + 6800542 * 2 ^ 59
def prefixEnd_6800542 : Nat := 4983230072969 + 3 ^ 40 * 6800542 * 2
def baseEnd_6800542 : Nat := 1163982252362745693949961

theorem tailTrace_6800542 : CollatzResearch.WordTrace tailWord_6800542 prefixEnd_6800542 1163982252362745693949961 := by
  unfold tailWord_6800542
  simp only [CollatzResearch.WordTrace]
  refine ⟨31004517966100656118967485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165357429152536832634493253 31004517966100656118967485)
  ·
    refine ⟨11626694237287746044612807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31004517966100656118967485 11626694237287746044612807)
    ·
      refine ⟨17440041355931619066919211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626694237287746044612807 17440041355931619066919211)
      ·
        refine ⟨26160062033897428600378817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17440041355931619066919211 26160062033897428600378817)
        ·
          refine ⟨19620046525423071450284113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26160062033897428600378817 19620046525423071450284113)
          ·
            refine ⟨14715034894067303587713085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19620046525423071450284113 14715034894067303587713085)
            ·
              refine ⟨5518138085275238845392407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14715034894067303587713085 5518138085275238845392407)
              ·
                refine ⟨8277207127912858268088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518138085275238845392407 8277207127912858268088611)
                ·
                  refine ⟨12415810691869287402132917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277207127912858268088611 12415810691869287402132917)
                  ·
                    refine ⟨1163982252362745693949961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12415810691869287402132917 1163982252362745693949961)
                    ·
                      rfl

theorem cell23_6800542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6800542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800542 prefixEnd_6800542 := by exact prefixLift 6800542
  have htrace : WordTrace (prefixWord ++ tailWord_6800542) baseStart_6800542 baseEnd_6800542 := by
    simpa [prefixWord, tailWord_6800542, baseEnd_6800542] using wordTrace_append hprefix tailTrace_6800542
  have hstable : (prefixWord ++ tailWord_6800542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800542).length < 2 ^ (prefixWord ++ tailWord_6800542).sum := by decide
  have hdescent : baseEnd_6800542 < baseStart_6800542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800545 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6800545 : Nat := 118140960795 + 6800545 * 2 ^ 59
def prefixEnd_6800545 : Nat := 4983230072969 + 3 ^ 40 * 6800545 * 2
def baseEnd_6800545 : Nat := 3491948297530200570112369

theorem tailTrace_6800545 : CollatzResearch.WordTrace tailWord_6800545 prefixEnd_6800545 3491948297530200570112369 := by
  unfold tailWord_6800545
  simp only [CollatzResearch.WordTrace]
  refine ⟨248036253147794380464099089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165357502098529586976066059 248036253147794380464099089)
  ·
    refine ⟨186027189860845785348074317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248036253147794380464099089 186027189860845785348074317)
    ·
      refine ⟨69760196197817169505527869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186027189860845785348074317 69760196197817169505527869)
      ·
        refine ⟨26160073574181438564572951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69760196197817169505527869 26160073574181438564572951)
        ·
          refine ⟨39240110361272157846859427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26160073574181438564572951 39240110361272157846859427)
          ·
            refine ⟨58860165541908236770289141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39240110361272157846859427 58860165541908236770289141)
            ·
              refine ⟨5518140519553897197214607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58860165541908236770289141 5518140519553897197214607)
              ·
                refine ⟨8277210779330845795821911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518140519553897197214607 8277210779330845795821911)
                ·
                  refine ⟨12415816168996268693732867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277210779330845795821911 12415816168996268693732867)
                  ·
                    refine ⟨18623724253494403040599301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12415816168996268693732867 18623724253494403040599301)
                    ·
                      refine ⟨3491948297530200570112369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18623724253494403040599301 3491948297530200570112369)
                      ·
                        rfl

theorem cell23_6800545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6800545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800545 prefixEnd_6800545 := by exact prefixLift 6800545
  have htrace : WordTrace (prefixWord ++ tailWord_6800545) baseStart_6800545 baseEnd_6800545 := by
    simpa [prefixWord, tailWord_6800545, baseEnd_6800545] using wordTrace_append hprefix tailTrace_6800545
  have hstable : (prefixWord ++ tailWord_6800545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800545).length < 2 ^ (prefixWord ++ tailWord_6800545).sum := by decide
  have hdescent : baseEnd_6800545 < baseStart_6800545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800548 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_6800548 : Nat := 118140960795 + 6800548 * 2 ^ 59
def prefixEnd_6800548 : Nat := 4983230072969 + 3 ^ 40 * 6800548 * 2
def baseEnd_6800548 : Nat := 3491949837972164058374855

theorem tailTrace_6800548 : CollatzResearch.WordTrace tailWord_6800548 prefixEnd_6800548 3491949837972164058374855 := by
  unfold tailWord_6800548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124018181283391755988229149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165357575044522341317638865 124018181283391755988229149)
  ·
    refine ⟨46506817981271908495585931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124018181283391755988229149 46506817981271908495585931)
    ·
      refine ⟨69760226971907862743378897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46506817981271908495585931 69760226971907862743378897)
      ·
        refine ⟨52320170228930897057534173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69760226971907862743378897 52320170228930897057534173)
        ·
          refine ⟨19620063835849086396575315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52320170228930897057534173 19620063835849086396575315)
          ·
            refine ⟨29430095753773629594862973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620063835849086396575315 29430095753773629594862973)
            ·
              refine ⟨11036285907665111098073615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29430095753773629594862973 11036285907665111098073615)
              ·
                refine ⟨16554428861497666647110423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036285907665111098073615 16554428861497666647110423)
                ·
                  refine ⟨24831643292246499970665635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16554428861497666647110423 24831643292246499970665635)
                  ·
                    refine ⟨37247464938369749955998453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24831643292246499970665635 37247464938369749955998453)
                    ·
                      refine ⟨3491949837972164058374855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37247464938369749955998453 3491949837972164058374855)
                      ·
                        rfl

theorem cell23_6800548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_6800548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800548 prefixEnd_6800548 := by exact prefixLift 6800548
  have htrace : WordTrace (prefixWord ++ tailWord_6800548) baseStart_6800548 baseEnd_6800548 := by
    simpa [prefixWord, tailWord_6800548, baseEnd_6800548] using wordTrace_append hprefix tailTrace_6800548
  have hstable : (prefixWord ++ tailWord_6800548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800548).length < 2 ^ (prefixWord ++ tailWord_6800548).sum := by decide
  have hdescent : baseEnd_6800548 < baseStart_6800548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800551 : List Nat := [1, 1, 6, 2, 1, 12]
def baseStart_6800551 : Nat := 118140960795 + 6800551 * 2 ^ 59
def prefixEnd_6800551 : Nat := 4983230072969 + 3 ^ 40 * 6800551 * 2
def baseEnd_6800551 : Nat := 14370170281539619533487

theorem tailTrace_6800551 : CollatzResearch.WordTrace tailWord_6800551 prefixEnd_6800551 14370170281539619533487 := by
  unfold tailWord_6800551
  simp only [CollatzResearch.WordTrace]
  refine ⟨248036471985772643488817507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165357647990515095659211671 248036471985772643488817507)
  ·
    refine ⟨372054707978658965233226261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248036471985772643488817507 372054707978658965233226261)
    ·
      refine ⟨17440064436499638995307481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 372054707978658965233226261 17440064436499638995307481)
      ·
        refine ⟨13080048327374729246480611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17440064436499638995307481 13080048327374729246480611)
        ·
          refine ⟨19620072491062093869720917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080048327374729246480611 19620072491062093869720917)
          ·
            refine ⟨14370170281539619533487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19620072491062093869720917 14370170281539619533487)
            ·
              rfl

theorem cell23_6800551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 12].length) (baseStart_6800551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800551 prefixEnd_6800551 := by exact prefixLift 6800551
  have htrace : WordTrace (prefixWord ++ tailWord_6800551) baseStart_6800551 baseEnd_6800551 := by
    simpa [prefixWord, tailWord_6800551, baseEnd_6800551] using wordTrace_append hprefix tailTrace_6800551
  have hstable : (prefixWord ++ tailWord_6800551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800551).length < 2 ^ (prefixWord ++ tailWord_6800551).sum := by decide
  have hdescent : baseEnd_6800551 < baseStart_6800551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800596 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6800596 : Nat := 118140960795 + 6800596 * 2 ^ 59
def prefixEnd_6800596 : Nat := 4983230072969 + 3 ^ 40 * 6800596 * 2
def baseEnd_6800596 : Nat := 3491974485043579870574635

theorem tailTrace_6800596 : CollatzResearch.WordTrace tailWord_6800596 prefixEnd_6800596 3491974485043579870574635 := by
  unfold tailWord_6800596
  simp only [CollatzResearch.WordTrace]
  refine ⟨124019056635304808087102821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165358742180406410782803761 124019056635304808087102821)
  ·
    refine ⟨23253573119119651516331779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124019056635304808087102821 23253573119119651516331779)
    ·
      refine ⟨34880359678679477274497669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23253573119119651516331779 34880359678679477274497669)
      ·
        refine ⟨6540067439752401988968313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34880359678679477274497669 6540067439752401988968313)
        ·
          refine ⟨4905050579814301491726235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6540067439752401988968313 4905050579814301491726235)
          ·
            refine ⟨7357575869721452237589353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905050579814301491726235 7357575869721452237589353)
            ·
              refine ⟨5518181902291089178192015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357575869721452237589353 5518181902291089178192015)
              ·
                refine ⟨8277272853436633767288023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518181902291089178192015 8277272853436633767288023)
                ·
                  refine ⟨12415909280154950650932035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277272853436633767288023 12415909280154950650932035)
                  ·
                    refine ⟨18623863920232425976398053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12415909280154950650932035 18623863920232425976398053)
                    ·
                      refine ⟨3491974485043579870574635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18623863920232425976398053 3491974485043579870574635)
                      ·
                        rfl

theorem cell23_6800596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6800596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800596 prefixEnd_6800596 := by exact prefixLift 6800596
  have htrace : WordTrace (prefixWord ++ tailWord_6800596) baseStart_6800596 baseEnd_6800596 := by
    simpa [prefixWord, tailWord_6800596, baseEnd_6800596] using wordTrace_append hprefix tailTrace_6800596
  have hstable : (prefixWord ++ tailWord_6800596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800596).length < 2 ^ (prefixWord ++ tailWord_6800596).sum := by decide
  have hdescent : baseEnd_6800596 < baseStart_6800596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800668 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6800668 : Nat := 118140960795 + 6800668 * 2 ^ 59
def prefixEnd_6800668 : Nat := 4983230072969 + 3 ^ 40 * 6800668 * 2
def baseEnd_6800668 : Nat := 3492011455650703588874303

theorem tailTrace_6800668 : CollatzResearch.WordTrace tailWord_6800668 prefixEnd_6800668 3492011455650703588874303 := by
  unfold tailWord_6800668
  simp only [CollatzResearch.WordTrace]
  refine ⟨124020369663174386235413329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165360492884232514980551105 124020369663174386235413329)
  ·
    refine ⟨93015277247380789676559997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124020369663174386235413329 93015277247380789676559997)
    ·
      refine ⟨34880728967767796128709999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93015277247380789676559997 34880728967767796128709999)
      ·
        refine ⟨52321093451651694193064999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34880728967767796128709999 52321093451651694193064999)
        ·
          refine ⟨78481640177477541289597499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52321093451651694193064999 78481640177477541289597499)
          ·
            refine ⟨117722460266216311934396249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78481640177477541289597499 117722460266216311934396249)
            ·
              refine ⟨88291845199662233950797187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117722460266216311934396249 88291845199662233950797187)
              ·
                refine ⟨132437767799493350926195781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88291845199662233950797187 132437767799493350926195781)
                ·
                  refine ⟨24832081462405003298661709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132437767799493350926195781 24832081462405003298661709)
                  ·
                    refine ⟨9312030548401876236998141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24832081462405003298661709 9312030548401876236998141)
                    ·
                      refine ⟨3492011455650703588874303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312030548401876236998141 3492011455650703588874303)
                      ·
                        rfl

theorem cell23_6800668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6800668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800668 prefixEnd_6800668 := by exact prefixLift 6800668
  have htrace : WordTrace (prefixWord ++ tailWord_6800668) baseStart_6800668 baseEnd_6800668 := by
    simpa [prefixWord, tailWord_6800668, baseEnd_6800668] using wordTrace_append hprefix tailTrace_6800668
  have hstable : (prefixWord ++ tailWord_6800668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800668).length < 2 ^ (prefixWord ++ tailWord_6800668).sum := by decide
  have hdescent : baseEnd_6800668 < baseStart_6800668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800705 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6800705 : Nat := 118140960795 + 6800705 * 2 ^ 59
def prefixEnd_6800705 : Nat := 4983230072969 + 3 ^ 40 * 6800705 * 2
def baseEnd_6800705 : Nat := 1164010151478306648037211

theorem tailTrace_6800705 : CollatzResearch.WordTrace tailWord_6800705 prefixEnd_6800705 1164010151478306648037211 := by
  unfold tailWord_6800705
  simp only [CollatzResearch.WordTrace]
  refine ⟨248042088827214727789923569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165361392551476485193282379 248042088827214727789923569)
  ·
    refine ⟨186031566620411045842442677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248042088827214727789923569 186031566620411045842442677)
    ·
      refine ⟨17440459370663535547729001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186031566620411045842442677 17440459370663535547729001)
      ·
        refine ⟨13080344527997651660796751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17440459370663535547729001 13080344527997651660796751)
        ·
          refine ⟨19620516791996477491195127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080344527997651660796751 19620516791996477491195127)
          ·
            refine ⟨29430775187994716236792691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620516791996477491195127 29430775187994716236792691)
            ·
              refine ⟨44146162781992074355189037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29430775187994716236792691 44146162781992074355189037)
              ·
                refine ⟨16554811043247027883195889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44146162781992074355189037 16554811043247027883195889)
                ·
                  refine ⟨12416108282435270912396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16554811043247027883195889 12416108282435270912396917)
                  ·
                    refine ⟨1164010151478306648037211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12416108282435270912396917 1164010151478306648037211)
                    ·
                      rfl

theorem cell23_6800705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6800705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800705 prefixEnd_6800705 := by exact prefixLift 6800705
  have htrace : WordTrace (prefixWord ++ tailWord_6800705) baseStart_6800705 baseEnd_6800705 := by
    simpa [prefixWord, tailWord_6800705, baseEnd_6800705] using wordTrace_append hprefix tailTrace_6800705
  have hstable : (prefixWord ++ tailWord_6800705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800705).length < 2 ^ (prefixWord ++ tailWord_6800705).sum := by decide
  have hdescent : baseEnd_6800705 < baseStart_6800705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800725 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6800725 : Nat := 118140960795 + 6800725 * 2 ^ 59
def prefixEnd_6800725 : Nat := 4983230072969 + 3 ^ 40 * 6800725 * 2
def baseEnd_6800725 : Nat := 3492040724048009865861541

theorem tailTrace_6800725 : CollatzResearch.WordTrace tailWord_6800725 prefixEnd_6800725 3492040724048009865861541 := by
  unfold tailWord_6800725
  simp only [CollatzResearch.WordTrace]
  refine ⟨248042818287142271205651629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165361878858094847470434419 248042818287142271205651629)
  ·
    refine ⟨93016056857678351702119361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248042818287142271205651629 93016056857678351702119361)
    ·
      refine ⟨69762042643258763776589521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93016056857678351702119361 69762042643258763776589521)
      ·
        refine ⟨52321531982444072832442141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69762042643258763776589521 52321531982444072832442141)
        ·
          refine ⟨19620574493416527312165803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52321531982444072832442141 19620574493416527312165803)
          ·
            refine ⟨29430861740124790968248705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620574493416527312165803 29430861740124790968248705)
            ·
              refine ⟨22073146305093593226186529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29430861740124790968248705 22073146305093593226186529)
              ·
                refine ⟨16554859728820194919639897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22073146305093593226186529 16554859728820194919639897)
                ·
                  refine ⟨12416144796615146189729923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16554859728820194919639897 12416144796615146189729923)
                  ·
                    refine ⟨18624217194922719284594885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12416144796615146189729923 18624217194922719284594885)
                    ·
                      refine ⟨3492040724048009865861541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18624217194922719284594885 3492040724048009865861541)
                      ·
                        rfl

theorem cell23_6800725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6800725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800725 prefixEnd_6800725 := by exact prefixLift 6800725
  have htrace : WordTrace (prefixWord ++ tailWord_6800725) baseStart_6800725 baseEnd_6800725 := by
    simpa [prefixWord, tailWord_6800725, baseEnd_6800725] using wordTrace_append hprefix tailTrace_6800725
  have hstable : (prefixWord ++ tailWord_6800725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800725).length < 2 ^ (prefixWord ++ tailWord_6800725).sum := by decide
  have hdescent : baseEnd_6800725 < baseStart_6800725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800802 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6800802 : Nat := 118140960795 + 6800802 * 2 ^ 59
def prefixEnd_6800802 : Nat := 4983230072969 + 3 ^ 40 * 6800802 * 2
def baseEnd_6800802 : Nat := 3492080262058406064598687

theorem tailTrace_6800802 : CollatzResearch.WordTrace tailWord_6800802 prefixEnd_6800802 3492080262058406064598687 := by
  unfold tailWord_6800802
  simp only [CollatzResearch.WordTrace]
  refine ⟨62011406676965828339051165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165363751138575542237469773 62011406676965828339051165)
  ·
    refine ⟨23254277503862185627144187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62011406676965828339051165 23254277503862185627144187)
    ·
      refine ⟨34881416255793278440716281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254277503862185627144187 34881416255793278440716281)
      ·
        refine ⟨26161062191844958830537211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34881416255793278440716281 26161062191844958830537211)
        ·
          refine ⟨39241593287767438245805817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26161062191844958830537211 39241593287767438245805817)
          ·
            refine ⟨29431194965825578684354363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39241593287767438245805817 29431194965825578684354363)
            ·
              refine ⟨44146792448738368026531545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29431194965825578684354363 44146792448738368026531545)
              ·
                refine ⟨33110094336553776019898659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44146792448738368026531545 33110094336553776019898659)
                ·
                  refine ⟨49665141504830664029847989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33110094336553776019898659 49665141504830664029847989)
                  ·
                    refine ⟨4656107016077874752798249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49665141504830664029847989 4656107016077874752798249)
                    ·
                      refine ⟨3492080262058406064598687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656107016077874752798249 3492080262058406064598687)
                      ·
                        rfl

theorem cell23_6800802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6800802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800802 prefixEnd_6800802 := by exact prefixLift 6800802
  have htrace : WordTrace (prefixWord ++ tailWord_6800802) baseStart_6800802 baseEnd_6800802 := by
    simpa [prefixWord, tailWord_6800802, baseEnd_6800802] using wordTrace_append hprefix tailTrace_6800802
  have hstable : (prefixWord ++ tailWord_6800802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800802).length < 2 ^ (prefixWord ++ tailWord_6800802).sum := by decide
  have hdescent : baseEnd_6800802 < baseStart_6800802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800832 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2]
def baseStart_6800832 : Nat := 118140960795 + 6800832 * 2 ^ 59
def prefixEnd_6800832 : Nat := 4983230072969 + 3 ^ 40 * 6800832 * 2
def baseEnd_6800832 : Nat := 3492095666478040947223549

theorem tailTrace_6800832 : CollatzResearch.WordTrace tailWord_6800832 prefixEnd_6800832 3492095666478040947223549 := by
  unfold tailWord_6800832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124023360448877314239898375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165364480598503085653197833 124023360448877314239898375)
  ·
    refine ⟨186035040673315971359847563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124023360448877314239898375 186035040673315971359847563)
    ·
      refine ⟨279052561009973957039771345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186035040673315971359847563 279052561009973957039771345)
      ·
        refine ⟨209289420757480467779828509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279052561009973957039771345 209289420757480467779828509)
        ·
          refine ⟨78483532784055175417435691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209289420757480467779828509 78483532784055175417435691)
          ·
            refine ⟨117725299176082763126153537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78483532784055175417435691 117725299176082763126153537)
            ·
              refine ⟨88293974382062072344615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117725299176082763126153537 88293974382062072344615153)
              ·
                refine ⟨66220480786546554258461365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88293974382062072344615153 66220480786546554258461365)
                ·
                  refine ⟨6208170073738739461730753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66220480786546554258461365 6208170073738739461730753)
                  ·
                    refine ⟨4656127555304054596298065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6208170073738739461730753 4656127555304054596298065)
                    ·
                      refine ⟨3492095666478040947223549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656127555304054596298065 3492095666478040947223549)
                      ·
                        rfl

theorem cell23_6800832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_6800832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800832 prefixEnd_6800832 := by exact prefixLift 6800832
  have htrace : WordTrace (prefixWord ++ tailWord_6800832) baseStart_6800832 baseEnd_6800832 := by
    simpa [prefixWord, tailWord_6800832, baseEnd_6800832] using wordTrace_append hprefix tailTrace_6800832
  have hstable : (prefixWord ++ tailWord_6800832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800832).length < 2 ^ (prefixWord ++ tailWord_6800832).sum := by decide
  have hdescent : baseEnd_6800832 < baseStart_6800832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800869 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6800869 : Nat := 118140960795 + 6800869 * 2 ^ 59
def prefixEnd_6800869 : Nat := 4983230072969 + 3 ^ 40 * 6800869 * 2
def baseEnd_6800869 : Nat := 3492114665262257302460879

theorem tailTrace_6800869 : CollatzResearch.WordTrace tailWord_6800869 prefixEnd_6800869 3492114665262257302460879 := by
  unfold tailWord_6800869
  simp only [CollatzResearch.WordTrace]
  refine ⟨248048070398620583798893661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165365380265747055865929107 248048070398620583798893661)
  ·
    refine ⟨93018026399482718924585123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248048070398620583798893661 93018026399482718924585123)
    ·
      refine ⟨139527039599224078386877685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93018026399482718924585123 139527039599224078386877685)
      ·
        refine ⟨13080659962427257348769783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139527039599224078386877685 13080659962427257348769783)
        ·
          refine ⟨19620989943640886023154675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080659962427257348769783 19620989943640886023154675)
          ·
            refine ⟨29431484915461329034732013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620989943640886023154675 29431484915461329034732013)
            ·
              refine ⟨11036806843297998388024505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29431484915461329034732013 11036806843297998388024505)
              ·
                refine ⟨8277605132473498791018379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11036806843297998388024505 8277605132473498791018379)
                ·
                  refine ⟨12416407698710248186527569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277605132473498791018379 12416407698710248186527569)
                  ·
                    refine ⟨9312305774032686139895677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12416407698710248186527569 9312305774032686139895677)
                    ·
                      refine ⟨3492114665262257302460879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312305774032686139895677 3492114665262257302460879)
                      ·
                        rfl

theorem cell23_6800869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6800869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800869 prefixEnd_6800869 := by exact prefixLift 6800869
  have htrace : WordTrace (prefixWord ++ tailWord_6800869) baseStart_6800869 baseEnd_6800869 := by
    simpa [prefixWord, tailWord_6800869, baseEnd_6800869] using wordTrace_append hprefix tailTrace_6800869
  have hstable : (prefixWord ++ tailWord_6800869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800869).length < 2 ^ (prefixWord ++ tailWord_6800869).sum := by decide
  have hdescent : baseEnd_6800869 < baseStart_6800869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800882 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6800882 : Nat := 118140960795 + 6800882 * 2 ^ 59
def prefixEnd_6800882 : Nat := 4983230072969 + 3 ^ 40 * 6800882 * 2
def baseEnd_6800882 : Nat := 3492121340510765751598319

theorem tailTrace_6800882 : CollatzResearch.WordTrace tailWord_6800882 prefixEnd_6800882 3492121340510765751598319 := by
  unfold tailWord_6800882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62012136136893371754779225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165365696365048991346077933 62012136136893371754779225)
  ·
    refine ⟨46509102102670028816084419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62012136136893371754779225 46509102102670028816084419)
    ·
      refine ⟨69763653154005043224126629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46509102102670028816084419 69763653154005043224126629)
      ·
        refine ⟨13080684966375945604523743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69763653154005043224126629 13080684966375945604523743)
        ·
          refine ⟨19621027449563918406785615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080684966375945604523743 19621027449563918406785615)
          ·
            refine ⟨29431541174345877610178423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19621027449563918406785615 29431541174345877610178423)
            ·
              refine ⟨44147311761518816415267635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29431541174345877610178423 44147311761518816415267635)
              ·
                refine ⟨66220967642278224622901453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44147311761518816415267635 66220967642278224622901453)
                ·
                  refine ⟨24832862865854334233588045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66220967642278224622901453 24832862865854334233588045)
                  ·
                    refine ⟨9312323574695375337595517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24832862865854334233588045 9312323574695375337595517)
                    ·
                      refine ⟨3492121340510765751598319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312323574695375337595517 3492121340510765751598319)
                      ·
                        rfl

theorem cell23_6800882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6800882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800882 prefixEnd_6800882 := by exact prefixLift 6800882
  have htrace : WordTrace (prefixWord ++ tailWord_6800882) baseStart_6800882 baseEnd_6800882 := by
    simpa [prefixWord, tailWord_6800882, baseEnd_6800882] using wordTrace_append hprefix tailTrace_6800882
  have hstable : (prefixWord ++ tailWord_6800882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800882).length < 2 ^ (prefixWord ++ tailWord_6800882).sum := by decide
  have hdescent : baseEnd_6800882 < baseStart_6800882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800886 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6800886 : Nat := 118140960795 + 6800886 * 2 ^ 59
def prefixEnd_6800886 : Nat := 4983230072969 + 3 ^ 40 * 6800886 * 2
def baseEnd_6800886 : Nat := 3492123394433383735948301

theorem tailTrace_6800886 : CollatzResearch.WordTrace tailWord_6800886 prefixEnd_6800886 3492123394433383735948301 := by
  unfold tailWord_6800886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503043152472437231391407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165365793626372663801508341 15503043152472437231391407)
  ·
    refine ⟨23254564728708655847087111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503043152472437231391407 23254564728708655847087111)
    ·
      refine ⟨34881847093062983770630667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254564728708655847087111 34881847093062983770630667)
      ·
        refine ⟨52322770639594475655946001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34881847093062983770630667 52322770639594475655946001)
        ·
          refine ⟨39242077979695856741959501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52322770639594475655946001 39242077979695856741959501)
          ·
            refine ⟨14715779242385946278234813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39242077979695856741959501 14715779242385946278234813)
            ·
              refine ⟨5518417215894729854338055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14715779242385946278234813 5518417215894729854338055)
              ·
                refine ⟨8277625823842094781507083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518417215894729854338055 8277625823842094781507083)
                ·
                  refine ⟨12416438735763142172260625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277625823842094781507083 12416438735763142172260625)
                  ·
                    refine ⟨9312329051822356629195469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12416438735763142172260625 9312329051822356629195469)
                    ·
                      refine ⟨3492123394433383735948301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312329051822356629195469 3492123394433383735948301)
                      ·
                        rfl

theorem cell23_6800886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6800886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800886 prefixEnd_6800886 := by exact prefixLift 6800886
  have htrace : WordTrace (prefixWord ++ tailWord_6800886) baseStart_6800886 baseEnd_6800886 := by
    simpa [prefixWord, tailWord_6800886, baseEnd_6800886] using wordTrace_append hprefix tailTrace_6800886
  have hstable : (prefixWord ++ tailWord_6800886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800886).length < 2 ^ (prefixWord ++ tailWord_6800886).sum := by decide
  have hdescent : baseEnd_6800886 < baseStart_6800886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800915 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 6]
def baseStart_6800915 : Nat := 118140960795 + 6800915 * 2 ^ 59
def prefixEnd_6800915 : Nat := 4983230072969 + 3 ^ 40 * 6800915 * 2
def baseEnd_6800915 : Nat := 1164046095124121374161889

theorem tailTrace_6800915 : CollatzResearch.WordTrace tailWord_6800915 prefixEnd_6800915 1164046095124121374161889 := by
  unfold tailWord_6800915
  simp only [CollatzResearch.WordTrace]
  refine ⟨248049748156453933655068199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165366498770969289103378799 248049748156453933655068199)
  ·
    refine ⟨372074622234680900482602299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248049748156453933655068199 372074622234680900482602299)
    ·
      refine ⟨558111933352021350723903449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372074622234680900482602299 558111933352021350723903449)
      ·
        refine ⟨418583950014016013042927587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558111933352021350723903449 418583950014016013042927587)
        ·
          refine ⟨627875925021024019564391381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418583950014016013042927587 627875925021024019564391381)
          ·
            refine ⟨14715841992680250458540423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 627875925021024019564391381 14715841992680250458540423)
            ·
              refine ⟨22073762989020375687810635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715841992680250458540423 22073762989020375687810635)
              ·
                refine ⟨33110644483530563531715953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22073762989020375687810635 33110644483530563531715953)
                ·
                  refine ⟨24832983362647922648786965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33110644483530563531715953 24832983362647922648786965)
                  ·
                    refine ⟨1164046095124121374161889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24832983362647922648786965 1164046095124121374161889)
                    ·
                      rfl

theorem cell23_6800915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_6800915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800915 prefixEnd_6800915 := by exact prefixLift 6800915
  have htrace : WordTrace (prefixWord ++ tailWord_6800915) baseStart_6800915 baseEnd_6800915 := by
    simpa [prefixWord, tailWord_6800915, baseEnd_6800915] using wordTrace_append hprefix tailTrace_6800915
  have hstable : (prefixWord ++ tailWord_6800915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800915).length < 2 ^ (prefixWord ++ tailWord_6800915).sum := by decide
  have hdescent : baseEnd_6800915 < baseStart_6800915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800916 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6800916 : Nat := 118140960795 + 6800916 * 2 ^ 59
def prefixEnd_6800916 : Nat := 4983230072969 + 3 ^ 40 * 6800916 * 2
def baseEnd_6800916 : Nat := 3492138798853018618573163

theorem tailTrace_6800916 : CollatzResearch.WordTrace tailWord_6800916 prefixEnd_6800916 3492138798853018618573163 := by
  unfold tailWord_6800916
  simp only [CollatzResearch.WordTrace]
  refine ⟨124024892314725155412927301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165366523086300207217236401 124024892314725155412927301)
  ·
    refine ⟨23254667309010966639923869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124024892314725155412927301 23254667309010966639923869)
    ·
      refine ⟨8720500240879112489971451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23254667309010966639923869 8720500240879112489971451)
      ·
        refine ⟨13080750361318668734957177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720500240879112489971451 13080750361318668734957177)
        ·
          refine ⟨9810562770989001551217883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13080750361318668734957177 9810562770989001551217883)
          ·
            refine ⟨14715844156483502326826825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810562770989001551217883 14715844156483502326826825)
            ·
              refine ⟨11036883117362626745120119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14715844156483502326826825 11036883117362626745120119)
              ·
                refine ⟨16555324676043940117680179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036883117362626745120119 16555324676043940117680179)
                ·
                  refine ⟨24832987014065910176520269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16555324676043940117680179 24832987014065910176520269)
                  ·
                    refine ⟨9312370130274716316195101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24832987014065910176520269 9312370130274716316195101)
                    ·
                      refine ⟨3492138798853018618573163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312370130274716316195101 3492138798853018618573163)
                      ·
                        rfl

theorem cell23_6800916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6800916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800916 prefixEnd_6800916 := by exact prefixLift 6800916
  have htrace : WordTrace (prefixWord ++ tailWord_6800916) baseStart_6800916 baseEnd_6800916 := by
    simpa [prefixWord, tailWord_6800916, baseEnd_6800916] using wordTrace_append hprefix tailTrace_6800916
  have hstable : (prefixWord ++ tailWord_6800916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800916).length < 2 ^ (prefixWord ++ tailWord_6800916).sum := by decide
  have hdescent : baseEnd_6800916 < baseStart_6800916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800950 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_6800950 : Nat := 118140960795 + 6800950 * 2 ^ 59
def prefixEnd_6800950 : Nat := 4983230072969 + 3 ^ 40 * 6800950 * 2
def baseEnd_6800950 : Nat := 3492156257195271485548007

theorem tailTrace_6800950 : CollatzResearch.WordTrace tailWord_6800950 prefixEnd_6800950 3492156257195271485548007 := by
  unfold tailWord_6800950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503189044457945914537019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165367349807551423088394869 15503189044457945914537019)
  ·
    refine ⟨23254783566686918871805529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503189044457945914537019 23254783566686918871805529)
    ·
      refine ⟨17441087675015189153854147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23254783566686918871805529 17441087675015189153854147)
      ·
        refine ⟨26161631512522783730781221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441087675015189153854147 26161631512522783730781221)
        ·
          refine ⟨4905305908598021949521479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26161631512522783730781221 4905305908598021949521479)
          ·
            refine ⟨7357958862897032924282219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905305908598021949521479 7357958862897032924282219)
            ·
              refine ⟨11036938294345549386423329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357958862897032924282219 11036938294345549386423329)
              ·
                refine ⟨8277703720759162039817497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11036938294345549386423329 8277703720759162039817497)
                ·
                  refine ⟨6208277790569371529863123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8277703720759162039817497 6208277790569371529863123)
                  ·
                    refine ⟨9312416685854057294794685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208277790569371529863123 9312416685854057294794685)
                    ·
                      refine ⟨3492156257195271485548007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312416685854057294794685 3492156257195271485548007)
                      ·
                        rfl

theorem cell23_6800950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_6800950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800950 prefixEnd_6800950 := by exact prefixLift 6800950
  have htrace : WordTrace (prefixWord ++ tailWord_6800950) baseStart_6800950 baseEnd_6800950 := by
    simpa [prefixWord, tailWord_6800950, baseEnd_6800950] using wordTrace_append hprefix tailTrace_6800950
  have hstable : (prefixWord ++ tailWord_6800950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800950).length < 2 ^ (prefixWord ++ tailWord_6800950).sum := by decide
  have hdescent : baseEnd_6800950 < baseStart_6800950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800956 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_6800956 : Nat := 118140960795 + 6800956 * 2 ^ 59
def prefixEnd_6800956 : Nat := 4983230072969 + 3 ^ 40 * 6800956 * 2
def baseEnd_6800956 : Nat := 3492159338079198462072979

theorem tailTrace_6800956 : CollatzResearch.WordTrace tailWord_6800956 prefixEnd_6800956 3492159338079198462072979 := by
  unfold tailWord_6800956
  simp only [CollatzResearch.WordTrace]
  refine ⟨124025621774652698828655361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165367495699536931771540481 124025621774652698828655361)
  ·
    refine ⟨93019216330989524121491521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124025621774652698828655361 93019216330989524121491521)
    ·
      refine ⟨69764412248242143091118641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93019216330989524121491521 69764412248242143091118641)
      ·
        refine ⟨52323309186181607318338981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69764412248242143091118641 52323309186181607318338981)
        ·
          refine ⟨9810620472409051372188559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52323309186181607318338981 9810620472409051372188559)
          ·
            refine ⟨14715930708613577058282839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810620472409051372188559 14715930708613577058282839)
            ·
              refine ⟨22073896062920365587424259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715930708613577058282839 22073896062920365587424259)
              ·
                refine ⟨33110844094380548381136389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22073896062920365587424259 33110844094380548381136389)
                ·
                  refine ⟨6208283267696352821463073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33110844094380548381136389 6208283267696352821463073)
                  ·
                    refine ⟨4656212450772264616097305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6208283267696352821463073 4656212450772264616097305)
                    ·
                      refine ⟨3492159338079198462072979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656212450772264616097305 3492159338079198462072979)
                      ·
                        rfl

theorem cell23_6800956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_6800956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800956 prefixEnd_6800956 := by exact prefixLift 6800956
  have htrace : WordTrace (prefixWord ++ tailWord_6800956) baseStart_6800956 baseEnd_6800956 := by
    simpa [prefixWord, tailWord_6800956, baseEnd_6800956] using wordTrace_append hprefix tailTrace_6800956
  have hstable : (prefixWord ++ tailWord_6800956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800956).length < 2 ^ (prefixWord ++ tailWord_6800956).sum := by decide
  have hdescent : baseEnd_6800956 < baseStart_6800956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800972 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6800972 : Nat := 118140960795 + 6800972 * 2 ^ 59
def prefixEnd_6800972 : Nat := 4983230072969 + 3 ^ 40 * 6800972 * 2
def baseEnd_6800972 : Nat := 3492167553769670399472905

theorem tailTrace_6800972 : CollatzResearch.WordTrace tailWord_6800972 prefixEnd_6800972 3492167553769670399472905 := by
  unfold tailWord_6800972
  simp only [CollatzResearch.WordTrace]
  refine ⟨124025913558623716194946585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165367884744831621593262113 124025913558623716194946585)
  ·
    refine ⟨93019435168967787146209939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124025913558623716194946585 93019435168967787146209939)
    ·
      refine ⟨139529152753451680719314909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93019435168967787146209939 139529152753451680719314909)
      ·
        refine ⟨52323432282544380269743091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139529152753451680719314909 52323432282544380269743091)
        ·
          refine ⟨78485148423816570404614637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52323432282544380269743091 78485148423816570404614637)
          ·
            refine ⟨29431930658931213901730489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78485148423816570404614637 29431930658931213901730489)
            ·
              refine ⟨22073947994198410426297867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29431930658931213901730489 22073947994198410426297867)
              ·
                refine ⟨33110921991297615639446801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22073947994198410426297867 33110921991297615639446801)
                ·
                  refine ⟨24833191493473211729585101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33110921991297615639446801 24833191493473211729585101)
                  ·
                    refine ⟨9312446810052454398594413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24833191493473211729585101 9312446810052454398594413)
                    ·
                      refine ⟨3492167553769670399472905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312446810052454398594413 3492167553769670399472905)
                      ·
                        rfl

theorem cell23_6800972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6800972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800972 prefixEnd_6800972 := by exact prefixLift 6800972
  have htrace : WordTrace (prefixWord ++ tailWord_6800972) baseStart_6800972 baseEnd_6800972 := by
    simpa [prefixWord, tailWord_6800972, baseEnd_6800972] using wordTrace_append hprefix tailTrace_6800972
  have hstable : (prefixWord ++ tailWord_6800972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800972).length < 2 ^ (prefixWord ++ tailWord_6800972).sum := by decide
  have hdescent : baseEnd_6800972 < baseStart_6800972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800973 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_6800973 : Nat := 118140960795 + 6800973 * 2 ^ 59
def prefixEnd_6800973 : Nat := 4983230072969 + 3 ^ 40 * 6800973 * 2
def baseEnd_6800973 : Nat := 3492168067250324895560401

theorem tailTrace_6800973 : CollatzResearch.WordTrace tailWord_6800973 prefixEnd_6800973 3492168067250324895560401 := by
  unfold tailWord_6800973
  simp only [CollatzResearch.WordTrace]
  refine ⟨248051863590243809560679573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165367909060162539707119715 248051863590243809560679573)
  ·
    refine ⟨11627431105792678573156855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248051863590243809560679573 11627431105792678573156855)
    ·
      refine ⟨17441146658689017859735283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11627431105792678573156855 17441146658689017859735283)
      ·
        refine ⟨26161719988033526789602925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441146658689017859735283 26161719988033526789602925)
        ·
          refine ⟨9810644995512572546101097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26161719988033526789602925 9810644995512572546101097)
          ·
            refine ⟨7357983746634429409575823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9810644995512572546101097 7357983746634429409575823)
            ·
              refine ⟨11036975619951644114363735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357983746634429409575823 11036975619951644114363735)
              ·
                refine ⟨16555463429927466171545603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036975619951644114363735 16555463429927466171545603)
                ·
                  refine ⟨24833195144891199257318405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16555463429927466171545603 24833195144891199257318405)
                  ·
                    refine ⟨4656224089667099860747201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24833195144891199257318405 4656224089667099860747201)
                    ·
                      refine ⟨3492168067250324895560401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656224089667099860747201 3492168067250324895560401)
                      ·
                        rfl

theorem cell23_6800973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_6800973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800973 prefixEnd_6800973 := by exact prefixLift 6800973
  have htrace : WordTrace (prefixWord ++ tailWord_6800973) baseStart_6800973 baseEnd_6800973 := by
    simpa [prefixWord, tailWord_6800973, baseEnd_6800973] using wordTrace_append hprefix tailTrace_6800973
  have hstable : (prefixWord ++ tailWord_6800973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800973).length < 2 ^ (prefixWord ++ tailWord_6800973).sum := by decide
  have hdescent : baseEnd_6800973 < baseStart_6800973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801069 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 6]
def baseStart_6801069 : Nat := 118140960795 + 6801069 * 2 ^ 59
def prefixEnd_6801069 : Nat := 4983230072969 + 3 ^ 40 * 6801069 * 2
def baseEnd_6801069 : Nat := 388024151265906279995551

theorem tailTrace_6801069 : CollatzResearch.WordTrace tailWord_6801069 prefixEnd_6801069 388024151265906279995551 := by
  unfold tailWord_6801069
  simp only [CollatzResearch.WordTrace]
  refine ⟨248055364997896017956174261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165370243331930678637449507 248055364997896017956174261)
  ·
    refine ⟨23255190468552751683391337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248055364997896017956174261 23255190468552751683391337)
    ·
      refine ⟨17441392851414563762543503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23255190468552751683391337 17441392851414563762543503)
      ·
        refine ⟨26162089277121845643815255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441392851414563762543503 26162089277121845643815255)
        ·
          refine ⟨39243133915682768465722883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26162089277121845643815255 39243133915682768465722883)
          ·
            refine ⟨58864700873524152698584325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39243133915682768465722883 58864700873524152698584325)
            ·
              refine ⟨11037131413785778630984561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58864700873524152698584325 11037131413785778630984561)
              ·
                refine ⟨8277848560339333973238421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11037131413785778630984561 8277848560339333973238421)
                ·
                  refine ⟨388024151265906279995551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8277848560339333973238421 388024151265906279995551)
                  ·
                    rfl

theorem cell23_6801069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_6801069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801069 prefixEnd_6801069 := by exact prefixLift 6801069
  have htrace : WordTrace (prefixWord ++ tailWord_6801069) baseStart_6801069 baseEnd_6801069 := by
    simpa [prefixWord, tailWord_6801069, baseEnd_6801069] using wordTrace_append hprefix tailTrace_6801069
  have hstable : (prefixWord ++ tailWord_6801069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801069).length < 2 ^ (prefixWord ++ tailWord_6801069).sum := by decide
  have hdescent : baseEnd_6801069 < baseStart_6801069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801082 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_6801082 : Nat := 118140960795 + 6801082 * 2 ^ 59
def prefixEnd_6801082 : Nat := 4983230072969 + 3 ^ 40 * 6801082 * 2
def baseEnd_6801082 : Nat := 1164074678880554989699133

theorem tailTrace_6801082 : CollatzResearch.WordTrace tailWord_6801082 prefixEnd_6801082 1164074678880554989699133 := by
  unfold tailWord_6801082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62013959786712230294099375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165370559431232614117598333 62013959786712230294099375)
  ·
    refine ⟨93020939680068345441149063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62013959786712230294099375 93020939680068345441149063)
    ·
      refine ⟨139531409520102518161723595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93020939680068345441149063 139531409520102518161723595)
      ·
        refine ⟨209297114280153777242585393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139531409520102518161723595 209297114280153777242585393)
        ·
          refine ⟨156972835710115332931939045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209297114280153777242585393 156972835710115332931939045)
          ·
            refine ⟨29432406695646624924738571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156972835710115332931939045 29432406695646624924738571)
            ·
              refine ⟨44148610043469937387107857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29432406695646624924738571 44148610043469937387107857)
              ·
                refine ⟨33111457532602453040330893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44148610043469937387107857 33111457532602453040330893)
                ·
                  refine ⟨12416796574725919890124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33111457532602453040330893 12416796574725919890124085)
                  ·
                    refine ⟨1164074678880554989699133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12416796574725919890124085 1164074678880554989699133)
                    ·
                      rfl

theorem cell23_6801082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_6801082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801082 prefixEnd_6801082 := by exact prefixLift 6801082
  have htrace : WordTrace (prefixWord ++ tailWord_6801082) baseStart_6801082 baseEnd_6801082 := by
    simpa [prefixWord, tailWord_6801082, baseEnd_6801082] using wordTrace_append hprefix tailTrace_6801082
  have hstable : (prefixWord ++ tailWord_6801082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801082).length < 2 ^ (prefixWord ++ tailWord_6801082).sum := by decide
  have hdescent : baseEnd_6801082 < baseStart_6801082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801090 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6801090 : Nat := 118140960795 + 6801090 * 2 ^ 59
def prefixEnd_6801090 : Nat := 4983230072969 + 3 ^ 40 * 6801090 * 2
def baseEnd_6801090 : Nat := 1164076048162300312599121

theorem tailTrace_6801090 : CollatzResearch.WordTrace tailWord_6801090 prefixEnd_6801090 1164076048162300312599121 := by
  unfold tailWord_6801090
  simp only [CollatzResearch.WordTrace]
  refine ⟨62014032732704984635672181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165370753953879959028459149 62014032732704984635672181)
  ·
    refine ⟨5813815568691092309594267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62014032732704984635672181 5813815568691092309594267)
    ·
      refine ⟨8720723353036638464391401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813815568691092309594267 8720723353036638464391401)
      ·
        refine ⟨6540542514777478848293551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8720723353036638464391401 6540542514777478848293551)
        ·
          refine ⟨9810813772166218272440327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540542514777478848293551 9810813772166218272440327)
          ·
            refine ⟨14716220658249327408660491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810813772166218272440327 14716220658249327408660491)
            ·
              refine ⟨22074330987373991112990737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716220658249327408660491 22074330987373991112990737)
              ·
                refine ⟨16555748240530493334743053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22074330987373991112990737 16555748240530493334743053)
                ·
                  refine ⟨6208405590198935000528645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16555748240530493334743053 6208405590198935000528645)
                  ·
                    refine ⟨1164076048162300312599121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208405590198935000528645 1164076048162300312599121)
                    ·
                      rfl

theorem cell23_6801090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6801090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801090 prefixEnd_6801090 := by exact prefixLift 6801090
  have htrace : WordTrace (prefixWord ++ tailWord_6801090) baseStart_6801090 baseEnd_6801090 := by
    simpa [prefixWord, tailWord_6801090, baseEnd_6801090] using wordTrace_append hprefix tailTrace_6801090
  have hstable : (prefixWord ++ tailWord_6801090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801090).length < 2 ^ (prefixWord ++ tailWord_6801090).sum := by decide
  have hdescent : baseEnd_6801090 < baseStart_6801090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801092 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6801092 : Nat := 118140960795 + 6801092 * 2 ^ 59
def prefixEnd_6801092 : Nat := 4983230072969 + 3 ^ 40 * 6801092 * 2
def baseEnd_6801092 : Nat := 3492229171448209929972353

theorem tailTrace_6801092 : CollatzResearch.WordTrace tailWord_6801092 prefixEnd_6801092 3492229171448209929972353 := by
  unfold tailWord_6801092
  simp only [CollatzResearch.WordTrace]
  refine ⟨124028101938406346442130765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165370802584541795256174353 124028101938406346442130765)
  ·
    refine ⟨46510538226902379915799037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124028101938406346442130765 46510538226902379915799037)
    ·
      refine ⟨17441451835088392468424639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46510538226902379915799037 17441451835088392468424639)
      ·
        refine ⟨26162177752632588702636959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441451835088392468424639 26162177752632588702636959)
        ·
          refine ⟨39243266628948883053955439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26162177752632588702636959 39243266628948883053955439)
          ·
            refine ⟨58864899943423324580933159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39243266628948883053955439 58864899943423324580933159)
            ·
              refine ⟨88297349915134986871399739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58864899943423324580933159 88297349915134986871399739)
              ·
                refine ⟨132446024872702480307099609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88297349915134986871399739 132446024872702480307099609)
                ·
                  refine ⟨99334518654526860230324707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132446024872702480307099609 99334518654526860230324707)
                  ·
                    refine ⟨149001777981790290345487061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99334518654526860230324707 149001777981790290345487061)
                    ·
                      refine ⟨3492229171448209929972353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149001777981790290345487061 3492229171448209929972353)
                      ·
                        rfl

theorem cell23_6801092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6801092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801092 prefixEnd_6801092 := by exact prefixLift 6801092
  have htrace : WordTrace (prefixWord ++ tailWord_6801092) baseStart_6801092 baseEnd_6801092 := by
    simpa [prefixWord, tailWord_6801092, baseEnd_6801092] using wordTrace_append hprefix tailTrace_6801092
  have hstable : (prefixWord ++ tailWord_6801092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801092).length < 2 ^ (prefixWord ++ tailWord_6801092).sum := by decide
  have hdescent : baseEnd_6801092 < baseStart_6801092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801106 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6801106 : Nat := 118140960795 + 6801106 * 2 ^ 59
def prefixEnd_6801106 : Nat := 4983230072969 + 3 ^ 40 * 6801106 * 2
def baseEnd_6801106 : Nat := 3492236360177372875197289

theorem tailTrace_6801106 : CollatzResearch.WordTrace tailWord_6801106 prefixEnd_6801106 3492236360177372875197289 := by
  unfold tailWord_6801106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62014178624690493318817793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165371142999174648850180781 62014178624690493318817793)
  ·
    refine ⟨46510633968517869989113345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62014178624690493318817793 46510633968517869989113345)
    ·
      refine ⟨34882975476388402491835009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46510633968517869989113345 34882975476388402491835009)
      ·
        refine ⟨26162231607291301868876257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34882975476388402491835009 26162231607291301868876257)
        ·
          refine ⟨19621673705468476401657193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26162231607291301868876257 19621673705468476401657193)
          ·
            refine ⟨14716255279101357301242895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19621673705468476401657193 14716255279101357301242895)
            ·
              refine ⟨22074382918652035951864343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716255279101357301242895 22074382918652035951864343)
              ·
                refine ⟨33111574377978053927796515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22074382918652035951864343 33111574377978053927796515)
                ·
                  refine ⟨49667361566967080891694773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33111574377978053927796515 49667361566967080891694773)
                  ·
                    refine ⟨4656315146903163833596385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49667361566967080891694773 4656315146903163833596385)
                    ·
                      refine ⟨3492236360177372875197289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656315146903163833596385 3492236360177372875197289)
                      ·
                        rfl

theorem cell23_6801106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6801106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801106 prefixEnd_6801106 := by exact prefixLift 6801106
  have htrace : WordTrace (prefixWord ++ tailWord_6801106) baseStart_6801106 baseEnd_6801106 := by
    simpa [prefixWord, tailWord_6801106, baseEnd_6801106] using wordTrace_append hprefix tailTrace_6801106
  have hstable : (prefixWord ++ tailWord_6801106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801106).length < 2 ^ (prefixWord ++ tailWord_6801106).sum := by decide
  have hdescent : baseEnd_6801106 < baseStart_6801106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801112 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_6801112 : Nat := 118140960795 + 6801112 * 2 ^ 59
def prefixEnd_6801112 : Nat := 4983230072969 + 3 ^ 40 * 6801112 * 2
def baseEnd_6801112 : Nat := 1164079813687099950574087

theorem tailTrace_6801112 : CollatzResearch.WordTrace tailWord_6801112 prefixEnd_6801112 1164079813687099950574087 := by
  unfold tailWord_6801112
  simp only [CollatzResearch.WordTrace]
  refine ⟨124028466668370118149994795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165371288891160157533326393 124028466668370118149994795)
  ·
    refine ⟨186042700002555177224992193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124028466668370118149994795 186042700002555177224992193)
    ·
      refine ⟨139532025001916382918744145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186042700002555177224992193 139532025001916382918744145)
      ·
        refine ⟨104649018751437287189058109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139532025001916382918744145 104649018751437287189058109)
        ·
          refine ⟨39243382031788982695896791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104649018751437287189058109 39243382031788982695896791)
          ·
            refine ⟨58865073047683474043845187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39243382031788982695896791 58865073047683474043845187)
            ·
              refine ⟨88297609571525211065767781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58865073047683474043845187 88297609571525211065767781)
              ·
                refine ⟨16555801794660977074831459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88297609571525211065767781 16555801794660977074831459)
                ·
                  refine ⟨24833702691991465612247189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16555801794660977074831459 24833702691991465612247189)
                  ·
                    refine ⟨1164079813687099950574087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24833702691991465612247189 1164079813687099950574087)
                    ·
                      rfl

theorem cell23_6801112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_6801112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801112 prefixEnd_6801112 := by exact prefixLift 6801112
  have htrace : WordTrace (prefixWord ++ tailWord_6801112) baseStart_6801112 baseEnd_6801112 := by
    simpa [prefixWord, tailWord_6801112, baseEnd_6801112] using wordTrace_append hprefix tailTrace_6801112
  have hstable : (prefixWord ++ tailWord_6801112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801112).length < 2 ^ (prefixWord ++ tailWord_6801112).sum := by decide
  have hdescent : baseEnd_6801112 < baseStart_6801112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801113 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 1, 1, 3]
def baseStart_6801113 : Nat := 118140960795 + 6801113 * 2 ^ 59
def prefixEnd_6801113 : Nat := 4983230072969 + 3 ^ 40 * 6801113 * 2
def baseEnd_6801113 : Nat := 3492239954541954347809757

theorem tailTrace_6801113 : CollatzResearch.WordTrace tailWord_6801113 prefixEnd_6801113 3492239954541954347809757 := by
  unfold tailWord_6801113
  simp only [CollatzResearch.WordTrace]
  refine ⟨248056969809736613470775993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165371313206491075647183995 248056969809736613470775993)
  ·
    refine ⟨186042727357302460103081995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248056969809736613470775993 186042727357302460103081995)
    ·
      refine ⟨279064091035953690154622993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186042727357302460103081995 279064091035953690154622993)
      ·
        refine ⟨209298068276965267615967245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279064091035953690154622993 209298068276965267615967245)
        ·
          refine ⟨78486775603861975355987717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209298068276965267615967245 78486775603861975355987717)
          ·
            refine ⟨14716270425724120379247697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78486775603861975355987717 14716270425724120379247697)
            ·
              refine ⟨11037202819293090284435773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14716270425724120379247697 11037202819293090284435773)
              ·
                refine ⟨4138951057234908856663415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11037202819293090284435773 4138951057234908856663415)
                ·
                  refine ⟨6208426585852363284995123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138951057234908856663415 6208426585852363284995123)
                  ·
                    refine ⟨9312639878778544927492685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208426585852363284995123 9312639878778544927492685)
                    ·
                      refine ⟨3492239954541954347809757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312639878778544927492685 3492239954541954347809757)
                      ·
                        rfl

theorem cell23_6801113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_6801113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801113 prefixEnd_6801113 := by exact prefixLift 6801113
  have htrace : WordTrace (prefixWord ++ tailWord_6801113) baseStart_6801113 baseEnd_6801113 := by
    simpa [prefixWord, tailWord_6801113, baseEnd_6801113] using wordTrace_append hprefix tailTrace_6801113
  have hstable : (prefixWord ++ tailWord_6801113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801113).length < 2 ^ (prefixWord ++ tailWord_6801113).sum := by decide
  have hdescent : baseEnd_6801113 < baseStart_6801113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801119 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_6801119 : Nat := 118140960795 + 6801119 * 2 ^ 59
def prefixEnd_6801119 : Nat := 4983230072969 + 3 ^ 40 * 6801119 * 2
def baseEnd_6801119 : Nat := 3492243035425881324334729

theorem tailTrace_6801119 : CollatzResearch.WordTrace tailWord_6801119 prefixEnd_6801119 3492243035425881324334729 := by
  unfold tailWord_6801119
  simp only [CollatzResearch.WordTrace]
  refine ⟨248057188647714876495494411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165371459098476584330329607 248057188647714876495494411)
  ·
    refine ⟨372085782971572314743241617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248057188647714876495494411 372085782971572314743241617)
    ·
      refine ⟨279064337228679236057431213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372085782971572314743241617 279064337228679236057431213)
      ·
        refine ⟨104649126460754713521536705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279064337228679236057431213 104649126460754713521536705)
        ·
          refine ⟨78486844845566035141152529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104649126460754713521536705 78486844845566035141152529)
          ·
            refine ⟨58865133634174526355864397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78486844845566035141152529 58865133634174526355864397)
            ·
              refine ⟨22074425112815447383449149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58865133634174526355864397 22074425112815447383449149)
              ·
                refine ⟨8277909417305792768793431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22074425112815447383449149 8277909417305792768793431)
                ·
                  refine ⟨12416864125958689153190147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277909417305792768793431 12416864125958689153190147)
                  ·
                    refine ⟨18625296188938033729785221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12416864125958689153190147 18625296188938033729785221)
                    ·
                      refine ⟨3492243035425881324334729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18625296188938033729785221 3492243035425881324334729)
                      ·
                        rfl

theorem cell23_6801119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_6801119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801119 prefixEnd_6801119 := by exact prefixLift 6801119
  have htrace : WordTrace (prefixWord ++ tailWord_6801119) baseStart_6801119 baseEnd_6801119 := by
    simpa [prefixWord, tailWord_6801119, baseEnd_6801119] using wordTrace_append hprefix tailTrace_6801119
  have hstable : (prefixWord ++ tailWord_6801119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801119).length < 2 ^ (prefixWord ++ tailWord_6801119).sum := by decide
  have hdescent : baseEnd_6801119 < baseStart_6801119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801132 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6801132 : Nat := 118140960795 + 6801132 * 2 ^ 59
def prefixEnd_6801132 : Nat := 4983230072969 + 3 ^ 40 * 6801132 * 2
def baseEnd_6801132 : Nat := 3492249710674389773472169

theorem tailTrace_6801132 : CollatzResearch.WordTrace tailWord_6801132 prefixEnd_6801132 3492249710674389773472169 := by
  unfold tailWord_6801132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124028831398333889857858825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165371775197778519810478433 124028831398333889857858825)
  ·
    refine ⟨93021623548750417393394119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124028831398333889857858825 93021623548750417393394119)
    ·
      refine ⟨139532435323125626090091179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93021623548750417393394119 139532435323125626090091179)
      ·
        refine ⟨209298652984688439135136769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139532435323125626090091179 209298652984688439135136769)
        ·
          refine ⟨156973989738516329351352577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209298652984688439135136769 156973989738516329351352577)
          ·
            refine ⟨117730492303887247013514433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156973989738516329351352577 117730492303887247013514433)
            ·
              refine ⟨88297869227915435260135825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117730492303887247013514433 88297869227915435260135825)
              ·
                refine ⟨66223401920936576445101869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88297869227915435260135825 66223401920936576445101869)
                ·
                  refine ⟨24833775720351216166913201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66223401920936576445101869 24833775720351216166913201)
                  ·
                    refine ⟨18625331790263412125184901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24833775720351216166913201 18625331790263412125184901)
                    ·
                      refine ⟨3492249710674389773472169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18625331790263412125184901 3492249710674389773472169)
                      ·
                        rfl

theorem cell23_6801132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6801132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801132 prefixEnd_6801132 := by exact prefixLift 6801132
  have htrace : WordTrace (prefixWord ++ tailWord_6801132) baseStart_6801132 baseEnd_6801132 := by
    simpa [prefixWord, tailWord_6801132, baseEnd_6801132] using wordTrace_append hprefix tailTrace_6801132
  have hstable : (prefixWord ++ tailWord_6801132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801132).length < 2 ^ (prefixWord ++ tailWord_6801132).sum := by decide
  have hdescent : baseEnd_6801132 < baseStart_6801132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801156 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6801156 : Nat := 118140960795 + 6801156 * 2 ^ 59
def prefixEnd_6801156 : Nat := 4983230072969 + 3 ^ 40 * 6801156 * 2
def baseEnd_6801156 : Nat := 3492262034210097679572059

theorem tailTrace_6801156 : CollatzResearch.WordTrace tailWord_6801156 prefixEnd_6801156 3492262034210097679572059 := by
  unfold tailWord_6801156
  simp only [CollatzResearch.WordTrace]
  refine ⟨124029269074290415907295661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165372358765720554543060881 124029269074290415907295661)
  ·
    refine ⟨46510975902858905965235873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124029269074290415907295661 46510975902858905965235873)
    ·
      refine ⟨34883231927144179473926905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46510975902858905965235873 34883231927144179473926905)
      ·
        refine ⟨26162423945358134605445179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34883231927144179473926905 26162423945358134605445179)
        ·
          refine ⟨39243635918037201908167769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26162423945358134605445179 39243635918037201908167769)
          ·
            refine ⟨29432726938527901431125827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39243635918037201908167769 29432726938527901431125827)
            ·
              refine ⟨44149090407791852146688741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29432726938527901431125827 44149090407791852146688741)
              ·
                refine ⟨8277954451460972277504139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44149090407791852146688741 8277954451460972277504139)
                ·
                  refine ⟨12416931677191458416256209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277954451460972277504139 12416931677191458416256209)
                  ·
                    refine ⟨9312698757893593812192157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12416931677191458416256209 9312698757893593812192157)
                    ·
                      refine ⟨3492262034210097679572059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312698757893593812192157 3492262034210097679572059)
                      ·
                        rfl

theorem cell23_6801156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6801156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801156 prefixEnd_6801156 := by exact prefixLift 6801156
  have htrace : WordTrace (prefixWord ++ tailWord_6801156) baseStart_6801156 baseEnd_6801156 := by
    simpa [prefixWord, tailWord_6801156, baseEnd_6801156] using wordTrace_append hprefix tailTrace_6801156
  have hstable : (prefixWord ++ tailWord_6801156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801156).length < 2 ^ (prefixWord ++ tailWord_6801156).sum := by decide
  have hdescent : baseEnd_6801156 < baseStart_6801156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801158 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6801158 : Nat := 118140960795 + 6801158 * 2 ^ 59
def prefixEnd_6801158 : Nat := 4983230072969 + 3 ^ 40 * 6801158 * 2
def baseEnd_6801158 : Nat := 1164087687057135557249017

theorem tailTrace_6801158 : CollatzResearch.WordTrace tailWord_6801158 prefixEnd_6801158 1164087687057135557249017 := by
  unfold tailWord_6801158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751831596705424567380129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165372407396382390770776085 7751831596705424567380129)
  ·
    refine ⟨5813873697529068425535097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7751831596705424567380129 5813873697529068425535097)
    ·
      refine ⟨4360405273146801319151323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5813873697529068425535097 4360405273146801319151323)
      ·
        refine ⟨6540607909720201978726985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360405273146801319151323 6540607909720201978726985)
        ·
          refine ⟨4905455932290151484045239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6540607909720201978726985 4905455932290151484045239)
          ·
            refine ⟨7358183898435227226067859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905455932290151484045239 7358183898435227226067859)
            ·
              refine ⟨11037275847652840839101789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358183898435227226067859 11037275847652840839101789)
              ·
                refine ⟨4138978442869815314663171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11037275847652840839101789 4138978442869815314663171)
                ·
                  refine ⟨6208467664304722971994757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138978442869815314663171 6208467664304722971994757)
                  ·
                    refine ⟨1164087687057135557249017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208467664304722971994757 1164087687057135557249017)
                    ·
                      rfl

theorem cell23_6801158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6801158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801158 prefixEnd_6801158 := by exact prefixLift 6801158
  have htrace : WordTrace (prefixWord ++ tailWord_6801158) baseStart_6801158 baseEnd_6801158 := by
    simpa [prefixWord, tailWord_6801158, baseEnd_6801158] using wordTrace_append hprefix tailTrace_6801158
  have hstable : (prefixWord ++ tailWord_6801158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801158).length < 2 ^ (prefixWord ++ tailWord_6801158).sum := by decide
  have hdescent : baseEnd_6801158 < baseStart_6801158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801159 : List Nat := [1, 1, 4, 4, 2, 1, 1, 9]
def baseStart_6801159 : Nat := 118140960795 + 6801159 * 2 ^ 59
def prefixEnd_6801159 : Nat := 4983230072969 + 3 ^ 40 * 6801159 * 2
def baseEnd_6801159 : Nat := 129343095357483746956835

theorem tailTrace_6801159 : CollatzResearch.WordTrace tailWord_6801159 prefixEnd_6801159 129343095357483746956835 := by
  unfold tailWord_6801159
  simp only [CollatzResearch.WordTrace]
  refine ⟨248058647567569963326950531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165372431711713308884633687 248058647567569963326950531)
  ·
    refine ⟨372087971351354944990425797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248058647567569963326950531 372087971351354944990425797)
    ·
      refine ⟨69766494628379052185704837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372087971351354944990425797 69766494628379052185704837)
      ·
        refine ⟨13081217742821072284819657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69766494628379052185704837 13081217742821072284819657)
        ·
          refine ⟨9810913307115804213614743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13081217742821072284819657 9810913307115804213614743)
          ·
            refine ⟨14716369960673706320422115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810913307115804213614743 14716369960673706320422115)
            ·
              refine ⟨22074554941010559480633173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716369960673706320422115 22074554941010559480633173)
              ·
                refine ⟨129343095357483746956835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22074554941010559480633173 129343095357483746956835)
                ·
                  rfl

theorem cell23_6801159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 9].length) (baseStart_6801159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801159 prefixEnd_6801159 := by exact prefixLift 6801159
  have htrace : WordTrace (prefixWord ++ tailWord_6801159) baseStart_6801159 baseEnd_6801159 := by
    simpa [prefixWord, tailWord_6801159, baseEnd_6801159] using wordTrace_append hprefix tailTrace_6801159
  have hstable : (prefixWord ++ tailWord_6801159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801159).length < 2 ^ (prefixWord ++ tailWord_6801159).sum := by decide
  have hdescent : baseEnd_6801159 < baseStart_6801159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801186 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_6801186 : Nat := 118140960795 + 6801186 * 2 ^ 59
def prefixEnd_6801186 : Nat := 4983230072969 + 3 ^ 40 * 6801186 * 2
def baseEnd_6801186 : Nat := 3492277438629732562196921

theorem tailTrace_6801186 : CollatzResearch.WordTrace tailWord_6801186 prefixEnd_6801186 3492277438629732562196921 := by
  unfold tailWord_6801186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62014908084618036734545853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165373088225648097958788941 62014908084618036734545853)
  ·
    refine ⟨23255590531731763775454695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62014908084618036734545853 23255590531731763775454695)
    ·
      refine ⟨34883385797597645663182043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23255590531731763775454695 34883385797597645663182043)
      ·
        refine ⟨52325078696396468494773065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34883385797597645663182043 52325078696396468494773065)
        ·
          refine ⟨39243809022297351371079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52325078696396468494773065 39243809022297351371079799)
          ·
            refine ⟨58865713533446027056619699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39243809022297351371079799 58865713533446027056619699)
            ·
              refine ⟨88298570300169040584929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58865713533446027056619699 88298570300169040584929549)
              ·
                refine ⟨33111963862563390219348581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88298570300169040584929549 33111963862563390219348581)
                ·
                  refine ⟨6208493224230635666127859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33111963862563390219348581 6208493224230635666127859)
                  ·
                    refine ⟨9312739836345953499191789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208493224230635666127859 9312739836345953499191789)
                    ·
                      refine ⟨3492277438629732562196921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312739836345953499191789 3492277438629732562196921)
                      ·
                        rfl

theorem cell23_6801186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_6801186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801186 prefixEnd_6801186 := by exact prefixLift 6801186
  have htrace : WordTrace (prefixWord ++ tailWord_6801186) baseStart_6801186 baseEnd_6801186 := by
    simpa [prefixWord, tailWord_6801186, baseEnd_6801186] using wordTrace_append hprefix tailTrace_6801186
  have hstable : (prefixWord ++ tailWord_6801186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801186).length < 2 ^ (prefixWord ++ tailWord_6801186).sum := by decide
  have hdescent : baseEnd_6801186 < baseStart_6801186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801203 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 3]
def baseStart_6801203 : Nat := 118140960795 + 6801203 * 2 ^ 59
def prefixEnd_6801203 : Nat := 4983230072969 + 3 ^ 40 * 6801203 * 2
def baseEnd_6801203 : Nat := 3492286167800858995684343

theorem tailTrace_6801203 : CollatzResearch.WordTrace tailWord_6801203 prefixEnd_6801203 3492286167800858995684343 := by
  unfold tailWord_6801203
  simp only [CollatzResearch.WordTrace]
  refine ⟨248060252379410558841552263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165373501586273705894368175 248060252379410558841552263)
  ·
    refine ⟨372090378569115838262328395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248060252379410558841552263 372090378569115838262328395)
    ·
      refine ⟨558135567853673757393492593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372090378569115838262328395 558135567853673757393492593)
      ·
        refine ⟨418601675890255318045119445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558135567853673757393492593 418601675890255318045119445)
        ·
          refine ⟨9810976778677859016682487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 418601675890255318045119445 9810976778677859016682487)
          ·
            refine ⟨14716465168016788525023731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810976778677859016682487 14716465168016788525023731)
            ·
              refine ⟨22074697752025182787535597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716465168016788525023731 22074697752025182787535597)
              ·
                refine ⟨8278011657009443545325849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22074697752025182787535597 8278011657009443545325849)
                ·
                  refine ⟨6208508742757082658994387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8278011657009443545325849 6208508742757082658994387)
                  ·
                    refine ⟨9312763114135623988491581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208508742757082658994387 9312763114135623988491581)
                    ·
                      refine ⟨3492286167800858995684343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312763114135623988491581 3492286167800858995684343)
                      ·
                        rfl

theorem cell23_6801203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_6801203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801203 prefixEnd_6801203 := by exact prefixLift 6801203
  have htrace : WordTrace (prefixWord ++ tailWord_6801203) baseStart_6801203 baseEnd_6801203 := by
    simpa [prefixWord, tailWord_6801203, baseEnd_6801203] using wordTrace_append hprefix tailTrace_6801203
  have hstable : (prefixWord ++ tailWord_6801203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801203).length < 2 ^ (prefixWord ++ tailWord_6801203).sum := by decide
  have hdescent : baseEnd_6801203 < baseStart_6801203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801213 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6801213 : Nat := 118140960795 + 6801213 * 2 ^ 59
def prefixEnd_6801213 : Nat := 4983230072969 + 3 ^ 40 * 6801213 * 2
def baseEnd_6801213 : Nat := 3492291302607403956559297

theorem tailTrace_6801213 : CollatzResearch.WordTrace tailWord_6801213 prefixEnd_6801213 3492291302607403956559297 := by
  unfold tailWord_6801213
  simp only [CollatzResearch.WordTrace]
  refine ⟨248060617109374330549416293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165373744739582887032944195 248060617109374330549416293)
  ·
    refine ⟨46511365708007686978015555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248060617109374330549416293 46511365708007686978015555)
    ·
      refine ⟨69767048562011530467023333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46511365708007686978015555 69767048562011530467023333)
      ·
        refine ⟨13081321605377161962566875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69767048562011530467023333 13081321605377161962566875)
        ·
          refine ⟨19621982408065742943850313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13081321605377161962566875 19621982408065742943850313)
          ·
            refine ⟨14716486806049307207887735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19621982408065742943850313 14716486806049307207887735)
            ·
              refine ⟨22074730209073960811831603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716486806049307207887735 22074730209073960811831603)
              ·
                refine ⟨33112095313610941217747405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22074730209073960811831603 33112095313610941217747405)
                ·
                  refine ⟨12417035742604102956655277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33112095313610941217747405 12417035742604102956655277)
                  ·
                    refine ⟨4656388403476538608745729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12417035742604102956655277 4656388403476538608745729)
                    ·
                      refine ⟨3492291302607403956559297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656388403476538608745729 3492291302607403956559297)
                      ·
                        rfl

theorem cell23_6801213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6801213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801213 prefixEnd_6801213 := by exact prefixLift 6801213
  have htrace : WordTrace (prefixWord ++ tailWord_6801213) baseStart_6801213 baseEnd_6801213 := by
    simpa [prefixWord, tailWord_6801213, baseEnd_6801213] using wordTrace_append hprefix tailTrace_6801213
  have hstable : (prefixWord ++ tailWord_6801213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801213).length < 2 ^ (prefixWord ++ tailWord_6801213).sum := by decide
  have hdescent : baseEnd_6801213 < baseStart_6801213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801226 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_6801226 : Nat := 118140960795 + 6801226 * 2 ^ 59
def prefixEnd_6801226 : Nat := 4983230072969 + 3 ^ 40 * 6801226 * 2
def baseEnd_6801226 : Nat := 3492297977855912405696737

theorem tailTrace_6801226 : CollatzResearch.WordTrace tailWord_6801226 prefixEnd_6801226 3492297977855912405696737 := by
  unfold tailWord_6801226
  simp only [CollatzResearch.WordTrace]
  refine ⟨62015272814581808442409883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165374060838884822513093021 62015272814581808442409883)
  ·
    refine ⟨93022909221872712663614825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62015272814581808442409883 93022909221872712663614825)
    ·
      refine ⟨69767181916404534497711119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93022909221872712663614825 69767181916404534497711119)
      ·
        refine ⟨104650772874606801746566679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69767181916404534497711119 104650772874606801746566679)
        ·
          refine ⟨156976159311910202619850019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104650772874606801746566679 156976159311910202619850019)
          ·
            refine ⟨235464238967865303929775029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156976159311910202619850019 235464238967865303929775029)
            ·
              refine ⟨22074772403237372243416409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235464238967865303929775029 22074772403237372243416409)
              ·
                refine ⟨16556079302428029182562307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22074772403237372243416409 16556079302428029182562307)
                ·
                  refine ⟨24834118953642043773843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16556079302428029182562307 24834118953642043773843461)
                  ·
                    refine ⟨4656397303807883207595649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24834118953642043773843461 4656397303807883207595649)
                    ·
                      refine ⟨3492297977855912405696737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656397303807883207595649 3492297977855912405696737)
                      ·
                        rfl

theorem cell23_6801226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_6801226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801226 prefixEnd_6801226 := by exact prefixLift 6801226
  have htrace : WordTrace (prefixWord ++ tailWord_6801226) baseStart_6801226 baseEnd_6801226 := by
    simpa [prefixWord, tailWord_6801226, baseEnd_6801226] using wordTrace_append hprefix tailTrace_6801226
  have hstable : (prefixWord ++ tailWord_6801226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801226).length < 2 ^ (prefixWord ++ tailWord_6801226).sum := by decide
  have hdescent : baseEnd_6801226 < baseStart_6801226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801294 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6801294 : Nat := 118140960795 + 6801294 * 2 ^ 59
def prefixEnd_6801294 : Nat := 4983230072969 + 3 ^ 40 * 6801294 * 2
def baseEnd_6801294 : Nat := 3492332894540418139646425

theorem tailTrace_6801294 : CollatzResearch.WordTrace tailWord_6801294 prefixEnd_6801294 3492332894540418139646425 := by
  unfold tailWord_6801294
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007946427760110172889367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165375714281387254255409957 31007946427760110172889367)
  ·
    refine ⟨46511919641640165259334051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007946427760110172889367 46511919641640165259334051)
    ·
      refine ⟨69767879462460247889001077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46511919641640165259334051 69767879462460247889001077)
      ·
        refine ⟨6540738699605648239593851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69767879462460247889001077 6540738699605648239593851)
        ·
          refine ⟨9811108049408472359390777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540738699605648239593851 9811108049408472359390777)
          ·
            refine ⟨7358331037056354269543083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9811108049408472359390777 7358331037056354269543083)
            ·
              refine ⟨11037496555584531404314625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358331037056354269543083 11037496555584531404314625)
              ·
                refine ⟨8278122416688398553235969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11037496555584531404314625 8278122416688398553235969)
                ·
                  refine ⟨6208591812516298914926977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8278122416688398553235969 6208591812516298914926977)
                  ·
                    refine ⟨4656443859387224186195233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6208591812516298914926977 4656443859387224186195233)
                    ·
                      refine ⟨3492332894540418139646425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656443859387224186195233 3492332894540418139646425)
                      ·
                        rfl

theorem cell23_6801294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6801294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801294 prefixEnd_6801294 := by exact prefixLift 6801294
  have htrace : WordTrace (prefixWord ++ tailWord_6801294) baseStart_6801294 baseEnd_6801294 := by
    simpa [prefixWord, tailWord_6801294, baseEnd_6801294] using wordTrace_append hprefix tailTrace_6801294
  have hstable : (prefixWord ++ tailWord_6801294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801294).length < 2 ^ (prefixWord ++ tailWord_6801294).sum := by decide
  have hdescent : baseEnd_6801294 < baseStart_6801294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801336 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_6801336 : Nat := 118140960795 + 6801336 * 2 ^ 59
def prefixEnd_6801336 : Nat := 4983230072969 + 3 ^ 40 * 6801336 * 2
def baseEnd_6801336 : Nat := 3492354460727906975321231

theorem tailTrace_6801336 : CollatzResearch.WordTrace tailWord_6801336 prefixEnd_6801336 3492354460727906975321231 := by
  unfold tailWord_6801336
  simp only [CollatzResearch.WordTrace]
  refine ⟨124032551643964361278071931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165376735525285815037429241 124032551643964361278071931)
  ·
    refine ⟨186048827465946541917107897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124032551643964361278071931 186048827465946541917107897)
    ·
      refine ⟨139536620599459906437830923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186048827465946541917107897 139536620599459906437830923)
      ·
        refine ⟨209304930899189859656746385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139536620599459906437830923 209304930899189859656746385)
        ·
          refine ⟨156978698174392394742559789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209304930899189859656746385 156978698174392394742559789)
          ·
            refine ⟨58867011815397148028459921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156978698174392394742559789 58867011815397148028459921)
            ·
              refine ⟨44150258861547861021344941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58867011815397148028459921 44150258861547861021344941)
              ·
                refine ⟨16556347073080447883004353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44150258861547861021344941 16556347073080447883004353)
                ·
                  refine ⟨12417260304810335912253265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16556347073080447883004353 12417260304810335912253265)
                  ·
                    refine ⟨9312945228607751934189949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12417260304810335912253265 9312945228607751934189949)
                    ·
                      refine ⟨3492354460727906975321231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9312945228607751934189949 3492354460727906975321231)
                      ·
                        rfl

theorem cell23_6801336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_6801336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801336 prefixEnd_6801336 := by exact prefixLift 6801336
  have htrace : WordTrace (prefixWord ++ tailWord_6801336) baseStart_6801336 baseEnd_6801336 := by
    simpa [prefixWord, tailWord_6801336, baseEnd_6801336] using wordTrace_append hprefix tailTrace_6801336
  have hstable : (prefixWord ++ tailWord_6801336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801336).length < 2 ^ (prefixWord ++ tailWord_6801336).sum := by decide
  have hdescent : baseEnd_6801336 < baseStart_6801336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801373 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 6]
def baseStart_6801373 : Nat := 118140960795 + 6801373 * 2 ^ 59
def prefixEnd_6801373 : Nat := 4983230072969 + 3 ^ 40 * 6801373 * 2
def baseEnd_6801373 : Nat := 388041495501347036728729

theorem tailTrace_6801373 : CollatzResearch.WordTrace tailWord_6801373 prefixEnd_6801373 388041495501347036728729 := by
  unfold tailWord_6801373
  simp only [CollatzResearch.WordTrace]
  refine ⟨248066452788794677875240773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165377635192529785250160515 248066452788794677875240773)
  ·
    refine ⟨46512459897899002101607645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248066452788794677875240773 46512459897899002101607645)
    ·
      refine ⟨17442172461712125788102867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46512459897899002101607645 17442172461712125788102867)
      ·
        refine ⟨26163258692568188682154301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17442172461712125788102867 26163258692568188682154301)
        ·
          refine ⟨9811222009713070755807863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26163258692568188682154301 9811222009713070755807863)
          ·
            refine ⟨14716833014569606133711795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9811222009713070755807863 14716833014569606133711795)
            ·
              refine ⟨22075249521854409200567693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716833014569606133711795 22075249521854409200567693)
              ·
                refine ⟨8278218570695403450212885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22075249521854409200567693 8278218570695403450212885)
                ·
                  refine ⟨388041495501347036728729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8278218570695403450212885 388041495501347036728729)
                  ·
                    rfl

theorem cell23_6801373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_6801373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801373 prefixEnd_6801373 := by exact prefixLift 6801373
  have htrace : WordTrace (prefixWord ++ tailWord_6801373) baseStart_6801373 baseEnd_6801373 := by
    simpa [prefixWord, tailWord_6801373, baseEnd_6801373] using wordTrace_append hprefix tailTrace_6801373
  have hstable : (prefixWord ++ tailWord_6801373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801373).length < 2 ^ (prefixWord ++ tailWord_6801373).sum := by decide
  have hdescent : baseEnd_6801373 < baseStart_6801373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801376 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2]
def baseStart_6801376 : Nat := 118140960795 + 6801376 * 2 ^ 59
def prefixEnd_6801376 : Nat := 4983230072969 + 3 ^ 40 * 6801376 * 2
def baseEnd_6801376 : Nat := 3492374999954086818821047

theorem tailTrace_6801376 : CollatzResearch.WordTrace tailWord_6801376 prefixEnd_6801376 3492374999954086818821047 := by
  unfold tailWord_6801376
  simp only [CollatzResearch.WordTrace]
  refine ⟨124033281103891904693799991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165377708138522539591733321 124033281103891904693799991)
  ·
    refine ⟨186049921655837857040699987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124033281103891904693799991 186049921655837857040699987)
    ·
      refine ⟨279074882483756785561049981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186049921655837857040699987 279074882483756785561049981)
      ·
        refine ⟨104653080931408794585393743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279074882483756785561049981 104653080931408794585393743)
        ·
          refine ⟨156979621397113191878090615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104653080931408794585393743 156979621397113191878090615)
          ·
            refine ⟨235469432095669787817135923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156979621397113191878090615 235469432095669787817135923)
            ·
              refine ⟨353204148143504681725703885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235469432095669787817135923 353204148143504681725703885)
              ·
                refine ⟨132451555553814255647138957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353204148143504681725703885 132451555553814255647138957)
                ·
                  refine ⟨49669333332680345867677109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132451555553814255647138957 49669333332680345867677109)
                  ·
                    refine ⟨4656499999938782425094729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49669333332680345867677109 4656499999938782425094729)
                    ·
                      refine ⟨3492374999954086818821047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656499999938782425094729 3492374999954086818821047)
                      ·
                        rfl

theorem cell23_6801376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_6801376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801376 prefixEnd_6801376 := by exact prefixLift 6801376
  have htrace : WordTrace (prefixWord ++ tailWord_6801376) baseStart_6801376 baseEnd_6801376 := by
    simpa [prefixWord, tailWord_6801376, baseEnd_6801376] using wordTrace_append hprefix tailTrace_6801376
  have hstable : (prefixWord ++ tailWord_6801376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801376).length < 2 ^ (prefixWord ++ tailWord_6801376).sum := by decide
  have hdescent : baseEnd_6801376 < baseStart_6801376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801386 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_6801386 : Nat := 118140960795 + 6801386 * 2 ^ 59
def prefixEnd_6801386 : Nat := 4983230072969 + 3 ^ 40 * 6801386 * 2
def baseEnd_6801386 : Nat := 1164126711586877259898667

theorem tailTrace_6801386 : CollatzResearch.WordTrace tailWord_6801386 prefixEnd_6801386 1164126711586877259898667 := by
  unfold tailWord_6801386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62016731734436895273866003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165377951291831720730309341 62016731734436895273866003)
  ·
    refine ⟨93025097601655342910799005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62016731734436895273866003 93025097601655342910799005)
    ·
      refine ⟨34884411600620753591549627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93025097601655342910799005 34884411600620753591549627)
      ·
        refine ⟨52326617400931130387324441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34884411600620753591549627 52326617400931130387324441)
        ·
          refine ⟨39244963050698347790493331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52326617400931130387324441 39244963050698347790493331)
          ·
            refine ⟨58867444576047521685739997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39244963050698347790493331 58867444576047521685739997)
            ·
              refine ⟨22075291716017820632152499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58867444576047521685739997 22075291716017820632152499)
              ·
                refine ⟨33112937574026730948228749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22075291716017820632152499 33112937574026730948228749)
                ·
                  refine ⟨12417351590260024105585781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33112937574026730948228749 12417351590260024105585781)
                  ·
                    refine ⟨1164126711586877259898667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12417351590260024105585781 1164126711586877259898667)
                    ·
                      rfl

theorem cell23_6801386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_6801386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801386 prefixEnd_6801386 := by exact prefixLift 6801386
  have htrace : WordTrace (prefixWord ++ tailWord_6801386) baseStart_6801386 baseEnd_6801386 := by
    simpa [prefixWord, tailWord_6801386, baseEnd_6801386] using wordTrace_append hprefix tailTrace_6801386
  have hstable : (prefixWord ++ tailWord_6801386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801386).length < 2 ^ (prefixWord ++ tailWord_6801386).sum := by decide
  have hdescent : baseEnd_6801386 < baseStart_6801386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801443 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 3]
def baseStart_6801443 : Nat := 118140960795 + 6801443 * 2 ^ 59
def prefixEnd_6801443 : Nat := 4983230072969 + 3 ^ 40 * 6801443 * 2
def baseEnd_6801443 : Nat := 3492409403157938056683239

theorem tailTrace_6801443 : CollatzResearch.WordTrace tailWord_6801443 prefixEnd_6801443 3492409403157938056683239 := by
  unfold tailWord_6801443
  simp only [CollatzResearch.WordTrace]
  refine ⟨248069005898541079830288983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165379337265694053220192655 248069005898541079830288983)
  ·
    refine ⟨372103508847811619745433475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248069005898541079830288983 372103508847811619745433475)
    ·
      refine ⟨558155263271717429618150213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372103508847811619745433475 558155263271717429618150213)
      ·
        refine ⟨104654111863447018053403165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558155263271717429618150213 104654111863447018053403165)
        ·
          refine ⟨39245291948792631770026187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104654111863447018053403165 39245291948792631770026187)
          ·
            refine ⟨58867937923188947655039281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39245291948792631770026187 58867937923188947655039281)
            ·
              refine ⟨44150953442391710741279461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58867937923188947655039281 44150953442391710741279461)
              ·
                refine ⟨8278303770448445763989899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44150953442391710741279461 8278303770448445763989899)
                ·
                  refine ⟨12417455655672668645984849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278303770448445763989899 12417455655672668645984849)
                  ·
                    refine ⟨9313091741754501484488637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12417455655672668645984849 9313091741754501484488637)
                    ·
                      refine ⟨3492409403157938056683239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313091741754501484488637 3492409403157938056683239)
                      ·
                        rfl

theorem cell23_6801443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_6801443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801443 prefixEnd_6801443 := by exact prefixLift 6801443
  have htrace : WordTrace (prefixWord ++ tailWord_6801443) baseStart_6801443 baseEnd_6801443 := by
    simpa [prefixWord, tailWord_6801443, baseEnd_6801443] using wordTrace_append hprefix tailTrace_6801443
  have hstable : (prefixWord ++ tailWord_6801443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801443).length < 2 ^ (prefixWord ++ tailWord_6801443).sum := by decide
  have hdescent : baseEnd_6801443 < baseStart_6801443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801444 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6801444 : Nat := 118140960795 + 6801444 * 2 ^ 59
def prefixEnd_6801444 : Nat := 4983230072969 + 3 ^ 40 * 6801444 * 2
def baseEnd_6801444 : Nat := 3492409916638592552770735

theorem tailTrace_6801444 : CollatzResearch.WordTrace tailWord_6801444 prefixEnd_6801444 3492409916638592552770735 := by
  unfold tailWord_6801444
  simp only [CollatzResearch.WordTrace]
  refine ⟨124034521185768728500537693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165379361581024971334050257 124034521185768728500537693)
  ·
    refine ⟨46512945444663273187701635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124034521185768728500537693 46512945444663273187701635)
    ·
      refine ⟨69769418166994909781552453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46512945444663273187701635 69769418166994909781552453)
      ·
        refine ⟨13081765906311545584041085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69769418166994909781552453 13081765906311545584041085)
        ·
          refine ⟨4905662214866829594015407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13081765906311545584041085 4905662214866829594015407)
          ·
            refine ⟨7358493322300244391023111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905662214866829594015407 7358493322300244391023111)
            ·
              refine ⟨11037739983450366586534667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358493322300244391023111 11037739983450366586534667)
              ·
                refine ⟨16556609975175549879802001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11037739983450366586534667 16556609975175549879802001)
                ·
                  refine ⟨12417457481381662409851501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16556609975175549879802001 12417457481381662409851501)
                  ·
                    refine ⟨4656546555518123403694313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12417457481381662409851501 4656546555518123403694313)
                    ·
                      refine ⟨3492409916638592552770735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656546555518123403694313 3492409916638592552770735)
                      ·
                        rfl

theorem cell23_6801444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6801444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801444 prefixEnd_6801444 := by exact prefixLift 6801444
  have htrace : WordTrace (prefixWord ++ tailWord_6801444) baseStart_6801444 baseEnd_6801444 := by
    simpa [prefixWord, tailWord_6801444, baseEnd_6801444] using wordTrace_append hprefix tailTrace_6801444
  have hstable : (prefixWord ++ tailWord_6801444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801444).length < 2 ^ (prefixWord ++ tailWord_6801444).sum := by decide
  have hdescent : baseEnd_6801444 < baseStart_6801444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801449 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_6801449 : Nat := 118140960795 + 6801449 * 2 ^ 59
def prefixEnd_6801449 : Nat := 4983230072969 + 3 ^ 40 * 6801449 * 2
def baseEnd_6801449 : Nat := 3492412484041865033208211

theorem tailTrace_6801449 : CollatzResearch.WordTrace tailWord_6801449 prefixEnd_6801449 3492412484041865033208211 := by
  unfold tailWord_6801449
  simp only [CollatzResearch.WordTrace]
  refine ⟨248069224736519342855007401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165379483157679561903338267 248069224736519342855007401)
  ·
    refine ⟨186051918552389507141255551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248069224736519342855007401 186051918552389507141255551)
    ·
      refine ⟨279077877828584260711883327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186051918552389507141255551 279077877828584260711883327)
      ·
        refine ⟨418616816742876391067824991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279077877828584260711883327 418616816742876391067824991)
        ·
          refine ⟨627925225114314586601737487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418616816742876391067824991 627925225114314586601737487)
          ·
            refine ⟨941887837671471879902606231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627925225114314586601737487 941887837671471879902606231)
            ·
              refine ⟨1412831756507207819853909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941887837671471879902606231 1412831756507207819853909347)
              ·
                refine ⟨2119247634760811729780864021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412831756507207819853909347 2119247634760811729780864021)
                ·
                  refine ⟨99339732879413049833478001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2119247634760811729780864021 99339732879413049833478001)
                  ·
                    refine ⟨74504799659559787375108501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99339732879413049833478001 74504799659559787375108501)
                    ·
                      refine ⟨3492412484041865033208211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74504799659559787375108501 3492412484041865033208211)
                      ·
                        rfl

theorem cell23_6801449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_6801449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801449 prefixEnd_6801449 := by exact prefixLift 6801449
  have htrace : WordTrace (prefixWord ++ tailWord_6801449) baseStart_6801449 baseEnd_6801449 := by
    simpa [prefixWord, tailWord_6801449, baseEnd_6801449] using wordTrace_append hprefix tailTrace_6801449
  have hstable : (prefixWord ++ tailWord_6801449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801449).length < 2 ^ (prefixWord ++ tailWord_6801449).sum := by decide
  have hdescent : baseEnd_6801449 < baseStart_6801449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801457 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_6801457 : Nat := 118140960795 + 6801457 * 2 ^ 59
def prefixEnd_6801457 : Nat := 4983230072969 + 3 ^ 40 * 6801457 * 2
def baseEnd_6801457 : Nat := 3492416591887101001908175

theorem tailTrace_6801457 : CollatzResearch.WordTrace tailWord_6801457 prefixEnd_6801457 3492416591887101001908175 := by
  unfold tailWord_6801457
  simp only [CollatzResearch.WordTrace]
  refine ⟨248069516520490360221298625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165379677680326906814199083 248069516520490360221298625)
  ·
    refine ⟨186052137390367770165973969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248069516520490360221298625 186052137390367770165973969)
    ·
      refine ⟨139539103042775827624480477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186052137390367770165973969 139539103042775827624480477)
      ·
        refine ⟨52327163641040935359180179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139539103042775827624480477 52327163641040935359180179)
        ·
          refine ⟨78490745461561403038770269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52327163641040935359180179 78490745461561403038770269)
          ·
            refine ⟨29434029548085526139538851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78490745461561403038770269 29434029548085526139538851)
            ·
              refine ⟨44151044322128289209308277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29434029548085526139538851 44151044322128289209308277)
              ·
                refine ⟨4139160405199527113372651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44151044322128289209308277 4139160405199527113372651)
                ·
                  refine ⟨6208740607799290670058977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139160405199527113372651 6208740607799290670058977)
                  ·
                    refine ⟨4656555455849468002544233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6208740607799290670058977 4656555455849468002544233)
                    ·
                      refine ⟨3492416591887101001908175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656555455849468002544233 3492416591887101001908175)
                      ·
                        rfl

theorem cell23_6801457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_6801457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801457 prefixEnd_6801457 := by exact prefixLift 6801457
  have htrace : WordTrace (prefixWord ++ tailWord_6801457) baseStart_6801457 baseEnd_6801457 := by
    simpa [prefixWord, tailWord_6801457, baseEnd_6801457] using wordTrace_append hprefix tailTrace_6801457
  have hstable : (prefixWord ++ tailWord_6801457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801457).length < 2 ^ (prefixWord ++ tailWord_6801457).sum := by decide
  have hdescent : baseEnd_6801457 < baseStart_6801457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801494 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6801494 : Nat := 118140960795 + 6801494 * 2 ^ 59
def prefixEnd_6801494 : Nat := 4983230072969 + 3 ^ 40 * 6801494 * 2
def baseEnd_6801494 : Nat := 3492435590671317357145505

theorem tailTrace_6801494 : CollatzResearch.WordTrace tailWord_6801494 prefixEnd_6801494 3492435590671317357145505 := by
  unfold tailWord_6801494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504429126334769721274721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165380577347570877026930357 15504429126334769721274721)
  ·
    refine ⟨11628321844751077290956041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15504429126334769721274721 11628321844751077290956041)
    ·
      refine ⟨8721241383563307968217031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11628321844751077290956041 8721241383563307968217031)
      ·
        refine ⟨13081862075344961952325547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721241383563307968217031 13081862075344961952325547)
        ·
          refine ⟨19622793113017442928488321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13081862075344961952325547 19622793113017442928488321)
          ·
            refine ⟨14717094834763082196366241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19622793113017442928488321 14717094834763082196366241)
            ·
              refine ⟨11037821126072311647274681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14717094834763082196366241 11037821126072311647274681)
              ·
                refine ⟨8278365844554233735456011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11037821126072311647274681 8278365844554233735456011)
                ·
                  refine ⟨12417548766831350603184017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278365844554233735456011 12417548766831350603184017)
                  ·
                    refine ⟨9313161575123512952388013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12417548766831350603184017 9313161575123512952388013)
                    ·
                      refine ⟨3492435590671317357145505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313161575123512952388013 3492435590671317357145505)
                      ·
                        rfl

theorem cell23_6801494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6801494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801494 prefixEnd_6801494 := by exact prefixLift 6801494
  have htrace : WordTrace (prefixWord ++ tailWord_6801494) baseStart_6801494 baseEnd_6801494 := by
    simpa [prefixWord, tailWord_6801494, baseEnd_6801494] using wordTrace_append hprefix tailTrace_6801494
  have hstable : (prefixWord ++ tailWord_6801494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801494).length < 2 ^ (prefixWord ++ tailWord_6801494).sum := by decide
  have hdescent : baseEnd_6801494 < baseStart_6801494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801513 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 4, 2]
def baseStart_6801513 : Nat := 118140960795 + 6801513 * 2 ^ 59
def prefixEnd_6801513 : Nat := 4983230072969 + 3 ^ 40 * 6801513 * 2
def baseEnd_6801513 : Nat := 3492445346803752782807917

theorem tailTrace_6801513 : CollatzResearch.WordTrace tailWord_6801513 prefixEnd_6801513 3492445346803752782807917 := by
  unfold tailWord_6801513
  simp only [CollatzResearch.WordTrace]
  refine ⟨248071559008287481785337193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165381039338858321190224795 248071559008287481785337193)
  ·
    refine ⟨186053669256215611339002895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248071559008287481785337193 186053669256215611339002895)
    ·
      refine ⟨279080503884323417008504343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186053669256215611339002895 279080503884323417008504343)
      ·
        refine ⟨418620755826485125512756515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279080503884323417008504343 418620755826485125512756515)
        ·
          refine ⟨627931133739727688269134773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418620755826485125512756515 627931133739727688269134773)
          ·
            refine ⟨58868543788099470775231385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 627931133739727688269134773 58868543788099470775231385)
            ·
              refine ⟨44151407841074603081423539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58868543788099470775231385 44151407841074603081423539)
              ·
                refine ⟨66227111761611904622135309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44151407841074603081423539 66227111761611904622135309)
                ·
                  refine ⟨24835166910604464233300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66227111761611904622135309 24835166910604464233300741)
                  ·
                    refine ⟨4656593795738337043743889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24835166910604464233300741 4656593795738337043743889)
                    ·
                      refine ⟨3492445346803752782807917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656593795738337043743889 3492445346803752782807917)
                      ·
                        rfl

theorem cell23_6801513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4, 2].length) (baseStart_6801513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801513 prefixEnd_6801513 := by exact prefixLift 6801513
  have htrace : WordTrace (prefixWord ++ tailWord_6801513) baseStart_6801513 baseEnd_6801513 := by
    simpa [prefixWord, tailWord_6801513, baseEnd_6801513] using wordTrace_append hprefix tailTrace_6801513
  have hstable : (prefixWord ++ tailWord_6801513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801513).length < 2 ^ (prefixWord ++ tailWord_6801513).sum := by decide
  have hdescent : baseEnd_6801513 < baseStart_6801513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801516 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6801516 : Nat := 118140960795 + 6801516 * 2 ^ 59
def prefixEnd_6801516 : Nat := 4983230072969 + 3 ^ 40 * 6801516 * 2
def baseEnd_6801516 : Nat := 3492446887245716271070403

theorem tailTrace_6801516 : CollatzResearch.WordTrace tailWord_6801516 prefixEnd_6801516 3492446887245716271070403 := by
  unfold tailWord_6801516
  simp only [CollatzResearch.WordTrace]
  refine ⟨124035834213638306648848201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165381112284851075531797601 124035834213638306648848201)
  ·
    refine ⟨93026875660228729986636151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124035834213638306648848201 93026875660228729986636151)
    ·
      refine ⟨139540313490343094979954227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93026875660228729986636151 139540313490343094979954227)
      ·
        refine ⟨209310470235514642469931341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139540313490343094979954227 209310470235514642469931341)
        ·
          refine ⟨78491426338317990926224253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209310470235514642469931341 78491426338317990926224253)
          ·
            refine ⟨29434284876869246597334095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78491426338317990926224253 29434284876869246597334095)
            ·
              refine ⟨44151427315303869896001143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29434284876869246597334095 44151427315303869896001143)
              ·
                refine ⟨66227140972955804844001715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44151427315303869896001143 66227140972955804844001715)
                ·
                  refine ⟨99340711459433707266002573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66227140972955804844001715 99340711459433707266002573)
                  ·
                    refine ⟨37252766797287640224750965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99340711459433707266002573 37252766797287640224750965)
                    ·
                      refine ⟨3492446887245716271070403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37252766797287640224750965 3492446887245716271070403)
                      ·
                        rfl

theorem cell23_6801516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6801516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801516 prefixEnd_6801516 := by exact prefixLift 6801516
  have htrace : WordTrace (prefixWord ++ tailWord_6801516) baseStart_6801516 baseEnd_6801516 := by
    simpa [prefixWord, tailWord_6801516, baseEnd_6801516] using wordTrace_append hprefix tailTrace_6801516
  have hstable : (prefixWord ++ tailWord_6801516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801516).length < 2 ^ (prefixWord ++ tailWord_6801516).sum := by decide
  have hdescent : baseEnd_6801516 < baseStart_6801516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801616 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_6801616 : Nat := 118140960795 + 6801616 * 2 ^ 59
def prefixEnd_6801616 : Nat := 4983230072969 + 3 ^ 40 * 6801616 * 2
def baseEnd_6801616 : Nat := 3492498235311165879819943

theorem tailTrace_6801616 : CollatzResearch.WordTrace tailWord_6801616 prefixEnd_6801616 3492498235311165879819943 := by
  unfold tailWord_6801616
  simp only [CollatzResearch.WordTrace]
  refine ⟨124037657863457165188168351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165383543817942886917557801 124037657863457165188168351)
  ·
    refine ⟨186056486795185747782252527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124037657863457165188168351 186056486795185747782252527)
    ·
      refine ⟨279084730192778621673378791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186056486795185747782252527 279084730192778621673378791)
      ·
        refine ⟨418627095289167932510068187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279084730192778621673378791 418627095289167932510068187)
        ·
          refine ⟨627940642933751898765102281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418627095289167932510068187 627940642933751898765102281)
          ·
            refine ⟨470955482200313924073826711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627940642933751898765102281 470955482200313924073826711)
            ·
              refine ⟨706433223300470886110740067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470955482200313924073826711 706433223300470886110740067)
              ·
                refine ⟨1059649834950706329166110101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706433223300470886110740067 1059649834950706329166110101)
                ·
                  refine ⟨49671086013314359179661411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1059649834950706329166110101 49671086013314359179661411)
                  ·
                    refine ⟨74506629019971538769492117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49671086013314359179661411 74506629019971538769492117)
                    ·
                      refine ⟨3492498235311165879819943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74506629019971538769492117 3492498235311165879819943)
                      ·
                        rfl

theorem cell23_6801616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_6801616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801616 prefixEnd_6801616 := by exact prefixLift 6801616
  have htrace : WordTrace (prefixWord ++ tailWord_6801616) baseStart_6801616 baseEnd_6801616 := by
    simpa [prefixWord, tailWord_6801616, baseEnd_6801616] using wordTrace_append hprefix tailTrace_6801616
  have hstable : (prefixWord ++ tailWord_6801616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801616).length < 2 ^ (prefixWord ++ tailWord_6801616).sum := by decide
  have hdescent : baseEnd_6801616 < baseStart_6801616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801647 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 1, 4]
def baseStart_6801647 : Nat := 118140960795 + 6801647 * 2 ^ 59
def prefixEnd_6801647 : Nat := 4983230072969 + 3 ^ 40 * 6801647 * 2
def baseEnd_6801647 : Nat := 1164171384403818419510767

theorem tailTrace_6801647 : CollatzResearch.WordTrace tailWord_6801647 prefixEnd_6801647 1164171384403818419510767 := by
  unfold tailWord_6801647
  simp only [CollatzResearch.WordTrace]
  refine ⟨248076446389802022670715195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165384297593201348447143463 248076446389802022670715195)
  ·
    refine ⟨372114669584703034006072793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248076446389802022670715195 372114669584703034006072793)
    ·
      refine ⟨279086002188527275504554595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372114669584703034006072793 279086002188527275504554595)
      ·
        refine ⟨418629003282790913256831893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279086002188527275504554595 418629003282790913256831893)
        ·
          refine ⟨19623234528880824058913995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 418629003282790913256831893 19623234528880824058913995)
          ·
            refine ⟨29434851793321236088370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19623234528880824058913995 29434851793321236088370993)
            ·
              refine ⟨22076138844990927066278245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29434851793321236088370993 22076138844990927066278245)
              ·
                refine ⟨4139276033435798824927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22076138844990927066278245 4139276033435798824927171)
                ·
                  refine ⟨6208914050153698237390757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139276033435798824927171 6208914050153698237390757)
                  ·
                    refine ⟨1164171384403818419510767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208914050153698237390757 1164171384403818419510767)
                    ·
                      rfl

theorem cell23_6801647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_6801647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801647 prefixEnd_6801647 := by exact prefixLift 6801647
  have htrace : WordTrace (prefixWord ++ tailWord_6801647) baseStart_6801647 baseEnd_6801647 := by
    simpa [prefixWord, tailWord_6801647, baseEnd_6801647] using wordTrace_append hprefix tailTrace_6801647
  have hstable : (prefixWord ++ tailWord_6801647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801647).length < 2 ^ (prefixWord ++ tailWord_6801647).sum := by decide
  have hdescent : baseEnd_6801647 < baseStart_6801647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801727 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 5, 2, 2]
def baseStart_6801727 : Nat := 118140960795 + 6801727 * 2 ^ 59
def prefixEnd_6801727 : Nat := 4983230072969 + 3 ^ 40 * 6801727 * 2
def baseEnd_6801727 : Nat := 3492555231663814945531933

theorem tailTrace_6801727 : CollatzResearch.WordTrace tailWord_6801727 prefixEnd_6801727 3492555231663814945531933 := by
  unfold tailWord_6801727
  simp only [CollatzResearch.WordTrace]
  refine ⟨248079364229512196333627435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165386242819674797555751623 248079364229512196333627435)
  ·
    refine ⟨372119046344268294500441153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248079364229512196333627435 372119046344268294500441153)
    ·
      refine ⟨279089284758201220875330865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372119046344268294500441153 279089284758201220875330865)
      ·
        refine ⟨209316963568650915656498149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279089284758201220875330865 209316963568650915656498149)
        ·
          refine ⟨39246930669122046685593403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209316963568650915656498149 39246930669122046685593403)
          ·
            refine ⟨58870396003683070028390105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39246930669122046685593403 58870396003683070028390105)
            ·
              refine ⟨44152797002762302521292579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58870396003683070028390105 44152797002762302521292579)
              ·
                refine ⟨66229195504143453781938869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44152797002762302521292579 66229195504143453781938869)
                ·
                  refine ⟨6208987078513448792056769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66229195504143453781938869 6208987078513448792056769)
                  ·
                    refine ⟨4656740308885086594042577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6208987078513448792056769 4656740308885086594042577)
                    ·
                      refine ⟨3492555231663814945531933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656740308885086594042577 3492555231663814945531933)
                      ·
                        rfl

theorem cell23_6801727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_6801727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801727 prefixEnd_6801727 := by exact prefixLift 6801727
  have htrace : WordTrace (prefixWord ++ tailWord_6801727) baseStart_6801727 baseEnd_6801727 := by
    simpa [prefixWord, tailWord_6801727, baseEnd_6801727] using wordTrace_append hprefix tailTrace_6801727
  have hstable : (prefixWord ++ tailWord_6801727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801727).length < 2 ^ (prefixWord ++ tailWord_6801727).sum := by decide
  have hdescent : baseEnd_6801727 < baseStart_6801727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801740 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6801740 : Nat := 118140960795 + 6801740 * 2 ^ 59
def prefixEnd_6801740 : Nat := 4983230072969 + 3 ^ 40 * 6801740 * 2
def baseEnd_6801740 : Nat := 3492561906912323394669373

theorem tailTrace_6801740 : CollatzResearch.WordTrace tailWord_6801740 prefixEnd_6801740 3492561906912323394669373 := by
  unfold tailWord_6801740
  simp only [CollatzResearch.WordTrace]
  refine ⟨124039919189232549776925337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165386558918976733035900449 124039919189232549776925337)
  ·
    refine ⟨93029939391924412332694003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124039919189232549776925337 93029939391924412332694003)
    ·
      refine ⟨139544909087886618499041005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93029939391924412332694003 139544909087886618499041005)
      ·
        refine ⟨52329340907957481937140377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139544909087886618499041005 52329340907957481937140377)
        ·
          refine ⟨39247005680968111452855283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52329340907957481937140377 39247005680968111452855283)
          ·
            refine ⟨58870508521452167179282925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39247005680968111452855283 58870508521452167179282925)
            ·
              refine ⟨22076440695544562692231097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58870508521452167179282925 22076440695544562692231097)
              ·
                refine ⟨16557330521658422019173323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22076440695544562692231097 16557330521658422019173323)
                ·
                  refine ⟨24835995782487633028759985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16557330521658422019173323 24835995782487633028759985)
                  ·
                    refine ⟨18626996836865724771569989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24835995782487633028759985 18626996836865724771569989)
                    ·
                      refine ⟨3492561906912323394669373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18626996836865724771569989 3492561906912323394669373)
                      ·
                        rfl

theorem cell23_6801740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6801740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801740 prefixEnd_6801740 := by exact prefixLift 6801740
  have htrace : WordTrace (prefixWord ++ tailWord_6801740) baseStart_6801740 baseEnd_6801740 := by
    simpa [prefixWord, tailWord_6801740, baseEnd_6801740] using wordTrace_append hprefix tailTrace_6801740
  have hstable : (prefixWord ++ tailWord_6801740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801740).length < 2 ^ (prefixWord ++ tailWord_6801740).sum := by decide
  have hdescent : baseEnd_6801740 < baseStart_6801740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801763 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 9]
def baseStart_6801763 : Nat := 118140960795 + 6801763 * 2 ^ 59
def prefixEnd_6801763 : Nat := 4983230072969 + 3 ^ 40 * 6801763 * 2
def baseEnd_6801763 : Nat := 1164191238989125601560589

theorem tailTrace_6801763 : CollatzResearch.WordTrace tailWord_6801763 prefixEnd_6801763 1164191238989125601560589 := by
  unfold tailWord_6801763
  simp only [CollatzResearch.WordTrace]
  refine ⟨248080677257381774481937943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165387118171587849654625295 248080677257381774481937943)
  ·
    refine ⟨372121015886072661722906915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248080677257381774481937943 372121015886072661722906915)
    ·
      refine ⟨558181523829108992584360373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372121015886072661722906915 558181523829108992584360373)
      ·
        refine ⟨52329517858978968054783785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 558181523829108992584360373 52329517858978968054783785)
        ·
          refine ⟨39247138394234226041087839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52329517858978968054783785 39247138394234226041087839)
          ·
            refine ⟨58870707591351339061631759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39247138394234226041087839 58870707591351339061631759)
            ·
              refine ⟨88306061387027008592447639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58870707591351339061631759 88306061387027008592447639)
              ·
                refine ⟨132459092080540512888671459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88306061387027008592447639 132459092080540512888671459)
                ·
                  refine ⟨198688638120810769333007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132459092080540512888671459 198688638120810769333007189)
                  ·
                    refine ⟨1164191238989125601560589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198688638120810769333007189 1164191238989125601560589)
                    ·
                      rfl

theorem cell23_6801763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_6801763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801763 prefixEnd_6801763 := by exact prefixLift 6801763
  have htrace : WordTrace (prefixWord ++ tailWord_6801763) baseStart_6801763 baseEnd_6801763 := by
    simpa [prefixWord, tailWord_6801763, baseEnd_6801763] using wordTrace_append hprefix tailTrace_6801763
  have hstable : (prefixWord ++ tailWord_6801763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801763).length < 2 ^ (prefixWord ++ tailWord_6801763).sum := by decide
  have hdescent : baseEnd_6801763 < baseStart_6801763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801787 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 3, 3, 2]
def baseStart_6801787 : Nat := 118140960795 + 6801787 * 2 ^ 59
def prefixEnd_6801787 : Nat := 4983230072969 + 3 ^ 40 * 6801787 * 2
def baseEnd_6801787 : Nat := 3492586040503084710781657

theorem tailTrace_6801787 : CollatzResearch.WordTrace tailWord_6801787 prefixEnd_6801787 3492586040503084710781657 := by
  unfold tailWord_6801787
  simp only [CollatzResearch.WordTrace]
  refine ⟨248081552609294826580811615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165387701739529884387207743 248081552609294826580811615)
  ·
    refine ⟨372122328913942239871217423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248081552609294826580811615 372122328913942239871217423)
    ·
      refine ⟨558183493370913359806826135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372122328913942239871217423 558183493370913359806826135)
      ·
        refine ⟨837275240056370039710239203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558183493370913359806826135 837275240056370039710239203)
        ·
          refine ⟨1255912860084555059565358805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837275240056370039710239203 1255912860084555059565358805)
          ·
            refine ⟨29435457658231759208563097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1255912860084555059565358805 29435457658231759208563097)
            ·
              refine ⟨22076593243673819406422323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29435457658231759208563097 22076593243673819406422323)
              ·
                refine ⟨33114889865510729109633485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22076593243673819406422323 33114889865510729109633485)
                ·
                  refine ⟨12418083699566523416112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33114889865510729109633485 12418083699566523416112557)
                  ·
                    refine ⟨4656781387337446281042209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12418083699566523416112557 4656781387337446281042209)
                    ·
                      refine ⟨3492586040503084710781657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656781387337446281042209 3492586040503084710781657)
                      ·
                        rfl

theorem cell23_6801787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3, 2].length) (baseStart_6801787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801787 prefixEnd_6801787 := by exact prefixLift 6801787
  have htrace : WordTrace (prefixWord ++ tailWord_6801787) baseStart_6801787 baseEnd_6801787 := by
    simpa [prefixWord, tailWord_6801787, baseEnd_6801787] using wordTrace_append hprefix tailTrace_6801787
  have hstable : (prefixWord ++ tailWord_6801787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801787).length < 2 ^ (prefixWord ++ tailWord_6801787).sum := by decide
  have hdescent : baseEnd_6801787 < baseStart_6801787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801804 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_6801804 : Nat := 118140960795 + 6801804 * 2 ^ 59
def prefixEnd_6801804 : Nat := 4983230072969 + 3 ^ 40 * 6801804 * 2
def baseEnd_6801804 : Nat := 3492594769674211144269079

theorem tailTrace_6801804 : CollatzResearch.WordTrace tailWord_6801804 prefixEnd_6801804 3492594769674211144269079 := by
  unfold tailWord_6801804
  simp only [CollatzResearch.WordTrace]
  refine ⟨124041086325116619242090233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165388115100155492322786977 124041086325116619242090233)
  ·
    refine ⟨93030814743837464431567675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124041086325116619242090233 93030814743837464431567675)
    ·
      refine ⟨139546222115756196647351513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93030814743837464431567675 139546222115756196647351513)
      ·
        refine ⟨104659666586817147485513635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139546222115756196647351513 104659666586817147485513635)
        ·
          refine ⟨156989499880225721228270453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104659666586817147485513635 156989499880225721228270453)
          ·
            refine ⟨14717765613771161365150355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156989499880225721228270453 14717765613771161365150355)
            ·
              refine ⟨22076648420656742047725533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14717765613771161365150355 22076648420656742047725533)
              ·
                refine ⟨8278743157746278267897075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22076648420656742047725533 8278743157746278267897075)
                ·
                  refine ⟨12418114736619417401845613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278743157746278267897075 12418114736619417401845613)
                  ·
                    refine ⟨4656793026232281525692105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12418114736619417401845613 4656793026232281525692105)
                    ·
                      refine ⟨3492594769674211144269079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656793026232281525692105 3492594769674211144269079)
                      ·
                        rfl

theorem cell23_6801804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_6801804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801804 prefixEnd_6801804 := by exact prefixLift 6801804
  have htrace : WordTrace (prefixWord ++ tailWord_6801804) baseStart_6801804 baseEnd_6801804 := by
    simpa [prefixWord, tailWord_6801804, baseEnd_6801804] using wordTrace_append hprefix tailTrace_6801804
  have hstable : (prefixWord ++ tailWord_6801804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801804).length < 2 ^ (prefixWord ++ tailWord_6801804).sum := by decide
  have hdescent : baseEnd_6801804 < baseStart_6801804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_6801833 : Nat := 118140960795 + 6801833 * 2 ^ 59
def prefixEnd_6801833 : Nat := 4983230072969 + 3 ^ 40 * 6801833 * 2
def baseEnd_6801833 : Nat := 3492609660613191530806445

theorem tailTrace_6801833 : CollatzResearch.WordTrace tailWord_6801833 prefixEnd_6801833 3492609660613191530806445 := by
  unfold tailWord_6801833
  simp only [CollatzResearch.WordTrace]
  refine ⟨248083230367128176436986153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165388820244752117624657435 248083230367128176436986153)
  ·
    refine ⟨186062422775346132327739615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248083230367128176436986153 186062422775346132327739615)
    ·
      refine ⟨279093634163019198491609423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186062422775346132327739615 279093634163019198491609423)
      ·
        refine ⟨418640451244528797737414135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279093634163019198491609423 418640451244528797737414135)
        ·
          refine ⟨627960676866793196606121203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418640451244528797737414135 627960676866793196606121203)
          ·
            refine ⟨941941015300189794909181805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627960676866793196606121203 941941015300189794909181805)
            ·
              refine ⟨353227880737571173090943177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941941015300189794909181805 353227880737571173090943177)
              ·
                refine ⟨264920910553178379818207383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353227880737571173090943177 264920910553178379818207383)
                ·
                  refine ⟨397381365829767569727311075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264920910553178379818207383 397381365829767569727311075)
                  ·
                    refine ⟨596072048744651354590966613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 397381365829767569727311075 596072048744651354590966613)
                    ·
                      refine ⟨3492609660613191530806445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 596072048744651354590966613 3492609660613191530806445)
                      ·
                        rfl

theorem cell23_6801833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_6801833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801833 prefixEnd_6801833 := by exact prefixLift 6801833
  have htrace : WordTrace (prefixWord ++ tailWord_6801833) baseStart_6801833 baseEnd_6801833 := by
    simpa [prefixWord, tailWord_6801833, baseEnd_6801833] using wordTrace_append hprefix tailTrace_6801833
  have hstable : (prefixWord ++ tailWord_6801833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801833).length < 2 ^ (prefixWord ++ tailWord_6801833).sum := by decide
  have hdescent : baseEnd_6801833 < baseStart_6801833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_6801850 : Nat := 118140960795 + 6801850 * 2 ^ 59
def prefixEnd_6801850 : Nat := 4983230072969 + 3 ^ 40 * 6801850 * 2
def baseEnd_6801850 : Nat := 3492618389784317964293867

theorem tailTrace_6801850 : CollatzResearch.WordTrace tailWord_6801850 prefixEnd_6801850 3492618389784317964293867 := by
  unfold tailWord_6801850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020962602016647085088751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165389233605377725560236669 62020962602016647085088751)
  ·
    refine ⟨93031443903024970627633127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62020962602016647085088751 93031443903024970627633127)
    ·
      refine ⟨139547165854537455941449691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93031443903024970627633127 139547165854537455941449691)
      ·
        refine ⟨209320748781806183912174537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139547165854537455941449691 209320748781806183912174537)
        ·
          refine ⟨156990561586354637934130903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209320748781806183912174537 156990561586354637934130903)
          ·
            refine ⟨235485842379531956901196355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156990561586354637934130903 235485842379531956901196355)
            ·
              refine ⟨353228763569297935351794533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235485842379531956901196355 353228763569297935351794533)
              ·
                refine ⟨66230393169243362878461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353228763569297935351794533 66230393169243362878461475)
                ·
                  refine ⟨99345589753865044317692213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66230393169243362878461475 99345589753865044317692213)
                  ·
                    refine ⟨9313649039424847904783645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99345589753865044317692213 9313649039424847904783645)
                    ·
                      refine ⟨3492618389784317964293867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313649039424847904783645 3492618389784317964293867)
                      ·
                        rfl

theorem cell23_6801850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_6801850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801850 prefixEnd_6801850 := by exact prefixLift 6801850
  have htrace : WordTrace (prefixWord ++ tailWord_6801850) baseStart_6801850 baseEnd_6801850 := by
    simpa [prefixWord, tailWord_6801850, baseEnd_6801850] using wordTrace_append hprefix tailTrace_6801850
  have hstable : (prefixWord ++ tailWord_6801850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801850).length < 2 ^ (prefixWord ++ tailWord_6801850).sum := by decide
  have hdescent : baseEnd_6801850 < baseStart_6801850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801907 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4]
def baseStart_6801907 : Nat := 118140960795 + 6801907 * 2 ^ 59
def prefixEnd_6801907 : Nat := 4983230072969 + 3 ^ 40 * 6801907 * 2
def baseEnd_6801907 : Nat := 3492647658181624241281105

theorem tailTrace_6801907 : CollatzResearch.WordTrace tailWord_6801907 prefixEnd_6801907 3492647658181624241281105 := by
  unfold tailWord_6801907
  simp only [CollatzResearch.WordTrace]
  refine ⟨248085929368860087075179975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165390619579240058050119983 248085929368860087075179975)
  ·
    refine ⟨372128894053290130612769963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248085929368860087075179975 372128894053290130612769963)
    ·
      refine ⟨558193341079935195919154945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372128894053290130612769963 558193341079935195919154945)
      ·
        refine ⟨418645005809951396939366209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558193341079935195919154945 418645005809951396939366209)
        ·
          refine ⟨313983754357463547704524657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418645005809951396939366209 313983754357463547704524657)
          ·
            refine ⟨235487815768097660778393493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313983754357463547704524657 235487815768097660778393493)
            ·
              refine ⟨11038491364129577848987195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235487815768097660778393493 11038491364129577848987195)
              ·
                refine ⟨16557737046194366773480793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038491364129577848987195 16557737046194366773480793)
                ·
                  refine ⟨12418302784645775080110595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16557737046194366773480793 12418302784645775080110595)
                  ·
                    refine ⟨18627454176968662620165893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12418302784645775080110595 18627454176968662620165893)
                    ·
                      refine ⟨3492647658181624241281105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18627454176968662620165893 3492647658181624241281105)
                      ·
                        rfl

theorem cell23_6801907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_6801907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801907 prefixEnd_6801907 := by exact prefixLift 6801907
  have htrace : WordTrace (prefixWord ++ tailWord_6801907) baseStart_6801907 baseEnd_6801907 := by
    simpa [prefixWord, tailWord_6801907, baseEnd_6801907] using wordTrace_append hprefix tailTrace_6801907
  have hstable : (prefixWord ++ tailWord_6801907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801907).length < 2 ^ (prefixWord ++ tailWord_6801907).sum := by decide
  have hdescent : baseEnd_6801907 < baseStart_6801907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801924 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6801924 : Nat := 118140960795 + 6801924 * 2 ^ 59
def prefixEnd_6801924 : Nat := 4983230072969 + 3 ^ 40 * 6801924 * 2
def baseEnd_6801924 : Nat := 3492656387352750674768527

theorem tailTrace_6801924 : CollatzResearch.WordTrace tailWord_6801924 prefixEnd_6801924 3492656387352750674768527 := by
  unfold tailWord_6801924
  simp only [CollatzResearch.WordTrace]
  refine ⟨124043274704899249489274413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165391032939865665985699217 124043274704899249489274413)
  ·
    refine ⟨46516228014337218558477905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124043274704899249489274413 46516228014337218558477905)
    ·
      refine ⟨34887171010752913918858429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46516228014337218558477905 34887171010752913918858429)
      ·
        refine ⟨13082689129032342719571911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34887171010752913918858429 13082689129032342719571911)
        ·
          refine ⟨19624033693548514079357867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082689129032342719571911 19624033693548514079357867)
          ·
            refine ⟨29436050540322771119036801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19624033693548514079357867 29436050540322771119036801)
            ·
              refine ⟨22077037905242078339277601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29436050540322771119036801 22077037905242078339277601)
              ·
                refine ⟨16557778428931558754458201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077037905242078339277601 16557778428931558754458201)
                ·
                  refine ⟨12418333821698669065843651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16557778428931558754458201 12418333821698669065843651)
                  ·
                    refine ⟨18627500732548003598765477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12418333821698669065843651 18627500732548003598765477)
                    ·
                      refine ⟨3492656387352750674768527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18627500732548003598765477 3492656387352750674768527)
                      ·
                        rfl

theorem cell23_6801924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6801924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801924 prefixEnd_6801924 := by exact prefixLift 6801924
  have htrace : WordTrace (prefixWord ++ tailWord_6801924) baseStart_6801924 baseEnd_6801924 := by
    simpa [prefixWord, tailWord_6801924, baseEnd_6801924] using wordTrace_append hprefix tailTrace_6801924
  have hstable : (prefixWord ++ tailWord_6801924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801924).length < 2 ^ (prefixWord ++ tailWord_6801924).sum := by decide
  have hdescent : baseEnd_6801924 < baseStart_6801924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801984 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2]
def baseStart_6801984 : Nat := 118140960795 + 6801984 * 2 ^ 59
def prefixEnd_6801984 : Nat := 4983230072969 + 3 ^ 40 * 6801984 * 2
def baseEnd_6801984 : Nat := 3492687196192020440018251

theorem tailTrace_6801984 : CollatzResearch.WordTrace tailWord_6801984 prefixEnd_6801984 3492687196192020440018251 := by
  unfold tailWord_6801984
  simp only [CollatzResearch.WordTrace]
  refine ⟨124044368894790564612866503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165392491859720752817155337 124044368894790564612866503)
  ·
    refine ⟨186066553342185846919299755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124044368894790564612866503 186066553342185846919299755)
    ·
      refine ⟨279099830013278770378949633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186066553342185846919299755 279099830013278770378949633)
      ·
        refine ⟨209324872509959077784212225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279099830013278770378949633 209324872509959077784212225)
        ·
          refine ⟨156993654382469308338159169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209324872509959077784212225 156993654382469308338159169)
          ·
            refine ⟨117745240786851981253619377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156993654382469308338159169 117745240786851981253619377)
            ·
              refine ⟨88308930590138985940214533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117745240786851981253619377 88308930590138985940214533)
              ·
                refine ⟨16557924485651059863790225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88308930590138985940214533 16557924485651059863790225)
                ·
                  refine ⟨12418443364238294897842669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16557924485651059863790225 12418443364238294897842669)
                  ·
                    refine ⟨4656916261589360586691001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12418443364238294897842669 4656916261589360586691001)
                    ·
                      refine ⟨3492687196192020440018251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656916261589360586691001 3492687196192020440018251)
                      ·
                        rfl

theorem cell23_6801984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_6801984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801984 prefixEnd_6801984 := by exact prefixLift 6801984
  have htrace : WordTrace (prefixWord ++ tailWord_6801984) baseStart_6801984 baseEnd_6801984 := by
    simpa [prefixWord, tailWord_6801984, baseEnd_6801984] using wordTrace_append hprefix tailTrace_6801984
  have hstable : (prefixWord ++ tailWord_6801984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801984).length < 2 ^ (prefixWord ++ tailWord_6801984).sum := by decide
  have hdescent : baseEnd_6801984 < baseStart_6801984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6801991 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_6801991 : Nat := 118140960795 + 6801991 * 2 ^ 59
def prefixEnd_6801991 : Nat := 4983230072969 + 3 ^ 40 * 6801991 * 2
def baseEnd_6801991 : Nat := 3492690790556601912630719

theorem tailTrace_6801991 : CollatzResearch.WordTrace tailWord_6801991 prefixEnd_6801991 3492690790556601912630719 := by
  unfold tailWord_6801991
  simp only [CollatzResearch.WordTrace]
  refine ⟨248088993100555769421237827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165392662067037179614158551 248088993100555769421237827)
  ·
    refine ⟨372133489650833654131856741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248088993100555769421237827 372133489650833654131856741)
    ·
      refine ⟨69775029309531310149723139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372133489650833654131856741 69775029309531310149723139)
      ·
        refine ⟨104662543964296965224584709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69775029309531310149723139 104662543964296965224584709)
        ·
          refine ⟨19624226993305680979609633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104662543964296965224584709 19624226993305680979609633)
          ·
            refine ⟨14718170244979260734707225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19624226993305680979609633 14718170244979260734707225)
            ·
              refine ⟨11038627683734445551030419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14718170244979260734707225 11038627683734445551030419)
              ·
                refine ⟨16557941525601668326545629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038627683734445551030419 16557941525601668326545629)
                ·
                  refine ⟨6209228072100625622454611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16557941525601668326545629 6209228072100625622454611)
                  ·
                    refine ⟨9313842108150938433681917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6209228072100625622454611 9313842108150938433681917)
                    ·
                      refine ⟨3492690790556601912630719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313842108150938433681917 3492690790556601912630719)
                      ·
                        rfl

theorem cell23_6801991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_6801991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6801991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6801991 prefixEnd_6801991 := by exact prefixLift 6801991
  have htrace : WordTrace (prefixWord ++ tailWord_6801991) baseStart_6801991 baseEnd_6801991 := by
    simpa [prefixWord, tailWord_6801991, baseEnd_6801991] using wordTrace_append hprefix tailTrace_6801991
  have hstable : (prefixWord ++ tailWord_6801991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6801991).length < 2 ^ (prefixWord ++ tailWord_6801991).sum := by decide
  have hdescent : baseEnd_6801991 < baseStart_6801991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6801991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_6802047 : Nat := 118140960795 + 6802047 * 2 ^ 59
def prefixEnd_6802047 : Nat := 4983230072969 + 3 ^ 40 * 6802047 * 2
def baseEnd_6802047 : Nat := 3492719545473253693530461

theorem tailTrace_6802047 : CollatzResearch.WordTrace tailWord_6802047 prefixEnd_6802047 3492719545473253693530461 := by
  unfold tailWord_6802047
  simp only [CollatzResearch.WordTrace]
  refine ⟨248091035588352890985276395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165394023725568593990184263 248091035588352890985276395)
  ·
    refine ⟨372136553382529336477914593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248091035588352890985276395 372136553382529336477914593)
    ·
      refine ⟨279102415036897002358435945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372136553382529336477914593 279102415036897002358435945)
      ·
        refine ⟨209326811277672751768826959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279102415036897002358435945 209326811277672751768826959)
        ·
          refine ⟨313990216916509127653240439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209326811277672751768826959 313990216916509127653240439)
          ·
            refine ⟨470985325374763691479860659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313990216916509127653240439 470985325374763691479860659)
            ·
              refine ⟨706477988062145537219790989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470985325374763691479860659 706477988062145537219790989)
              ·
                refine ⟨264929245523304576457421621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706477988062145537219790989 264929245523304576457421621)
                ·
                  refine ⟨24837116767809804042883277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264929245523304576457421621 24837116767809804042883277)
                  ·
                    refine ⟨9313918787928676516081229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24837116767809804042883277 9313918787928676516081229)
                    ·
                      refine ⟨3492719545473253693530461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313918787928676516081229 3492719545473253693530461)
                      ·
                        rfl

theorem cell23_6802047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_6802047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802047 prefixEnd_6802047 := by exact prefixLift 6802047
  have htrace : WordTrace (prefixWord ++ tailWord_6802047) baseStart_6802047 baseEnd_6802047 := by
    simpa [prefixWord, tailWord_6802047, baseEnd_6802047] using wordTrace_append hprefix tailTrace_6802047
  have hstable : (prefixWord ++ tailWord_6802047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802047).length < 2 ^ (prefixWord ++ tailWord_6802047).sum := by decide
  have hdescent : baseEnd_6802047 < baseStart_6802047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802048 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2]
def baseStart_6802048 : Nat := 118140960795 + 6802048 * 2 ^ 59
def prefixEnd_6802048 : Nat := 4983230072969 + 3 ^ 40 * 6802048 * 2
def baseEnd_6802048 : Nat := 3492720058953908189617957

theorem tailTrace_6802048 : CollatzResearch.WordTrace tailWord_6802048 prefixEnd_6802048 3492720058953908189617957 := by
  unfold tailWord_6802048
  simp only [CollatzResearch.WordTrace]
  refine ⟨124045536030674634078031399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165394048040899512104041865 124045536030674634078031399)
  ·
    refine ⟨186068304046011951117047099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124045536030674634078031399 186068304046011951117047099)
    ·
      refine ⟨279102456069017926675570649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186068304046011951117047099 279102456069017926675570649)
      ·
        refine ⟨209326842051763445006677987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279102456069017926675570649 209326842051763445006677987)
        ·
          refine ⟨313990263077645167510016981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209326842051763445006677987 313990263077645167510016981)
          ·
            refine ⟨7359146790882308613516023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 313990263077645167510016981 7359146790882308613516023)
            ·
              refine ⟨11038720186323462920274035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359146790882308613516023 11038720186323462920274035)
              ·
                refine ⟨16558080279485194380411053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038720186323462920274035 16558080279485194380411053)
                ·
                  refine ⟨6209280104806947892654145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16558080279485194380411053 6209280104806947892654145)
                  ·
                    refine ⟨4656960078605210919490609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209280104806947892654145 4656960078605210919490609)
                    ·
                      refine ⟨3492720058953908189617957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4656960078605210919490609 3492720058953908189617957)
                      ·
                        rfl

theorem cell23_6802048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_6802048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802048 prefixEnd_6802048 := by exact prefixLift 6802048
  have htrace : WordTrace (prefixWord ++ tailWord_6802048) baseStart_6802048 baseEnd_6802048 := by
    simpa [prefixWord, tailWord_6802048, baseEnd_6802048] using wordTrace_append hprefix tailTrace_6802048
  have hstable : (prefixWord ++ tailWord_6802048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802048).length < 2 ^ (prefixWord ++ tailWord_6802048).sum := by decide
  have hdescent : baseEnd_6802048 < baseStart_6802048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802068 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6802068 : Nat := 118140960795 + 6802068 * 2 ^ 59
def prefixEnd_6802068 : Nat := 4983230072969 + 3 ^ 40 * 6802068 * 2
def baseEnd_6802068 : Nat := 3492730328566998111367865

theorem tailTrace_6802068 : CollatzResearch.WordTrace tailWord_6802068 prefixEnd_6802068 3492730328566998111367865 := by
  unfold tailWord_6802068
  simp only [CollatzResearch.WordTrace]
  refine ⟨124045900760638405785895429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165394534347517874381193905 124045900760638405785895429)
  ·
    refine ⟨23258606392619701084855393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124045900760638405785895429 23258606392619701084855393)
    ·
      refine ⟨17443954794464775813641545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23258606392619701084855393 17443954794464775813641545)
      ·
        refine ⟨13082966095848581860231159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17443954794464775813641545 13082966095848581860231159)
        ·
          refine ⟨19624449143772872790346739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082966095848581860231159 19624449143772872790346739)
          ·
            refine ⟨29436673715659309185520109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19624449143772872790346739 29436673715659309185520109)
            ·
              refine ⟨11038752643372240944570041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29436673715659309185520109 11038752643372240944570041)
              ·
                refine ⟨8279064482529180708427531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11038752643372240944570041 8279064482529180708427531)
                ·
                  refine ⟨12418596723793771062641297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8279064482529180708427531 12418596723793771062641297)
                  ·
                    refine ⟨9313947542845328296980973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12418596723793771062641297 9313947542845328296980973)
                    ·
                      refine ⟨3492730328566998111367865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313947542845328296980973 3492730328566998111367865)
                      ·
                        rfl

theorem cell23_6802068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6802068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802068 prefixEnd_6802068 := by exact prefixLift 6802068
  have htrace : WordTrace (prefixWord ++ tailWord_6802068) baseStart_6802068 baseEnd_6802068 := by
    simpa [prefixWord, tailWord_6802068, baseEnd_6802068] using wordTrace_append hprefix tailTrace_6802068
  have hstable : (prefixWord ++ tailWord_6802068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802068).length < 2 ^ (prefixWord ++ tailWord_6802068).sum := by decide
  have hdescent : baseEnd_6802068 < baseStart_6802068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802077 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6802077 : Nat := 118140960795 + 6802077 * 2 ^ 59
def prefixEnd_6802077 : Nat := 4983230072969 + 3 ^ 40 * 6802077 * 2
def baseEnd_6802077 : Nat := 3492734949892888576155323

theorem tailTrace_6802077 : CollatzResearch.WordTrace tailWord_6802077 prefixEnd_6802077 3492734949892888576155323 := by
  unfold tailWord_6802077
  simp only [CollatzResearch.WordTrace]
  refine ⟨248092129778244206108868485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165394753185496137405912323 248092129778244206108868485)
  ·
    refine ⟨46517274333420788645412841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248092129778244206108868485 46517274333420788645412841)
    ·
      refine ⟨34887955750065591484059631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46517274333420788645412841 34887955750065591484059631)
      ·
        refine ⟨52331933625098387226089447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34887955750065591484059631 52331933625098387226089447)
        ·
          refine ⟨78497900437647580839134171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52331933625098387226089447 78497900437647580839134171)
          ·
            refine ⟨117746850656471371258701257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78497900437647580839134171 117746850656471371258701257)
            ·
              refine ⟨88310137992353528444025943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117746850656471371258701257 88310137992353528444025943)
              ·
                refine ⟨132465206988530292666038915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88310137992353528444025943 132465206988530292666038915)
                ·
                  refine ⟨198697810482795438999058373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132465206988530292666038915 198697810482795438999058373)
                  ·
                    refine ⟨37255839465524144812323445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198697810482795438999058373 37255839465524144812323445)
                    ·
                      refine ⟨3492734949892888576155323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37255839465524144812323445 3492734949892888576155323)
                      ·
                        rfl

theorem cell23_6802077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6802077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802077 prefixEnd_6802077 := by exact prefixLift 6802077
  have htrace : WordTrace (prefixWord ++ tailWord_6802077) baseStart_6802077 baseEnd_6802077 := by
    simpa [prefixWord, tailWord_6802077, baseEnd_6802077] using wordTrace_append hprefix tailTrace_6802077
  have hstable : (prefixWord ++ tailWord_6802077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802077).length < 2 ^ (prefixWord ++ tailWord_6802077).sum := by decide
  have hdescent : baseEnd_6802077 < baseStart_6802077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802081 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6802081 : Nat := 118140960795 + 6802081 * 2 ^ 59
def prefixEnd_6802081 : Nat := 4983230072969 + 3 ^ 40 * 6802081 * 2
def baseEnd_6802081 : Nat := 3492737003815506560505305

theorem tailTrace_6802081 : CollatzResearch.WordTrace tailWord_6802081 prefixEnd_6802081 3492737003815506560505305 := by
  unfold tailWord_6802081
  simp only [CollatzResearch.WordTrace]
  refine ⟨248092275670229714792014097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165394850446819809861342731 248092275670229714792014097)
  ·
    refine ⟨186069206752672286094010573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248092275670229714792014097 186069206752672286094010573)
    ·
      refine ⟨69775952532252107285253965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186069206752672286094010573 69775952532252107285253965)
      ·
        refine ⟨26165982199594540231970237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69775952532252107285253965 26165982199594540231970237)
        ·
          refine ⟨9812243324847952586988839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26165982199594540231970237 9812243324847952586988839)
          ·
            refine ⟨14718364987271928880483259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812243324847952586988839 14718364987271928880483259)
            ·
              refine ⟨22077547480907893320724889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718364987271928880483259 22077547480907893320724889)
              ·
                refine ⟨16558160610680919990543667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077547480907893320724889 16558160610680919990543667)
                ·
                  refine ⟨24837240916021379985815501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16558160610680919990543667 24837240916021379985815501)
                  ·
                    refine ⟨9313965343508017494680813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24837240916021379985815501 9313965343508017494680813)
                    ·
                      refine ⟨3492737003815506560505305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9313965343508017494680813 3492737003815506560505305)
                      ·
                        rfl

theorem cell23_6802081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6802081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802081 prefixEnd_6802081 := by exact prefixLift 6802081
  have htrace : WordTrace (prefixWord ++ tailWord_6802081) baseStart_6802081 baseEnd_6802081 := by
    simpa [prefixWord, tailWord_6802081, baseEnd_6802081] using wordTrace_append hprefix tailTrace_6802081
  have hstable : (prefixWord ++ tailWord_6802081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802081).length < 2 ^ (prefixWord ++ tailWord_6802081).sum := by decide
  have hdescent : baseEnd_6802081 < baseStart_6802081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802167 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_6802167 : Nat := 118140960795 + 6802167 * 2 ^ 59
def prefixEnd_6802167 : Nat := 4983230072969 + 3 ^ 40 * 6802167 * 2
def baseEnd_6802167 : Nat := 3492781163151793224029909

theorem tailTrace_6802167 : CollatzResearch.WordTrace tailWord_6802167 prefixEnd_6802167 3492781163151793224029909 := by
  unfold tailWord_6802167
  simp only [CollatzResearch.WordTrace]
  refine ⟨248095412347918151479644755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165396941565278767653096503 248095412347918151479644755)
  ·
    refine ⟨372143118521877227219467133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248095412347918151479644755 372143118521877227219467133)
    ·
      refine ⟨139553669445703960207300175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372143118521877227219467133 139553669445703960207300175)
      ·
        refine ⟨209330504168555940310950263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139553669445703960207300175 209330504168555940310950263)
        ·
          refine ⟨313995756252833910466425395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209330504168555940310950263 313995756252833910466425395)
          ·
            refine ⟨470993634379250865699638093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313995756252833910466425395 470993634379250865699638093)
            ·
              refine ⟨176622612892219074637364285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470993634379250865699638093 176622612892219074637364285)
              ·
                refine ⟨66233479834582152989011607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176622612892219074637364285 66233479834582152989011607)
                ·
                  refine ⟨99350219751873229483517411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66233479834582152989011607 99350219751873229483517411)
                  ·
                    refine ⟨149025329627809844225276117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99350219751873229483517411 149025329627809844225276117)
                    ·
                      refine ⟨3492781163151793224029909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149025329627809844225276117 3492781163151793224029909)
                      ·
                        rfl

theorem cell23_6802167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_6802167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802167 prefixEnd_6802167 := by exact prefixLift 6802167
  have htrace : WordTrace (prefixWord ++ tailWord_6802167) baseStart_6802167 baseEnd_6802167 := by
    simpa [prefixWord, tailWord_6802167, baseEnd_6802167] using wordTrace_append hprefix tailTrace_6802167
  have hstable : (prefixWord ++ tailWord_6802167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802167).length < 2 ^ (prefixWord ++ tailWord_6802167).sum := by decide
  have hdescent : baseEnd_6802167 < baseStart_6802167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802187 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 10]
def baseStart_6802187 : Nat := 118140960795 + 6802187 * 2 ^ 59
def prefixEnd_6802187 : Nat := 4983230072969 + 3 ^ 40 * 6802187 * 2
def baseEnd_6802187 : Nat := 1164263810921627715259939

theorem tailTrace_6802187 : CollatzResearch.WordTrace tailWord_6802187 prefixEnd_6802187 1164263810921627715259939 := by
  unfold tailWord_6802187
  simp only [CollatzResearch.WordTrace]
  refine ⟨248096141807845694895372815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165397427871897129930248543 248096141807845694895372815)
  ·
    refine ⟨372144212711768542343059223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248096141807845694895372815 372144212711768542343059223)
    ·
      refine ⟨558216319067652813514588835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372144212711768542343059223 558216319067652813514588835)
      ·
        refine ⟨837324478601479220271883253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558216319067652813514588835 837324478601479220271883253)
        ·
          refine ⟨78499169868888676900489055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 837324478601479220271883253 78499169868888676900489055)
          ·
            refine ⟨117748754803333015350733583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78499169868888676900489055 117748754803333015350733583)
            ·
              refine ⟨176623132204999523026100375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117748754803333015350733583 176623132204999523026100375)
              ·
                refine ⟨264934698307499284539150563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176623132204999523026100375 264934698307499284539150563)
                ·
                  refine ⟨397402047461248926808725845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264934698307499284539150563 397402047461248926808725845)
                  ·
                    refine ⟨1164263810921627715259939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 397402047461248926808725845 1164263810921627715259939)
                    ·
                      rfl

theorem cell23_6802187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_6802187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802187 prefixEnd_6802187 := by exact prefixLift 6802187
  have htrace : WordTrace (prefixWord ++ tailWord_6802187) baseStart_6802187 baseEnd_6802187 := by
    simpa [prefixWord, tailWord_6802187, baseEnd_6802187] using wordTrace_append hprefix tailTrace_6802187
  have hstable : (prefixWord ++ tailWord_6802187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802187).length < 2 ^ (prefixWord ++ tailWord_6802187).sum := by decide
  have hdescent : baseEnd_6802187 < baseStart_6802187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802218 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6802218 : Nat := 118140960795 + 6802218 * 2 ^ 59
def prefixEnd_6802218 : Nat := 4983230072969 + 3 ^ 40 * 6802218 * 2
def baseEnd_6802218 : Nat := 3492807350665172524492175

theorem tailTrace_6802218 : CollatzResearch.WordTrace tailWord_6802218 prefixEnd_6802218 3492807350665172524492175 := by
  unfold tailWord_6802218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62024318117683346797437827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165398181647155591459834205 62024318117683346797437827)
  ·
    refine ⟨93036477176525020196156741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62024318117683346797437827 93036477176525020196156741)
    ·
      refine ⟨17444339470598441286779389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93036477176525020196156741 17444339470598441286779389)
      ·
        refine ⟨6541627301474415482542271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17444339470598441286779389 6541627301474415482542271)
        ·
          refine ⟨9812440952211623223813407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541627301474415482542271 9812440952211623223813407)
          ·
            refine ⟨14718661428317434835720111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812440952211623223813407 14718661428317434835720111)
            ·
              refine ⟨22077992142476152253580167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718661428317434835720111 22077992142476152253580167)
              ·
                refine ⟨33116988213714228380370251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22077992142476152253580167 33116988213714228380370251)
                ·
                  refine ⟨49675482320571342570555377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33116988213714228380370251 49675482320571342570555377)
                  ·
                    refine ⟨37256611740428506927916533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49675482320571342570555377 37256611740428506927916533)
                    ·
                      refine ⟨3492807350665172524492175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37256611740428506927916533 3492807350665172524492175)
                      ·
                        rfl

theorem cell23_6802218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6802218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802218 prefixEnd_6802218 := by exact prefixLift 6802218
  have htrace : WordTrace (prefixWord ++ tailWord_6802218) baseStart_6802218 baseEnd_6802218 := by
    simpa [prefixWord, tailWord_6802218, baseEnd_6802218] using wordTrace_append hprefix tailTrace_6802218
  have hstable : (prefixWord ++ tailWord_6802218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802218).length < 2 ^ (prefixWord ++ tailWord_6802218).sum := by decide
  have hdescent : baseEnd_6802218 < baseStart_6802218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802268 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 6]
def baseStart_6802268 : Nat := 118140960795 + 6802268 * 2 ^ 59
def prefixEnd_6802268 : Nat := 4983230072969 + 3 ^ 40 * 6802268 * 2
def baseEnd_6802268 : Nat := 388092558299766369874105

theorem tailTrace_6802268 : CollatzResearch.WordTrace tailWord_6802268 prefixEnd_6802268 388092558299766369874105 := by
  unfold tailWord_6802268
  simp only [CollatzResearch.WordTrace]
  refine ⟨124049548060276122864535729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165399397413701497152714305 124049548060276122864535729)
  ·
    refine ⟨93037161045207092148401797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124049548060276122864535729 93037161045207092148401797)
    ·
      refine ⟨17444467695976329777825337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93037161045207092148401797 17444467695976329777825337)
      ·
        refine ⟨13083350771982247333369003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17444467695976329777825337 13083350771982247333369003)
        ·
          refine ⟨19625026157973371000053505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13083350771982247333369003 19625026157973371000053505)
          ·
            refine ⟨14718769618480028250040129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19625026157973371000053505 14718769618480028250040129)
            ·
              refine ⟨11039077213860021187530097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14718769618480028250040129 11039077213860021187530097)
              ·
                refine ⟨8279307910395015890647573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11039077213860021187530097 8279307910395015890647573)
                ·
                  refine ⟨388092558299766369874105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8279307910395015890647573 388092558299766369874105)
                  ·
                    rfl

theorem cell23_6802268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_6802268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802268 prefixEnd_6802268 := by exact prefixLift 6802268
  have htrace : WordTrace (prefixWord ++ tailWord_6802268) baseStart_6802268 baseEnd_6802268 := by
    simpa [prefixWord, tailWord_6802268, baseEnd_6802268] using wordTrace_append hprefix tailTrace_6802268
  have hstable : (prefixWord ++ tailWord_6802268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802268).length < 2 ^ (prefixWord ++ tailWord_6802268).sum := by decide
  have hdescent : baseEnd_6802268 < baseStart_6802268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802301 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6802301 : Nat := 118140960795 + 6802301 * 2 ^ 59
def prefixEnd_6802301 : Nat := 4983230072969 + 3 ^ 40 * 6802301 * 2
def baseEnd_6802301 : Nat := 3492849969559495699754293

theorem tailTrace_6802301 : CollatzResearch.WordTrace tailWord_6802301 prefixEnd_6802301 3492849969559495699754293 := by
  unfold tailWord_6802301
  simp only [CollatzResearch.WordTrace]
  refine ⟨248100299729432692365022757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165400199819621794910015171 248100299729432692365022757)
  ·
    refine ⟨46518806199268629818441767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248100299729432692365022757 46518806199268629818441767)
    ·
      refine ⟨69778209298902944727662651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46518806199268629818441767 69778209298902944727662651)
      ·
        refine ⟨104667313948354417091493977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69778209298902944727662651 104667313948354417091493977)
        ·
          refine ⟨78500485461265812818620483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104667313948354417091493977 78500485461265812818620483)
          ·
            refine ⟨117750728191898719227930725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78500485461265812818620483 117750728191898719227930725)
            ·
              refine ⟨22078261535981009855237011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117750728191898719227930725 22078261535981009855237011)
              ·
                refine ⟨33117392303971514782855517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22078261535981009855237011 33117392303971514782855517)
                ·
                  refine ⟨12419022113989318043570819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33117392303971514782855517 12419022113989318043570819)
                  ·
                    refine ⟨18628533170983977065356229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12419022113989318043570819 18628533170983977065356229)
                    ·
                      refine ⟨3492849969559495699754293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18628533170983977065356229 3492849969559495699754293)
                      ·
                        rfl

theorem cell23_6802301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6802301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802301 prefixEnd_6802301 := by exact prefixLift 6802301
  have htrace : WordTrace (prefixWord ++ tailWord_6802301) baseStart_6802301 baseEnd_6802301 := by
    simpa [prefixWord, tailWord_6802301, baseEnd_6802301] using wordTrace_append hprefix tailTrace_6802301
  have hstable : (prefixWord ++ tailWord_6802301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802301).length < 2 ^ (prefixWord ++ tailWord_6802301).sum := by decide
  have hdescent : baseEnd_6802301 < baseStart_6802301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_6802304 : Nat := 118140960795 + 6802304 * 2 ^ 59
def prefixEnd_6802304 : Nat := 4983230072969 + 3 ^ 40 * 6802304 * 2
def baseEnd_6802304 : Nat := 3492851510001459188016779

theorem tailTrace_6802304 : CollatzResearch.WordTrace tailWord_6802304 prefixEnd_6802304 3492851510001459188016779 := by
  unfold tailWord_6802304
  simp only [CollatzResearch.WordTrace]
  refine ⟨124050204574210911938690983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165400272765614549251587977 124050204574210911938690983)
  ·
    refine ⟨186075306861316367908036475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124050204574210911938690983 186075306861316367908036475)
    ·
      refine ⟨279112960291974551862054713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186075306861316367908036475 279112960291974551862054713)
      ·
        refine ⟨209334720218980913896541035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279112960291974551862054713 209334720218980913896541035)
        ·
          refine ⟨314002080328471370844811553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209334720218980913896541035 314002080328471370844811553)
          ·
            refine ⟨235501560246353528133608665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314002080328471370844811553 235501560246353528133608665)
            ·
              refine ⟨176626170184765146100206499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235501560246353528133608665 176626170184765146100206499)
              ·
                refine ⟨264939255277147719150309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176626170184765146100206499 264939255277147719150309749)
                ·
                  refine ⟨24838055182232598670341539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264939255277147719150309749 24838055182232598670341539)
                  ·
                    refine ⟨37257082773348898005512309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24838055182232598670341539 37257082773348898005512309)
                    ·
                      refine ⟨3492851510001459188016779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37257082773348898005512309 3492851510001459188016779)
                      ·
                        rfl

theorem cell23_6802304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_6802304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802304 prefixEnd_6802304 := by exact prefixLift 6802304
  have htrace : WordTrace (prefixWord ++ tailWord_6802304) baseStart_6802304 baseEnd_6802304 := by
    simpa [prefixWord, tailWord_6802304, baseEnd_6802304] using wordTrace_append hprefix tailTrace_6802304
  have hstable : (prefixWord ++ tailWord_6802304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802304).length < 2 ^ (prefixWord ++ tailWord_6802304).sum := by decide
  have hdescent : baseEnd_6802304 < baseStart_6802304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802311 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 6]
def baseStart_6802311 : Nat := 118140960795 + 6802311 * 2 ^ 59
def prefixEnd_6802311 : Nat := 4983230072969 + 3 ^ 40 * 6802311 * 2
def baseEnd_6802311 : Nat := 1164285034788680220209749

theorem tailTrace_6802311 : CollatzResearch.WordTrace tailWord_6802311 prefixEnd_6802311 1164285034788680220209749 := by
  unfold tailWord_6802311
  simp only [CollatzResearch.WordTrace]
  refine ⟨248100664459396464072886787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165400442972930976048591191 248100664459396464072886787)
  ·
    refine ⟨372150996689094696109330181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248100664459396464072886787 372150996689094696109330181)
    ·
      refine ⟨69778311879205255520499409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372150996689094696109330181 69778311879205255520499409)
      ·
        refine ⟨52333733909403941640374557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69778311879205255520499409 52333733909403941640374557)
        ·
          refine ⟨19625150216026478115140459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52333733909403941640374557 19625150216026478115140459)
          ·
            refine ⟨29437725324039717172710689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625150216026478115140459 29437725324039717172710689)
            ·
              refine ⟨22078293993029787879533017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29437725324039717172710689 22078293993029787879533017)
              ·
                refine ⟨16558720494772340909649763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22078293993029787879533017 16558720494772340909649763)
                ·
                  refine ⟨24838080742158511364474645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16558720494772340909649763 24838080742158511364474645)
                  ·
                    refine ⟨1164285034788680220209749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24838080742158511364474645 1164285034788680220209749)
                    ·
                      rfl

theorem cell23_6802311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_6802311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802311 prefixEnd_6802311 := by exact prefixLift 6802311
  have htrace : WordTrace (prefixWord ++ tailWord_6802311) baseStart_6802311 baseEnd_6802311 := by
    simpa [prefixWord, tailWord_6802311, baseEnd_6802311] using wordTrace_append hprefix tailTrace_6802311
  have hstable : (prefixWord ++ tailWord_6802311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802311).length < 2 ^ (prefixWord ++ tailWord_6802311).sum := by decide
  have hdescent : baseEnd_6802311 < baseStart_6802311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802312 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6802312 : Nat := 118140960795 + 6802312 * 2 ^ 59
def prefixEnd_6802312 : Nat := 4983230072969 + 3 ^ 40 * 6802312 * 2
def baseEnd_6802312 : Nat := 3492855617846695156716743

theorem tailTrace_6802312 : CollatzResearch.WordTrace tailWord_6802312 prefixEnd_6802312 3492855617846695156716743 := by
  unfold tailWord_6802312
  simp only [CollatzResearch.WordTrace]
  refine ⟨124050350466196420621836595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165400467288261894162448793 124050350466196420621836595)
  ·
    refine ⟨186075525699294630932754893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124050350466196420621836595 186075525699294630932754893)
    ·
      refine ⟨69778322137235486599783085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186075525699294630932754893 69778322137235486599783085)
      ·
        refine ⟨26166870801463307474918657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69778322137235486599783085 26166870801463307474918657)
        ·
          refine ⟨19625153101097480606188993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166870801463307474918657 19625153101097480606188993)
          ·
            refine ⟨14718864825823110454641745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19625153101097480606188993 14718864825823110454641745)
            ·
              refine ⟨11039148619367332840981309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14718864825823110454641745 11039148619367332840981309)
              ·
                refine ⟨4139680732262749815367991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11039148619367332840981309 4139680732262749815367991)
                ·
                  refine ⟨6209521098394124723051987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139680732262749815367991 6209521098394124723051987)
                  ·
                    refine ⟨9314281647591187084577981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6209521098394124723051987 9314281647591187084577981)
                    ·
                      refine ⟨3492855617846695156716743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314281647591187084577981 3492855617846695156716743)
                      ·
                        rfl

theorem cell23_6802312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6802312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802312 prefixEnd_6802312 := by exact prefixLift 6802312
  have htrace : WordTrace (prefixWord ++ tailWord_6802312) baseStart_6802312 baseEnd_6802312 := by
    simpa [prefixWord, tailWord_6802312, baseEnd_6802312] using wordTrace_append hprefix tailTrace_6802312
  have hstable : (prefixWord ++ tailWord_6802312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802312).length < 2 ^ (prefixWord ++ tailWord_6802312).sum := by decide
  have hdescent : baseEnd_6802312 < baseStart_6802312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802335 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 3, 2, 2]
def baseStart_6802335 : Nat := 118140960795 + 6802335 * 2 ^ 59
def prefixEnd_6802335 : Nat := 4983230072969 + 3 ^ 40 * 6802335 * 2
def baseEnd_6802335 : Nat := 3492867427901748566729137

theorem tailTrace_6802335 : CollatzResearch.WordTrace tailWord_6802335 prefixEnd_6802335 3492867427901748566729137 := by
  unfold tailWord_6802335
  simp only [CollatzResearch.WordTrace]
  refine ⟨248101539811309516171760459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165401026540873010781173639 248101539811309516171760459)
  ·
    refine ⟨372152309716964274257640689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248101539811309516171760459 372152309716964274257640689)
    ·
      refine ⟨279114232287723205693230517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372152309716964274257640689 279114232287723205693230517)
      ·
        refine ⟨26166959276974050533740361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279114232287723205693230517 26166959276974050533740361)
        ·
          refine ⟨19625219457730537900305271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166959276974050533740361 19625219457730537900305271)
          ·
            refine ⟨29437829186595806850457907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625219457730537900305271 29437829186595806850457907)
            ·
              refine ⟨44156743779893710275686861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29437829186595806850457907 44156743779893710275686861)
              ·
                refine ⟨16558778917460141353382573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44156743779893710275686861 16558778917460141353382573)
                ·
                  refine ⟨6209542094047553007518465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16558778917460141353382573 6209542094047553007518465)
                  ·
                    refine ⟨4657156570535664755638849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209542094047553007518465 4657156570535664755638849)
                    ·
                      refine ⟨3492867427901748566729137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657156570535664755638849 3492867427901748566729137)
                      ·
                        rfl

theorem cell23_6802335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_6802335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802335 prefixEnd_6802335 := by exact prefixLift 6802335
  have htrace : WordTrace (prefixWord ++ tailWord_6802335) baseStart_6802335 baseEnd_6802335 := by
    simpa [prefixWord, tailWord_6802335, baseEnd_6802335] using wordTrace_append hprefix tailTrace_6802335
  have hstable : (prefixWord ++ tailWord_6802335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802335).length < 2 ^ (prefixWord ++ tailWord_6802335).sum := by decide
  have hdescent : baseEnd_6802335 < baseStart_6802335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802338 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6802338 : Nat := 118140960795 + 6802338 * 2 ^ 59
def prefixEnd_6802338 : Nat := 4983230072969 + 3 ^ 40 * 6802338 * 2
def baseEnd_6802338 : Nat := 3492868968343712054991623

theorem tailTrace_6802338 : CollatzResearch.WordTrace tailWord_6802338 prefixEnd_6802338 3492868968343712054991623 := by
  unfold tailWord_6802338
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025412307574661921029917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165401099486865765122746445 62025412307574661921029917)
  ·
    refine ⟨23259529615340498220386219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62025412307574661921029917 23259529615340498220386219)
    ·
      refine ⟨34889294423010747330579329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23259529615340498220386219 34889294423010747330579329)
      ·
        refine ⟨26166970817258060497934497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34889294423010747330579329 26166970817258060497934497)
        ·
          refine ⟨19625228112943545373450873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166970817258060497934497 19625228112943545373450873)
          ·
            refine ⟨14718921084707659030088155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19625228112943545373450873 14718921084707659030088155)
            ·
              refine ⟨22078381627061488545132233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718921084707659030088155 22078381627061488545132233)
              ·
                refine ⟨16558786220296116408849175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22078381627061488545132233 16558786220296116408849175)
                ·
                  refine ⟨24838179330444174613273763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16558786220296116408849175 24838179330444174613273763)
                  ·
                    refine ⟨37257268995666261919910645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24838179330444174613273763 37257268995666261919910645)
                    ·
                      refine ⟨3492868968343712054991623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37257268995666261919910645 3492868968343712054991623)
                      ·
                        rfl

theorem cell23_6802338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6802338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802338 prefixEnd_6802338 := by exact prefixLift 6802338
  have htrace : WordTrace (prefixWord ++ tailWord_6802338) baseStart_6802338 baseEnd_6802338 := by
    simpa [prefixWord, tailWord_6802338, baseEnd_6802338] using wordTrace_append hprefix tailTrace_6802338
  have hstable : (prefixWord ++ tailWord_6802338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802338).length < 2 ^ (prefixWord ++ tailWord_6802338).sum := by decide
  have hdescent : baseEnd_6802338 < baseStart_6802338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802351 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_6802351 : Nat := 118140960795 + 6802351 * 2 ^ 59
def prefixEnd_6802351 : Nat := 4983230072969 + 3 ^ 40 * 6802351 * 2
def baseEnd_6802351 : Nat := 3492875643592220504129063

theorem tailTrace_6802351 : CollatzResearch.WordTrace tailWord_6802351 prefixEnd_6802351 3492875643592220504129063 := by
  unfold tailWord_6802351
  simp only [CollatzResearch.WordTrace]
  refine ⟨248102123379251550904342907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165401415586167700602895271 248102123379251550904342907)
  ·
    refine ⟨372153185068877326356514361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248102123379251550904342907 372153185068877326356514361)
    ·
      refine ⟨279114888801657994767385771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372153185068877326356514361 279114888801657994767385771)
      ·
        refine ⟨418672333202486992151078657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279114888801657994767385771 418672333202486992151078657)
        ·
          refine ⟨314004249901865244113308993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418672333202486992151078657 314004249901865244113308993)
          ·
            refine ⟨235503187426398933084981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314004249901865244113308993 235503187426398933084981745)
            ·
              refine ⟨176627390569799199813736309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235503187426398933084981745 176627390569799199813736309)
              ·
                refine ⟨16558817865918674982537779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176627390569799199813736309 16558817865918674982537779)
                ·
                  refine ⟨24838226798878012473806669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16558817865918674982537779 24838226798878012473806669)
                  ·
                    refine ⟨9314335049579254677677501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24838226798878012473806669 9314335049579254677677501)
                    ·
                      refine ⟨3492875643592220504129063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314335049579254677677501 3492875643592220504129063)
                      ·
                        rfl

theorem cell23_6802351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_6802351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802351 prefixEnd_6802351 := by exact prefixLift 6802351
  have htrace : WordTrace (prefixWord ++ tailWord_6802351) baseStart_6802351 baseEnd_6802351 := by
    simpa [prefixWord, tailWord_6802351, baseEnd_6802351] using wordTrace_append hprefix tailTrace_6802351
  have hstable : (prefixWord ++ tailWord_6802351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802351).length < 2 ^ (prefixWord ++ tailWord_6802351).sum := by decide
  have hdescent : baseEnd_6802351 < baseStart_6802351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802368 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_6802368 : Nat := 118140960795 + 6802368 * 2 ^ 59
def prefixEnd_6802368 : Nat := 4983230072969 + 3 ^ 40 * 6802368 * 2
def baseEnd_6802368 : Nat := 3492884372763346937616485

theorem tailTrace_6802368 : CollatzResearch.WordTrace tailWord_6802368 prefixEnd_6802368 3492884372763346937616485 := by
  unfold tailWord_6802368
  simp only [CollatzResearch.WordTrace]
  refine ⟨124051371710094981403855879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165401828946793308538474505 124051371710094981403855879)
  ·
    refine ⟨186077057565142472105783819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124051371710094981403855879 186077057565142472105783819)
    ·
      refine ⟨279115586347713708158675729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186077057565142472105783819 279115586347713708158675729)
      ·
        refine ⟨209336689760785281119006797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279115586347713708158675729 209336689760785281119006797)
        ·
          refine ⟨78501258660294480419627549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209336689760785281119006797 78501258660294480419627549)
          ·
            refine ⟨29437971997610430157360331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78501258660294480419627549 29437971997610430157360331)
            ·
              refine ⟨44156957996415645236040497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29437971997610430157360331 44156957996415645236040497)
              ·
                refine ⟨33117718497311733927030373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44156957996415645236040497 33117718497311733927030373)
                ·
                  refine ⟨6209572218245950111318195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33117718497311733927030373 6209572218245950111318195)
                  ·
                    refine ⟨9314358327368925166977293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6209572218245950111318195 9314358327368925166977293)
                    ·
                      refine ⟨3492884372763346937616485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314358327368925166977293 3492884372763346937616485)
                      ·
                        rfl

theorem cell23_6802368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_6802368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802368 prefixEnd_6802368 := by exact prefixLift 6802368
  have htrace : WordTrace (prefixWord ++ tailWord_6802368) baseStart_6802368 baseEnd_6802368 := by
    simpa [prefixWord, tailWord_6802368, baseEnd_6802368] using wordTrace_append hprefix tailTrace_6802368
  have hstable : (prefixWord ++ tailWord_6802368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802368).length < 2 ^ (prefixWord ++ tailWord_6802368).sum := by decide
  have hdescent : baseEnd_6802368 < baseStart_6802368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802378 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_6802378 : Nat := 118140960795 + 6802378 * 2 ^ 59
def prefixEnd_6802378 : Nat := 4983230072969 + 3 ^ 40 * 6802378 * 2
def baseEnd_6802378 : Nat := 3492889507569891898491439

theorem tailTrace_6802378 : CollatzResearch.WordTrace tailWord_6802378 prefixEnd_6802378 3492889507569891898491439 := by
  unfold tailWord_6802378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025777037538433628893947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165402072100102489677050525 62025777037538433628893947)
  ·
    refine ⟨93038665556307650443340921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62025777037538433628893947 93038665556307650443340921)
    ·
      refine ⟨69778999167230737832505691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93038665556307650443340921 69778999167230737832505691)
      ·
        refine ⟨104668498750846106748758537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69778999167230737832505691 104668498750846106748758537)
        ·
          refine ⟨78501374063134580061568903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104668498750846106748758537 78501374063134580061568903)
          ·
            refine ⟨117752061094701870092353355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78501374063134580061568903 117752061094701870092353355)
            ·
              refine ⟨176628091642052805138530033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117752061094701870092353355 176628091642052805138530033)
              ·
                refine ⟨132471068731539603853897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176628091642052805138530033 132471068731539603853897525)
                ·
                  refine ⟨12419162693581837861302893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132471068731539603853897525 12419162693581837861302893)
                  ·
                    refine ⟨4657186010093189197988585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12419162693581837861302893 4657186010093189197988585)
                    ·
                      refine ⟨3492889507569891898491439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657186010093189197988585 3492889507569891898491439)
                      ·
                        rfl

theorem cell23_6802378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_6802378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802378 prefixEnd_6802378 := by exact prefixLift 6802378
  have htrace : WordTrace (prefixWord ++ tailWord_6802378) baseStart_6802378 baseEnd_6802378 := by
    simpa [prefixWord, tailWord_6802378, baseEnd_6802378] using wordTrace_append hprefix tailTrace_6802378
  have hstable : (prefixWord ++ tailWord_6802378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802378).length < 2 ^ (prefixWord ++ tailWord_6802378).sum := by decide
  have hdescent : baseEnd_6802378 < baseStart_6802378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802386 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6802386 : Nat := 118140960795 + 6802386 * 2 ^ 59
def prefixEnd_6802386 : Nat := 4983230072969 + 3 ^ 40 * 6802386 * 2
def baseEnd_6802386 : Nat := 3492893615415127867191403

theorem tailTrace_6802386 : CollatzResearch.WordTrace tailWord_6802386 prefixEnd_6802386 3492893615415127867191403 := by
  unfold tailWord_6802386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025849983531187970466753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165402266622749834587911341 62025849983531187970466753)
  ·
    refine ⟨46519387487648390977850065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62025849983531187970466753 46519387487648390977850065)
    ·
      refine ⟨34889540615736293233387549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46519387487648390977850065 34889540615736293233387549)
      ·
        refine ⟨13083577730901109962520331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34889540615736293233387549 13083577730901109962520331)
        ·
          refine ⟨19625366596351664943780497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13083577730901109962520331 19625366596351664943780497)
          ·
            refine ⟨14719024947263748707835373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19625366596351664943780497 14719024947263748707835373)
            ·
              refine ⟨5519634355223905765438265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14719024947263748707835373 5519634355223905765438265)
              ·
                refine ⟨4139725766417929324078699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519634355223905765438265 4139725766417929324078699)
                ·
                  refine ⟨6209588649626893986118049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139725766417929324078699 6209588649626893986118049)
                  ·
                    refine ⟨4657191487220170489588537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209588649626893986118049 4657191487220170489588537)
                    ·
                      refine ⟨3492893615415127867191403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657191487220170489588537 3492893615415127867191403)
                      ·
                        rfl

theorem cell23_6802386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6802386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802386 prefixEnd_6802386 := by exact prefixLift 6802386
  have htrace : WordTrace (prefixWord ++ tailWord_6802386) baseStart_6802386 baseEnd_6802386 := by
    simpa [prefixWord, tailWord_6802386, baseEnd_6802386] using wordTrace_append hprefix tailTrace_6802386
  have hstable : (prefixWord ++ tailWord_6802386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802386).length < 2 ^ (prefixWord ++ tailWord_6802386).sum := by decide
  have hdescent : baseEnd_6802386 < baseStart_6802386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802441 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_6802441 : Nat := 118140960795 + 6802441 * 2 ^ 59
def prefixEnd_6802441 : Nat := 4983230072969 + 3 ^ 40 * 6802441 * 2
def baseEnd_6802441 : Nat := 3492921856851125152003649

theorem tailTrace_6802441 : CollatzResearch.WordTrace tailWord_6802441 prefixEnd_6802441 3492921856851125152003649 := by
  unfold tailWord_6802441
  simp only [CollatzResearch.WordTrace]
  refine ⟨248105405948925496275119177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165403603965950330850079451 248105405948925496275119177)
  ·
    refine ⟨186079054461694122206339383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248105405948925496275119177 186079054461694122206339383)
    ·
      refine ⟨279118581692541183309509075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186079054461694122206339383 279118581692541183309509075)
      ·
        refine ⟨418677872538811774964263613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279118581692541183309509075 418677872538811774964263613)
        ·
          refine ⟨157004202202054415611598855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418677872538811774964263613 157004202202054415611598855)
          ·
            refine ⟨235506303303081623417398283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157004202202054415611598855 235506303303081623417398283)
            ·
              refine ⟨353259454954622435126097425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235506303303081623417398283 353259454954622435126097425)
              ·
                refine ⟨264944591215966826344573069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353259454954622435126097425 264944591215966826344573069)
                ·
                  refine ⟨99354221705987559879214901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264944591215966826344573069 99354221705987559879214901)
                  ·
                    refine ⟨9314458284936333738676397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99354221705987559879214901 9314458284936333738676397)
                    ·
                      refine ⟨3492921856851125152003649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314458284936333738676397 3492921856851125152003649)
                      ·
                        rfl

theorem cell23_6802441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_6802441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802441 prefixEnd_6802441 := by exact prefixLift 6802441
  have htrace : WordTrace (prefixWord ++ tailWord_6802441) baseStart_6802441 baseEnd_6802441 := by
    simpa [prefixWord, tailWord_6802441, baseEnd_6802441] using wordTrace_append hprefix tailTrace_6802441
  have hstable : (prefixWord ++ tailWord_6802441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802441).length < 2 ^ (prefixWord ++ tailWord_6802441).sum := by decide
  have hdescent : baseEnd_6802441 < baseStart_6802441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802442 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_6802442 : Nat := 118140960795 + 6802442 * 2 ^ 59
def prefixEnd_6802442 : Nat := 4983230072969 + 3 ^ 40 * 6802442 * 2
def baseEnd_6802442 : Nat := 3492922370331779648091145

theorem tailTrace_6802442 : CollatzResearch.WordTrace tailWord_6802442 prefixEnd_6802442 3492922370331779648091145 := by
  unfold tailWord_6802442
  simp only [CollatzResearch.WordTrace]
  refine ⟨62026360605480468361476395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165403628281281248963937053 62026360605480468361476395)
  ·
    refine ⟨93039540908220702542214593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62026360605480468361476395 93039540908220702542214593)
    ·
      refine ⟨69779655681165526906660945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93039540908220702542214593 69779655681165526906660945)
      ·
        refine ⟨52334741760874145179995709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69779655681165526906660945 52334741760874145179995709)
        ·
          refine ⟨19625528160327804442498391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52334741760874145179995709 19625528160327804442498391)
          ·
            refine ⟨29438292240491706663747587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625528160327804442498391 29438292240491706663747587)
            ·
              refine ⟨44157438360737559995621381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29438292240491706663747587 44157438360737559995621381)
              ·
                refine ⟨8279519692638292499179009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44157438360737559995621381 8279519692638292499179009)
                ·
                  refine ⟨6209639769478719374384257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279519692638292499179009 6209639769478719374384257)
                  ·
                    refine ⟨4657229827109039530788193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209639769478719374384257 4657229827109039530788193)
                    ·
                      refine ⟨3492922370331779648091145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657229827109039530788193 3492922370331779648091145)
                      ·
                        rfl

theorem cell23_6802442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_6802442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802442 prefixEnd_6802442 := by exact prefixLift 6802442
  have htrace : WordTrace (prefixWord ++ tailWord_6802442) baseStart_6802442 baseEnd_6802442 := by
    simpa [prefixWord, tailWord_6802442, baseEnd_6802442] using wordTrace_append hprefix tailTrace_6802442
  have hstable : (prefixWord ++ tailWord_6802442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802442).length < 2 ^ (prefixWord ++ tailWord_6802442).sum := by decide
  have hdescent : baseEnd_6802442 < baseStart_6802442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802458 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_6802458 : Nat := 118140960795 + 6802458 * 2 ^ 59
def prefixEnd_6802458 : Nat := 4983230072969 + 3 ^ 40 * 6802458 * 2
def baseEnd_6802458 : Nat := 3492930586022251585491071

theorem tailTrace_6802458 : CollatzResearch.WordTrace tailWord_6802458 prefixEnd_6802458 3492930586022251585491071 := by
  unfold tailWord_6802458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62026506497465977044622007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165404017326575938785658685 62026506497465977044622007)
  ·
    refine ⟨93039759746198965566933011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62026506497465977044622007 93039759746198965566933011)
    ·
      refine ⟨139559639619298448350399517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93039759746198965566933011 139559639619298448350399517)
      ·
        refine ⟨52334864857236918131399819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139559639619298448350399517 52334864857236918131399819)
        ·
          refine ⟨78502297285855377197099729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52334864857236918131399819 78502297285855377197099729)
          ·
            refine ⟨58876722964391532897824797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78502297285855377197099729 58876722964391532897824797)
            ·
              refine ⟨22078771111646824836684299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58876722964391532897824797 22078771111646824836684299)
              ·
                refine ⟨33118156667470237255026449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22078771111646824836684299 33118156667470237255026449)
                ·
                  refine ⟨24838617500602677941269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33118156667470237255026449 24838617500602677941269837)
                  ·
                    refine ⟨9314481562726004227976189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24838617500602677941269837 9314481562726004227976189)
                    ·
                      refine ⟨3492930586022251585491071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314481562726004227976189 3492930586022251585491071)
                      ·
                        rfl

theorem cell23_6802458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_6802458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802458 prefixEnd_6802458 := by exact prefixLift 6802458
  have htrace : WordTrace (prefixWord ++ tailWord_6802458) baseStart_6802458 baseEnd_6802458 := by
    simpa [prefixWord, tailWord_6802458, baseEnd_6802458] using wordTrace_append hprefix tailTrace_6802458
  have hstable : (prefixWord ++ tailWord_6802458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802458).length < 2 ^ (prefixWord ++ tailWord_6802458).sum := by decide
  have hdescent : baseEnd_6802458 < baseStart_6802458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802478 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_6802478 : Nat := 118140960795 + 6802478 * 2 ^ 59
def prefixEnd_6802478 : Nat := 4983230072969 + 3 ^ 40 * 6802478 * 2
def baseEnd_6802478 : Nat := 1164313618545113835746993

theorem tailTrace_6802478 : CollatzResearch.WordTrace tailWord_6802478 prefixEnd_6802478 1164313618545113835746993 := by
  unfold tailWord_6802478
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013344431223931449277011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165404503633194301062810725 31013344431223931449277011)
  ·
    refine ⟨46520016646835897173915517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31013344431223931449277011 46520016646835897173915517)
    ·
      refine ⟨17445006242563461440218319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46520016646835897173915517 17445006242563461440218319)
      ·
        refine ⟨26167509363845192160327479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17445006242563461440218319 26167509363845192160327479)
        ·
          refine ⟨39251264045767788240491219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26167509363845192160327479 39251264045767788240491219)
          ·
            refine ⟨58876896068651682360736829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39251264045767788240491219 58876896068651682360736829)
            ·
              refine ⟨22078836025744380885276311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58876896068651682360736829 22078836025744380885276311)
              ·
                refine ⟨33118254038616571327914467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22078836025744380885276311 33118254038616571327914467)
                ·
                  refine ⟨49677381057924856991871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33118254038616571327914467 49677381057924856991871701)
                  ·
                    refine ⟨1164313618545113835746993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49677381057924856991871701 1164313618545113835746993)
                    ·
                      rfl

theorem cell23_6802478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_6802478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802478 prefixEnd_6802478 := by exact prefixLift 6802478
  have htrace : WordTrace (prefixWord ++ tailWord_6802478) baseStart_6802478 baseEnd_6802478 := by
    simpa [prefixWord, tailWord_6802478, baseEnd_6802478] using wordTrace_append hprefix tailTrace_6802478
  have hstable : (prefixWord ++ tailWord_6802478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802478).length < 2 ^ (prefixWord ++ tailWord_6802478).sum := by decide
  have hdescent : baseEnd_6802478 < baseStart_6802478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802501 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_6802501 : Nat := 118140960795 + 6802501 * 2 ^ 59
def prefixEnd_6802501 : Nat := 4983230072969 + 3 ^ 40 * 6802501 * 2
def baseEnd_6802501 : Nat := 3492952665690394917253373

theorem tailTrace_6802501 : CollatzResearch.WordTrace tailWord_6802501 prefixEnd_6802501 3492952665690394917253373 := by
  unfold tailWord_6802501
  simp only [CollatzResearch.WordTrace]
  refine ⟨248107594328708126522303357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165405062885805417681535571 248107594328708126522303357)
  ·
    refine ⟨93040347873265547445863759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248107594328708126522303357 93040347873265547445863759)
    ·
      refine ⟨139560521809898321168795639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93040347873265547445863759 139560521809898321168795639)
      ·
        refine ⟨209340782714847481753193459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139560521809898321168795639 209340782714847481753193459)
        ·
          refine ⟨314011174072271222629790189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209340782714847481753193459 314011174072271222629790189)
          ·
            refine ⟨117754190277101708486171321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314011174072271222629790189 117754190277101708486171321)
            ·
              refine ⟨88315642707826281364628491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117754190277101708486171321 88315642707826281364628491)
              ·
                refine ⟨132473464061739422046942737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88315642707826281364628491 132473464061739422046942737)
                ·
                  refine ⟨99355098046304566535207053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132473464061739422046942737 99355098046304566535207053)
                  ·
                    refine ⟨37258161767364212450702645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99355098046304566535207053 37258161767364212450702645)
                    ·
                      refine ⟨3492952665690394917253373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37258161767364212450702645 3492952665690394917253373)
                      ·
                        rfl

theorem cell23_6802501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_6802501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802501 prefixEnd_6802501 := by exact prefixLift 6802501
  have htrace : WordTrace (prefixWord ++ tailWord_6802501) baseStart_6802501 baseEnd_6802501 := by
    simpa [prefixWord, tailWord_6802501, baseEnd_6802501] using wordTrace_append hprefix tailTrace_6802501
  have hstable : (prefixWord ++ tailWord_6802501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802501).length < 2 ^ (prefixWord ++ tailWord_6802501).sum := by decide
  have hdescent : baseEnd_6802501 < baseStart_6802501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802511 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_6802511 : Nat := 118140960795 + 6802511 * 2 ^ 59
def prefixEnd_6802511 : Nat := 4983230072969 + 3 ^ 40 * 6802511 * 2
def baseEnd_6802511 : Nat := 3492957800496939878128327

theorem tailTrace_6802511 : CollatzResearch.WordTrace tailWord_6802511 prefixEnd_6802511 3492957800496939878128327 := by
  unfold tailWord_6802511
  simp only [CollatzResearch.WordTrace]
  refine ⟨248107959058671898230167387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165405306039114598820111591 248107959058671898230167387)
  ·
    refine ⟨372161938588007847345251081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248107959058671898230167387 372161938588007847345251081)
    ·
      refine ⟨279121453941005885508938311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372161938588007847345251081 279121453941005885508938311)
      ·
        refine ⟨418682180911508828263407467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279121453941005885508938311 418682180911508828263407467)
        ·
          refine ⟨628023271367263242395111201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418682180911508828263407467 628023271367263242395111201)
          ·
            refine ⟨471017453525447431796333401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628023271367263242395111201 471017453525447431796333401)
            ·
              refine ⟨353263090144085573847250051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471017453525447431796333401 353263090144085573847250051)
              ·
                refine ⟨529894635216128360770875077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353263090144085573847250051 529894635216128360770875077)
                ·
                  refine ⟨99355244103024067644539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529894635216128360770875077 99355244103024067644539077)
                  ·
                    refine ⟨18629108269317012683351077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99355244103024067644539077 18629108269317012683351077)
                    ·
                      refine ⟨3492957800496939878128327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18629108269317012683351077 3492957800496939878128327)
                      ·
                        rfl

theorem cell23_6802511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_6802511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802511 prefixEnd_6802511 := by exact prefixLift 6802511
  have htrace : WordTrace (prefixWord ++ tailWord_6802511) baseStart_6802511 baseEnd_6802511 := by
    simpa [prefixWord, tailWord_6802511, baseEnd_6802511] using wordTrace_append hprefix tailTrace_6802511
  have hstable : (prefixWord ++ tailWord_6802511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802511).length < 2 ^ (prefixWord ++ tailWord_6802511).sum := by decide
  have hdescent : baseEnd_6802511 < baseStart_6802511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802538 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_6802538 : Nat := 118140960795 + 6802538 * 2 ^ 59
def prefixEnd_6802538 : Nat := 4983230072969 + 3 ^ 40 * 6802538 * 2
def baseEnd_6802538 : Nat := 388107962719401252498967

theorem tailTrace_6802538 : CollatzResearch.WordTrace tailWord_6802538 prefixEnd_6802538 388107962719401252498967 := by
  unfold tailWord_6802538
  simp only [CollatzResearch.WordTrace]
  refine ⟨62027235957393520460350067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165405962553049387894266845 62027235957393520460350067)
  ·
    refine ⟨93040853936090280690525101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62027235957393520460350067 93040853936090280690525101)
    ·
      refine ⟨34890320226033855258946913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93040853936090280690525101 34890320226033855258946913)
      ·
        refine ⟨26167740169525391444210185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34890320226033855258946913 26167740169525391444210185)
        ·
          refine ⟨19625805127144043583157639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26167740169525391444210185 19625805127144043583157639)
          ·
            refine ⟨29438707690716065374736459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625805127144043583157639 29438707690716065374736459)
            ·
              refine ⟨44158061536074098062104689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29438707690716065374736459 44158061536074098062104689)
              ·
                refine ⟨33118546152055573546578517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44158061536074098062104689 33118546152055573546578517)
                ·
                  refine ⟨388107962719401252498967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33118546152055573546578517 388107962719401252498967)
                  ·
                    rfl

theorem cell23_6802538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_6802538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802538 prefixEnd_6802538 := by exact prefixLift 6802538
  have htrace : WordTrace (prefixWord ++ tailWord_6802538) baseStart_6802538 baseEnd_6802538 := by
    simpa [prefixWord, tailWord_6802538, baseEnd_6802538] using wordTrace_append hprefix tailTrace_6802538
  have hstable : (prefixWord ++ tailWord_6802538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802538).length < 2 ^ (prefixWord ++ tailWord_6802538).sum := by decide
  have hdescent : baseEnd_6802538 < baseStart_6802538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802592 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2]
def baseStart_6802592 : Nat := 118140960795 + 6802592 * 2 ^ 59
def prefixEnd_6802592 : Nat := 4983230072969 + 3 ^ 40 * 6802592 * 2
def baseEnd_6802592 : Nat := 3492999392429954061215455

theorem tailTrace_6802592 : CollatzResearch.WordTrace tailWord_6802592 prefixEnd_6802592 3492999392429954061215455 := by
  unfold tailWord_6802592
  simp only [CollatzResearch.WordTrace]
  refine ⟨124055456685689224531933015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165407275580918966042577353 124055456685689224531933015)
  ·
    refine ⟨186083185028533836797899523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124055456685689224531933015 186083185028533836797899523)
    ·
      refine ⟨279124777542800755196849285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186083185028533836797899523 279124777542800755196849285)
      ·
        refine ⟨52335895789275141599409241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279124777542800755196849285 52335895789275141599409241)
        ·
          refine ⟨39251921841956356199556931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52335895789275141599409241 39251921841956356199556931)
          ·
            refine ⟨58877882762934534299335397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39251921841956356199556931 58877882762934534299335397)
            ·
              refine ⟨11039603018050225181125387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58877882762934534299335397 11039603018050225181125387)
              ·
                refine ⟨16559404527075337771688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11039603018050225181125387 16559404527075337771688081)
                ·
                  refine ⟨12419553395306503328766061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16559404527075337771688081 12419553395306503328766061)
                  ·
                    refine ⟨4657332523239938748287273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12419553395306503328766061 4657332523239938748287273)
                    ·
                      refine ⟨3492999392429954061215455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657332523239938748287273 3492999392429954061215455)
                      ·
                        rfl

theorem cell23_6802592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_6802592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802592 prefixEnd_6802592 := by exact prefixLift 6802592
  have htrace : WordTrace (prefixWord ++ tailWord_6802592) baseStart_6802592 baseEnd_6802592 := by
    simpa [prefixWord, tailWord_6802592, baseEnd_6802592] using wordTrace_append hprefix tailTrace_6802592
  have hstable : (prefixWord ++ tailWord_6802592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802592).length < 2 ^ (prefixWord ++ tailWord_6802592).sum := by decide
  have hdescent : baseEnd_6802592 < baseStart_6802592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802618 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_6802618 : Nat := 118140960795 + 6802618 * 2 ^ 59
def prefixEnd_6802618 : Nat := 4983230072969 + 3 ^ 40 * 6802618 * 2
def baseEnd_6802618 : Nat := 3493012742926970959490335

theorem tailTrace_6802618 : CollatzResearch.WordTrace tailWord_6802618 prefixEnd_6802618 3493012742926970959490335 := by
  unfold tailWord_6802618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62027965417321063876078127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165407907779522837002875005 62027965417321063876078127)
  ·
    refine ⟨93041948125981595814117191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62027965417321063876078127 93041948125981595814117191)
    ·
      refine ⟨139562922188972393721175787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93041948125981595814117191 139562922188972393721175787)
      ·
        refine ⟨209344383283458590581763681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139562922188972393721175787 209344383283458590581763681)
        ·
          refine ⟨157008287462593942936322761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209344383283458590581763681 157008287462593942936322761)
          ·
            refine ⟨117756215596945457202242071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157008287462593942936322761 117756215596945457202242071)
            ·
              refine ⟨176634323395418185803363107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117756215596945457202242071 176634323395418185803363107)
              ·
                refine ⟨264951485093127278705044661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176634323395418185803363107 264951485093127278705044661)
                ·
                  refine ⟨24839201727480682378597937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264951485093127278705044661 24839201727480682378597937)
                  ·
                    refine ⟨18629401295610511783948453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24839201727480682378597937 18629401295610511783948453)
                    ·
                      refine ⟨3493012742926970959490335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18629401295610511783948453 3493012742926970959490335)
                      ·
                        rfl

theorem cell23_6802618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_6802618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802618 prefixEnd_6802618 := by exact prefixLift 6802618
  have htrace : WordTrace (prefixWord ++ tailWord_6802618) baseStart_6802618 baseEnd_6802618 := by
    simpa [prefixWord, tailWord_6802618, baseEnd_6802618] using wordTrace_append hprefix tailTrace_6802618
  have hstable : (prefixWord ++ tailWord_6802618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802618).length < 2 ^ (prefixWord ++ tailWord_6802618).sum := by decide
  have hdescent : baseEnd_6802618 < baseStart_6802618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802642 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6802642 : Nat := 118140960795 + 6802642 * 2 ^ 59
def prefixEnd_6802642 : Nat := 4983230072969 + 3 ^ 40 * 6802642 * 2
def baseEnd_6802642 : Nat := 3493025066462678865590225

theorem tailTrace_6802642 : CollatzResearch.WordTrace tailWord_6802642 prefixEnd_6802642 3493025066462678865590225 := by
  unfold tailWord_6802642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62028184255299326900796545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165408491347464871735457453 62028184255299326900796545)
  ·
    refine ⟨46521138191474495175597409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62028184255299326900796545 46521138191474495175597409)
    ·
      refine ⟨34890853643605871381698057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46521138191474495175597409 34890853643605871381698057)
      ·
        refine ⟨26168140232704403536273543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34890853643605871381698057 26168140232704403536273543)
        ·
          refine ⟨39252210349056605304410315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26168140232704403536273543 39252210349056605304410315)
          ·
            refine ⟨58878315523584907956615473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39252210349056605304410315 58878315523584907956615473)
            ·
              refine ⟨44158736642688680967461605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58878315523584907956615473 44158736642688680967461605)
              ·
                refine ⟨8279763120504127681399051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44158736642688680967461605 8279763120504127681399051)
                ·
                  refine ⟨12419644680756191522098577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8279763120504127681399051 12419644680756191522098577)
                  ·
                    refine ⟨9314733510567143641573933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12419644680756191522098577 9314733510567143641573933)
                    ·
                      refine ⟨3493025066462678865590225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314733510567143641573933 3493025066462678865590225)
                      ·
                        rfl

theorem cell23_6802642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6802642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802642 prefixEnd_6802642 := by exact prefixLift 6802642
  have htrace : WordTrace (prefixWord ++ tailWord_6802642) baseStart_6802642 baseEnd_6802642 := by
    simpa [prefixWord, tailWord_6802642, baseEnd_6802642] using wordTrace_append hprefix tailTrace_6802642
  have hstable : (prefixWord ++ tailWord_6802642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802642).length < 2 ^ (prefixWord ++ tailWord_6802642).sum := by decide
  have hdescent : baseEnd_6802642 < baseStart_6802642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802655 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_6802655 : Nat := 118140960795 + 6802655 * 2 ^ 59
def prefixEnd_6802655 : Nat := 4983230072969 + 3 ^ 40 * 6802655 * 2
def baseEnd_6802655 : Nat := 3493031741711187314727665

theorem tailTrace_6802655 : CollatzResearch.WordTrace tailWord_6802655 prefixEnd_6802655 3493031741711187314727665 := by
  unfold tailWord_6802655
  simp only [CollatzResearch.WordTrace]
  refine ⟨248113211170150210823409419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165408807446766807215606279 248113211170150210823409419)
  ·
    refine ⟨372169816755225316235114129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248113211170150210823409419 372169816755225316235114129)
    ·
      refine ⟨279127362566418987176335597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372169816755225316235114129 279127362566418987176335597)
      ·
        refine ⟨104672760962407120191125849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279127362566418987176335597 104672760962407120191125849)
        ·
          refine ⟨78504570721805340143344387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104672760962407120191125849 78504570721805340143344387)
          ·
            refine ⟨117756856082708010215016581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78504570721805340143344387 117756856082708010215016581)
            ·
              refine ⟨22079410515507751915315609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117756856082708010215016581 22079410515507751915315609)
              ·
                refine ⟨16559557886630813936486707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22079410515507751915315609 16559557886630813936486707)
                ·
                  refine ⟨24839336829946220904730061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16559557886630813936486707 24839336829946220904730061)
                  ·
                    refine ⟨9314751311229832839273773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24839336829946220904730061 9314751311229832839273773)
                    ·
                      refine ⟨3493031741711187314727665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314751311229832839273773 3493031741711187314727665)
                      ·
                        rfl

theorem cell23_6802655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_6802655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802655 prefixEnd_6802655 := by exact prefixLift 6802655
  have htrace : WordTrace (prefixWord ++ tailWord_6802655) baseStart_6802655 baseEnd_6802655 := by
    simpa [prefixWord, tailWord_6802655, baseEnd_6802655] using wordTrace_append hprefix tailTrace_6802655
  have hstable : (prefixWord ++ tailWord_6802655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802655).length < 2 ^ (prefixWord ++ tailWord_6802655).sum := by decide
  have hdescent : baseEnd_6802655 < baseStart_6802655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802656 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 1, 2, 2]
def baseStart_6802656 : Nat := 118140960795 + 6802656 * 2 ^ 59
def prefixEnd_6802656 : Nat := 4983230072969 + 3 ^ 40 * 6802656 * 2
def baseEnd_6802656 : Nat := 3493032255191841810815161

theorem tailTrace_6802656 : CollatzResearch.WordTrace tailWord_6802656 prefixEnd_6802656 3493032255191841810815161 := by
  unfold tailWord_6802656
  simp only [CollatzResearch.WordTrace]
  refine ⟨124056623821573293997097911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165408831762097725329463881 124056623821573293997097911)
  ·
    refine ⟨186084935732359940995646867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124056623821573293997097911 186084935732359940995646867)
    ·
      refine ⟨279127403598539911493470301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186084935732359940995646867 279127403598539911493470301)
      ·
        refine ⟨104672776349452466810051363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279127403598539911493470301 104672776349452466810051363)
        ·
          refine ⟨157009164524178700215077045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104672776349452466810051363 157009164524178700215077045)
          ·
            refine ⟨14719609174141753145163473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157009164524178700215077045 14719609174141753145163473)
            ·
              refine ⟨11039706880606314858872605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14719609174141753145163473 11039706880606314858872605)
              ·
                refine ⟨4139890080227368072077227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11039706880606314858872605 4139890080227368072077227)
                ·
                  refine ⟨6209835120341052108115841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139890080227368072077227 6209835120341052108115841)
                  ·
                    refine ⟨4657376340255789081086881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209835120341052108115841 4657376340255789081086881)
                    ·
                      refine ⟨3493032255191841810815161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657376340255789081086881 3493032255191841810815161)
                      ·
                        rfl

theorem cell23_6802656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_6802656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802656 prefixEnd_6802656 := by exact prefixLift 6802656
  have htrace : WordTrace (prefixWord ++ tailWord_6802656) baseStart_6802656 baseEnd_6802656 := by
    simpa [prefixWord, tailWord_6802656, baseEnd_6802656] using wordTrace_append hprefix tailTrace_6802656
  have hstable : (prefixWord ++ tailWord_6802656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802656).length < 2 ^ (prefixWord ++ tailWord_6802656).sum := by decide
  have hdescent : baseEnd_6802656 < baseStart_6802656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802676 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6802676 : Nat := 118140960795 + 6802676 * 2 ^ 59
def prefixEnd_6802676 : Nat := 4983230072969 + 3 ^ 40 * 6802676 * 2
def baseEnd_6802676 : Nat := 3493042524804931732565069

theorem tailTrace_6802676 : CollatzResearch.WordTrace tailWord_6802676 prefixEnd_6802676 3493042524804931732565069 := by
  unfold tailWord_6802676
  simp only [CollatzResearch.WordTrace]
  refine ⟨124056988551537065704961941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165409318068716087606615921 124056988551537065704961941)
  ·
    refine ⟨5815171338353299954920091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124056988551537065704961941 5815171338353299954920091)
    ·
      refine ⟨8722757007529949932380137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815171338353299954920091 8722757007529949932380137)
      ·
        refine ⟨6542067755647462449285103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8722757007529949932380137 6542067755647462449285103)
        ·
          refine ⟨9813101633471193673927655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542067755647462449285103 9813101633471193673927655)
          ·
            refine ⟨14719652450206790510891483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813101633471193673927655 14719652450206790510891483)
            ·
              refine ⟨22079478675310185766337225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14719652450206790510891483 22079478675310185766337225)
              ·
                refine ⟨16559609006482639324752919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22079478675310185766337225 16559609006482639324752919)
                ·
                  refine ⟨24839413509723958987129379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16559609006482639324752919 24839413509723958987129379)
                  ·
                    refine ⟨37259120264585938480694069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24839413509723958987129379 37259120264585938480694069)
                    ·
                      refine ⟨3493042524804931732565069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37259120264585938480694069 3493042524804931732565069)
                      ·
                        rfl

theorem cell23_6802676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6802676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802676 prefixEnd_6802676 := by exact prefixLift 6802676
  have htrace : WordTrace (prefixWord ++ tailWord_6802676) baseStart_6802676 baseEnd_6802676 := by
    simpa [prefixWord, tailWord_6802676, baseEnd_6802676] using wordTrace_append hprefix tailTrace_6802676
  have hstable : (prefixWord ++ tailWord_6802676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802676).length < 2 ^ (prefixWord ++ tailWord_6802676).sum := by decide
  have hdescent : baseEnd_6802676 < baseStart_6802676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802699 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 1, 3, 2]
def baseStart_6802699 : Nat := 118140960795 + 6802699 * 2 ^ 59
def prefixEnd_6802699 : Nat := 4983230072969 + 3 ^ 40 * 6802699 * 2
def baseEnd_6802699 : Nat := 3493054334859985142577463

theorem tailTrace_6802699 : CollatzResearch.WordTrace tailWord_6802699 prefixEnd_6802699 3493054334859985142577463 := by
  unfold tailWord_6802699
  simp only [CollatzResearch.WordTrace]
  refine ⟨248114815981990806338011151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165409877321327204225340767 248114815981990806338011151)
  ·
    refine ⟨372172223972986209507016727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248114815981990806338011151 372172223972986209507016727)
    ·
      refine ⟨558258335959479314260525091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372172223972986209507016727 558258335959479314260525091)
      ·
        refine ⟨837387503939218971390787637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558258335959479314260525091 837387503939218971390787637)
        ·
          refine ⟨78505078494301778567886341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 837387503939218971390787637 78505078494301778567886341)
          ·
            refine ⟨14719702217681583481478689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78505078494301778567886341 14719702217681583481478689)
            ·
              refine ⟨11039776663261187611109017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14719702217681583481478689 11039776663261187611109017)
              ·
                refine ⟨8279832497445890708331763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11039776663261187611109017 8279832497445890708331763)
                ·
                  refine ⟨12419748746168836062497645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8279832497445890708331763 12419748746168836062497645)
                  ·
                    refine ⟨4657405779813313523436617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12419748746168836062497645 4657405779813313523436617)
                    ·
                      refine ⟨3493054334859985142577463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657405779813313523436617 3493054334859985142577463)
                      ·
                        rfl

theorem cell23_6802699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3, 2].length) (baseStart_6802699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802699 prefixEnd_6802699 := by exact prefixLift 6802699
  have htrace : WordTrace (prefixWord ++ tailWord_6802699) baseStart_6802699 baseEnd_6802699 := by
    simpa [prefixWord, tailWord_6802699, baseEnd_6802699] using wordTrace_append hprefix tailTrace_6802699
  have hstable : (prefixWord ++ tailWord_6802699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802699).length < 2 ^ (prefixWord ++ tailWord_6802699).sum := by decide
  have hdescent : baseEnd_6802699 < baseStart_6802699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802775 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_6802775 : Nat := 118140960795 + 6802775 * 2 ^ 59
def prefixEnd_6802775 : Nat := 4983230072969 + 3 ^ 40 * 6802775 * 2
def baseEnd_6802775 : Nat := 3493093359389726845227113

theorem tailTrace_6802775 : CollatzResearch.WordTrace tailWord_6802775 prefixEnd_6802775 3493093359389726845227113 := by
  unfold tailWord_6802775
  simp only [CollatzResearch.WordTrace]
  refine ⟨248117587929715471317777779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165411725286476980878518519 248117587929715471317777779)
  ·
    refine ⟨372176381894573206976666669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248117587929715471317777779 372176381894573206976666669)
    ·
      refine ⟨139566143210464952616250001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372176381894573206976666669 139566143210464952616250001)
      ·
        refine ⟨104674607407848714462187501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139566143210464952616250001 104674607407848714462187501)
        ·
          refine ⟨39252977777943267923320313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104674607407848714462187501 39252977777943267923320313)
          ·
            refine ⟨29439733333457450942490235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39252977777943267923320313 29439733333457450942490235)
            ·
              refine ⟨44159600000186176413735353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29439733333457450942490235 44159600000186176413735353)
              ·
                refine ⟨33119700000139632310301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44159600000186176413735353 33119700000139632310301515)
                ·
                  refine ⟨49679550000209448465452273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33119700000139632310301515 49679550000209448465452273)
                  ·
                    refine ⟨37259662500157086349089205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49679550000209448465452273 37259662500157086349089205)
                    ·
                      refine ⟨3493093359389726845227113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37259662500157086349089205 3493093359389726845227113)
                      ·
                        rfl

theorem cell23_6802775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_6802775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802775 prefixEnd_6802775 := by exact prefixLift 6802775
  have htrace : WordTrace (prefixWord ++ tailWord_6802775) baseStart_6802775 baseEnd_6802775 := by
    simpa [prefixWord, tailWord_6802775, baseEnd_6802775] using wordTrace_append hprefix tailTrace_6802775
  have hstable : (prefixWord ++ tailWord_6802775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802775).length < 2 ^ (prefixWord ++ tailWord_6802775).sum := by decide
  have hdescent : baseEnd_6802775 < baseStart_6802775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802812 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_6802812 : Nat := 118140960795 + 6802812 * 2 ^ 59
def prefixEnd_6802812 : Nat := 4983230072969 + 3 ^ 40 * 6802812 * 2
def baseEnd_6802812 : Nat := 1164370786057981066821481

theorem tailTrace_6802812 : CollatzResearch.WordTrace tailWord_6802812 prefixEnd_6802812 1164370786057981066821481 := by
  unfold tailWord_6802812
  simp only [CollatzResearch.WordTrace]
  refine ⟨124059468715290713318437345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165412624953720951091249793 124059468715290713318437345)
  ·
    refine ⟨93044601536468034988828009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124059468715290713318437345 93044601536468034988828009)
    ·
      refine ⟨69783451152351026241621007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93044601536468034988828009 69783451152351026241621007)
      ·
        refine ⟨104675176728526539362431511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69783451152351026241621007 104675176728526539362431511)
        ·
          refine ⟨157012765092789809043647267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104675176728526539362431511 157012765092789809043647267)
          ·
            refine ⟨235519147639184713565470901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157012765092789809043647267 235519147639184713565470901)
            ·
              refine ⟨22079920091173566896762897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235519147639184713565470901 22079920091173566896762897)
              ·
                refine ⟨16559940068380175172572173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22079920091173566896762897 16559940068380175172572173)
                ·
                  refine ⟨6209977525642565689714565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16559940068380175172572173 6209977525642565689714565)
                  ·
                    refine ⟨1164370786057981066821481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6209977525642565689714565 1164370786057981066821481)
                    ·
                      rfl

theorem cell23_6802812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_6802812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802812 prefixEnd_6802812 := by exact prefixLift 6802812
  have htrace : WordTrace (prefixWord ++ tailWord_6802812) baseStart_6802812 baseEnd_6802812 := by
    simpa [prefixWord, tailWord_6802812, baseEnd_6802812] using wordTrace_append hprefix tailTrace_6802812
  have hstable : (prefixWord ++ tailWord_6802812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802812).length < 2 ^ (prefixWord ++ tailWord_6802812).sum := by decide
  have hdescent : baseEnd_6802812 < baseStart_6802812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802819 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 4]
def baseStart_6802819 : Nat := 118140960795 + 6802819 * 2 ^ 59
def prefixEnd_6802819 : Nat := 4983230072969 + 3 ^ 40 * 6802819 * 2
def baseEnd_6802819 : Nat := 3493115952538524673076911

theorem tailTrace_6802819 : CollatzResearch.WordTrace tailWord_6802819 prefixEnd_6802819 3493115952538524673076911 := by
  unfold tailWord_6802819
  simp only [CollatzResearch.WordTrace]
  refine ⟨248119192741556066832379511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165412795161037377888253007 248119192741556066832379511)
  ·
    refine ⟨372178789112334100248569267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248119192741556066832379511 372178789112334100248569267)
    ·
      refine ⟨558268183668501150372853901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372178789112334100248569267 558268183668501150372853901)
      ·
        refine ⟨209350568875687931389820213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558268183668501150372853901 209350568875687931389820213)
        ·
          refine ⟨19626615832095743567795645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209350568875687931389820213 19626615832095743567795645)
          ·
            refine ⟨7359980937035903837923367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19626615832095743567795645 7359980937035903837923367)
            ·
              refine ⟨11039971405553855756885051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359980937035903837923367 11039971405553855756885051)
              ·
                refine ⟨16559957108330783635327577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11039971405553855756885051 16559957108330783635327577)
                ·
                  refine ⟨12419967831248087726495683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16559957108330783635327577 12419967831248087726495683)
                  ·
                    refine ⟨18629951746872131589743525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12419967831248087726495683 18629951746872131589743525)
                    ·
                      refine ⟨3493115952538524673076911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18629951746872131589743525 3493115952538524673076911)
                      ·
                        rfl

theorem cell23_6802819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_6802819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802819 prefixEnd_6802819 := by exact prefixLift 6802819
  have htrace : WordTrace (prefixWord ++ tailWord_6802819) baseStart_6802819 baseEnd_6802819 := by
    simpa [prefixWord, tailWord_6802819, baseEnd_6802819] using wordTrace_append hprefix tailTrace_6802819
  have hstable : (prefixWord ++ tailWord_6802819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802819).length < 2 ^ (prefixWord ++ tailWord_6802819).sum := by decide
  have hdescent : baseEnd_6802819 < baseStart_6802819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802835 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3]
def baseStart_6802835 : Nat := 118140960795 + 6802835 * 2 ^ 59
def prefixEnd_6802835 : Nat := 4983230072969 + 3 ^ 40 * 6802835 * 2
def baseEnd_6802835 : Nat := 3493124168228996610476837

theorem tailTrace_6802835 : CollatzResearch.WordTrace tailWord_6802835 prefixEnd_6802835 3493124168228996610476837 := by
  unfold tailWord_6802835
  simp only [CollatzResearch.WordTrace]
  refine ⟨248119776309498101564961959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165413184206332067709974639 248119776309498101564961959)
  ·
    refine ⟨372179664464247152347442939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248119776309498101564961959 372179664464247152347442939)
    ·
      refine ⟨558269496696370728521164409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372179664464247152347442939 558269496696370728521164409)
      ·
        refine ⟨418702122522278046390873307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558269496696370728521164409 418702122522278046390873307)
        ·
          refine ⟨628053183783417069586309961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418702122522278046390873307 628053183783417069586309961)
          ·
            refine ⟨471039887837562802189732471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628053183783417069586309961 471039887837562802189732471)
            ·
              refine ⟨706559831756344203284598707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471039887837562802189732471 706559831756344203284598707)
              ·
                refine ⟨1059839747634516304926898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706559831756344203284598707 1059839747634516304926898061)
                ·
                  refine ⟨397439905362943614347586773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059839747634516304926898061 397439905362943614347586773)
                  ·
                    refine ⟨9314997781943990961271565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 397439905362943614347586773 9314997781943990961271565)
                    ·
                      refine ⟨3493124168228996610476837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9314997781943990961271565 3493124168228996610476837)
                      ·
                        rfl

theorem cell23_6802835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_6802835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802835 prefixEnd_6802835 := by exact prefixLift 6802835
  have htrace : WordTrace (prefixWord ++ tailWord_6802835) baseStart_6802835 baseEnd_6802835 := by
    simpa [prefixWord, tailWord_6802835, baseEnd_6802835] using wordTrace_append hprefix tailTrace_6802835
  have hstable : (prefixWord ++ tailWord_6802835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802835).length < 2 ^ (prefixWord ++ tailWord_6802835).sum := by decide
  have hdescent : baseEnd_6802835 < baseStart_6802835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802872 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_6802872 : Nat := 118140960795 + 6802872 * 2 ^ 59
def prefixEnd_6802872 : Nat := 4983230072969 + 3 ^ 40 * 6802872 * 2
def baseEnd_6802872 : Nat := 1164381055671070988571389

theorem tailTrace_6802872 : CollatzResearch.WordTrace tailWord_6802872 prefixEnd_6802872 1164381055671070988571389 := by
  unfold tailWord_6802872
  simp only [CollatzResearch.WordTrace]
  refine ⟨124060562905182028442029435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165414083873576037922705913 124060562905182028442029435)
  ·
    refine ⟨186090844357773042663044153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124060562905182028442029435 186090844357773042663044153)
    ·
      refine ⟨139568133268329781997283115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186090844357773042663044153 139568133268329781997283115)
      ·
        refine ⟨209352199902494672995924673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139568133268329781997283115 209352199902494672995924673)
        ·
          refine ⟨157014149926871004746943505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209352199902494672995924673 157014149926871004746943505)
          ·
            refine ⟨117760612445153253560207629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157014149926871004746943505 117760612445153253560207629)
            ·
              refine ⟨44160229666932470085077861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117760612445153253560207629 44160229666932470085077861)
              ·
                refine ⟨8280043062549838140952099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44160229666932470085077861 8280043062549838140952099)
                ·
                  refine ⟨12420064593824757211428149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8280043062549838140952099 12420064593824757211428149)
                  ·
                    refine ⟨1164381055671070988571389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12420064593824757211428149 1164381055671070988571389)
                    ·
                      rfl

theorem cell23_6802872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_6802872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802872 prefixEnd_6802872 := by exact prefixLift 6802872
  have htrace : WordTrace (prefixWord ++ tailWord_6802872) baseStart_6802872 baseEnd_6802872 := by
    simpa [prefixWord, tailWord_6802872, baseEnd_6802872] using wordTrace_append hprefix tailTrace_6802872
  have hstable : (prefixWord ++ tailWord_6802872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802872).length < 2 ^ (prefixWord ++ tailWord_6802872).sum := by decide
  have hdescent : baseEnd_6802872 < baseStart_6802872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802926 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_6802926 : Nat := 118140960795 + 6802926 * 2 ^ 59
def prefixEnd_6802926 : Nat := 4983230072969 + 3 ^ 40 * 6802926 * 2
def baseEnd_6802926 : Nat := 3493170894968555754438919

theorem tailTrace_6802926 : CollatzResearch.WordTrace tailWord_6802926 prefixEnd_6802926 3493170894968555754438919 := by
  unfold tailWord_6802926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015386919021053013315579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165415396901445616071016421 31015386919021053013315579)
  ·
    refine ⟨46523080378531579519973369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31015386919021053013315579 46523080378531579519973369)
    ·
      refine ⟨34892310283898684639980027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46523080378531579519973369 34892310283898684639980027)
      ·
        refine ⟨52338465425848026959970041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34892310283898684639980027 52338465425848026959970041)
        ·
          refine ⟨39253849069386020219977531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52338465425848026959970041 39253849069386020219977531)
          ·
            refine ⟨58880773604079030329966297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39253849069386020219977531 58880773604079030329966297)
            ·
              refine ⟨44160580203059272747474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58880773604079030329966297 44160580203059272747474723)
              ·
                refine ⟨66240870304588909121212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44160580203059272747474723 66240870304588909121212085)
                ·
                  refine ⟨6210081591055210230113633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66240870304588909121212085 6210081591055210230113633)
                  ·
                    refine ⟨4657561193291407672585225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210081591055210230113633 4657561193291407672585225)
                    ·
                      refine ⟨3493170894968555754438919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657561193291407672585225 3493170894968555754438919)
                      ·
                        rfl

theorem cell23_6802926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_6802926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802926 prefixEnd_6802926 := by exact prefixLift 6802926
  have htrace : WordTrace (prefixWord ++ tailWord_6802926) baseStart_6802926 baseEnd_6802926 := by
    simpa [prefixWord, tailWord_6802926, baseEnd_6802926] using wordTrace_append hprefix tailTrace_6802926
  have hstable : (prefixWord ++ tailWord_6802926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802926).length < 2 ^ (prefixWord ++ tailWord_6802926).sum := by decide
  have hdescent : baseEnd_6802926 < baseStart_6802926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802929 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_6802929 : Nat := 118140960795 + 6802929 * 2 ^ 59
def prefixEnd_6802929 : Nat := 4983230072969 + 3 ^ 40 * 6802929 * 2
def baseEnd_6802929 : Nat := 3493172435410519242701405

theorem tailTrace_6802929 : CollatzResearch.WordTrace tailWord_6802929 prefixEnd_6802929 3493172435410519242701405 := by
  unfold tailWord_6802929
  simp only [CollatzResearch.WordTrace]
  refine ⟨248123204771157555618883841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165415469847438370412589227 248123204771157555618883841)
  ·
    refine ⟨186092403578368166714162881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248123204771157555618883841 186092403578368166714162881)
    ·
      refine ⟨139569302683776125035622161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186092403578368166714162881 139569302683776125035622161)
      ·
        refine ⟨104676977012832093776716621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139569302683776125035622161 104676977012832093776716621)
        ·
          refine ⟨39253866379812035166268733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104676977012832093776716621 39253866379812035166268733)
          ·
            refine ⟨14720199892429513187350775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39253866379812035166268733 14720199892429513187350775)
            ·
              refine ⟨22080299838644269781026163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720199892429513187350775 22080299838644269781026163)
              ·
                refine ⟨33120449757966404671539245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22080299838644269781026163 33120449757966404671539245)
                ·
                  refine ⟨12420168659237401751827217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33120449757966404671539245 12420168659237401751827217)
                  ·
                    refine ⟨9315126494428051313870413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12420168659237401751827217 9315126494428051313870413)
                    ·
                      refine ⟨3493172435410519242701405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9315126494428051313870413 3493172435410519242701405)
                      ·
                        rfl

theorem cell23_6802929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_6802929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802929 prefixEnd_6802929 := by exact prefixLift 6802929
  have htrace : WordTrace (prefixWord ++ tailWord_6802929) baseStart_6802929 baseEnd_6802929 := by
    simpa [prefixWord, tailWord_6802929, baseEnd_6802929] using wordTrace_append hprefix tailTrace_6802929
  have hstable : (prefixWord ++ tailWord_6802929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802929).length < 2 ^ (prefixWord ++ tailWord_6802929).sum := by decide
  have hdescent : baseEnd_6802929 < baseStart_6802929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802946 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6802946 : Nat := 118140960795 + 6802946 * 2 ^ 59
def prefixEnd_6802946 : Nat := 4983230072969 + 3 ^ 40 * 6802946 * 2
def baseEnd_6802946 : Nat := 3493181164581645676188827

theorem tailTrace_6802946 : CollatzResearch.WordTrace tailWord_6802946 prefixEnd_6802946 3493181164581645676188827 := by
  unfold tailWord_6802946
  simp only [CollatzResearch.WordTrace]
  refine ⟨62030956203023991880563173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165415883208063978348168461 62030956203023991880563173)
  ·
    refine ⟨11630804288066998477605595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62030956203023991880563173 11630804288066998477605595)
    ·
      refine ⟨17446206432100497716408393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630804288066998477605595 17446206432100497716408393)
      ·
        refine ⟨13084654824075373287306295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17446206432100497716408393 13084654824075373287306295)
        ·
          refine ⟨19626982236113059930959443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084654824075373287306295 19626982236113059930959443)
          ·
            refine ⟨29440473354169589896439165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19626982236113059930959443 29440473354169589896439165)
            ·
              refine ⟨11040177507813596211164687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29440473354169589896439165 11040177507813596211164687)
              ·
                refine ⟨16560266261720394316747031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040177507813596211164687 16560266261720394316747031)
                ·
                  refine ⟨24840399392580591475120547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16560266261720394316747031 24840399392580591475120547)
                  ·
                    refine ⟨37260599088870887212680821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24840399392580591475120547 37260599088870887212680821)
                    ·
                      refine ⟨3493181164581645676188827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37260599088870887212680821 3493181164581645676188827)
                      ·
                        rfl

theorem cell23_6802946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6802946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802946 prefixEnd_6802946 := by exact prefixLift 6802946
  have htrace : WordTrace (prefixWord ++ tailWord_6802946) baseStart_6802946 baseEnd_6802946 := by
    simpa [prefixWord, tailWord_6802946, baseEnd_6802946] using wordTrace_append hprefix tailTrace_6802946
  have hstable : (prefixWord ++ tailWord_6802946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802946).length < 2 ^ (prefixWord ++ tailWord_6802946).sum := by decide
  have hdescent : baseEnd_6802946 < baseStart_6802946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802976 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6802976 : Nat := 118140960795 + 6802976 * 2 ^ 59
def prefixEnd_6802976 : Nat := 4983230072969 + 3 ^ 40 * 6802976 * 2
def baseEnd_6802976 : Nat := 3493196569001280558813689

theorem tailTrace_6802976 : CollatzResearch.WordTrace tailWord_6802976 prefixEnd_6802976 3493196569001280558813689 := by
  unfold tailWord_6802976
  simp only [CollatzResearch.WordTrace]
  refine ⟨124062459500993641322922391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165416612667991521763896521 124062459500993641322922391)
  ·
    refine ⟨186093689251490461984383587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124062459500993641322922391 186093689251490461984383587)
    ·
      refine ⟨279140533877235692976575381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186093689251490461984383587 279140533877235692976575381)
      ·
        refine ⟨13084712525495423108276971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279140533877235692976575381 13084712525495423108276971)
        ·
          refine ⟨19627068788243134662415457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084712525495423108276971 19627068788243134662415457)
          ·
            refine ⟨14720301591182350996811593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19627068788243134662415457 14720301591182350996811593)
            ·
              refine ⟨11040226193386763247608695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720301591182350996811593 11040226193386763247608695)
              ·
                refine ⟨16560339290080144871413043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040226193386763247608695 16560339290080144871413043)
                ·
                  refine ⟨24840508935120217307119565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16560339290080144871413043 24840508935120217307119565)
                  ·
                    refine ⟨9315190850670081490169837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24840508935120217307119565 9315190850670081490169837)
                    ·
                      refine ⟨3493196569001280558813689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9315190850670081490169837 3493196569001280558813689)
                      ·
                        rfl

theorem cell23_6802976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6802976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802976 prefixEnd_6802976 := by exact prefixLift 6802976
  have htrace : WordTrace (prefixWord ++ tailWord_6802976) baseStart_6802976 baseEnd_6802976 := by
    simpa [prefixWord, tailWord_6802976, baseEnd_6802976] using wordTrace_append hprefix tailTrace_6802976
  have hstable : (prefixWord ++ tailWord_6802976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802976).length < 2 ^ (prefixWord ++ tailWord_6802976).sum := by decide
  have hdescent : baseEnd_6802976 < baseStart_6802976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6802986 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6802986 : Nat := 118140960795 + 6802986 * 2 ^ 59
def prefixEnd_6802986 : Nat := 4983230072969 + 3 ^ 40 * 6802986 * 2
def baseEnd_6802986 : Nat := 3493201703807825519688643

theorem tailTrace_6802986 : CollatzResearch.WordTrace tailWord_6802986 prefixEnd_6802986 3493201703807825519688643 := by
  unfold tailWord_6802986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62031320932987763588427203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165416855821300702902472541 62031320932987763588427203)
  ·
    refine ⟨93046981399481645382640805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62031320932987763588427203 93046981399481645382640805)
    ·
      refine ⟨17446309012402808509245151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93046981399481645382640805 17446309012402808509245151)
      ·
        refine ⟨26169463518604212763867727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17446309012402808509245151 26169463518604212763867727)
        ·
          refine ⟨39254195277906319145801591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26169463518604212763867727 39254195277906319145801591)
          ·
            refine ⟨58881292916859478718702387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39254195277906319145801591 58881292916859478718702387)
            ·
              refine ⟨88321939375289218078053581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58881292916859478718702387 88321939375289218078053581)
              ·
                refine ⟨33120727265733456779270093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88321939375289218078053581 33120727265733456779270093)
                ·
                  refine ⟨12420272724650046292226285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33120727265733456779270093 12420272724650046292226285)
                  ·
                    refine ⟨4657602271743767359584857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12420272724650046292226285 4657602271743767359584857)
                    ·
                      refine ⟨3493201703807825519688643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657602271743767359584857 3493201703807825519688643)
                      ·
                        rfl

theorem cell23_6802986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6802986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6802986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6802986 prefixEnd_6802986 := by exact prefixLift 6802986
  have htrace : WordTrace (prefixWord ++ tailWord_6802986) baseStart_6802986 baseEnd_6802986 := by
    simpa [prefixWord, tailWord_6802986, baseEnd_6802986] using wordTrace_append hprefix tailTrace_6802986
  have hstable : (prefixWord ++ tailWord_6802986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6802986).length < 2 ^ (prefixWord ++ tailWord_6802986).sum := by decide
  have hdescent : baseEnd_6802986 < baseStart_6802986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6802986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803002 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_6803002 : Nat := 118140960795 + 6803002 * 2 ^ 59
def prefixEnd_6803002 : Nat := 4983230072969 + 3 ^ 40 * 6803002 * 2
def baseEnd_6803002 : Nat := 3493209919498297457088569

theorem tailTrace_6803002 : CollatzResearch.WordTrace tailWord_6803002 prefixEnd_6803002 3493209919498297457088569 := by
  unfold tailWord_6803002
  simp only [CollatzResearch.WordTrace]
  refine ⟨62031466824973272271572815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165417244866595392724194173 62031466824973272271572815)
  ·
    refine ⟨93047200237459908407359223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62031466824973272271572815 93047200237459908407359223)
    ·
      refine ⟨139570800356189862611038835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93047200237459908407359223 139570800356189862611038835)
      ·
        refine ⟨209356200534284793916558253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139570800356189862611038835 209356200534284793916558253)
        ·
          refine ⟨78508575200356797718709345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209356200534284793916558253 78508575200356797718709345)
          ·
            refine ⟨58881431400267598289032009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78508575200356797718709345 58881431400267598289032009)
            ·
              refine ⟨44161073550200698716774007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58881431400267598289032009 44161073550200698716774007)
              ·
                refine ⟨66241610325301048075161011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44161073550200698716774007 66241610325301048075161011)
                ·
                  refine ⟨99362415487951572112741517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66241610325301048075161011 99362415487951572112741517)
                  ·
                    refine ⟨37260905807981839542278069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99362415487951572112741517 37260905807981839542278069)
                    ·
                      refine ⟨3493209919498297457088569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37260905807981839542278069 3493209919498297457088569)
                      ·
                        rfl

theorem cell23_6803002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_6803002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803002 prefixEnd_6803002 := by exact prefixLift 6803002
  have htrace : WordTrace (prefixWord ++ tailWord_6803002) baseStart_6803002 baseEnd_6803002 := by
    simpa [prefixWord, tailWord_6803002, baseEnd_6803002] using wordTrace_append hprefix tailTrace_6803002
  have hstable : (prefixWord ++ tailWord_6803002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803002).length < 2 ^ (prefixWord ++ tailWord_6803002).sum := by decide
  have hdescent : baseEnd_6803002 < baseStart_6803002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803037 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6803037 : Nat := 118140960795 + 6803037 * 2 ^ 59
def prefixEnd_6803037 : Nat := 4983230072969 + 3 ^ 40 * 6803037 * 2
def baseEnd_6803037 : Nat := 3493227891321204820150909

theorem tailTrace_6803037 : CollatzResearch.WordTrace tailWord_6803037 prefixEnd_6803037 3493227891321204820150909 := by
  unfold tailWord_6803037
  simp only [CollatzResearch.WordTrace]
  refine ⟨248127143854766290063815365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165418095903177526709210243 248127143854766290063815365)
  ·
    refine ⟨46523839472768679386965381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248127143854766290063815365 46523839472768679386965381)
    ·
      refine ⟨8723219901144127385056009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46523839472768679386965381 8723219901144127385056009)
      ·
        refine ⟨6542414925858095538792007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8723219901144127385056009 6542414925858095538792007)
        ·
          refine ⟨9813622388787143308188011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542414925858095538792007 9813622388787143308188011)
          ·
            refine ⟨14720433583180714962282017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813622388787143308188011 14720433583180714962282017)
            ·
              refine ⟨11040325187385536221711513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720433583180714962282017 11040325187385536221711513)
              ·
                refine ⟨8280243890539152166283635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040325187385536221711513 8280243890539152166283635)
                ·
                  refine ⟨12420365835808728249425453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8280243890539152166283635 12420365835808728249425453)
                  ·
                    refine ⟨4657637188428273093534545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12420365835808728249425453 4657637188428273093534545)
                    ·
                      refine ⟨3493227891321204820150909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657637188428273093534545 3493227891321204820150909)
                      ·
                        rfl

theorem cell23_6803037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6803037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803037 prefixEnd_6803037 := by exact prefixLift 6803037
  have htrace : WordTrace (prefixWord ++ tailWord_6803037) baseStart_6803037 baseEnd_6803037 := by
    simpa [prefixWord, tailWord_6803037, baseEnd_6803037] using wordTrace_append hprefix tailTrace_6803037
  have hstable : (prefixWord ++ tailWord_6803037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803037).length < 2 ^ (prefixWord ++ tailWord_6803037).sum := by decide
  have hdescent : baseEnd_6803037 < baseStart_6803037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803056 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 5]
def baseStart_6803056 : Nat := 118140960795 + 6803056 * 2 ^ 59
def prefixEnd_6803056 : Nat := 4983230072969 + 3 ^ 40 * 6803056 * 2
def baseEnd_6803056 : Nat := 388137516383737805090369

theorem tailTrace_6803056 : CollatzResearch.WordTrace tailWord_6803056 prefixEnd_6803056 388137516383737805090369 := by
  unfold tailWord_6803056
  simp only [CollatzResearch.WordTrace]
  refine ⟨124063918420848728154378511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165418557894464970872504681 124063918420848728154378511)
  ·
    refine ⟨186095877631273092231567767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124063918420848728154378511 186095877631273092231567767)
    ·
      refine ⟨279143816446909638347351651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186095877631273092231567767 279143816446909638347351651)
      ·
        refine ⟨418715724670364457521027477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279143816446909638347351651 418715724670364457521027477)
        ·
          refine ⟨19627299593923333946298163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 418715724670364457521027477 19627299593923333946298163)
          ·
            refine ⟨29440949390885000919447245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19627299593923333946298163 29440949390885000919447245)
            ·
              refine ⟨11040356021581875344792717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29440949390885000919447245 11040356021581875344792717)
              ·
                refine ⟨4140133508093203254297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11040356021581875344792717 4140133508093203254297269)
                ·
                  refine ⟨388137516383737805090369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140133508093203254297269 388137516383737805090369)
                  ·
                    rfl

theorem cell23_6803056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 5].length) (baseStart_6803056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803056 prefixEnd_6803056 := by exact prefixLift 6803056
  have htrace : WordTrace (prefixWord ++ tailWord_6803056) baseStart_6803056 baseEnd_6803056 := by
    simpa [prefixWord, tailWord_6803056, baseEnd_6803056] using wordTrace_append hprefix tailTrace_6803056
  have hstable : (prefixWord ++ tailWord_6803056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803056).length < 2 ^ (prefixWord ++ tailWord_6803056).sum := by decide
  have hdescent : baseEnd_6803056 < baseStart_6803056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803069 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_6803069 : Nat := 118140960795 + 6803069 * 2 ^ 59
def prefixEnd_6803069 : Nat := 4983230072969 + 3 ^ 40 * 6803069 * 2
def baseEnd_6803069 : Nat := 1164414774234049564983587

theorem tailTrace_6803069 : CollatzResearch.WordTrace tailWord_6803069 prefixEnd_6803069 1164414774234049564983587 := by
  unfold tailWord_6803069
  simp only [CollatzResearch.WordTrace]
  refine ⟨248128310990650359528980261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165418873993766906352653507 248128310990650359528980261)
  ·
    refine ⟨46524058310746942411683799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248128310990650359528980261 46524058310746942411683799)
    ·
      refine ⟨69786087466120413617525699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46524058310746942411683799 69786087466120413617525699)
      ·
        refine ⟨104679131199180620426288549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69786087466120413617525699 104679131199180620426288549)
        ·
          refine ⟨19627337099846366329929103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104679131199180620426288549 19627337099846366329929103)
          ·
            refine ⟨29441005649769549494893655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19627337099846366329929103 29441005649769549494893655)
            ·
              refine ⟨44161508474654324242340483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29441005649769549494893655 44161508474654324242340483)
              ·
                refine ⟨66242262711981486363510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44161508474654324242340483 66242262711981486363510725)
                ·
                  refine ⟨12420424258496528693158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66242262711981486363510725 12420424258496528693158261)
                  ·
                    refine ⟨1164414774234049564983587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12420424258496528693158261 1164414774234049564983587)
                    ·
                      rfl

theorem cell23_6803069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_6803069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803069 prefixEnd_6803069 := by exact prefixLift 6803069
  have htrace : WordTrace (prefixWord ++ tailWord_6803069) baseStart_6803069 baseEnd_6803069 := by
    simpa [prefixWord, tailWord_6803069, baseEnd_6803069] using wordTrace_append hprefix tailTrace_6803069
  have hstable : (prefixWord ++ tailWord_6803069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803069).length < 2 ^ (prefixWord ++ tailWord_6803069).sum := by decide
  have hdescent : baseEnd_6803069 < baseStart_6803069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803073 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 5]
def baseStart_6803073 : Nat := 118140960795 + 6803073 * 2 ^ 59
def prefixEnd_6803073 : Nat := 4983230072969 + 3 ^ 40 * 6803073 * 2
def baseEnd_6803073 : Nat := 388138486291640742144527

theorem tailTrace_6803073 : CollatzResearch.WordTrace tailWord_6803073 prefixEnd_6803073 388138486291640742144527 := by
  unfold tailWord_6803073
  simp only [CollatzResearch.WordTrace]
  refine ⟨248128456882635868212125873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165418971255090578808083915 248128456882635868212125873)
  ·
    refine ⟨186096342661976901159094405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248128456882635868212125873 186096342661976901159094405)
    ·
      refine ⟨34893064249120668967330201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186096342661976901159094405 34893064249120668967330201)
      ·
        refine ⟨26169798186840501725497651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34893064249120668967330201 26169798186840501725497651)
        ·
          refine ⟨39254697280260752588246477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26169798186840501725497651 39254697280260752588246477)
          ·
            refine ⟨14720511480097782220592429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39254697280260752588246477 14720511480097782220592429)
            ·
              refine ⟨5520191805036668332722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14720511480097782220592429 5520191805036668332722161)
              ·
                refine ⟨4140143853777501249541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520191805036668332722161 4140143853777501249541621)
                ·
                  refine ⟨388138486291640742144527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140143853777501249541621 388138486291640742144527)
                  ·
                    rfl

theorem cell23_6803073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 5].length) (baseStart_6803073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803073 prefixEnd_6803073 := by exact prefixLift 6803073
  have htrace : WordTrace (prefixWord ++ tailWord_6803073) baseStart_6803073 baseEnd_6803073 := by
    simpa [prefixWord, tailWord_6803073, baseEnd_6803073] using wordTrace_append hprefix tailTrace_6803073
  have hstable : (prefixWord ++ tailWord_6803073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803073).length < 2 ^ (prefixWord ++ tailWord_6803073).sum := by decide
  have hdescent : baseEnd_6803073 < baseStart_6803073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803079 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_6803079 : Nat := 118140960795 + 6803079 * 2 ^ 59
def prefixEnd_6803079 : Nat := 4983230072969 + 3 ^ 40 * 6803079 * 2
def baseEnd_6803079 : Nat := 3493249457508693655825715

theorem tailTrace_6803079 : CollatzResearch.WordTrace tailWord_6803079 prefixEnd_6803079 3493249457508693655825715 := by
  unfold tailWord_6803079
  simp only [CollatzResearch.WordTrace]
  refine ⟨248128675720614131236844291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165419117147076087491229527 248128675720614131236844291)
  ·
    refine ⟨372193013580921196855266437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248128675720614131236844291 372193013580921196855266437)
    ·
      refine ⟨69786190046422724410362457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372193013580921196855266437 69786190046422724410362457)
      ·
        refine ⟨52339642534817043307771843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69786190046422724410362457 52339642534817043307771843)
        ·
          refine ⟨78509463802225564961657765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52339642534817043307771843 78509463802225564961657765)
          ·
            refine ⟨14720524462917293430310831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78509463802225564961657765 14720524462917293430310831)
            ·
              refine ⟨22080786694375940145466247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720524462917293430310831 22080786694375940145466247)
              ·
                refine ⟨33121180041563910218199371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22080786694375940145466247 33121180041563910218199371)
                ·
                  refine ⟨49681770062345865327299057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33121180041563910218199371 49681770062345865327299057)
                  ·
                    refine ⟨37261327546759398995474293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49681770062345865327299057 37261327546759398995474293)
                    ·
                      refine ⟨3493249457508693655825715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37261327546759398995474293 3493249457508693655825715)
                      ·
                        rfl

theorem cell23_6803079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_6803079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803079 prefixEnd_6803079 := by exact prefixLift 6803079
  have htrace : WordTrace (prefixWord ++ tailWord_6803079) baseStart_6803079 baseEnd_6803079 := by
    simpa [prefixWord, tailWord_6803079, baseEnd_6803079] using wordTrace_append hprefix tailTrace_6803079
  have hstable : (prefixWord ++ tailWord_6803079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803079).length < 2 ^ (prefixWord ++ tailWord_6803079).sum := by decide
  have hdescent : baseEnd_6803079 < baseStart_6803079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803103 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 2, 5]
def baseStart_6803103 : Nat := 118140960795 + 6803103 * 2 ^ 59
def prefixEnd_6803103 : Nat := 4983230072969 + 3 ^ 40 * 6803103 * 2
def baseEnd_6803103 : Nat := 1164420593681467187308535

theorem tailTrace_6803103 : CollatzResearch.WordTrace tailWord_6803103 prefixEnd_6803103 1164420593681467187308535 := by
  unfold tailWord_6803103
  simp only [CollatzResearch.WordTrace]
  refine ⟨248129551072527183335717963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165419700715018122223811975 248129551072527183335717963)
  ·
    refine ⟨372194326608790775003576945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248129551072527183335717963 372194326608790775003576945)
    ·
      refine ⟨279145744956593081252682709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372194326608790775003576945 279145744956593081252682709)
      ·
        refine ⟨6542478397420150341859751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 279145744956593081252682709 6542478397420150341859751)
        ·
          refine ⟨9813717596130225512789627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542478397420150341859751 9813717596130225512789627)
          ·
            refine ⟨14720576394195338269184441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813717596130225512789627 14720576394195338269184441)
            ·
              refine ⟨11040432295646503701888331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720576394195338269184441 11040432295646503701888331)
              ·
                refine ⟨16560648443469755552832497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040432295646503701888331 16560648443469755552832497)
                ·
                  refine ⟨12420486332602316664624373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16560648443469755552832497 12420486332602316664624373)
                  ·
                    refine ⟨1164420593681467187308535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12420486332602316664624373 1164420593681467187308535)
                    ·
                      rfl

theorem cell23_6803103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_6803103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803103 prefixEnd_6803103 := by exact prefixLift 6803103
  have htrace : WordTrace (prefixWord ++ tailWord_6803103) baseStart_6803103 baseEnd_6803103 := by
    simpa [prefixWord, tailWord_6803103, baseEnd_6803103] using wordTrace_append hprefix tailTrace_6803103
  have hstable : (prefixWord ++ tailWord_6803103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803103).length < 2 ^ (prefixWord ++ tailWord_6803103).sum := by decide
  have hdescent : baseEnd_6803103 < baseStart_6803103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803109 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_6803109 : Nat := 118140960795 + 6803109 * 2 ^ 59
def prefixEnd_6803109 : Nat := 4983230072969 + 3 ^ 40 * 6803109 * 2
def baseEnd_6803109 : Nat := 3493264861928328538450577

theorem tailTrace_6803109 : CollatzResearch.WordTrace tailWord_6803109 prefixEnd_6803109 3493264861928328538450577 := by
  unfold tailWord_6803109
  simp only [CollatzResearch.WordTrace]
  refine ⟨248129769910505446360436381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165419846607003630906957587 248129769910505446360436381)
  ·
    refine ⟨93048663716439542385163643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248129769910505446360436381 93048663716439542385163643)
    ·
      refine ⟨139572995574659313577745465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93048663716439542385163643 139572995574659313577745465)
      ·
        refine ⟨104679746680994485183309099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139572995574659313577745465 104679746680994485183309099)
        ·
          refine ⟨157019620021491727774963649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104679746680994485183309099 157019620021491727774963649)
          ·
            refine ⟨117764715016118795831222737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157019620021491727774963649 117764715016118795831222737)
            ·
              refine ⟨88323536262089096873417053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117764715016118795831222737 88323536262089096873417053)
              ·
                refine ⟨33121326098283411327531395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88323536262089096873417053 33121326098283411327531395)
                ·
                  refine ⟨49681989147425116991297093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33121326098283411327531395 49681989147425116991297093)
                  ·
                    refine ⟨9315372965142209435868205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49681989147425116991297093 9315372965142209435868205)
                    ·
                      refine ⟨3493264861928328538450577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9315372965142209435868205 3493264861928328538450577)
                      ·
                        rfl

theorem cell23_6803109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_6803109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803109 prefixEnd_6803109 := by exact prefixLift 6803109
  have htrace : WordTrace (prefixWord ++ tailWord_6803109) baseStart_6803109 baseEnd_6803109 := by
    simpa [prefixWord, tailWord_6803109, baseEnd_6803109] using wordTrace_append hprefix tailTrace_6803109
  have hstable : (prefixWord ++ tailWord_6803109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803109).length < 2 ^ (prefixWord ++ tailWord_6803109).sum := by decide
  have hdescent : baseEnd_6803109 < baseStart_6803109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803129 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 6]
def baseStart_6803129 : Nat := 118140960795 + 6803129 * 2 ^ 59
def prefixEnd_6803129 : Nat := 4983230072969 + 3 ^ 40 * 6803129 * 2
def baseEnd_6803129 : Nat := 388141681282379828911165

theorem tailTrace_6803129 : CollatzResearch.WordTrace tailWord_6803129 prefixEnd_6803129 388141681282379828911165 := by
  unfold tailWord_6803129
  simp only [CollatzResearch.WordTrace]
  refine ⟨248130499370432989776164441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165420332913621993184109627 248130499370432989776164441)
  ·
    refine ⟨186097874527824742332123331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248130499370432989776164441 186097874527824742332123331)
    ·
      refine ⟨279146811791737113498184997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186097874527824742332123331 279146811791737113498184997)
      ·
        refine ⟨52340027210950708780909687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279146811791737113498184997 52340027210950708780909687)
        ·
          refine ⟨78510040816426063171364531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52340027210950708780909687 78510040816426063171364531)
          ·
            refine ⟨117765061224639094757046797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78510040816426063171364531 117765061224639094757046797)
            ·
              refine ⟨44161897959239660533892549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117765061224639094757046797 44161897959239660533892549)
              ·
                refine ⟨8280355867357436350104853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44161897959239660533892549 8280355867357436350104853)
                ·
                  refine ⟨388141681282379828911165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8280355867357436350104853 388141681282379828911165)
                  ·
                    rfl

theorem cell23_6803129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_6803129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803129 prefixEnd_6803129 := by exact prefixLift 6803129
  have htrace : WordTrace (prefixWord ++ tailWord_6803129) baseStart_6803129 baseEnd_6803129 := by
    simpa [prefixWord, tailWord_6803129, baseEnd_6803129] using wordTrace_append hprefix tailTrace_6803129
  have hstable : (prefixWord ++ tailWord_6803129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803129).length < 2 ^ (prefixWord ++ tailWord_6803129).sum := by decide
  have hdescent : baseEnd_6803129 < baseStart_6803129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803133 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6803133 : Nat := 118140960795 + 6803133 * 2 ^ 59
def prefixEnd_6803133 : Nat := 4983230072969 + 3 ^ 40 * 6803133 * 2
def baseEnd_6803133 : Nat := 1164425728488012148183489

theorem tailTrace_6803133 : CollatzResearch.WordTrace tailWord_6803133 prefixEnd_6803133 1164425728488012148183489 := by
  unfold tailWord_6803133
  simp only [CollatzResearch.WordTrace]
  refine ⟨248130645262418498459310053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165420430174945665639540035 248130645262418498459310053)
  ·
    refine ⟨46524495986703468461120635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248130645262418498459310053 46524495986703468461120635)
    ·
      refine ⟨69786743980055202691680953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46524495986703468461120635 69786743980055202691680953)
      ·
        refine ⟨52340057985041402018760715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69786743980055202691680953 52340057985041402018760715)
        ·
          refine ⟨78510086977562103028141073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52340057985041402018760715 78510086977562103028141073)
          ·
            refine ⟨58882565233171577271105805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78510086977562103028141073 58882565233171577271105805)
            ·
              refine ⟨22080961962439341476664677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58882565233171577271105805 22080961962439341476664677)
              ·
                refine ⟨4140180367957376526874627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22080961962439341476664677 4140180367957376526874627)
                ·
                  refine ⟨6210270551936064790311941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140180367957376526874627 6210270551936064790311941)
                  ·
                    refine ⟨1164425728488012148183489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210270551936064790311941 1164425728488012148183489)
                    ·
                      rfl

theorem cell23_6803133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6803133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803133 prefixEnd_6803133 := by exact prefixLift 6803133
  have htrace : WordTrace (prefixWord ++ tailWord_6803133) baseStart_6803133 baseEnd_6803133 := by
    simpa [prefixWord, tailWord_6803133, baseEnd_6803133] using wordTrace_append hprefix tailTrace_6803133
  have hstable : (prefixWord ++ tailWord_6803133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803133).length < 2 ^ (prefixWord ++ tailWord_6803133).sum := by decide
  have hdescent : baseEnd_6803133 < baseStart_6803133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803159 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 3, 5]
def baseStart_6803159 : Nat := 118140960795 + 6803159 * 2 ^ 59
def prefixEnd_6803159 : Nat := 4983230072969 + 3 ^ 40 * 6803159 * 2
def baseEnd_6803159 : Nat := 1164430178653684447608449

theorem tailTrace_6803159 : CollatzResearch.WordTrace tailWord_6803159 prefixEnd_6803159 1164430178653684447608449 := by
  unfold tailWord_6803159
  simp only [CollatzResearch.WordTrace]
  refine ⟨248131593560324304899756531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165421062373549536599837687 248131593560324304899756531)
  ·
    refine ⟨372197390340486457349634797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248131593560324304899756531 372197390340486457349634797)
    ·
      refine ⟨139574021377682421506113049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372197390340486457349634797 139574021377682421506113049)
      ·
        refine ⟨104680516033261816129584787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139574021377682421506113049 104680516033261816129584787)
        ·
          refine ⟨157020774049892724194377181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104680516033261816129584787 157020774049892724194377181)
          ·
            refine ⟨58882790268709771572891443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157020774049892724194377181 58882790268709771572891443)
            ·
              refine ⟨88324185403064657359337165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58882790268709771572891443 88324185403064657359337165)
              ·
                refine ⟨33121569526149246509751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88324185403064657359337165 33121569526149246509751437)
                ·
                  refine ⟨12420588572305967441156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33121569526149246509751437 12420588572305967441156789)
                  ·
                    refine ⟨1164430178653684447608449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12420588572305967441156789 1164430178653684447608449)
                    ·
                      rfl

theorem cell23_6803159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_6803159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803159 prefixEnd_6803159 := by exact prefixLift 6803159
  have htrace : WordTrace (prefixWord ++ tailWord_6803159) baseStart_6803159 baseEnd_6803159 := by
    simpa [prefixWord, tailWord_6803159, baseEnd_6803159] using wordTrace_append hprefix tailTrace_6803159
  have hstable : (prefixWord ++ tailWord_6803159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803159).length < 2 ^ (prefixWord ++ tailWord_6803159).sum := by decide
  have hdescent : baseEnd_6803159 < baseStart_6803159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803190 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6803190 : Nat := 118140960795 + 6803190 * 2 ^ 59
def prefixEnd_6803190 : Nat := 4983230072969 + 3 ^ 40 * 6803190 * 2
def baseEnd_6803190 : Nat := 3493306453861342721537705

theorem tailTrace_6803190 : CollatzResearch.WordTrace tailWord_6803190 prefixEnd_6803190 3493306453861342721537705 := by
  unfold tailWord_6803190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508295263950749824633439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165421816148807998129423349 15508295263950749824633439)
  ·
    refine ⟨23262442895926124736950159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15508295263950749824633439 23262442895926124736950159)
    ·
      refine ⟨34893664343889187105425239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23262442895926124736950159 34893664343889187105425239)
      ·
        refine ⟨52340496515833780658137859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34893664343889187105425239 52340496515833780658137859)
        ·
          refine ⟨78510744773750670987206789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52340496515833780658137859 78510744773750670987206789)
          ·
            refine ⟨14720764645078250810101273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78510744773750670987206789 14720764645078250810101273)
            ·
              refine ⟨11040573483808688107575955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720764645078250810101273 11040573483808688107575955)
              ·
                refine ⟨16560860225713032161363933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040573483808688107575955 16560860225713032161363933)
                ·
                  refine ⟨6210322584642387060511475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16560860225713032161363933 6210322584642387060511475)
                  ·
                    refine ⟨9315483876963580590767213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6210322584642387060511475 9315483876963580590767213)
                    ·
                      refine ⟨3493306453861342721537705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9315483876963580590767213 3493306453861342721537705)
                      ·
                        rfl

theorem cell23_6803190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6803190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803190 prefixEnd_6803190 := by exact prefixLift 6803190
  have htrace : WordTrace (prefixWord ++ tailWord_6803190) baseStart_6803190 baseEnd_6803190 := by
    simpa [prefixWord, tailWord_6803190, baseEnd_6803190] using wordTrace_append hprefix tailTrace_6803190
  have hstable : (prefixWord ++ tailWord_6803190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803190).length < 2 ^ (prefixWord ++ tailWord_6803190).sum := by decide
  have hdescent : baseEnd_6803190 < baseStart_6803190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803199 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_6803199 : Nat := 118140960795 + 6803199 * 2 ^ 59
def prefixEnd_6803199 : Nat := 4983230072969 + 3 ^ 40 * 6803199 * 2
def baseEnd_6803199 : Nat := 3493311075187233186325163

theorem tailTrace_6803199 : CollatzResearch.WordTrace tailWord_6803199 prefixEnd_6803199 3493311075187233186325163 := by
  unfold tailWord_6803199
  simp only [CollatzResearch.WordTrace]
  refine ⟨248133052480179391731212651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165422034986786261154141767 248133052480179391731212651)
  ·
    refine ⟨372199578720269087596818977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248133052480179391731212651 372199578720269087596818977)
    ·
      refine ⟨279149684040201815697614233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372199578720269087596818977 279149684040201815697614233)
      ·
        refine ⟨209362263030151361773210675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279149684040201815697614233 209362263030151361773210675)
        ·
          refine ⟨314043394545227042659816013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209362263030151361773210675 314043394545227042659816013)
          ·
            refine ⟨117766272954460140997431005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314043394545227042659816013 117766272954460140997431005)
            ·
              refine ⟨44162352357922552874036627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117766272954460140997431005 44162352357922552874036627)
              ·
                refine ⟨66243528536883829311054941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44162352357922552874036627 66243528536883829311054941)
                ·
                  refine ⟨24841323201331435991645603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66243528536883829311054941 24841323201331435991645603)
                  ·
                    refine ⟨37261984801997153987468405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24841323201331435991645603 37261984801997153987468405)
                    ·
                      refine ⟨3493311075187233186325163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37261984801997153987468405 3493311075187233186325163)
                      ·
                        rfl

theorem cell23_6803199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_6803199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803199 prefixEnd_6803199 := by exact prefixLift 6803199
  have htrace : WordTrace (prefixWord ++ tailWord_6803199) baseStart_6803199 baseEnd_6803199 := by
    simpa [prefixWord, tailWord_6803199, baseEnd_6803199] using wordTrace_append hprefix tailTrace_6803199
  have hstable : (prefixWord ++ tailWord_6803199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803199).length < 2 ^ (prefixWord ++ tailWord_6803199).sum := by decide
  have hdescent : baseEnd_6803199 < baseStart_6803199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803233 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6803233 : Nat := 118140960795 + 6803233 * 2 ^ 59
def prefixEnd_6803233 : Nat := 4983230072969 + 3 ^ 40 * 6803233 * 2
def baseEnd_6803233 : Nat := 3493328533529486053300007

theorem tailTrace_6803233 : CollatzResearch.WordTrace tailWord_6803233 prefixEnd_6803233 3493328533529486053300007 := by
  unfold tailWord_6803233
  simp only [CollatzResearch.WordTrace]
  refine ⟨248134292562056215537950353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165422861708037477025300235 248134292562056215537950353)
  ·
    refine ⟨186100719421542161653462765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248134292562056215537950353 186100719421542161653462765)
    ·
      refine ⟨69787769783078310620048537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186100719421542161653462765 69787769783078310620048537)
      ·
        refine ⟨52340827337308732965036403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69787769783078310620048537 52340827337308732965036403)
        ·
          refine ⟨78511241005963099447554605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52340827337308732965036403 78511241005963099447554605)
          ·
            refine ⟨29441715377236162292832977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78511241005963099447554605 29441715377236162292832977)
            ·
              refine ⟨22081286532927121719624733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29441715377236162292832977 22081286532927121719624733)
              ·
                refine ⟨8280482449847670644859275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22081286532927121719624733 8280482449847670644859275)
                ·
                  refine ⟨12420723674771505967288913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8280482449847670644859275 12420723674771505967288913)
                  ·
                    refine ⟨9315542756078629475466685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12420723674771505967288913 9315542756078629475466685)
                    ·
                      refine ⟨3493328533529486053300007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9315542756078629475466685 3493328533529486053300007)
                      ·
                        rfl

theorem cell23_6803233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6803233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803233 prefixEnd_6803233 := by exact prefixLift 6803233
  have htrace : WordTrace (prefixWord ++ tailWord_6803233) baseStart_6803233 baseEnd_6803233 := by
    simpa [prefixWord, tailWord_6803233, baseEnd_6803233] using wordTrace_append hprefix tailTrace_6803233
  have hstable : (prefixWord ++ tailWord_6803233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803233).length < 2 ^ (prefixWord ++ tailWord_6803233).sum := by decide
  have hdescent : baseEnd_6803233 < baseStart_6803233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803236 : List Nat := [2, 3, 1, 3, 2, 3, 9]
def baseStart_6803236 : Nat := 118140960795 + 6803236 * 2 ^ 59
def prefixEnd_6803236 : Nat := 4983230072969 + 3 ^ 40 * 6803236 * 2
def baseEnd_6803236 : Nat := 43127531777425302982253

theorem tailTrace_6803236 : CollatzResearch.WordTrace tailWord_6803236 prefixEnd_6803236 43127531777425302982253 := by
  unfold tailWord_6803236
  simp only [CollatzResearch.WordTrace]
  refine ⟨124067200990522673525154781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165422934654030231366873041 124067200990522673525154781)
  ·
    refine ⟨46525200371446002571933043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124067200990522673525154781 46525200371446002571933043)
    ·
      refine ⟨69787800557169003857899565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46525200371446002571933043 69787800557169003857899565)
      ·
        refine ⟨26170425208938376446712337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69787800557169003857899565 26170425208938376446712337)
        ·
          refine ⟨19627818906703782335034253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26170425208938376446712337 19627818906703782335034253)
          ·
            refine ⟨7360432090013918375637845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19627818906703782335034253 7360432090013918375637845)
            ·
              refine ⟨43127531777425302982253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7360432090013918375637845 43127531777425302982253)
              ·
                rfl

theorem cell23_6803236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 9].length) (baseStart_6803236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803236 prefixEnd_6803236 := by exact prefixLift 6803236
  have htrace : WordTrace (prefixWord ++ tailWord_6803236) baseStart_6803236 baseEnd_6803236 := by
    simpa [prefixWord, tailWord_6803236, baseEnd_6803236] using wordTrace_append hprefix tailTrace_6803236
  have hstable : (prefixWord ++ tailWord_6803236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803236).length < 2 ^ (prefixWord ++ tailWord_6803236).sum := by decide
  have hdescent : baseEnd_6803236 < baseStart_6803236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803273 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 3, 3, 2]
def baseStart_6803273 : Nat := 118140960795 + 6803273 * 2 ^ 59
def prefixEnd_6803273 : Nat := 4983230072969 + 3 ^ 40 * 6803273 * 2
def baseEnd_6803273 : Nat := 3493349072755665896799823

theorem tailTrace_6803273 : CollatzResearch.WordTrace tailWord_6803273 prefixEnd_6803273 3493349072755665896799823 := by
  unfold tailWord_6803273
  simp only [CollatzResearch.WordTrace]
  refine ⟨248135751481911302369406473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165423834321274201579604315 248135751481911302369406473)
  ·
    refine ⟨186101813611433476777054855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248135751481911302369406473 186101813611433476777054855)
    ·
      refine ⟨279152720417150215165582283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186101813611433476777054855 279152720417150215165582283)
      ·
        refine ⟨418729080625725322748373425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279152720417150215165582283 418729080625725322748373425)
        ·
          refine ⟨314046810469293992061280069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418729080625725322748373425 314046810469293992061280069)
          ·
            refine ⟨58883776962992623511490013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314046810469293992061280069 58883776962992623511490013)
            ·
              refine ⟨22081416361122233816808755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58883776962992623511490013 22081416361122233816808755)
              ·
                refine ⟨33122124541683350725213133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22081416361122233816808755 33122124541683350725213133)
                ·
                  refine ⟨12420796703131256521954925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33122124541683350725213133 12420796703131256521954925)
                  ·
                    refine ⟨4657798763674221195733097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12420796703131256521954925 4657798763674221195733097)
                    ·
                      refine ⟨3493349072755665896799823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657798763674221195733097 3493349072755665896799823)
                      ·
                        rfl

theorem cell23_6803273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3, 2].length) (baseStart_6803273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803273 prefixEnd_6803273 := by exact prefixLift 6803273
  have htrace : WordTrace (prefixWord ++ tailWord_6803273) baseStart_6803273 baseEnd_6803273 := by
    simpa [prefixWord, tailWord_6803273, baseEnd_6803273] using wordTrace_append hprefix tailTrace_6803273
  have hstable : (prefixWord ++ tailWord_6803273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803273).length < 2 ^ (prefixWord ++ tailWord_6803273).sum := by decide
  have hdescent : baseEnd_6803273 < baseStart_6803273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803303 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_6803303 : Nat := 118140960795 + 6803303 * 2 ^ 59
def prefixEnd_6803303 : Nat := 4983230072969 + 3 ^ 40 * 6803303 * 2
def baseEnd_6803303 : Nat := 3493364477175300779424685

theorem tailTrace_6803303 : CollatzResearch.WordTrace tailWord_6803303 prefixEnd_6803303 3493364477175300779424685 := by
  unfold tailWord_6803303
  simp only [CollatzResearch.WordTrace]
  refine ⟨248136845671802617492998563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165424563781201744995332375 248136845671802617492998563)
  ·
    refine ⟨372205268507703926239497845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248136845671802617492998563 372205268507703926239497845)
    ·
      refine ⟨34894243922597243084952923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372205268507703926239497845 34894243922597243084952923)
      ·
        refine ⟨52341365883895864627429385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34894243922597243084952923 52341365883895864627429385)
        ·
          refine ⟨39256024412921898470572039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52341365883895864627429385 39256024412921898470572039)
          ·
            refine ⟨58884036619382847705858059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39256024412921898470572039 58884036619382847705858059)
            ·
              refine ⟨88326054929074271558787089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58884036619382847705858059 88326054929074271558787089)
              ·
                refine ⟨66244541196805703669090317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88326054929074271558787089 66244541196805703669090317)
                ·
                  refine ⟨24841702948802138875908869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66244541196805703669090317 24841702948802138875908869)
                  ·
                    refine ⟨4657819302900401039232913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24841702948802138875908869 4657819302900401039232913)
                    ·
                      refine ⟨3493364477175300779424685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657819302900401039232913 3493364477175300779424685)
                      ·
                        rfl

theorem cell23_6803303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_6803303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803303 prefixEnd_6803303 := by exact prefixLift 6803303
  have htrace : WordTrace (prefixWord ++ tailWord_6803303) baseStart_6803303 baseEnd_6803303 := by
    simpa [prefixWord, tailWord_6803303, baseEnd_6803303] using wordTrace_append hprefix tailTrace_6803303
  have hstable : (prefixWord ++ tailWord_6803303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803303).length < 2 ^ (prefixWord ++ tailWord_6803303).sum := by decide
  have hdescent : baseEnd_6803303 < baseStart_6803303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803354 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6803354 : Nat := 118140960795 + 6803354 * 2 ^ 59
def prefixEnd_6803354 : Nat := 4983230072969 + 3 ^ 40 * 6803354 * 2
def baseEnd_6803354 : Nat := 3493390664688680079886951

theorem tailTrace_6803354 : CollatzResearch.WordTrace tailWord_6803354 prefixEnd_6803354 3493390664688680079886951 := by
  unfold tailWord_6803354
  simp only [CollatzResearch.WordTrace]
  refine ⟨62034676448654463300776279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165425803863078568802070077 62034676448654463300776279)
  ·
    refine ⟨93052014672981694951164419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62034676448654463300776279 93052014672981694951164419)
    ·
      refine ⟨139578022009472542426746629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93052014672981694951164419 139578022009472542426746629)
      ·
        refine ⟨26170879126776101705014993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139578022009472542426746629 26170879126776101705014993)
        ·
          refine ⟨19628159345082076278761245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26170879126776101705014993 19628159345082076278761245)
          ·
            refine ⟨7360559754405778604535467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19628159345082076278761245 7360559754405778604535467)
            ·
              refine ⟨11040839631608667906803201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360559754405778604535467 11040839631608667906803201)
              ·
                refine ⟨8280629723706500930102401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040839631608667906803201 8280629723706500930102401)
                ·
                  refine ⟨6210472292779875697576801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8280629723706500930102401 6210472292779875697576801)
                  ·
                    refine ⟨4657854219584906773182601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210472292779875697576801 4657854219584906773182601)
                    ·
                      refine ⟨3493390664688680079886951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657854219584906773182601 3493390664688680079886951)
                      ·
                        rfl

theorem cell23_6803354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6803354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803354 prefixEnd_6803354 := by exact prefixLift 6803354
  have htrace : WordTrace (prefixWord ++ tailWord_6803354) baseStart_6803354 baseEnd_6803354 := by
    simpa [prefixWord, tailWord_6803354, baseEnd_6803354] using wordTrace_append hprefix tailTrace_6803354
  have hstable : (prefixWord ++ tailWord_6803354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803354).length < 2 ^ (prefixWord ++ tailWord_6803354).sum := by decide
  have hdescent : baseEnd_6803354 < baseStart_6803354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803416 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 8]
def baseStart_6803416 : Nat := 118140960795 + 6803416 * 2 ^ 59
def prefixEnd_6803416 : Nat := 4983230072969 + 3 ^ 40 * 6803416 * 2
def baseEnd_6803416 : Nat := 388158055609917648590185

theorem tailTrace_6803416 : CollatzResearch.WordTrace tailWord_6803416 prefixEnd_6803416 388158055609917648590185 := by
  unfold tailWord_6803416
  simp only [CollatzResearch.WordTrace]
  refine ⟨124070483560196618895931051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165427311413595491861241401 124070483560196618895931051)
  ·
    refine ⟨186105725340294928343896577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124070483560196618895931051 186105725340294928343896577)
    ·
      refine ⟨139579294005221196257922433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186105725340294928343896577 139579294005221196257922433)
      ·
        refine ⟨104684470503915897193441825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139579294005221196257922433 104684470503915897193441825)
        ·
          refine ⟨78513352877936922895081369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104684470503915897193441825 78513352877936922895081369)
          ·
            refine ⟨58885014658452692171311027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78513352877936922895081369 58885014658452692171311027)
            ·
              refine ⟨88327521987679038256966541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58885014658452692171311027 88327521987679038256966541)
              ·
                refine ⟨33122820745379639346362453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88327521987679038256966541 33122820745379639346362453)
                ·
                  refine ⟨388158055609917648590185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33122820745379639346362453 388158055609917648590185)
                  ·
                    rfl

theorem cell23_6803416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_6803416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803416 prefixEnd_6803416 := by exact prefixLift 6803416
  have htrace : WordTrace (prefixWord ++ tailWord_6803416) baseStart_6803416 baseEnd_6803416 := by
    simpa [prefixWord, tailWord_6803416, baseEnd_6803416] using wordTrace_append hprefix tailTrace_6803416
  have hstable : (prefixWord ++ tailWord_6803416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803416).length < 2 ^ (prefixWord ++ tailWord_6803416).sum := by decide
  have hdescent : baseEnd_6803416 < baseStart_6803416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803436 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6803436 : Nat := 118140960795 + 6803436 * 2 ^ 59
def prefixEnd_6803436 : Nat := 4983230072969 + 3 ^ 40 * 6803436 * 2
def baseEnd_6803436 : Nat := 3493432770102348759061573

theorem tailTrace_6803436 : CollatzResearch.WordTrace tailWord_6803436 prefixEnd_6803436 3493432770102348759061573 := by
  unfold tailWord_6803436
  simp only [CollatzResearch.WordTrace]
  refine ⟨124070848290160390603795081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165427797720213854138393441 124070848290160390603795081)
  ·
    refine ⟨93053136217620292952846311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124070848290160390603795081 93053136217620292952846311)
    ·
      refine ⟨139579704326430439429269467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93053136217620292952846311 139579704326430439429269467)
      ·
        refine ⟨209369556489645659143904201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139579704326430439429269467 209369556489645659143904201)
        ·
          refine ⟨157027167367234244357928151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209369556489645659143904201 157027167367234244357928151)
          ·
            refine ⟨235540751050851366536892227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157027167367234244357928151 235540751050851366536892227)
            ·
              refine ⟨353311126576277049805338341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235540751050851366536892227 353311126576277049805338341)
              ·
                refine ⟨66245836233051946838500939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353311126576277049805338341 66245836233051946838500939)
                ·
                  refine ⟨99368754349577920257751409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66245836233051946838500939 99368754349577920257751409)
                  ·
                    refine ⟨74526565762183440193313557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99368754349577920257751409 74526565762183440193313557)
                    ·
                      refine ⟨3493432770102348759061573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74526565762183440193313557 3493432770102348759061573)
                      ·
                        rfl

theorem cell23_6803436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6803436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803436 prefixEnd_6803436 := by exact prefixLift 6803436
  have htrace : WordTrace (prefixWord ++ tailWord_6803436) baseStart_6803436 baseEnd_6803436 := by
    simpa [prefixWord, tailWord_6803436, baseEnd_6803436] using wordTrace_append hprefix tailTrace_6803436
  have hstable : (prefixWord ++ tailWord_6803436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803436).length < 2 ^ (prefixWord ++ tailWord_6803436).sum := by decide
  have hdescent : baseEnd_6803436 < baseStart_6803436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803456 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_6803456 : Nat := 118140960795 + 6803456 * 2 ^ 59
def prefixEnd_6803456 : Nat := 4983230072969 + 3 ^ 40 * 6803456 * 2
def baseEnd_6803456 : Nat := 3493443039715438680811481

theorem tailTrace_6803456 : CollatzResearch.WordTrace tailWord_6803456 prefixEnd_6803456 3493443039715438680811481 := by
  unfold tailWord_6803456
  simp only [CollatzResearch.WordTrace]
  refine ⟨124071213020124162311659111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165428284026832216415545481 124071213020124162311659111)
  ·
    refine ⟨186106819530186243467488667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124071213020124162311659111 186106819530186243467488667)
    ·
      refine ⟨279160229295279365201233001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186106819530186243467488667 279160229295279365201233001)
      ·
        refine ⟨209370171971459523900924751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279160229295279365201233001 209370171971459523900924751)
        ·
          refine ⟨314055257957189285851387127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209370171971459523900924751 314055257957189285851387127)
          ·
            refine ⟨471082886935783928777080691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314055257957189285851387127 471082886935783928777080691)
            ·
              refine ⟨706624330403675893165621037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471082886935783928777080691 706624330403675893165621037)
              ·
                refine ⟨264984123901378459937107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706624330403675893165621037 264984123901378459937107889)
                ·
                  refine ⟨198738092926033844952830917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264984123901378459937107889 198738092926033844952830917)
                  ·
                    refine ⟨37263392423631345928655797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198738092926033844952830917 37263392423631345928655797)
                    ·
                      refine ⟨3493443039715438680811481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37263392423631345928655797 3493443039715438680811481)
                      ·
                        rfl

theorem cell23_6803456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_6803456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803456 prefixEnd_6803456 := by exact prefixLift 6803456
  have htrace : WordTrace (prefixWord ++ tailWord_6803456) baseStart_6803456 baseEnd_6803456 := by
    simpa [prefixWord, tailWord_6803456, baseEnd_6803456] using wordTrace_append hprefix tailTrace_6803456
  have hstable : (prefixWord ++ tailWord_6803456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803456).length < 2 ^ (prefixWord ++ tailWord_6803456).sum := by decide
  have hdescent : baseEnd_6803456 < baseStart_6803456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803493 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_6803493 : Nat := 118140960795 + 6803493 * 2 ^ 59
def prefixEnd_6803493 : Nat := 4983230072969 + 3 ^ 40 * 6803493 * 2
def baseEnd_6803493 : Nat := 1164487346166551678682937

theorem tailTrace_6803493 : CollatzResearch.WordTrace tailWord_6803493 prefixEnd_6803493 1164487346166551678682937 := by
  unfold tailWord_6803493
  simp only [CollatzResearch.WordTrace]
  refine ⟨248143775541114279942415133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165429183694076186628276755 248143775541114279942415133)
  ·
    refine ⟨93053915827917854978405675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248143775541114279942415133 93053915827917854978405675)
    ·
      refine ⟨139580873741876782467608513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93053915827917854978405675 139580873741876782467608513)
      ·
        refine ⟨104685655306407586850706385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139580873741876782467608513 104685655306407586850706385)
        ·
          refine ⟨78514241479805690138029789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104685655306407586850706385 78514241479805690138029789)
          ·
            refine ⟨29442840554927133801761171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78514241479805690138029789 29442840554927133801761171)
            ·
              refine ⟨44164260832390700702641757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29442840554927133801761171 44164260832390700702641757)
              ·
                refine ⟨16561597812146512763490659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44164260832390700702641757 16561597812146512763490659)
                ·
                  refine ⟨24842396718219769145235989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16561597812146512763490659 24842396718219769145235989)
                  ·
                    refine ⟨1164487346166551678682937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24842396718219769145235989 1164487346166551678682937)
                    ·
                      rfl

theorem cell23_6803493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_6803493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803493 prefixEnd_6803493 := by exact prefixLift 6803493
  have htrace : WordTrace (prefixWord ++ tailWord_6803493) baseStart_6803493 baseEnd_6803493 := by
    simpa [prefixWord, tailWord_6803493, baseEnd_6803493] using wordTrace_append hprefix tailTrace_6803493
  have hstable : (prefixWord ++ tailWord_6803493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803493).length < 2 ^ (prefixWord ++ tailWord_6803493).sum := by decide
  have hdescent : baseEnd_6803493 < baseStart_6803493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803510 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6803510 : Nat := 118140960795 + 6803510 * 2 ^ 59
def prefixEnd_6803510 : Nat := 4983230072969 + 3 ^ 40 * 6803510 * 2
def baseEnd_6803510 : Nat := 1164490255890260489845411

theorem tailTrace_6803510 : CollatzResearch.WordTrace tailWord_6803510 prefixEnd_6803510 1164490255890260489845411 := by
  unfold tailWord_6803510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509024723878293240361499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165429597054701794563855989 15509024723878293240361499)
  ·
    refine ⟨23263537085817439860542249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509024723878293240361499 23263537085817439860542249)
    ·
      refine ⟨17447652814363079895406687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23263537085817439860542249 17447652814363079895406687)
      ·
        refine ⟨26171479221544619843110031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17447652814363079895406687 26171479221544619843110031)
        ·
          refine ⟨39257218832316929764665047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26171479221544619843110031 39257218832316929764665047)
          ·
            refine ⟨58885828248475394646997571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39257218832316929764665047 58885828248475394646997571)
            ·
              refine ⟨88328742372713091970496357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58885828248475394646997571 88328742372713091970496357)
              ·
                refine ⟨16561639194883704744468067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88328742372713091970496357 16561639194883704744468067)
                ·
                  refine ⟨24842458792325557116702101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16561639194883704744468067 24842458792325557116702101)
                  ·
                    refine ⟨1164490255890260489845411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24842458792325557116702101 1164490255890260489845411)
                    ·
                      rfl

theorem cell23_6803510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6803510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803510 prefixEnd_6803510 := by exact prefixLift 6803510
  have htrace : WordTrace (prefixWord ++ tailWord_6803510) baseStart_6803510 baseEnd_6803510 := by
    simpa [prefixWord, tailWord_6803510, baseEnd_6803510] using wordTrace_append hprefix tailTrace_6803510
  have hstable : (prefixWord ++ tailWord_6803510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803510).length < 2 ^ (prefixWord ++ tailWord_6803510).sum := by decide
  have hdescent : baseEnd_6803510 < baseStart_6803510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803517 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6803517 : Nat := 118140960795 + 6803517 * 2 ^ 59
def prefixEnd_6803517 : Nat := 4983230072969 + 3 ^ 40 * 6803517 * 2
def baseEnd_6803517 : Nat := 3493474362035362942148701

theorem tailTrace_6803517 : CollatzResearch.WordTrace tailWord_6803517 prefixEnd_6803517 3493474362035362942148701 := by
  unfold tailWord_6803517
  simp only [CollatzResearch.WordTrace]
  refine ⟨248144650893027332041288805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165429767262018221360859203 248144650893027332041288805)
  ·
    refine ⟨46527122042442624757741651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248144650893027332041288805 46527122042442624757741651)
    ·
      refine ⟨69790683063663937136612477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46527122042442624757741651 69790683063663937136612477)
      ·
        refine ⟨26171506148873976426229679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69790683063663937136612477 26171506148873976426229679)
        ·
          refine ⟨39257259223310964639344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26171506148873976426229679 39257259223310964639344519)
          ·
            refine ⟨58885888834966446959016779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39257259223310964639344519 58885888834966446959016779)
            ·
              refine ⟨88328833252449670438525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58885888834966446959016779 88328833252449670438525169)
              ·
                refine ⟨66246624939337252828893877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88328833252449670438525169 66246624939337252828893877)
                ·
                  refine ⟨6210621088062867452708801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66246624939337252828893877 6210621088062867452708801)
                  ·
                    refine ⟨4657965816047150589531601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210621088062867452708801 4657965816047150589531601)
                    ·
                      refine ⟨3493474362035362942148701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657965816047150589531601 3493474362035362942148701)
                      ·
                        rfl

theorem cell23_6803517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6803517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803517 prefixEnd_6803517 := by exact prefixLift 6803517
  have htrace : WordTrace (prefixWord ++ tailWord_6803517) baseStart_6803517 baseEnd_6803517 := by
    simpa [prefixWord, tailWord_6803517, baseEnd_6803517] using wordTrace_append hprefix tailTrace_6803517
  have hstable : (prefixWord ++ tailWord_6803517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803517).length < 2 ^ (prefixWord ++ tailWord_6803517).sum := by decide
  have hdescent : baseEnd_6803517 < baseStart_6803517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803534 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_6803534 : Nat := 118140960795 + 6803534 * 2 ^ 59
def prefixEnd_6803534 : Nat := 4983230072969 + 3 ^ 40 * 6803534 * 2
def baseEnd_6803534 : Nat := 3493483091206489375636123

theorem tailTrace_6803534 : CollatzResearch.WordTrace tailWord_6803534 prefixEnd_6803534 3493483091206489375636123 := by
  unfold tailWord_6803534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018158866745717993082207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165430180622643829296438437 31018158866745717993082207)
  ·
    refine ⟨46527238300118576989623311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31018158866745717993082207 46527238300118576989623311)
    ·
      refine ⟨69790857450177865484434967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46527238300118576989623311 69790857450177865484434967)
      ·
        refine ⟨104686286175266798226652451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69790857450177865484434967 104686286175266798226652451)
        ·
          refine ⟨157029429262900197339978677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104686286175266798226652451 157029429262900197339978677)
          ·
            refine ⟨14721508993396893500623001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157029429262900197339978677 14721508993396893500623001)
            ·
              refine ⟨11041131745047670125467251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14721508993396893500623001 11041131745047670125467251)
              ·
                refine ⟨16561697617571505188200877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041131745047670125467251 16561697617571505188200877)
                ·
                  refine ⟨6210636606589314445575329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16561697617571505188200877 6210636606589314445575329)
                  ·
                    refine ⟨4657977454941985834181497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210636606589314445575329 4657977454941985834181497)
                    ·
                      refine ⟨3493483091206489375636123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4657977454941985834181497 3493483091206489375636123)
                      ·
                        rfl

theorem cell23_6803534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_6803534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803534 prefixEnd_6803534 := by exact prefixLift 6803534
  have htrace : WordTrace (prefixWord ++ tailWord_6803534) baseStart_6803534 baseEnd_6803534 := by
    simpa [prefixWord, tailWord_6803534, baseEnd_6803534] using wordTrace_append hprefix tailTrace_6803534
  have hstable : (prefixWord ++ tailWord_6803534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803534).length < 2 ^ (prefixWord ++ tailWord_6803534).sum := by decide
  have hdescent : baseEnd_6803534 < baseStart_6803534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803593 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_6803593 : Nat := 118140960795 + 6803593 * 2 ^ 59
def prefixEnd_6803593 : Nat := 4983230072969 + 3 ^ 40 * 6803593 * 2
def baseEnd_6803593 : Nat := 3493513386565104644798351

theorem tailTrace_6803593 : CollatzResearch.WordTrace tailWord_6803593 prefixEnd_6803593 3493513386565104644798351 := by
  unfold tailWord_6803593
  simp only [CollatzResearch.WordTrace]
  refine ⟨248147422840751997021055433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165431615227167998014036955 248147422840751997021055433)
  ·
    refine ⟨186110567130563997765791575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248147422840751997021055433 186110567130563997765791575)
    ·
      refine ⟨279165850695845996648687363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186110567130563997765791575 279165850695845996648687363)
      ·
        refine ⟨418748776043768994973031045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279165850695845996648687363 418748776043768994973031045)
        ·
          refine ⟨78515395508206686557443321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418748776043768994973031045 78515395508206686557443321)
          ·
            refine ⟨58886546631155014918082491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78515395508206686557443321 58886546631155014918082491)
            ·
              refine ⟨88329819946732522377123737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58886546631155014918082491 88329819946732522377123737)
              ·
                refine ⟨66247364960049391782842803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88329819946732522377123737 66247364960049391782842803)
                ·
                  refine ⟨99371047440074087674264205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66247364960049391782842803 99371047440074087674264205)
                  ·
                    refine ⟨37264142790027782877849077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99371047440074087674264205 37264142790027782877849077)
                    ·
                      refine ⟨3493513386565104644798351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37264142790027782877849077 3493513386565104644798351)
                      ·
                        rfl

theorem cell23_6803593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_6803593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803593 prefixEnd_6803593 := by exact prefixLift 6803593
  have htrace : WordTrace (prefixWord ++ tailWord_6803593) baseStart_6803593 baseEnd_6803593 := by
    simpa [prefixWord, tailWord_6803593, baseEnd_6803593] using wordTrace_append hprefix tailTrace_6803593
  have hstable : (prefixWord ++ tailWord_6803593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803593).length < 2 ^ (prefixWord ++ tailWord_6803593).sum := by decide
  have hdescent : baseEnd_6803593 < baseStart_6803593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803603 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_6803603 : Nat := 118140960795 + 6803603 * 2 ^ 59
def prefixEnd_6803603 : Nat := 4983230072969 + 3 ^ 40 * 6803603 * 2
def baseEnd_6803603 : Nat := 3493518521371649605673305

theorem tailTrace_6803603 : CollatzResearch.WordTrace tailWord_6803603 prefixEnd_6803603 3493518521371649605673305 := by
  unfold tailWord_6803603
  simp only [CollatzResearch.WordTrace]
  refine ⟨248147787570715768728919463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165431858380477179152612975 248147787570715768728919463)
  ·
    refine ⟨372221681356073653093379195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248147787570715768728919463 372221681356073653093379195)
    ·
      refine ⟨558332522034110479640068793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372221681356073653093379195 558332522034110479640068793)
      ·
        refine ⟨418749391525582859730051595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558332522034110479640068793 418749391525582859730051595)
        ·
          refine ⟨628124087288374289595077393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418749391525582859730051595 628124087288374289595077393)
          ·
            refine ⟨471093065466280717196308045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628124087288374289595077393 471093065466280717196308045)
            ·
              refine ⟨176659899549855268948615517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471093065466280717196308045 176659899549855268948615517)
              ·
                refine ⟨66247462331195725855730819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176659899549855268948615517 66247462331195725855730819)
                ·
                  refine ⟨99371193496793588783596229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66247462331195725855730819 99371193496793588783596229)
                  ·
                    refine ⟨18632098780648797896924293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99371193496793588783596229 18632098780648797896924293)
                    ·
                      refine ⟨3493518521371649605673305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18632098780648797896924293 3493518521371649605673305)
                      ·
                        rfl

theorem cell23_6803603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_6803603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803603 prefixEnd_6803603 := by exact prefixLift 6803603
  have htrace : WordTrace (prefixWord ++ tailWord_6803603) baseStart_6803603 baseEnd_6803603 := by
    simpa [prefixWord, tailWord_6803603, baseEnd_6803603] using wordTrace_append hprefix tailTrace_6803603
  have hstable : (prefixWord ++ tailWord_6803603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803603).length < 2 ^ (prefixWord ++ tailWord_6803603).sum := by decide
  have hdescent : baseEnd_6803603 < baseStart_6803603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803636 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6803636 : Nat := 118140960795 + 6803636 * 2 ^ 59
def prefixEnd_6803636 : Nat := 4983230072969 + 3 ^ 40 * 6803636 * 2
def baseEnd_6803636 : Nat := 3493535466233247976560655

theorem tailTrace_6803636 : CollatzResearch.WordTrace tailWord_6803636 prefixEnd_6803636 3493535466233247976560655 := by
  unfold tailWord_6803636
  simp only [CollatzResearch.WordTrace]
  refine ⟨124074495589798107682435381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165432660786397476909913841 124074495589798107682435381)
  ·
    refine ⟨11631983961543572595228317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124074495589798107682435381 11631983961543572595228317)
    ·
      refine ⟨4361993985578839723210619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11631983961543572595228317 4361993985578839723210619)
      ·
        refine ⟨6542990978368259584815929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361993985578839723210619 6542990978368259584815929)
        ·
          refine ⟨4907243233776194688611947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6542990978368259584815929 4907243233776194688611947)
          ·
            refine ⟨7360864850664292032917921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907243233776194688611947 7360864850664292032917921)
            ·
              refine ⟨5520648637998219024688441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360864850664292032917921 5520648637998219024688441)
              ·
                refine ⟨4140486478498664268516331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520648637998219024688441 4140486478498664268516331)
                ·
                  refine ⟨6210729717747996402774497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140486478498664268516331 6210729717747996402774497)
                  ·
                    refine ⟨4658047288310997302080873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210729717747996402774497 4658047288310997302080873)
                    ·
                      refine ⟨3493535466233247976560655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658047288310997302080873 3493535466233247976560655)
                      ·
                        rfl

theorem cell23_6803636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6803636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803636 prefixEnd_6803636 := by exact prefixLift 6803636
  have htrace : WordTrace (prefixWord ++ tailWord_6803636) baseStart_6803636 baseEnd_6803636 := by
    simpa [prefixWord, tailWord_6803636, baseEnd_6803636] using wordTrace_append hprefix tailTrace_6803636
  have hstable : (prefixWord ++ tailWord_6803636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803636).length < 2 ^ (prefixWord ++ tailWord_6803636).sum := by decide
  have hdescent : baseEnd_6803636 < baseStart_6803636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803640 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_6803640 : Nat := 118140960795 + 6803640 * 2 ^ 59
def prefixEnd_6803640 : Nat := 4983230072969 + 3 ^ 40 * 6803640 * 2
def baseEnd_6803640 : Nat := 3493537520155865960910635

theorem tailTrace_6803640 : CollatzResearch.WordTrace tailWord_6803640 prefixEnd_6803640 3493537520155865960910635 := by
  unfold tailWord_6803640
  simp only [CollatzResearch.WordTrace]
  refine ⟨124074568535790862024008187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165432758047721149365344249 124074568535790862024008187)
  ·
    refine ⟨186111852803686293036012281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124074568535790862024008187 186111852803686293036012281)
    ·
      refine ⟨139583889602764719777009211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186111852803686293036012281 139583889602764719777009211)
      ·
        refine ⟨209375834404147079665513817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139583889602764719777009211 209375834404147079665513817)
        ·
          refine ⟨157031875803110309749135363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209375834404147079665513817 157031875803110309749135363)
          ·
            refine ⟨235547813704665464623703045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157031875803110309749135363 235547813704665464623703045)
            ·
              refine ⟨44165215069624774616944321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235547813704665464623703045 44165215069624774616944321)
              ·
                refine ⟨33123911302218580962708241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44165215069624774616944321 33123911302218580962708241)
                ·
                  refine ⟨24842933476663935722031181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33123911302218580962708241 24842933476663935722031181)
                  ·
                    refine ⟨9316100053748975895761693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24842933476663935722031181 9316100053748975895761693)
                    ·
                      refine ⟨3493537520155865960910635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9316100053748975895761693 3493537520155865960910635)
                      ·
                        rfl

theorem cell23_6803640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_6803640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803640 prefixEnd_6803640 := by exact prefixLift 6803640
  have htrace : WordTrace (prefixWord ++ tailWord_6803640) baseStart_6803640 baseEnd_6803640 := by
    simpa [prefixWord, tailWord_6803640, baseEnd_6803640] using wordTrace_append hprefix tailTrace_6803640
  have hstable : (prefixWord ++ tailWord_6803640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803640).length < 2 ^ (prefixWord ++ tailWord_6803640).sum := by decide
  have hdescent : baseEnd_6803640 < baseStart_6803640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803677 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6803677 : Nat := 118140960795 + 6803677 * 2 ^ 59
def prefixEnd_6803677 : Nat := 4983230072969 + 3 ^ 40 * 6803677 * 2
def baseEnd_6803677 : Nat := 1164518839646694105382655

theorem tailTrace_6803677 : CollatzResearch.WordTrace tailWord_6803677 prefixEnd_6803677 1164518839646694105382655 := by
  unfold tailWord_6803677
  simp only [CollatzResearch.WordTrace]
  refine ⟨248150486572447679367113285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165433657714965119578075523 248150486572447679367113285)
  ·
    refine ⟨46528216232333939881333741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248150486572447679367113285 46528216232333939881333741)
    ·
      refine ⟨17448081087125227455500153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46528216232333939881333741 17448081087125227455500153)
      ·
        refine ⟨13086060815343920591625115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17448081087125227455500153 13086060815343920591625115)
        ·
          refine ⟨19629091223015880887437673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086060815343920591625115 19629091223015880887437673)
          ·
            refine ⟨14721818417261910665578255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19629091223015880887437673 14721818417261910665578255)
            ·
              refine ⟨22082727625892865998367383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14721818417261910665578255 22082727625892865998367383)
              ·
                refine ⟨33124091438839298997551075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22082727625892865998367383 33124091438839298997551075)
                ·
                  refine ⟨49686137158258948496326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33124091438839298997551075 49686137158258948496326613)
                  ·
                    refine ⟨1164518839646694105382655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49686137158258948496326613 1164518839646694105382655)
                    ·
                      rfl

theorem cell23_6803677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6803677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803677 prefixEnd_6803677 := by exact prefixLift 6803677
  have htrace : WordTrace (prefixWord ++ tailWord_6803677) baseStart_6803677 baseEnd_6803677 := by
    simpa [prefixWord, tailWord_6803677, baseEnd_6803677] using wordTrace_append hprefix tailTrace_6803677
  have hstable : (prefixWord ++ tailWord_6803677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803677).length < 2 ^ (prefixWord ++ tailWord_6803677).sum := by decide
  have hdescent : baseEnd_6803677 < baseStart_6803677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803680 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_6803680 : Nat := 118140960795 + 6803680 * 2 ^ 59
def prefixEnd_6803680 : Nat := 4983230072969 + 3 ^ 40 * 6803680 * 2
def baseEnd_6803680 : Nat := 3493558059382045804410451

theorem tailTrace_6803680 : CollatzResearch.WordTrace tailWord_6803680 prefixEnd_6803680 3493558059382045804410451 := by
  unfold tailWord_6803680
  simp only [CollatzResearch.WordTrace]
  refine ⟨124075297995718405439736247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165433730660957873919648329 124075297995718405439736247)
  ·
    refine ⟨186112946993577608159604371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124075297995718405439736247 186112946993577608159604371)
    ·
      refine ⟨279169420490366412239406557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186112946993577608159604371 279169420490366412239406557)
      ·
        refine ⟨104688532683887404589777459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279169420490366412239406557 104688532683887404589777459)
        ·
          refine ⟨157032799025831106884666189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104688532683887404589777459 157032799025831106884666189)
          ·
            refine ⟨58887299634686665081749821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157032799025831106884666189 58887299634686665081749821)
            ·
              refine ⟨22082737363007499405656183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58887299634686665081749821 22082737363007499405656183)
              ·
                refine ⟨33124106044511249108484275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22082737363007499405656183 33124106044511249108484275)
                ·
                  refine ⟨49686159066766873662726413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33124106044511249108484275 49686159066766873662726413)
                  ·
                    refine ⟨18632309650037577623522405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49686159066766873662726413 18632309650037577623522405)
                    ·
                      refine ⟨3493558059382045804410451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18632309650037577623522405 3493558059382045804410451)
                      ·
                        rfl

theorem cell23_6803680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_6803680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803680 prefixEnd_6803680 := by exact prefixLift 6803680
  have htrace : WordTrace (prefixWord ++ tailWord_6803680) baseStart_6803680 baseEnd_6803680 := by
    simpa [prefixWord, tailWord_6803680, baseEnd_6803680] using wordTrace_append hprefix tailTrace_6803680
  have hstable : (prefixWord ++ tailWord_6803680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803680).length < 2 ^ (prefixWord ++ tailWord_6803680).sum := by decide
  have hdescent : baseEnd_6803680 < baseStart_6803680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803697 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_6803697 : Nat := 118140960795 + 6803697 * 2 ^ 59
def prefixEnd_6803697 : Nat := 4983230072969 + 3 ^ 40 * 6803697 * 2
def baseEnd_6803697 : Nat := 3493566788553172237897873

theorem tailTrace_6803697 : CollatzResearch.WordTrace tailWord_6803697 prefixEnd_6803697 3493566788553172237897873 := by
  unfold tailWord_6803697
  simp only [CollatzResearch.WordTrace]
  refine ⟨248151216032375222782841345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165434144021583481855227563 248151216032375222782841345)
  ·
    refine ⟨186113412024281417087131009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248151216032375222782841345 186113412024281417087131009)
    ·
      refine ⟨139585059018211062815348257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186113412024281417087131009 139585059018211062815348257)
      ·
        refine ⟨104688794263658297111511193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139585059018211062815348257 104688794263658297111511193)
        ·
          refine ⟨78516595697743722833633395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104688794263658297111511193 78516595697743722833633395)
          ·
            refine ⟨117774893546615584250450093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78516595697743722833633395 117774893546615584250450093)
            ·
              refine ⟨44165585079980844093918785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117774893546615584250450093 44165585079980844093918785)
              ·
                refine ⟨33124188809985633070439089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44165585079980844093918785 33124188809985633070439089)
                ·
                  refine ⟨24843141607489224802829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33124188809985633070439089 24843141607489224802829317)
                  ·
                    refine ⟨4658089051404229650530497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24843141607489224802829317 4658089051404229650530497)
                    ·
                      refine ⟨3493566788553172237897873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658089051404229650530497 3493566788553172237897873)
                      ·
                        rfl

theorem cell23_6803697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_6803697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803697 prefixEnd_6803697 := by exact prefixLift 6803697
  have htrace : WordTrace (prefixWord ++ tailWord_6803697) baseStart_6803697 baseEnd_6803697 := by
    simpa [prefixWord, tailWord_6803697, baseEnd_6803697] using wordTrace_append hprefix tailTrace_6803697
  have hstable : (prefixWord ++ tailWord_6803697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803697).length < 2 ^ (prefixWord ++ tailWord_6803697).sum := by decide
  have hdescent : baseEnd_6803697 < baseStart_6803697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803758 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6803758 : Nat := 118140960795 + 6803758 * 2 ^ 59
def prefixEnd_6803758 : Nat := 4983230072969 + 3 ^ 40 * 6803758 * 2
def baseEnd_6803758 : Nat := 1164532703624365499745031

theorem tailTrace_6803758 : CollatzResearch.WordTrace tailWord_6803758 prefixEnd_6803758 1164532703624365499745031 := by
  unfold tailWord_6803758
  simp only [CollatzResearch.WordTrace]
  refine ⟨31019180110644278775101491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165435627256769486800541285 31019180110644278775101491)
  ·
    refine ⟨46528770165966418162652237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31019180110644278775101491 46528770165966418162652237)
    ·
      refine ⟨17448288812237406810994589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46528770165966418162652237 17448288812237406810994589)
      ·
        refine ⟨6543108304589027554122971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17448288812237406810994589 6543108304589027554122971)
        ·
          refine ⟨9814662456883541331184457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543108304589027554122971 9814662456883541331184457)
          ·
            refine ⟨7360996842662655998388343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9814662456883541331184457 7360996842662655998388343)
            ·
              refine ⟨11041495263993983997582515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360996842662655998388343 11041495263993983997582515)
              ·
                refine ⟨16562242895990975996373773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041495263993983997582515 16562242895990975996373773)
                ·
                  refine ⟨6210841085996615998640165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16562242895990975996373773 6210841085996615998640165)
                  ·
                    refine ⟨1164532703624365499745031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210841085996615998640165 1164532703624365499745031)
                    ·
                      rfl

theorem cell23_6803758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6803758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803758 prefixEnd_6803758 := by exact prefixLift 6803758
  have htrace : WordTrace (prefixWord ++ tailWord_6803758) baseStart_6803758 baseEnd_6803758 := by
    simpa [prefixWord, tailWord_6803758, baseEnd_6803758] using wordTrace_append hprefix tailTrace_6803758
  have hstable : (prefixWord ++ tailWord_6803758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803758).length < 2 ^ (prefixWord ++ tailWord_6803758).sum := by decide
  have hdescent : baseEnd_6803758 < baseStart_6803758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 4]
def baseStart_6803787 : Nat := 118140960795 + 6803787 * 2 ^ 59
def prefixEnd_6803787 : Nat := 4983230072969 + 3 ^ 40 * 6803787 * 2
def baseEnd_6803787 : Nat := 3493613001812076885772459

theorem tailTrace_6803787 : CollatzResearch.WordTrace tailWord_6803787 prefixEnd_6803787 3493613001812076885772459 := by
  unfold tailWord_6803787
  simp only [CollatzResearch.WordTrace]
  refine ⟨248154498602049168153617615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165436332401366112102411743 248154498602049168153617615)
  ·
    refine ⟨372231747903073752230426423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248154498602049168153617615 372231747903073752230426423)
    ·
      refine ⟨558347621854610628345639635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372231747903073752230426423 558347621854610628345639635)
      ·
        refine ⟨837521432781915942518459453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558347621854610628345639635 837521432781915942518459453)
        ·
          refine ⟨314070537293218478444422295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 837521432781915942518459453 314070537293218478444422295)
          ·
            refine ⟨471105805939827717666633443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314070537293218478444422295 471105805939827717666633443)
            ·
              refine ⟨706658708909741576499950165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471105805939827717666633443 706658708909741576499950165)
              ·
                refine ⟨8281156745036034099608791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 706658708909741576499950165 8281156745036034099608791)
                ·
                  refine ⟨12421735117554051149413187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281156745036034099608791 12421735117554051149413187)
                  ·
                    refine ⟨18632602676331076724119781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12421735117554051149413187 18632602676331076724119781)
                    ·
                      refine ⟨3493613001812076885772459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18632602676331076724119781 3493613001812076885772459)
                      ·
                        rfl

theorem cell23_6803787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 4].length) (baseStart_6803787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803787 prefixEnd_6803787 := by exact prefixLift 6803787
  have htrace : WordTrace (prefixWord ++ tailWord_6803787) baseStart_6803787 baseEnd_6803787 := by
    simpa [prefixWord, tailWord_6803787, baseEnd_6803787] using wordTrace_append hprefix tailTrace_6803787
  have hstable : (prefixWord ++ tailWord_6803787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803787).length < 2 ^ (prefixWord ++ tailWord_6803787).sum := by decide
  have hdescent : baseEnd_6803787 < baseStart_6803787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803800 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6803800 : Nat := 118140960795 + 6803800 * 2 ^ 59
def prefixEnd_6803800 : Nat := 4983230072969 + 3 ^ 40 * 6803800 * 2
def baseEnd_6803800 : Nat := 3493619677060585334909899

theorem tailTrace_6803800 : CollatzResearch.WordTrace tailWord_6803800 prefixEnd_6803800 3493619677060585334909899 := by
  unfold tailWord_6803800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124077486375501035686920427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165436648500668047582560569 124077486375501035686920427)
  ·
    refine ⟨186116229563251553530380641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124077486375501035686920427 186116229563251553530380641)
    ·
      refine ⟨139587172172438665147785481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186116229563251553530380641 139587172172438665147785481)
      ·
        refine ⟨104690379129328998860839111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139587172172438665147785481 104690379129328998860839111)
        ·
          refine ⟨157035568693993498291258667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104690379129328998860839111 157035568693993498291258667)
          ·
            refine ⟨235553353040990247436888001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157035568693993498291258667 235553353040990247436888001)
            ·
              refine ⟨176665014780742685577666001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235553353040990247436888001 176665014780742685577666001)
              ·
                refine ⟨132498761085557014183249501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176665014780742685577666001 132498761085557014183249501)
                ·
                  refine ⟨49687035407083880318718563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132498761085557014183249501 49687035407083880318718563)
                  ·
                    refine ⟨74530553110625820478077845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49687035407083880318718563 74530553110625820478077845)
                    ·
                      refine ⟨3493619677060585334909899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74530553110625820478077845 3493619677060585334909899)
                      ·
                        rfl

theorem cell23_6803800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6803800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803800 prefixEnd_6803800 := by exact prefixLift 6803800
  have htrace : WordTrace (prefixWord ++ tailWord_6803800) baseStart_6803800 baseEnd_6803800 := by
    simpa [prefixWord, tailWord_6803800, baseEnd_6803800] using wordTrace_append hprefix tailTrace_6803800
  have hstable : (prefixWord ++ tailWord_6803800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803800).length < 2 ^ (prefixWord ++ tailWord_6803800).sum := by decide
  have hdescent : baseEnd_6803800 < baseStart_6803800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803807 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_6803807 : Nat := 118140960795 + 6803807 * 2 ^ 59
def prefixEnd_6803807 : Nat := 4983230072969 + 3 ^ 40 * 6803807 * 2
def baseEnd_6803807 : Nat := 3493623271425166807522367

theorem tailTrace_6803807 : CollatzResearch.WordTrace tailWord_6803807 prefixEnd_6803807 3493623271425166807522367 := by
  unfold tailWord_6803807
  simp only [CollatzResearch.WordTrace]
  refine ⟨248155228061976711569345675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165436818707984474379563783 248155228061976711569345675)
  ·
    refine ⟨372232842092965067354018513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248155228061976711569345675 372232842092965067354018513)
    ·
      refine ⟨279174631569723800515513885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372232842092965067354018513 279174631569723800515513885)
      ·
        refine ⟨104690486838646425193317707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279174631569723800515513885 104690486838646425193317707)
        ·
          refine ⟨157035730257969637789976561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104690486838646425193317707 157035730257969637789976561)
          ·
            refine ⟨117776797693477228342482421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157035730257969637789976561 117776797693477228342482421)
            ·
              refine ⟨11041574783763490157107727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117776797693477228342482421 11041574783763490157107727)
              ·
                refine ⟨16562362175645235235661591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041574783763490157107727 16562362175645235235661591)
                ·
                  refine ⟨24843543263467852853492387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16562362175645235235661591 24843543263467852853492387)
                  ·
                    refine ⟨37265314895201779280238581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24843543263467852853492387 37265314895201779280238581)
                    ·
                      refine ⟨3493623271425166807522367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37265314895201779280238581 3493623271425166807522367)
                      ·
                        rfl

theorem cell23_6803807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_6803807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803807 prefixEnd_6803807 := by exact prefixLift 6803807
  have htrace : WordTrace (prefixWord ++ tailWord_6803807) baseStart_6803807 baseEnd_6803807 := by
    simpa [prefixWord, tailWord_6803807, baseEnd_6803807] using wordTrace_append hprefix tailTrace_6803807
  have hstable : (prefixWord ++ tailWord_6803807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803807).length < 2 ^ (prefixWord ++ tailWord_6803807).sum := by decide
  have hdescent : baseEnd_6803807 < baseStart_6803807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803815 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_6803815 : Nat := 118140960795 + 6803815 * 2 ^ 59
def prefixEnd_6803815 : Nat := 4983230072969 + 3 ^ 40 * 6803815 * 2
def baseEnd_6803815 : Nat := 3493627379270402776222331

theorem tailTrace_6803815 : CollatzResearch.WordTrace tailWord_6803815 prefixEnd_6803815 3493627379270402776222331 := by
  unfold tailWord_6803815
  simp only [CollatzResearch.WordTrace]
  refine ⟨248155519845947728935636899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165437013230631819290424599 248155519845947728935636899)
  ·
    refine ⟨372233279768921593403455349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248155519845947728935636899 372233279768921593403455349)
    ·
      refine ⟨34896869978336399381573939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372233279768921593403455349 34896869978336399381573939)
      ·
        refine ⟨52345304967504599072360909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34896869978336399381573939 52345304967504599072360909)
        ·
          refine ⟨19629489362814224652135341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52345304967504599072360909 19629489362814224652135341)
          ·
            refine ⟨7361058511055334244550753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19629489362814224652135341 7361058511055334244550753)
            ·
              refine ⟨5520793883291500683413065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7361058511055334244550753 5520793883291500683413065)
              ·
                refine ⟨4140595412468625512559799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520793883291500683413065 4140595412468625512559799)
                ·
                  refine ⟨6210893118702938268839699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140595412468625512559799 6210893118702938268839699)
                  ·
                    refine ⟨9316339678054407403259549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6210893118702938268839699 9316339678054407403259549)
                    ·
                      refine ⟨3493627379270402776222331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9316339678054407403259549 3493627379270402776222331)
                      ·
                        rfl

theorem cell23_6803815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_6803815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803815 prefixEnd_6803815 := by exact prefixLift 6803815
  have htrace : WordTrace (prefixWord ++ tailWord_6803815) baseStart_6803815 baseEnd_6803815 := by
    simpa [prefixWord, tailWord_6803815, baseEnd_6803815] using wordTrace_append hprefix tailTrace_6803815
  have hstable : (prefixWord ++ tailWord_6803815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803815).length < 2 ^ (prefixWord ++ tailWord_6803815).sum := by decide
  have hdescent : baseEnd_6803815 < baseStart_6803815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803821 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_6803821 : Nat := 118140960795 + 6803821 * 2 ^ 59
def prefixEnd_6803821 : Nat := 4983230072969 + 3 ^ 40 * 6803821 * 2
def baseEnd_6803821 : Nat := 3493630460154329752747303

theorem tailTrace_6803821 : CollatzResearch.WordTrace tailWord_6803821 prefixEnd_6803821 3493630460154329752747303 := by
  unfold tailWord_6803821
  simp only [CollatzResearch.WordTrace]
  refine ⟨248155738683925991960355317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165437159122617327973570211 248155738683925991960355317)
  ·
    refine ⟨23264600501618061746283311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248155738683925991960355317 23264600501618061746283311)
    ·
      refine ⟨34896900752427092619424967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23264600501618061746283311 34896900752427092619424967)
      ·
        refine ⟨52345351128640638929137451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34896900752427092619424967 52345351128640638929137451)
        ·
          refine ⟨78518026692960958393706177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52345351128640638929137451 78518026692960958393706177)
          ·
            refine ⟨58888520019720718795279633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78518026692960958393706177 58888520019720718795279633)
            ·
              refine ⟨44166390014790539096459725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58888520019720718795279633 44166390014790539096459725)
              ·
                refine ⟨16562396255546452161172397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44166390014790539096459725 16562396255546452161172397)
                ·
                  refine ⟨6210898595829919560439649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16562396255546452161172397 6210898595829919560439649)
                  ·
                    refine ⟨4658173946872439670329737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210898595829919560439649 4658173946872439670329737)
                    ·
                      refine ⟨3493630460154329752747303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658173946872439670329737 3493630460154329752747303)
                      ·
                        rfl

theorem cell23_6803821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_6803821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803821 prefixEnd_6803821 := by exact prefixLift 6803821
  have htrace : WordTrace (prefixWord ++ tailWord_6803821) baseStart_6803821 baseEnd_6803821 := by
    simpa [prefixWord, tailWord_6803821, baseEnd_6803821] using wordTrace_append hprefix tailTrace_6803821
  have hstable : (prefixWord ++ tailWord_6803821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803821).length < 2 ^ (prefixWord ++ tailWord_6803821).sum := by decide
  have hdescent : baseEnd_6803821 < baseStart_6803821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803842 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6803842 : Nat := 118140960795 + 6803842 * 2 ^ 59
def prefixEnd_6803842 : Nat := 4983230072969 + 3 ^ 40 * 6803842 * 2
def baseEnd_6803842 : Nat := 3493641243248074170584707

theorem tailTrace_6803842 : CollatzResearch.WordTrace tailWord_6803842 prefixEnd_6803842 3493641243248074170584707 := by
  unfold tailWord_6803842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62039126154212478136717445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165437669744566608364579853 62039126154212478136717445)
  ·
    refine ⟨11632336153914839650634521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62039126154212478136717445 11632336153914839650634521)
    ·
      refine ⟨8724252115436129737975891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11632336153914839650634521 8724252115436129737975891)
      ·
        refine ⟨13086378173154194606963837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724252115436129737975891 13086378173154194606963837)
        ·
          refine ⟨4907391814932822977611439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13086378173154194606963837 4907391814932822977611439)
          ·
            refine ⟨7361087722399234466417159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907391814932822977611439 7361087722399234466417159)
            ·
              refine ⟨11041631583598851699625739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361087722399234466417159 11041631583598851699625739)
              ·
                refine ⟨16562447375398277549438609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041631583598851699625739 16562447375398277549438609)
                ·
                  refine ⟨12421835531548708162078957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16562447375398277549438609 12421835531548708162078957)
                  ·
                    refine ⟨4658188324330765560779609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12421835531548708162078957 4658188324330765560779609)
                    ·
                      refine ⟨3493641243248074170584707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658188324330765560779609 3493641243248074170584707)
                      ·
                        rfl

theorem cell23_6803842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6803842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803842 prefixEnd_6803842 := by exact prefixLift 6803842
  have htrace : WordTrace (prefixWord ++ tailWord_6803842) baseStart_6803842 baseEnd_6803842 := by
    simpa [prefixWord, tailWord_6803842, baseEnd_6803842] using wordTrace_append hprefix tailTrace_6803842
  have hstable : (prefixWord ++ tailWord_6803842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803842).length < 2 ^ (prefixWord ++ tailWord_6803842).sum := by decide
  have hdescent : baseEnd_6803842 < baseStart_6803842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803882 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6803882 : Nat := 118140960795 + 6803882 * 2 ^ 59
def prefixEnd_6803882 : Nat := 4983230072969 + 3 ^ 40 * 6803882 * 2
def baseEnd_6803882 : Nat := 1164553927491418004694841

theorem tailTrace_6803882 : CollatzResearch.WordTrace tailWord_6803882 prefixEnd_6803882 1164553927491418004694841 := by
  unfold tailWord_6803882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62039490884176249844581475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165438642357803332918883933 62039490884176249844581475)
  ·
    refine ⟨93059236326264374766872213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62039490884176249844581475 93059236326264374766872213)
    ·
      refine ⟨4362151702793642567197135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93059236326264374766872213 4362151702793642567197135)
      ·
        refine ⟨6543227554190463850795703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362151702793642567197135 6543227554190463850795703)
        ·
          refine ⟨9814841331285695776193555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543227554190463850795703 9814841331285695776193555)
          ·
            refine ⟨14722261996928543664290333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814841331285695776193555 14722261996928543664290333)
            ·
              refine ⟨5520848248848203874108875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14722261996928543664290333 5520848248848203874108875)
              ·
                refine ⟨8281272373272305811163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520848248848203874108875 8281272373272305811163313)
                ·
                  refine ⟨6210954279954229358372485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8281272373272305811163313 6210954279954229358372485)
                  ·
                    refine ⟨1164553927491418004694841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6210954279954229358372485 1164553927491418004694841)
                    ·
                      rfl

theorem cell23_6803882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6803882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803882 prefixEnd_6803882 := by exact prefixLift 6803882
  have htrace : WordTrace (prefixWord ++ tailWord_6803882) baseStart_6803882 baseEnd_6803882 := by
    simpa [prefixWord, tailWord_6803882, baseEnd_6803882] using wordTrace_append hprefix tailTrace_6803882
  have hstable : (prefixWord ++ tailWord_6803882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803882).length < 2 ^ (prefixWord ++ tailWord_6803882).sum := by decide
  have hdescent : baseEnd_6803882 < baseStart_6803882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803911 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_6803911 : Nat := 118140960795 + 6803911 * 2 ^ 59
def prefixEnd_6803911 : Nat := 4983230072969 + 3 ^ 40 * 6803911 * 2
def baseEnd_6803911 : Nat := 3493676673413234400621889

theorem tailTrace_6803911 : CollatzResearch.WordTrace tailWord_6803911 prefixEnd_6803911 3493676673413234400621889 := by
  unfold tailWord_6803911
  simp only [CollatzResearch.WordTrace]
  refine ⟨248159021253599937331131587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165439347502399958220754391 248159021253599937331131587)
  ·
    refine ⟨372238531880399905996697381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248159021253599937331131587 372238531880399905996697381)
    ·
      refine ⟨69794724727574982374380759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372238531880399905996697381 69794724727574982374380759)
      ·
        refine ⟨104692087091362473561571139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69794724727574982374380759 104692087091362473561571139)
        ·
          refine ⟨157038130637043710342356709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104692087091362473561571139 157038130637043710342356709)
          ·
            refine ⟨29444649494445695689191883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157038130637043710342356709 29444649494445695689191883)
            ·
              refine ⟨44166974241668543533787825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29444649494445695689191883 44166974241668543533787825)
              ·
                refine ⟨33125230681251407650340869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44166974241668543533787825 33125230681251407650340869)
                ·
                  refine ⟨6210980752734638934438913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33125230681251407650340869 6210980752734638934438913)
                  ·
                    refine ⟨4658235564550979200829185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210980752734638934438913 4658235564550979200829185)
                    ·
                      refine ⟨3493676673413234400621889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658235564550979200829185 3493676673413234400621889)
                      ·
                        rfl

theorem cell23_6803911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_6803911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803911 prefixEnd_6803911 := by exact prefixLift 6803911
  have htrace : WordTrace (prefixWord ++ tailWord_6803911) baseStart_6803911 baseEnd_6803911 := by
    simpa [prefixWord, tailWord_6803911, baseEnd_6803911] using wordTrace_append hprefix tailTrace_6803911
  have hstable : (prefixWord ++ tailWord_6803911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803911).length < 2 ^ (prefixWord ++ tailWord_6803911).sum := by decide
  have hdescent : baseEnd_6803911 < baseStart_6803911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803947 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 4, 5]
def baseStart_6803947 : Nat := 118140960795 + 6803947 * 2 ^ 59
def prefixEnd_6803947 : Nat := 4983230072969 + 3 ^ 40 * 6803947 * 2
def baseEnd_6803947 : Nat := 1164565052905598753257241

theorem tailTrace_6803947 : CollatzResearch.WordTrace tailWord_6803947 prefixEnd_6803947 1164565052905598753257241 := by
  unfold tailWord_6803947
  simp only [CollatzResearch.WordTrace]
  refine ⟨248160334281469515479442095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165440222854313010319628063 248160334281469515479442095)
  ·
    refine ⟨372240501422204273219163143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248160334281469515479442095 372240501422204273219163143)
    ·
      refine ⟨558360752133306409828744715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372240501422204273219163143 558360752133306409828744715)
      ·
        refine ⟨837541128199959614743117073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558360752133306409828744715 837541128199959614743117073)
        ·
          refine ⟨628155846149969711057337805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837541128199959614743117073 628155846149969711057337805)
          ·
            refine ⟨235558442306238641646501677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628155846149969711057337805 235558442306238641646501677)
            ·
              refine ⟨88334415864839490617438129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235558442306238641646501677 88334415864839490617438129)
              ·
                refine ⟨66250811898629617963078597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88334415864839490617438129 66250811898629617963078597)
                ·
                  refine ⟨12422027230993053368077237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66250811898629617963078597 12422027230993053368077237)
                  ·
                    refine ⟨1164565052905598753257241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12422027230993053368077237 1164565052905598753257241)
                    ·
                      rfl

theorem cell23_6803947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].length) (baseStart_6803947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803947 prefixEnd_6803947 := by exact prefixLift 6803947
  have htrace : WordTrace (prefixWord ++ tailWord_6803947) baseStart_6803947 baseEnd_6803947 := by
    simpa [prefixWord, tailWord_6803947, baseEnd_6803947] using wordTrace_append hprefix tailTrace_6803947
  have hstable : (prefixWord ++ tailWord_6803947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803947).length < 2 ^ (prefixWord ++ tailWord_6803947).sum := by decide
  have hdescent : baseEnd_6803947 < baseStart_6803947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803987 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_6803987 : Nat := 118140960795 + 6803987 * 2 ^ 59
def prefixEnd_6803987 : Nat := 4983230072969 + 3 ^ 40 * 6803987 * 2
def baseEnd_6803987 : Nat := 3493715697942976103271539

theorem tailTrace_6803987 : CollatzResearch.WordTrace tailWord_6803987 prefixEnd_6803987 3493715697942976103271539 := by
  unfold tailWord_6803987
  simp only [CollatzResearch.WordTrace]
  refine ⟨248161793201324602310898215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165441195467549734873932143 248161793201324602310898215)
  ·
    refine ⟨372242689801986903466347323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248161793201324602310898215 372242689801986903466347323)
    ·
      refine ⟨558364034702980355199520985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372242689801986903466347323 558364034702980355199520985)
      ·
        refine ⟨418773026027235266399640739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558364034702980355199520985 418773026027235266399640739)
        ·
          refine ⟨628159539040852899599461109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418773026027235266399640739 628159539040852899599461109)
          ·
            refine ⟨58889956785079959337449479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 628159539040852899599461109 58889956785079959337449479)
            ·
              refine ⟨88334935177619939006174219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58889956785079959337449479 88334935177619939006174219)
              ·
                refine ⟨132502402766429908509261329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88334935177619939006174219 132502402766429908509261329)
                ·
                  refine ⟨99376802074822431381945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132502402766429908509261329 99376802074822431381945997)
                  ·
                    refine ⟨37266300778058411768229749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99376802074822431381945997 37266300778058411768229749)
                    ·
                      refine ⟨3493715697942976103271539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37266300778058411768229749 3493715697942976103271539)
                      ·
                        rfl

theorem cell23_6803987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_6803987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803987 prefixEnd_6803987 := by exact prefixLift 6803987
  have htrace : WordTrace (prefixWord ++ tailWord_6803987) baseStart_6803987 baseEnd_6803987 := by
    simpa [prefixWord, tailWord_6803987, baseEnd_6803987] using wordTrace_append hprefix tailTrace_6803987
  have hstable : (prefixWord ++ tailWord_6803987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803987).length < 2 ^ (prefixWord ++ tailWord_6803987).sum := by decide
  have hdescent : baseEnd_6803987 < baseStart_6803987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6803988 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6803988 : Nat := 118140960795 + 6803988 * 2 ^ 59
def prefixEnd_6803988 : Nat := 4983230072969 + 3 ^ 40 * 6803988 * 2
def baseEnd_6803988 : Nat := 3493716211423630599359035

theorem tailTrace_6803988 : CollatzResearch.WordTrace tailWord_6803988 prefixEnd_6803988 3493716211423630599359035 := by
  unfold tailWord_6803988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124080914837160489740842309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165441219782880652987789745 124080914837160489740842309)
  ·
    refine ⟨23265171531967591826407933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124080914837160489740842309 23265171531967591826407933)
    ·
      refine ⟨8724439324487846934902975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23265171531967591826407933 8724439324487846934902975)
      ·
        refine ⟨13086658986731770402354463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724439324487846934902975 13086658986731770402354463)
        ·
          refine ⟨19629988480097655603531695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086658986731770402354463 19629988480097655603531695)
          ·
            refine ⟨29444982720146483405297543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19629988480097655603531695 29444982720146483405297543)
            ·
              refine ⟨44167474080219725107946315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29444982720146483405297543 44167474080219725107946315)
              ·
                refine ⟨66251211120329587661919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44167474080219725107946315 66251211120329587661919473)
                ·
                  refine ⟨49688408340247190746439605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66251211120329587661919473 49688408340247190746439605)
                  ·
                    refine ⟨4658288281898174132478713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49688408340247190746439605 4658288281898174132478713)
                    ·
                      refine ⟨3493716211423630599359035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658288281898174132478713 3493716211423630599359035)
                      ·
                        rfl

theorem cell23_6803988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6803988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6803988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6803988 prefixEnd_6803988 := by exact prefixLift 6803988
  have htrace : WordTrace (prefixWord ++ tailWord_6803988) baseStart_6803988 baseEnd_6803988 := by
    simpa [prefixWord, tailWord_6803988, baseEnd_6803988] using wordTrace_append hprefix tailTrace_6803988
  have hstable : (prefixWord ++ tailWord_6803988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6803988).length < 2 ^ (prefixWord ++ tailWord_6803988).sum := by decide
  have hdescent : baseEnd_6803988 < baseStart_6803988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6803988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804001 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6804001 : Nat := 118140960795 + 6804001 * 2 ^ 59
def prefixEnd_6804001 : Nat := 4983230072969 + 3 ^ 40 * 6804001 * 2
def baseEnd_6804001 : Nat := 3493722886672139048496475

theorem tailTrace_6804001 : CollatzResearch.WordTrace tailWord_6804001 prefixEnd_6804001 3493722886672139048496475 := by
  unfold tailWord_6804001
  simp only [CollatzResearch.WordTrace]
  refine ⟨248162303823273882701907857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165441535882182588467938571 248162303823273882701907857)
  ·
    refine ⟨186121727867455412026430893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248162303823273882701907857 186121727867455412026430893)
    ·
      refine ⟨69795647950295779509911585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186121727867455412026430893 69795647950295779509911585)
      ·
        refine ⟨52346735962721834632433689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69795647950295779509911585 52346735962721834632433689)
        ·
          refine ⟨39260051972041375974325267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52346735962721834632433689 39260051972041375974325267)
          ·
            refine ⟨58890077958062063961487901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39260051972041375974325267 58890077958062063961487901)
            ·
              refine ⟨22083779234273273985557963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58890077958062063961487901 22083779234273273985557963)
              ·
                refine ⟨33125668851409910978336945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22083779234273273985557963 33125668851409910978336945)
                ·
                  refine ⟨24844251638557433233752709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33125668851409910978336945 24844251638557433233752709)
                  ·
                    refine ⟨4658297182229518731328633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24844251638557433233752709 4658297182229518731328633)
                    ·
                      refine ⟨3493722886672139048496475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658297182229518731328633 3493722886672139048496475)
                      ·
                        rfl

theorem cell23_6804001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6804001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804001 prefixEnd_6804001 := by exact prefixLift 6804001
  have htrace : WordTrace (prefixWord ++ tailWord_6804001) baseStart_6804001 baseEnd_6804001 := by
    simpa [prefixWord, tailWord_6804001, baseEnd_6804001] using wordTrace_append hprefix tailTrace_6804001
  have hstable : (prefixWord ++ tailWord_6804001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804001).length < 2 ^ (prefixWord ++ tailWord_6804001).sum := by decide
  have hdescent : baseEnd_6804001 < baseStart_6804001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804028 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_6804028 : Nat := 118140960795 + 6804028 * 2 ^ 59
def prefixEnd_6804028 : Nat := 4983230072969 + 3 ^ 40 * 6804028 * 2
def baseEnd_6804028 : Nat := 1164578916883270147619617

theorem tailTrace_6804028 : CollatzResearch.WordTrace tailWord_6804028 prefixEnd_6804028 1164578916883270147619617 := by
  unfold tailWord_6804028
  simp only [CollatzResearch.WordTrace]
  refine ⟨124081644297088033156570369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165442192396117377542093825 124081644297088033156570369)
  ·
    refine ⟨93061233222816024867427777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124081644297088033156570369 93061233222816024867427777)
    ·
      refine ⟨69795924917112018650570833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93061233222816024867427777 69795924917112018650570833)
      ·
        refine ⟨52346943687834013987928125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69795924917112018650570833 52346943687834013987928125)
        ·
          refine ⟨19630103882937755245473047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52346943687834013987928125 19630103882937755245473047)
          ·
            refine ⟨29445155824406632868209571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19630103882937755245473047 29445155824406632868209571)
            ·
              refine ⟨44167733736609949302314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29445155824406632868209571 44167733736609949302314357)
              ·
                refine ⟨4140725037807182747091971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44167733736609949302314357 4140725037807182747091971)
                ·
                  refine ⟨6211087556710774120637957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140725037807182747091971 6211087556710774120637957)
                  ·
                    refine ⟨1164578916883270147619617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211087556710774120637957 1164578916883270147619617)
                    ·
                      rfl

theorem cell23_6804028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_6804028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804028 prefixEnd_6804028 := by exact prefixLift 6804028
  have htrace : WordTrace (prefixWord ++ tailWord_6804028) baseStart_6804028 baseEnd_6804028 := by
    simpa [prefixWord, tailWord_6804028, baseEnd_6804028] using wordTrace_append hprefix tailTrace_6804028
  have hstable : (prefixWord ++ tailWord_6804028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804028).length < 2 ^ (prefixWord ++ tailWord_6804028).sum := by decide
  have hdescent : baseEnd_6804028 < baseStart_6804028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804045 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6804045 : Nat := 118140960795 + 6804045 * 2 ^ 59
def prefixEnd_6804045 : Nat := 4983230072969 + 3 ^ 40 * 6804045 * 2
def baseEnd_6804045 : Nat := 1164581826606978958782091

theorem tailTrace_6804045 : CollatzResearch.WordTrace tailWord_6804045 prefixEnd_6804045 1164581826606978958782091 := by
  unfold tailWord_6804045
  simp only [CollatzResearch.WordTrace]
  refine ⟨248163908635114478216509589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165442605756742985477673059 248163908635114478216509589)
  ·
    refine ⟨11632683217270991166398887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248163908635114478216509589 11632683217270991166398887)
    ·
      refine ⟨17449024825906486749598331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11632683217270991166398887 17449024825906486749598331)
      ·
        refine ⟨26173537238859730124397497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17449024825906486749598331 26173537238859730124397497)
        ·
          refine ⟨19630152929144797593298123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26173537238859730124397497 19630152929144797593298123)
          ·
            refine ⟨29445229393717196389947185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19630152929144797593298123 29445229393717196389947185)
            ·
              refine ⟨22083922045287897292460389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29445229393717196389947185 22083922045287897292460389)
              ·
                refine ⟨4140735383491480742336323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22083922045287897292460389 4140735383491480742336323)
                ·
                  refine ⟨6211103075237221113504485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140735383491480742336323 6211103075237221113504485)
                  ·
                    refine ⟨1164581826606978958782091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211103075237221113504485 1164581826606978958782091)
                    ·
                      rfl

theorem cell23_6804045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6804045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804045 prefixEnd_6804045 := by exact prefixLift 6804045
  have htrace : WordTrace (prefixWord ++ tailWord_6804045) baseStart_6804045 baseEnd_6804045 := by
    simpa [prefixWord, tailWord_6804045, baseEnd_6804045] using wordTrace_append hprefix tailTrace_6804045
  have hstable : (prefixWord ++ tailWord_6804045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804045).length < 2 ^ (prefixWord ++ tailWord_6804045).sum := by decide
  have hdescent : baseEnd_6804045 < baseStart_6804045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804078 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6804078 : Nat := 118140960795 + 6804078 * 2 ^ 59
def prefixEnd_6804078 : Nat := 4983230072969 + 3 ^ 40 * 6804078 * 2
def baseEnd_6804078 : Nat := 3493762424682535247233621

theorem tailTrace_6804078 : CollatzResearch.WordTrace tailWord_6804078 prefixEnd_6804078 3493762424682535247233621 := by
  unfold tailWord_6804078
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020639030499365606557611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165443408162663283234973925 31020639030499365606557611)
  ·
    refine ⟨46530958545749048409836417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31020639030499365606557611 46530958545749048409836417)
    ·
      refine ⟨34898218909311786307377313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46530958545749048409836417 34898218909311786307377313)
      ·
        refine ⟨26173664181983839730532985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34898218909311786307377313 26173664181983839730532985)
        ·
          refine ⟨19630248136487879797899739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26173664181983839730532985 19630248136487879797899739)
          ·
            refine ⟨29445372204731819696849609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19630248136487879797899739 29445372204731819696849609)
            ·
              refine ⟨22084029153548864772637207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29445372204731819696849609 22084029153548864772637207)
              ·
                refine ⟨33126043730323297158955811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22084029153548864772637207 33126043730323297158955811)
                ·
                  refine ⟨49689065595484945738433717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33126043730323297158955811 49689065595484945738433717)
                  ·
                    refine ⟨4658349899576713662978161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49689065595484945738433717 4658349899576713662978161)
                    ·
                      refine ⟨3493762424682535247233621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658349899576713662978161 3493762424682535247233621)
                      ·
                        rfl

theorem cell23_6804078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6804078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804078 prefixEnd_6804078 := by exact prefixLift 6804078
  have htrace : WordTrace (prefixWord ++ tailWord_6804078) baseStart_6804078 baseEnd_6804078 := by
    simpa [prefixWord, tailWord_6804078, baseEnd_6804078] using wordTrace_append hprefix tailTrace_6804078
  have hstable : (prefixWord ++ tailWord_6804078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804078).length < 2 ^ (prefixWord ++ tailWord_6804078).sum := by decide
  have hdescent : baseEnd_6804078 < baseStart_6804078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804101 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_6804101 : Nat := 118140960795 + 6804101 * 2 ^ 59
def prefixEnd_6804101 : Nat := 4983230072969 + 3 ^ 40 * 6804101 * 2
def baseEnd_6804101 : Nat := 1164591411579196219082005

theorem tailTrace_6804101 : CollatzResearch.WordTrace tailWord_6804101 prefixEnd_6804101 1164591411579196219082005 := by
  unfold tailWord_6804101
  simp only [CollatzResearch.WordTrace]
  refine ⟨248165951122911599780548157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165443967415274399853698771 248165951122911599780548157)
  ·
    refine ⟨93062231671091849917705559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248165951122911599780548157 93062231671091849917705559)
    ·
      refine ⟨139593347506637774876558339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93062231671091849917705559 139593347506637774876558339)
      ·
        refine ⟨209390021259956662314837509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139593347506637774876558339 209390021259956662314837509)
        ·
          refine ⟨39260628986241874184032033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209390021259956662314837509 39260628986241874184032033)
          ·
            refine ⟨29445471739681405638024025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39260628986241874184032033 29445471739681405638024025)
            ·
              refine ⟨22084103804761054228518019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29445471739681405638024025 22084103804761054228518019)
              ·
                refine ⟨33126155707141581342777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22084103804761054228518019 33126155707141581342777029)
                ·
                  refine ⟨6211154195089046501770693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33126155707141581342777029 6211154195089046501770693)
                  ·
                    refine ⟨1164591411579196219082005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211154195089046501770693 1164591411579196219082005)
                    ·
                      rfl

theorem cell23_6804101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_6804101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804101 prefixEnd_6804101 := by exact prefixLift 6804101
  have htrace : WordTrace (prefixWord ++ tailWord_6804101) baseStart_6804101 baseEnd_6804101 := by
    simpa [prefixWord, tailWord_6804101, baseEnd_6804101] using wordTrace_append hprefix tailTrace_6804101
  have hstable : (prefixWord ++ tailWord_6804101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804101).length < 2 ^ (prefixWord ++ tailWord_6804101).sum := by decide
  have hdescent : baseEnd_6804101 < baseStart_6804101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804108 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_6804108 : Nat := 118140960795 + 6804108 * 2 ^ 59
def prefixEnd_6804108 : Nat := 4983230072969 + 3 ^ 40 * 6804108 * 2
def baseEnd_6804108 : Nat := 3493777829102170129858483

theorem tailTrace_6804108 : CollatzResearch.WordTrace tailWord_6804108 prefixEnd_6804108 3493777829102170129858483 := by
  unfold tailWord_6804108
  simp only [CollatzResearch.WordTrace]
  refine ⟨124083103216943119988026489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165444137622590826650701985 124083103216943119988026489)
  ·
    refine ⟨93062327412707339991019867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124083103216943119988026489 93062327412707339991019867)
    ·
      refine ⟨139593491119061009986529801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93062327412707339991019867 139593491119061009986529801)
      ·
        refine ⟨104695118339295757489897351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139593491119061009986529801 104695118339295757489897351)
        ·
          refine ⟨157042677508943636234846027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104695118339295757489897351 157042677508943636234846027)
          ·
            refine ⟨235564016263415454352269041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157042677508943636234846027 235564016263415454352269041)
            ·
              refine ⟨176673012197561590764201781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235564016263415454352269041 176673012197561590764201781)
              ·
                refine ⟨16563094893521399134143917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176673012197561590764201781 16563094893521399134143917)
                ·
                  refine ⟨6211160585070524675303969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16563094893521399134143917 6211160585070524675303969)
                  ·
                    refine ⟨4658370438802893506477977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211160585070524675303969 4658370438802893506477977)
                    ·
                      refine ⟨3493777829102170129858483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658370438802893506477977 3493777829102170129858483)
                      ·
                        rfl

theorem cell23_6804108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_6804108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804108 prefixEnd_6804108 := by exact prefixLift 6804108
  have htrace : WordTrace (prefixWord ++ tailWord_6804108) baseStart_6804108 baseEnd_6804108 := by
    simpa [prefixWord, tailWord_6804108, baseEnd_6804108] using wordTrace_append hprefix tailTrace_6804108
  have hstable : (prefixWord ++ tailWord_6804108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804108).length < 2 ^ (prefixWord ++ tailWord_6804108).sum := by decide
  have hdescent : baseEnd_6804108 < baseStart_6804108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804122 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_6804122 : Nat := 118140960795 + 6804122 * 2 ^ 59
def prefixEnd_6804122 : Nat := 4983230072969 + 3 ^ 40 * 6804122 * 2
def baseEnd_6804122 : Nat := 1164595005943777691694473

theorem tailTrace_6804122 : CollatzResearch.WordTrace tailWord_6804122 prefixEnd_6804122 1164595005943777691694473 := by
  unfold tailWord_6804122
  simp only [CollatzResearch.WordTrace]
  refine ⟨62041679263958880091765655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165444478037223680244708413 62041679263958880091765655)
  ·
    refine ⟨93062518895938320137648483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62041679263958880091765655 93062518895938320137648483)
    ·
      refine ⟨139593778343907480206472725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93062518895938320137648483 139593778343907480206472725)
      ·
        refine ⟨6543458359870663134678409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139593778343907480206472725 6543458359870663134678409)
        ·
          refine ⟨4907593769902997351008807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6543458359870663134678409 4907593769902997351008807)
          ·
            refine ⟨7361390654854496026513211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907593769902997351008807 7361390654854496026513211)
            ·
              refine ⟨11042085982281744039769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361390654854496026513211 11042085982281744039769817)
              ·
                refine ⟨8281564486711308029827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11042085982281744039769817 8281564486711308029827363)
                ·
                  refine ⟨12422346730066962044741045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281564486711308029827363 12422346730066962044741045)
                  ·
                    refine ⟨1164595005943777691694473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12422346730066962044741045 1164595005943777691694473)
                    ·
                      rfl

theorem cell23_6804122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_6804122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804122 prefixEnd_6804122 := by exact prefixLift 6804122
  have htrace : WordTrace (prefixWord ++ tailWord_6804122) baseStart_6804122 baseEnd_6804122 := by
    simpa [prefixWord, tailWord_6804122, baseEnd_6804122] using wordTrace_append hprefix tailTrace_6804122
  have hstable : (prefixWord ++ tailWord_6804122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804122).length < 2 ^ (prefixWord ++ tailWord_6804122).sum := by decide
  have hdescent : baseEnd_6804122 < baseStart_6804122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804128 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_6804128 : Nat := 118140960795 + 6804128 * 2 ^ 59
def prefixEnd_6804128 : Nat := 4983230072969 + 3 ^ 40 * 6804128 * 2
def baseEnd_6804128 : Nat := 3493788098715260051608391

theorem tailTrace_6804128 : CollatzResearch.WordTrace tailWord_6804128 prefixEnd_6804128 3493788098715260051608391 := by
  unfold tailWord_6804128
  simp only [CollatzResearch.WordTrace]
  refine ⟨124083467946906891695890519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165444623929209188927854025 124083467946906891695890519)
  ·
    refine ⟨186125201920360337543835779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124083467946906891695890519 186125201920360337543835779)
    ·
      refine ⟨279187802880540506315753669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186125201920360337543835779 279187802880540506315753669)
      ·
        refine ⟨52347713040101344934203813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279187802880540506315753669 52347713040101344934203813)
        ·
          refine ⟨9815196195019002175163215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52347713040101344934203813 9815196195019002175163215)
          ·
            refine ⟨14722794292528503262744823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815196195019002175163215 14722794292528503262744823)
            ·
              refine ⟨22084191438792754894117235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14722794292528503262744823 22084191438792754894117235)
              ·
                refine ⟨33126287158189132341175853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22084191438792754894117235 33126287158189132341175853)
                ·
                  refine ⟨12422357684320924627940945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33126287158189132341175853 12422357684320924627940945)
                  ·
                    refine ⟨9316768263240693470955709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12422357684320924627940945 9316768263240693470955709)
                    ·
                      refine ⟨3493788098715260051608391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9316768263240693470955709 3493788098715260051608391)
                      ·
                        rfl

theorem cell23_6804128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_6804128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804128 prefixEnd_6804128 := by exact prefixLift 6804128
  have htrace : WordTrace (prefixWord ++ tailWord_6804128) baseStart_6804128 baseEnd_6804128 := by
    simpa [prefixWord, tailWord_6804128, baseEnd_6804128] using wordTrace_append hprefix tailTrace_6804128
  have hstable : (prefixWord ++ tailWord_6804128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804128).length < 2 ^ (prefixWord ++ tailWord_6804128).sum := by decide
  have hdescent : baseEnd_6804128 < baseStart_6804128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804142 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6804142 : Nat := 118140960795 + 6804142 * 2 ^ 59
def prefixEnd_6804142 : Nat := 4983230072969 + 3 ^ 40 * 6804142 * 2
def baseEnd_6804142 : Nat := 3493795287444422996833327

theorem tailTrace_6804142 : CollatzResearch.WordTrace tailWord_6804142 prefixEnd_6804142 3493795287444422996833327 := by
  unfold tailWord_6804142
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020930814470382972848835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165444964343842042521860453 31020930814470382972848835)
  ·
    refine ⟨46531396221705574459273253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31020930814470382972848835 46531396221705574459273253)
    ·
      refine ⟨8724636791569795211113735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46531396221705574459273253 8724636791569795211113735)
      ·
        refine ⟨13086955187354692816670603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724636791569795211113735 13086955187354692816670603)
        ·
          refine ⟨19630432781032039225005905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086955187354692816670603 19630432781032039225005905)
          ·
            refine ⟨14722824585774029418754429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19630432781032039225005905 14722824585774029418754429)
            ·
              refine ⟨5521059219665261032032911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14722824585774029418754429 5521059219665261032032911)
              ·
                refine ⟨8281588829497891548049367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521059219665261032032911 8281588829497891548049367)
                ·
                  refine ⟨12422383244246837322074051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281588829497891548049367 12422383244246837322074051)
                  ·
                    refine ⟨18633574866370255983111077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12422383244246837322074051 18633574866370255983111077)
                    ·
                      refine ⟨3493795287444422996833327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18633574866370255983111077 3493795287444422996833327)
                      ·
                        rfl

theorem cell23_6804142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6804142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804142 prefixEnd_6804142 := by exact prefixLift 6804142
  have htrace : WordTrace (prefixWord ++ tailWord_6804142) baseStart_6804142 baseEnd_6804142 := by
    simpa [prefixWord, tailWord_6804142, baseEnd_6804142] using wordTrace_append hprefix tailTrace_6804142
  have hstable : (prefixWord ++ tailWord_6804142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804142).length < 2 ^ (prefixWord ++ tailWord_6804142).sum := by decide
  have hdescent : baseEnd_6804142 < baseStart_6804142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804145 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6804145 : Nat := 118140960795 + 6804145 * 2 ^ 59
def prefixEnd_6804145 : Nat := 4983230072969 + 3 ^ 40 * 6804145 * 2
def baseEnd_6804145 : Nat := 3493796827886386485095813

theorem tailTrace_6804145 : CollatzResearch.WordTrace tailWord_6804145 prefixEnd_6804145 3493796827886386485095813 := by
  unfold tailWord_6804145
  simp only [CollatzResearch.WordTrace]
  refine ⟨248167555934752195295149889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165445037289834796863433259 248167555934752195295149889)
  ·
    refine ⟨186125666951064146471362417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248167555934752195295149889 186125666951064146471362417)
    ·
      refine ⟨139594250213298109853521813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186125666951064146471362417 139594250213298109853521813)
      ·
        refine ⟨6543480478748348899383835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139594250213298109853521813 6543480478748348899383835)
        ·
          refine ⟨9815220718122523349075753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543480478748348899383835 9815220718122523349075753)
          ·
            refine ⟨7361415538591892511806815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815220718122523349075753 7361415538591892511806815)
            ·
              refine ⟨11042123307887838767710223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361415538591892511806815 11042123307887838767710223)
              ·
                refine ⟨16563184961831758151565335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11042123307887838767710223 16563184961831758151565335)
                ·
                  refine ⟨24844777442747637227348003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16563184961831758151565335 24844777442747637227348003)
                  ·
                    refine ⟨37267166164121455841022005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24844777442747637227348003 37267166164121455841022005)
                    ·
                      refine ⟨3493796827886386485095813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37267166164121455841022005 3493796827886386485095813)
                      ·
                        rfl

theorem cell23_6804145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6804145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804145 prefixEnd_6804145 := by exact prefixLift 6804145
  have htrace : WordTrace (prefixWord ++ tailWord_6804145) baseStart_6804145 baseEnd_6804145 := by
    simpa [prefixWord, tailWord_6804145, baseEnd_6804145] using wordTrace_append hprefix tailTrace_6804145
  have hstable : (prefixWord ++ tailWord_6804145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804145).length < 2 ^ (prefixWord ++ tailWord_6804145).sum := by decide
  have hdescent : baseEnd_6804145 < baseStart_6804145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804159 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 1, 2, 2]
def baseStart_6804159 : Nat := 118140960795 + 6804159 * 2 ^ 59
def prefixEnd_6804159 : Nat := 4983230072969 + 3 ^ 40 * 6804159 * 2
def baseEnd_6804159 : Nat := 3493804016615549430320749

theorem tailTrace_6804159 : CollatzResearch.WordTrace tailWord_6804159 prefixEnd_6804159 3493804016615549430320749 := by
  unfold tailWord_6804159
  simp only [CollatzResearch.WordTrace]
  refine ⟨248168066556701475686159531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165445377704467650457439687 248168066556701475686159531)
  ·
    refine ⟨372252099835052213529239297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248168066556701475686159531 372252099835052213529239297)
    ·
      refine ⟨279189074876289160146929473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372252099835052213529239297 279189074876289160146929473)
      ·
        refine ⟨209391806157216870110197105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279189074876289160146929473 209391806157216870110197105)
        ·
          refine ⟨157043854617912652582647829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209391806157216870110197105 157043854617912652582647829)
          ·
            refine ⟨7361430685214655589811617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157043854617912652582647829 7361430685214655589811617)
            ·
              refine ⟨5521073013910991692358713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7361430685214655589811617 5521073013910991692358713)
              ·
                refine ⟨4140804760433243769269035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521073013910991692358713 4140804760433243769269035)
                ·
                  refine ⟨6211207140649865653903553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140804760433243769269035 6211207140649865653903553)
                  ·
                    refine ⟨4658405355487399240427665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211207140649865653903553 4658405355487399240427665)
                    ·
                      refine ⟨3493804016615549430320749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658405355487399240427665 3493804016615549430320749)
                      ·
                        rfl

theorem cell23_6804159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_6804159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804159 prefixEnd_6804159 := by exact prefixLift 6804159
  have htrace : WordTrace (prefixWord ++ tailWord_6804159) baseStart_6804159 baseEnd_6804159 := by
    simpa [prefixWord, tailWord_6804159, baseEnd_6804159] using wordTrace_append hprefix tailTrace_6804159
  have hstable : (prefixWord ++ tailWord_6804159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804159).length < 2 ^ (prefixWord ++ tailWord_6804159).sum := by decide
  have hdescent : baseEnd_6804159 < baseStart_6804159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804168 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_6804168 : Nat := 118140960795 + 6804168 * 2 ^ 59
def prefixEnd_6804168 : Nat := 4983230072969 + 3 ^ 40 * 6804168 * 2
def baseEnd_6804168 : Nat := 3493808637941439895108207

theorem tailTrace_6804168 : CollatzResearch.WordTrace tailWord_6804168 prefixEnd_6804168 3493808637941439895108207 := by
  unfold tailWord_6804168
  simp only [CollatzResearch.WordTrace]
  refine ⟨124084197406834435111618579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165445596542445913482158105 124084197406834435111618579)
  ·
    refine ⟨186126296110251652667427869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124084197406834435111618579 186126296110251652667427869)
    ·
      refine ⟨69797361041344369750285451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186126296110251652667427869 69797361041344369750285451)
      ·
        refine ⟨104696041562016554625428177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69797361041344369750285451 104696041562016554625428177)
        ·
          refine ⟨78522031171512415969071133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104696041562016554625428177 78522031171512415969071133)
          ·
            refine ⟨29445761689317155988401675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78522031171512415969071133 29445761689317155988401675)
            ·
              refine ⟨44168642533975733982602513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29445761689317155988401675 44168642533975733982602513)
              ·
                refine ⟨33126481900481800486951885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44168642533975733982602513 33126481900481800486951885)
                ·
                  refine ⟨12422430712680675182606957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33126481900481800486951885 12422430712680675182606957)
                  ·
                    refine ⟨4658411517255253193477609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12422430712680675182606957 4658411517255253193477609)
                    ·
                      refine ⟨3493808637941439895108207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658411517255253193477609 3493808637941439895108207)
                      ·
                        rfl

theorem cell23_6804168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_6804168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804168 prefixEnd_6804168 := by exact prefixLift 6804168
  have htrace : WordTrace (prefixWord ++ tailWord_6804168) baseStart_6804168 baseEnd_6804168 := by
    simpa [prefixWord, tailWord_6804168, baseEnd_6804168] using wordTrace_append hprefix tailTrace_6804168
  have hstable : (prefixWord ++ tailWord_6804168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804168).length < 2 ^ (prefixWord ++ tailWord_6804168).sum := by decide
  have hdescent : baseEnd_6804168 < baseStart_6804168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804204 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 11]
def baseStart_6804204 : Nat := 118140960795 + 6804204 * 2 ^ 59
def prefixEnd_6804204 : Nat := 4983230072969 + 3 ^ 40 * 6804204 * 2
def baseEnd_6804204 : Nat := 388203013693889083806449

theorem tailTrace_6804204 : CollatzResearch.WordTrace tailWord_6804204 prefixEnd_6804204 388203013693889083806449 := by
  unfold tailWord_6804204
  simp only [CollatzResearch.WordTrace]
  refine ⟨124084853920769224185773833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165446471894358965581031777 124084853920769224185773833)
  ·
    refine ⟨93063640440576918139330375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124084853920769224185773833 93063640440576918139330375)
    ·
      refine ⟨139595460660865377208995563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93063640440576918139330375 139595460660865377208995563)
      ·
        refine ⟨209393190991298065813493345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139595460660865377208995563 209393190991298065813493345)
        ·
          refine ⟨157044893243473549360120009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209393190991298065813493345 157044893243473549360120009)
          ·
            refine ⟨117783669932605162020090007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157044893243473549360120009 117783669932605162020090007)
            ·
              refine ⟨176675504898907743030135011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117783669932605162020090007 176675504898907743030135011)
              ·
                refine ⟨265013257348361614545202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176675504898907743030135011 265013257348361614545202517)
                ·
                  refine ⟨388203013693889083806449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 265013257348361614545202517 388203013693889083806449)
                  ·
                    rfl

theorem cell23_6804204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_6804204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804204 prefixEnd_6804204 := by exact prefixLift 6804204
  have htrace : WordTrace (prefixWord ++ tailWord_6804204) baseStart_6804204 baseEnd_6804204 := by
    simpa [prefixWord, tailWord_6804204, baseEnd_6804204] using wordTrace_append hprefix tailTrace_6804204
  have hstable : (prefixWord ++ tailWord_6804204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804204).length < 2 ^ (prefixWord ++ tailWord_6804204).sum := by decide
  have hdescent : baseEnd_6804204 < baseStart_6804204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804221 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 7]
def baseStart_6804221 : Nat := 118140960795 + 6804221 * 2 ^ 59
def prefixEnd_6804221 : Nat := 4983230072969 + 3 ^ 40 * 6804221 * 2
def baseEnd_6804221 : Nat := 388203983601792020860607

theorem tailTrace_6804221 : CollatzResearch.WordTrace tailWord_6804221 prefixEnd_6804221 388203983601792020860607 := by
  unfold tailWord_6804221
  simp only [CollatzResearch.WordTrace]
  refine ⟨248170327882476860274916517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165446885254984573516611011 248170327882476860274916517)
  ·
    refine ⟨46531936477964411301546847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248170327882476860274916517 46531936477964411301546847)
    ·
      refine ⟨69797904716946616952320271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46531936477964411301546847 69797904716946616952320271)
      ·
        refine ⟨104696857075419925428480407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69797904716946616952320271 104696857075419925428480407)
        ·
          refine ⟨157045285613129888142720611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104696857075419925428480407 157045285613129888142720611)
          ·
            refine ⟨235567928419694832214080917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157045285613129888142720611 235567928419694832214080917)
            ·
              refine ⟨11042246644673195260035043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235567928419694832214080917 11042246644673195260035043)
              ·
                refine ⟨16563369967009792890052565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11042246644673195260035043 16563369967009792890052565)
                ·
                  refine ⟨388203983601792020860607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16563369967009792890052565 388203983601792020860607)
                  ·
                    rfl

theorem cell23_6804221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_6804221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804221 prefixEnd_6804221 := by exact prefixLift 6804221
  have htrace : WordTrace (prefixWord ++ tailWord_6804221) baseStart_6804221 baseEnd_6804221 := by
    simpa [prefixWord, tailWord_6804221, baseEnd_6804221] using wordTrace_append hprefix tailTrace_6804221
  have hstable : (prefixWord ++ tailWord_6804221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804221).length < 2 ^ (prefixWord ++ tailWord_6804221).sum := by decide
  have hdescent : baseEnd_6804221 < baseStart_6804221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804224 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_6804224 : Nat := 118140960795 + 6804224 * 2 ^ 59
def prefixEnd_6804224 : Nat := 4983230072969 + 3 ^ 40 * 6804224 * 2
def baseEnd_6804224 : Nat := 3493837392858091676007949

theorem tailTrace_6804224 : CollatzResearch.WordTrace tailWord_6804224 prefixEnd_6804224 3493837392858091676007949 := by
  unfold tailWord_6804224
  simp only [CollatzResearch.WordTrace]
  refine ⟨124085218650732995893637863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165446958200977327858183817 124085218650732995893637863)
  ·
    refine ⟨186127827976099493840456795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124085218650732995893637863 186127827976099493840456795)
    ·
      refine ⟨279191741964149240760685193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186127827976099493840456795 279191741964149240760685193)
      ·
        refine ⟨209393806473111930570513895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279191741964149240760685193 209393806473111930570513895)
        ·
          refine ⟨314090709709667895855770843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209393806473111930570513895 314090709709667895855770843)
          ·
            refine ⟨471136064564501843783656265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314090709709667895855770843 471136064564501843783656265)
            ·
              refine ⟨353352048423376382837742199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471136064564501843783656265 353352048423376382837742199)
              ·
                refine ⟨530028072635064574256613299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353352048423376382837742199 530028072635064574256613299)
                ·
                  refine ⟨795042108952596861384919949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530028072635064574256613299 795042108952596861384919949)
                  ·
                    refine ⟨298140790857223823019344981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795042108952596861384919949 298140790857223823019344981)
                    ·
                      refine ⟨3493837392858091676007949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298140790857223823019344981 3493837392858091676007949)
                      ·
                        rfl

theorem cell23_6804224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_6804224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804224 prefixEnd_6804224 := by exact prefixLift 6804224
  have htrace : WordTrace (prefixWord ++ tailWord_6804224) baseStart_6804224 baseEnd_6804224 := by
    simpa [prefixWord, tailWord_6804224, baseEnd_6804224] using wordTrace_append hprefix tailTrace_6804224
  have hstable : (prefixWord ++ tailWord_6804224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804224).length < 2 ^ (prefixWord ++ tailWord_6804224).sum := by decide
  have hdescent : baseEnd_6804224 < baseStart_6804224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804255 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 5]
def baseStart_6804255 : Nat := 118140960795 + 6804255 * 2 ^ 59
def prefixEnd_6804255 : Nat := 4983230072969 + 3 ^ 40 * 6804255 * 2
def baseEnd_6804255 : Nat := 388205923417597894968923

theorem tailTrace_6804255 : CollatzResearch.WordTrace tailWord_6804255 prefixEnd_6804255 388205923417597894968923 := by
  unfold tailWord_6804255
  simp only [CollatzResearch.WordTrace]
  refine ⟨248171567964353684081654219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165447711976235789387769479 248171567964353684081654219)
  ·
    refine ⟨372257351946530526122481329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248171567964353684081654219 372257351946530526122481329)
    ·
      refine ⟨279193013959897894591860997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372257351946530526122481329 279193013959897894591860997)
      ·
        refine ⟨52348690117480855235973937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279193013959897894591860997 52348690117480855235973937)
        ·
          refine ⟨39261517588110641426980453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52348690117480855235973937 39261517588110641426980453)
          ·
            refine ⟨7361534547770745267558835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39261517588110641426980453 7361534547770745267558835)
            ·
              refine ⟨11042301821656117901338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361534547770745267558835 11042301821656117901338253)
              ·
                refine ⟨4140863183121044213001845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11042301821656117901338253 4140863183121044213001845)
                ·
                  refine ⟨388205923417597894968923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140863183121044213001845 388205923417597894968923)
                  ·
                    rfl

theorem cell23_6804255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 5].length) (baseStart_6804255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804255 prefixEnd_6804255 := by exact prefixLift 6804255
  have htrace : WordTrace (prefixWord ++ tailWord_6804255) baseStart_6804255 baseEnd_6804255 := by
    simpa [prefixWord, tailWord_6804255, baseEnd_6804255] using wordTrace_append hprefix tailTrace_6804255
  have hstable : (prefixWord ++ tailWord_6804255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804255).length < 2 ^ (prefixWord ++ tailWord_6804255).sum := by decide
  have hdescent : baseEnd_6804255 < baseStart_6804255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804261 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_6804261 : Nat := 118140960795 + 6804261 * 2 ^ 59
def prefixEnd_6804261 : Nat := 4983230072969 + 3 ^ 40 * 6804261 * 2
def baseEnd_6804261 : Nat := 3493856391642308031245279

theorem tailTrace_6804261 : CollatzResearch.WordTrace tailWord_6804261 prefixEnd_6804261 3493856391642308031245279 := by
  unfold tailWord_6804261
  simp only [CollatzResearch.WordTrace]
  refine ⟨248171786802331947106372637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165447857868221298070915091 248171786802331947106372637)
  ·
    refine ⟨93064420050874480164889739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248171786802331947106372637 93064420050874480164889739)
    ·
      refine ⟨139596630076311720247334609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93064420050874480164889739 139596630076311720247334609)
      ·
        refine ⟨104697472557233790185500957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139596630076311720247334609 104697472557233790185500957)
        ·
          refine ⟨39261552208962671319562859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104697472557233790185500957 39261552208962671319562859)
          ·
            refine ⟨58892328313444006979344289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39261552208962671319562859 58892328313444006979344289)
            ·
              refine ⟨44169246235083005234508217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58892328313444006979344289 44169246235083005234508217)
              ·
                refine ⟨33126934676312253925881163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44169246235083005234508217 33126934676312253925881163)
                ·
                  refine ⟨49690402014468380888821745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33126934676312253925881163 49690402014468380888821745)
                  ·
                    refine ⟨37267801510851285666616309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49690402014468380888821745 37267801510851285666616309)
                    ·
                      refine ⟨3493856391642308031245279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37267801510851285666616309 3493856391642308031245279)
                      ·
                        rfl

theorem cell23_6804261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_6804261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804261 prefixEnd_6804261 := by exact prefixLift 6804261
  have htrace : WordTrace (prefixWord ++ tailWord_6804261) baseStart_6804261 baseEnd_6804261 := by
    simpa [prefixWord, tailWord_6804261, baseEnd_6804261] using wordTrace_append hprefix tailTrace_6804261
  have hstable : (prefixWord ++ tailWord_6804261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804261).length < 2 ^ (prefixWord ++ tailWord_6804261).sum := by decide
  have hdescent : baseEnd_6804261 < baseStart_6804261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804288 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2]
def baseStart_6804288 : Nat := 118140960795 + 6804288 * 2 ^ 59
def prefixEnd_6804288 : Nat := 4983230072969 + 3 ^ 40 * 6804288 * 2
def baseEnd_6804288 : Nat := 3493870255619979425607655

theorem tailTrace_6804288 : CollatzResearch.WordTrace tailWord_6804288 prefixEnd_6804288 3493870255619979425607655 := by
  unfold tailWord_6804288
  simp only [CollatzResearch.WordTrace]
  refine ⟨124086385786617065358802759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165448514382156087145070345 124086385786617065358802759)
  ·
    refine ⟨186129578679925598038204139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124086385786617065358802759 186129578679925598038204139)
    ·
      refine ⟨279194368019888397057306209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186129578679925598038204139 279194368019888397057306209)
      ·
        refine ⟨209395776014916297792979657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279194368019888397057306209 209395776014916297792979657)
        ·
          refine ⟨157046832011187223344734743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209395776014916297792979657 157046832011187223344734743)
          ·
            refine ⟨235570248016780835017102115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157046832011187223344734743 235570248016780835017102115)
            ·
              refine ⟨353355372025171252525653173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235570248016780835017102115 353355372025171252525653173)
              ·
                refine ⟨33127066127359804924279985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353355372025171252525653173 33127066127359804924279985)
                ·
                  refine ⟨24845299595519853693209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33127066127359804924279985 24845299595519853693209989)
                  ·
                    refine ⟨4658493674159972567476873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24845299595519853693209989 4658493674159972567476873)
                    ·
                      refine ⟨3493870255619979425607655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658493674159972567476873 3493870255619979425607655)
                      ·
                        rfl

theorem cell23_6804288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_6804288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804288 prefixEnd_6804288 := by exact prefixLift 6804288
  have htrace : WordTrace (prefixWord ++ tailWord_6804288) baseStart_6804288 baseEnd_6804288 := by
    simpa [prefixWord, tailWord_6804288, baseEnd_6804288] using wordTrace_append hprefix tailTrace_6804288
  have hstable : (prefixWord ++ tailWord_6804288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804288).length < 2 ^ (prefixWord ++ tailWord_6804288).sum := by decide
  have hdescent : baseEnd_6804288 < baseStart_6804288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804305 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_6804305 : Nat := 118140960795 + 6804305 * 2 ^ 59
def prefixEnd_6804305 : Nat := 4983230072969 + 3 ^ 40 * 6804305 * 2
def baseEnd_6804305 : Nat := 3493878984791105859095077

theorem tailTrace_6804305 : CollatzResearch.WordTrace tailWord_6804305 prefixEnd_6804305 3493878984791105859095077 := by
  unfold tailWord_6804305
  simp only [CollatzResearch.WordTrace]
  refine ⟨248173391614172542620974369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165448927742781695080649579 248173391614172542620974369)
  ·
    refine ⟨186130043710629406965730777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248173391614172542620974369 186130043710629406965730777)
    ·
      refine ⟨139597532782972055224298083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186130043710629406965730777 139597532782972055224298083)
      ·
        refine ⟨209396299174458082836447125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139597532782972055224298083 209396299174458082836447125)
        ·
          refine ⟨9815451523802722632958459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209396299174458082836447125 9815451523802722632958459)
          ·
            refine ⟨14723177285704083949437689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815451523802722632958459 14723177285704083949437689)
            ·
              refine ⟨11042382964278062962078267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14723177285704083949437689 11042382964278062962078267)
              ·
                refine ⟨16563574446417094443117401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11042382964278062962078267 16563574446417094443117401)
                ·
                  refine ⟨12422680834812820832338051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16563574446417094443117401 12422680834812820832338051)
                  ·
                    refine ⟨18634021252219231248507077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12422680834812820832338051 18634021252219231248507077)
                    ·
                      refine ⟨3493878984791105859095077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18634021252219231248507077 3493878984791105859095077)
                      ·
                        rfl

theorem cell23_6804305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_6804305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804305 prefixEnd_6804305 := by exact prefixLift 6804305
  have htrace : WordTrace (prefixWord ++ tailWord_6804305) baseStart_6804305 baseEnd_6804305 := by
    simpa [prefixWord, tailWord_6804305, baseEnd_6804305] using wordTrace_append hprefix tailTrace_6804305
  have hstable : (prefixWord ++ tailWord_6804305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804305).length < 2 ^ (prefixWord ++ tailWord_6804305).sum := by decide
  have hdescent : baseEnd_6804305 < baseStart_6804305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804328 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 6]
def baseStart_6804328 : Nat := 118140960795 + 6804328 * 2 ^ 59
def prefixEnd_6804328 : Nat := 4983230072969 + 3 ^ 40 * 6804328 * 2
def baseEnd_6804328 : Nat := 388210088316239918789719

theorem tailTrace_6804328 : CollatzResearch.WordTrace tailWord_6804328 prefixEnd_6804328 388210088316239918789719 := by
  unfold tailWord_6804328
  simp only [CollatzResearch.WordTrace]
  refine ⟨124087115246544608774530819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165449486995392811699374425 124087115246544608774530819)
  ·
    refine ⟨186130672869816913161796229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124087115246544608774530819 186130672869816913161796229)
    ·
      refine ⟨34899501163090671217836793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186130672869816913161796229 34899501163090671217836793)
      ·
        refine ⟨26174625872318003413377595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34899501163090671217836793 26174625872318003413377595)
        ·
          refine ⟨39261938808477005120066393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26174625872318003413377595 39261938808477005120066393)
          ·
            refine ⟨29446454106357753840049795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39261938808477005120066393 29446454106357753840049795)
            ·
              refine ⟨44169681159536630760074693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29446454106357753840049795 44169681159536630760074693)
              ·
                refine ⟨8281815217413118267514005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44169681159536630760074693 8281815217413118267514005)
                ·
                  refine ⟨388210088316239918789719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8281815217413118267514005 388210088316239918789719)
                  ·
                    rfl

theorem cell23_6804328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_6804328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804328 prefixEnd_6804328 := by exact prefixLift 6804328
  have htrace : WordTrace (prefixWord ++ tailWord_6804328) baseStart_6804328 baseEnd_6804328 := by
    simpa [prefixWord, tailWord_6804328, baseEnd_6804328] using wordTrace_append hprefix tailTrace_6804328
  have hstable : (prefixWord ++ tailWord_6804328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804328).length < 2 ^ (prefixWord ++ tailWord_6804328).sum := by decide
  have hdescent : baseEnd_6804328 < baseStart_6804328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804355 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 3]
def baseStart_6804355 : Nat := 118140960795 + 6804355 * 2 ^ 59
def prefixEnd_6804355 : Nat := 4983230072969 + 3 ^ 40 * 6804355 * 2
def baseEnd_6804355 : Nat := 3493904658823830663469847

theorem tailTrace_6804355 : CollatzResearch.WordTrace tailWord_6804355 prefixEnd_6804355 3493904658823830663469847 := by
  unfold tailWord_6804355
  simp only [CollatzResearch.WordTrace]
  refine ⟨248175215263991401160294519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165450143509327600773529679 248175215263991401160294519)
  ·
    refine ⟨372262822895987101740441779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248175215263991401160294519 372262822895987101740441779)
    ·
      refine ⟨558394234343980652610662669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372262822895987101740441779 558394234343980652610662669)
      ·
        refine ⟨209397837878992744728998501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558394234343980652610662669 209397837878992744728998501)
        ·
          refine ⟨39262094602311139636687219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209397837878992744728998501 39262094602311139636687219)
          ·
            refine ⟨58893141903466709455030829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39262094602311139636687219 58893141903466709455030829)
            ·
              refine ⟨22084928213800016045636561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58893141903466709455030829 22084928213800016045636561)
              ·
                refine ⟨16563696160350012034227421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22084928213800016045636561 16563696160350012034227421)
                ·
                  refine ⟨6211386060131254512835283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16563696160350012034227421 6211386060131254512835283)
                  ·
                    refine ⟨9317079090196881769252925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6211386060131254512835283 9317079090196881769252925)
                    ·
                      refine ⟨3493904658823830663469847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317079090196881769252925 3493904658823830663469847)
                      ·
                        rfl

theorem cell23_6804355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_6804355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804355 prefixEnd_6804355 := by exact prefixLift 6804355
  have htrace : WordTrace (prefixWord ++ tailWord_6804355) baseStart_6804355 baseEnd_6804355 := by
    simpa [prefixWord, tailWord_6804355, baseEnd_6804355] using wordTrace_append hprefix tailTrace_6804355
  have hstable : (prefixWord ++ tailWord_6804355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804355).length < 2 ^ (prefixWord ++ tailWord_6804355).sum := by decide
  have hdescent : baseEnd_6804355 < baseStart_6804355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804371 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 6]
def baseStart_6804371 : Nat := 118140960795 + 6804371 * 2 ^ 59
def prefixEnd_6804371 : Nat := 4983230072969 + 3 ^ 40 * 6804371 * 2
def baseEnd_6804371 : Nat := 1164637624838100866956591

theorem tailTrace_6804371 : CollatzResearch.WordTrace tailWord_6804371 prefixEnd_6804371 1164637624838100866956591 := by
  unfold tailWord_6804371
  simp only [CollatzResearch.WordTrace]
  refine ⟨248175798831933435892876967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165450532554622290595251311 248175798831933435892876967)
  ·
    refine ⟨372263698247900153839315451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248175798831933435892876967 372263698247900153839315451)
    ·
      refine ⟨558395547371850230758973177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372263698247900153839315451 558395547371850230758973177)
      ·
        refine ⟨418796660528887673069229883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558395547371850230758973177 418796660528887673069229883)
        ·
          refine ⟨628194990793331509603844825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418796660528887673069229883 628194990793331509603844825)
          ·
            refine ⟨471146243094998632202883619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628194990793331509603844825 471146243094998632202883619)
            ·
              refine ⟨706719364642497948304325429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471146243094998632202883619 706719364642497948304325429)
              ·
                refine ⟨66254940435234182653530509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 706719364642497948304325429 66254940435234182653530509)
                ·
                  refine ⟨24845602663212818495073941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66254940435234182653530509 24845602663212818495073941)
                  ·
                    refine ⟨1164637624838100866956591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24845602663212818495073941 1164637624838100866956591)
                    ·
                      rfl

theorem cell23_6804371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_6804371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804371 prefixEnd_6804371 := by exact prefixLift 6804371
  have htrace : WordTrace (prefixWord ++ tailWord_6804371) baseStart_6804371 baseEnd_6804371 := by
    simpa [prefixWord, tailWord_6804371, baseEnd_6804371] using wordTrace_append hprefix tailTrace_6804371
  have hstable : (prefixWord ++ tailWord_6804371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804371).length < 2 ^ (prefixWord ++ tailWord_6804371).sum := by decide
  have hdescent : baseEnd_6804371 < baseStart_6804371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 7, 2, 2]
def baseStart_6804395 : Nat := 118140960795 + 6804395 * 2 ^ 59
def prefixEnd_6804395 : Nat := 4983230072969 + 3 ^ 40 * 6804395 * 2
def baseEnd_6804395 : Nat := 3493925198050010506969663

theorem tailTrace_6804395 : CollatzResearch.WordTrace tailWord_6804395 prefixEnd_6804395 3493925198050010506969663 := by
  unfold tailWord_6804395
  simp only [CollatzResearch.WordTrace]
  refine ⟨248176674183846487991750639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165451116122564325327833759 248176674183846487991750639)
  ·
    refine ⟨372265011275769731987625959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248176674183846487991750639 372265011275769731987625959)
    ·
      refine ⟨558397516913654597981438939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372265011275769731987625959 558397516913654597981438939)
      ·
        refine ⟨837596275370481896972158409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558397516913654597981438939 837596275370481896972158409)
        ·
          refine ⟨628197206527861422729118807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837596275370481896972158409 628197206527861422729118807)
          ·
            refine ⟨942295809791792134093678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628197206527861422729118807 942295809791792134093678211)
            ·
              refine ⟨1413443714687688201140517317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942295809791792134093678211 1413443714687688201140517317)
              ·
                refine ⟨265020696503941537713846997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1413443714687688201140517317 265020696503941537713846997)
                ·
                  refine ⟨6211422574311129790168289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 265020696503941537713846997 6211422574311129790168289)
                  ·
                    refine ⟨4658566930733347342626217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211422574311129790168289 4658566930733347342626217)
                    ·
                      refine ⟨3493925198050010506969663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658566930733347342626217 3493925198050010506969663)
                      ·
                        rfl

theorem cell23_6804395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2, 2].length) (baseStart_6804395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804395 prefixEnd_6804395 := by exact prefixLift 6804395
  have htrace : WordTrace (prefixWord ++ tailWord_6804395) baseStart_6804395 baseEnd_6804395 := by
    simpa [prefixWord, tailWord_6804395, baseEnd_6804395] using wordTrace_append hprefix tailTrace_6804395
  have hstable : (prefixWord ++ tailWord_6804395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804395).length < 2 ^ (prefixWord ++ tailWord_6804395).sum := by decide
  have hdescent : baseEnd_6804395 < baseStart_6804395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804408 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_6804408 : Nat := 118140960795 + 6804408 * 2 ^ 59
def prefixEnd_6804408 : Nat := 4983230072969 + 3 ^ 40 * 6804408 * 2
def baseEnd_6804408 : Nat := 3493931873298518956107103

theorem tailTrace_6804408 : CollatzResearch.WordTrace tailWord_6804408 prefixEnd_6804408 3493931873298518956107103 := by
  unfold tailWord_6804408
  simp only [CollatzResearch.WordTrace]
  refine ⟨124088574166399695605986939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165451432221866260807982585 124088574166399695605986939)
  ·
    refine ⟨186132861249599543408980409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124088574166399695605986939 186132861249599543408980409)
    ·
      refine ⟨139599645937199657556735307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186132861249599543408980409 139599645937199657556735307)
      ·
        refine ⟨209399468905799486335102961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139599645937199657556735307 209399468905799486335102961)
        ·
          refine ⟨157049601679349614751327221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209399468905799486335102961 157049601679349614751327221)
          ·
            refine ⟨14723400157439026382936927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157049601679349614751327221 14723400157439026382936927)
            ·
              refine ⟨22085100236158539574405391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723400157439026382936927 22085100236158539574405391)
              ·
                refine ⟨33127650354237809361608087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22085100236158539574405391 33127650354237809361608087)
                ·
                  refine ⟨49691475531356714042412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33127650354237809361608087 49691475531356714042412131)
                  ·
                    refine ⟨74537213297035071063618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49691475531356714042412131 74537213297035071063618197)
                    ·
                      refine ⟨3493931873298518956107103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74537213297035071063618197 3493931873298518956107103)
                      ·
                        rfl

theorem cell23_6804408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_6804408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804408 prefixEnd_6804408 := by exact prefixLift 6804408
  have htrace : WordTrace (prefixWord ++ tailWord_6804408) baseStart_6804408 baseEnd_6804408 := by
    simpa [prefixWord, tailWord_6804408, baseEnd_6804408] using wordTrace_append hprefix tailTrace_6804408
  have hstable : (prefixWord ++ tailWord_6804408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804408).length < 2 ^ (prefixWord ++ tailWord_6804408).sum := by decide
  have hdescent : baseEnd_6804408 < baseStart_6804408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804466 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6804466 : Nat := 118140960795 + 6804466 * 2 ^ 59
def prefixEnd_6804466 : Nat := 4983230072969 + 3 ^ 40 * 6804466 * 2
def baseEnd_6804466 : Nat := 3493961655176479729181837

theorem tailTrace_6804466 : CollatzResearch.WordTrace tailWord_6804466 prefixEnd_6804466 3493961655176479729181837 := by
  unfold tailWord_6804466
  simp only [CollatzResearch.WordTrace]
  refine ⟨62044815941647316779396313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165452842511059511411723501 62044815941647316779396313)
  ·
    refine ⟨46533611956235487584547235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62044815941647316779396313 46533611956235487584547235)
    ·
      refine ⟨69800417934353231376820853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46533611956235487584547235 69800417934353231376820853)
      ·
        refine ⟨6543789181345615441576955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69800417934353231376820853 6543789181345615441576955)
        ·
          refine ⟨9815683772018423162365433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543789181345615441576955 9815683772018423162365433)
          ·
            refine ⟨7361762829013817371774075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815683772018423162365433 7361762829013817371774075)
            ·
              refine ⟨11042644243520726057661113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361762829013817371774075 11042644243520726057661113)
              ·
                refine ⟨8281983182640544543245835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11042644243520726057661113 8281983182640544543245835)
                ·
                  refine ⟨12422974773960816814868753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281983182640544543245835 12422974773960816814868753)
                  ·
                    refine ⟨9317231080470612611151565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12422974773960816814868753 9317231080470612611151565)
                    ·
                      refine ⟨3493961655176479729181837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317231080470612611151565 3493961655176479729181837)
                      ·
                        rfl

theorem cell23_6804466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6804466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804466 prefixEnd_6804466 := by exact prefixLift 6804466
  have htrace : WordTrace (prefixWord ++ tailWord_6804466) baseStart_6804466 baseEnd_6804466 := by
    simpa [prefixWord, tailWord_6804466, baseEnd_6804466] using wordTrace_append hprefix tailTrace_6804466
  have hstable : (prefixWord ++ tailWord_6804466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804466).length < 2 ^ (prefixWord ++ tailWord_6804466).sum := by decide
  have hdescent : baseEnd_6804466 < baseStart_6804466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804512 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_6804512 : Nat := 118140960795 + 6804512 * 2 ^ 59
def prefixEnd_6804512 : Nat := 4983230072969 + 3 ^ 40 * 6804512 * 2
def baseEnd_6804512 : Nat := 1164661758428862183068875

theorem tailTrace_6804512 : CollatzResearch.WordTrace tailWord_6804512 prefixEnd_6804512 1164661758428862183068875 := by
  unfold tailWord_6804512
  simp only [CollatzResearch.WordTrace]
  refine ⟨124090470762211308486879895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165453961016281744649173193 124090470762211308486879895)
  ·
    refine ⟨186135706143316962730319843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124090470762211308486879895 186135706143316962730319843)
    ·
      refine ⟨279203559214975444095479765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186135706143316962730319843 279203559214975444095479765)
      ·
        refine ⟨6543833419100986970987807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 279203559214975444095479765 6543833419100986970987807)
        ·
          refine ⟨9815750128651480456481711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543833419100986970987807 9815750128651480456481711)
          ·
            refine ⟨14723625192977220684722567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815750128651480456481711 14723625192977220684722567)
            ·
              refine ⟨22085437789465831027083851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723625192977220684722567 22085437789465831027083851)
              ·
                refine ⟨33128156684198746540625777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22085437789465831027083851 33128156684198746540625777)
                ·
                  refine ⟨24846117513149059905469333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33128156684198746540625777 24846117513149059905469333)
                  ·
                    refine ⟨1164661758428862183068875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24846117513149059905469333 1164661758428862183068875)
                    ·
                      rfl

theorem cell23_6804512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_6804512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804512 prefixEnd_6804512 := by exact prefixLift 6804512
  have htrace : WordTrace (prefixWord ++ tailWord_6804512) baseStart_6804512 baseEnd_6804512 := by
    simpa [prefixWord, tailWord_6804512, baseEnd_6804512] using wordTrace_append hprefix tailTrace_6804512
  have hstable : (prefixWord ++ tailWord_6804512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804512).length < 2 ^ (prefixWord ++ tailWord_6804512).sum := by decide
  have hdescent : baseEnd_6804512 < baseStart_6804512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804515 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6804515 : Nat := 118140960795 + 6804515 * 2 ^ 59
def prefixEnd_6804515 : Nat := 4983230072969 + 3 ^ 40 * 6804515 * 2
def baseEnd_6804515 : Nat := 3493986815728550037469111

theorem tailTrace_6804515 : CollatzResearch.WordTrace tailWord_6804515 prefixEnd_6804515 3493986815728550037469111 := by
  unfold tailWord_6804515
  simp only [CollatzResearch.WordTrace]
  refine ⟨248181050943411748486118999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165454033962274498990745999 248181050943411748486118999)
  ·
    refine ⟨372271576415117622729178499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248181050943411748486118999 372271576415117622729178499)
    ·
      refine ⟨558407364622676434093767749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372271576415117622729178499 558407364622676434093767749)
      ·
        refine ⟨104701380866751831392581453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558407364622676434093767749 104701380866751831392581453)
        ·
          refine ⟨39263017825031936772218045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104701380866751831392581453 39263017825031936772218045)
          ·
            refine ⟨14723631684386976289581767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39263017825031936772218045 14723631684386976289581767)
            ·
              refine ⟨22085447526580464434372651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723631684386976289581767 22085447526580464434372651)
              ·
                refine ⟨33128171289870696651558977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22085447526580464434372651 33128171289870696651558977)
                ·
                  refine ⟨24846128467403022488669233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33128171289870696651558977 24846128467403022488669233)
                  ·
                    refine ⟨18634596350552266866501925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24846128467403022488669233 18634596350552266866501925)
                    ·
                      refine ⟨3493986815728550037469111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18634596350552266866501925 3493986815728550037469111)
                      ·
                        rfl

theorem cell23_6804515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6804515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804515 prefixEnd_6804515 := by exact prefixLift 6804515
  have htrace : WordTrace (prefixWord ++ tailWord_6804515) baseStart_6804515 baseEnd_6804515 := by
    simpa [prefixWord, tailWord_6804515, baseEnd_6804515] using wordTrace_append hprefix tailTrace_6804515
  have hstable : (prefixWord ++ tailWord_6804515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804515).length < 2 ^ (prefixWord ++ tailWord_6804515).sum := by decide
  have hdescent : baseEnd_6804515 < baseStart_6804515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804519 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6804519 : Nat := 118140960795 + 6804519 * 2 ^ 59
def prefixEnd_6804519 : Nat := 4983230072969 + 3 ^ 40 * 6804519 * 2
def baseEnd_6804519 : Nat := 3493988869651168021819093

theorem tailTrace_6804519 : CollatzResearch.WordTrace tailWord_6804519 prefixEnd_6804519 3493988869651168021819093 := by
  unfold tailWord_6804519
  simp only [CollatzResearch.WordTrace]
  refine ⟨248181196835397257169264611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165454131223598171446176407 248181196835397257169264611)
  ·
    refine ⟨372271795253095885753896917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248181196835397257169264611 372271795253095885753896917)
    ·
      refine ⟨8725120201244434822356959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 372271795253095885753896917 8725120201244434822356959)
      ·
        refine ⟨13087680301866652233535439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725120201244434822356959 13087680301866652233535439)
        ·
          refine ⟨19631520452799978350303159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13087680301866652233535439 19631520452799978350303159)
          ·
            refine ⟨29447280679199967525454739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19631520452799978350303159 29447280679199967525454739)
            ·
              refine ⟨44170921018799951288182109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29447280679199967525454739 44170921018799951288182109)
              ·
                refine ⟨16564095382049981733068291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44170921018799951288182109 16564095382049981733068291)
                ·
                  refine ⟨24846143073074972599602437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16564095382049981733068291 24846143073074972599602437)
                  ·
                    refine ⟨4658651826201557362425457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24846143073074972599602437 4658651826201557362425457)
                    ·
                      refine ⟨3493988869651168021819093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658651826201557362425457 3493988869651168021819093)
                      ·
                        rfl

theorem cell23_6804519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6804519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804519 prefixEnd_6804519 := by exact prefixLift 6804519
  have htrace : WordTrace (prefixWord ++ tailWord_6804519) baseStart_6804519 baseEnd_6804519 := by
    simpa [prefixWord, tailWord_6804519, baseEnd_6804519] using wordTrace_append hprefix tailTrace_6804519
  have hstable : (prefixWord ++ tailWord_6804519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804519).length < 2 ^ (prefixWord ++ tailWord_6804519).sum := by decide
  have hdescent : baseEnd_6804519 < baseStart_6804519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804595 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3]
def baseStart_6804595 : Nat := 118140960795 + 6804595 * 2 ^ 59
def prefixEnd_6804595 : Nat := 4983230072969 + 3 ^ 40 * 6804595 * 2
def baseEnd_6804595 : Nat := 3494027894180909724468743

theorem tailTrace_6804595 : CollatzResearch.WordTrace tailWord_6804595 prefixEnd_6804595 3494027894180909724468743 := by
  unfold tailWord_6804595
  simp only [CollatzResearch.WordTrace]
  refine ⟨248183968783121922149031239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165455979188747948099354159 248183968783121922149031239)
  ·
    refine ⟨372275953174682883223546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248183968783121922149031239 372275953174682883223546859)
    ·
      refine ⟨558413929762024324835320289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372275953174682883223546859 558413929762024324835320289)
      ·
        refine ⟨418810447321518243626490217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558413929762024324835320289 418810447321518243626490217)
        ·
          refine ⟨314107835491138682719867663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418810447321518243626490217 314107835491138682719867663)
          ·
            refine ⟨471161753236708024079801495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314107835491138682719867663 471161753236708024079801495)
            ·
              refine ⟨706742629855062036119702243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471161753236708024079801495 706742629855062036119702243)
              ·
                refine ⟨1060113944782593054179553365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706742629855062036119702243 1060113944782593054179553365)
                ·
                  refine ⟨12423210290421012353666641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1060113944782593054179553365 12423210290421012353666641)
                  ·
                    refine ⟨9317407717815759265249981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12423210290421012353666641 9317407717815759265249981)
                    ·
                      refine ⟨3494027894180909724468743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317407717815759265249981 3494027894180909724468743)
                      ·
                        rfl

theorem cell23_6804595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_6804595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804595 prefixEnd_6804595 := by exact prefixLift 6804595
  have htrace : WordTrace (prefixWord ++ tailWord_6804595) baseStart_6804595 baseEnd_6804595 := by
    simpa [prefixWord, tailWord_6804595, baseEnd_6804595] using wordTrace_append hprefix tailTrace_6804595
  have hstable : (prefixWord ++ tailWord_6804595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804595).length < 2 ^ (prefixWord ++ tailWord_6804595).sum := by decide
  have hdescent : baseEnd_6804595 < baseStart_6804595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804612 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6804612 : Nat := 118140960795 + 6804612 * 2 ^ 59
def prefixEnd_6804612 : Nat := 4983230072969 + 3 ^ 40 * 6804612 * 2
def baseEnd_6804612 : Nat := 3494036623352036157956165

theorem tailTrace_6804612 : CollatzResearch.WordTrace tailWord_6804612 prefixEnd_6804612 3494036623352036157956165 := by
  unfold tailWord_6804612
  simp only [CollatzResearch.WordTrace]
  refine ⟨124092294412030167026200045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165456392549373556034933393 124092294412030167026200045)
  ·
    refine ⟨46534610404511312634825017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124092294412030167026200045 46534610404511312634825017)
    ·
      refine ⟨34900957803383484476118763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46534610404511312634825017 34900957803383484476118763)
      ·
        refine ⟨52351436705075226714178145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34900957803383484476118763 52351436705075226714178145)
        ·
          refine ⟨39263577528806420035633609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52351436705075226714178145 39263577528806420035633609)
          ·
            refine ⟨29447683146604815026725207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39263577528806420035633609 29447683146604815026725207)
            ·
              refine ⟨44171524719907222540087811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29447683146604815026725207 44171524719907222540087811)
              ·
                refine ⟨66257287079860833810131717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44171524719907222540087811 66257287079860833810131717)
                ·
                  refine ⟨12423241327473906339399697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66257287079860833810131717 12423241327473906339399697)
                  ·
                    refine ⟨9317430995605429754549773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12423241327473906339399697 9317430995605429754549773)
                    ·
                      refine ⟨3494036623352036157956165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317430995605429754549773 3494036623352036157956165)
                      ·
                        rfl

theorem cell23_6804612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6804612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804612 prefixEnd_6804612 := by exact prefixLift 6804612
  have htrace : WordTrace (prefixWord ++ tailWord_6804612) baseStart_6804612 baseEnd_6804612 := by
    simpa [prefixWord, tailWord_6804612, baseEnd_6804612] using wordTrace_append hprefix tailTrace_6804612
  have hstable : (prefixWord ++ tailWord_6804612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804612).length < 2 ^ (prefixWord ++ tailWord_6804612).sum := by decide
  have hdescent : baseEnd_6804612 < baseStart_6804612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804615 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 6]
def baseStart_6804615 : Nat := 118140960795 + 6804615 * 2 ^ 59
def prefixEnd_6804615 : Nat := 4983230072969 + 3 ^ 40 * 6804615 * 2
def baseEnd_6804615 : Nat := 388226462643777738468739

theorem tailTrace_6804615 : CollatzResearch.WordTrace tailWord_6804615 prefixEnd_6804615 388226462643777738468739 := by
  unfold tailWord_6804615
  simp only [CollatzResearch.WordTrace]
  refine ⟨248184698243049465564759299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165456465495366310376506199 248184698243049465564759299)
  ·
    refine ⟨372277047364574198347138949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248184698243049465564759299 372277047364574198347138949)
    ·
      refine ⟨69801946380857662190088553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372277047364574198347138949 69801946380857662190088553)
      ·
        refine ⟨52351459785643246642566415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69801946380857662190088553 52351459785643246642566415)
        ·
          refine ⟨78527189678464869963849623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52351459785643246642566415 78527189678464869963849623)
          ·
            refine ⟨117790784517697304945774435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78527189678464869963849623 117790784517697304945774435)
            ·
              refine ⟨176686176776545957418661653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117790784517697304945774435 176686176776545957418661653)
              ·
                refine ⟨8282164536400591753999765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176686176776545957418661653 8282164536400591753999765)
                ·
                  refine ⟨388226462643777738468739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8282164536400591753999765 388226462643777738468739)
                  ·
                    rfl

theorem cell23_6804615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 6].length) (baseStart_6804615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804615 prefixEnd_6804615 := by exact prefixLift 6804615
  have htrace : WordTrace (prefixWord ++ tailWord_6804615) baseStart_6804615 baseEnd_6804615 := by
    simpa [prefixWord, tailWord_6804615, baseEnd_6804615] using wordTrace_append hprefix tailTrace_6804615
  have hstable : (prefixWord ++ tailWord_6804615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804615).length < 2 ^ (prefixWord ++ tailWord_6804615).sum := by decide
  have hdescent : baseEnd_6804615 < baseStart_6804615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804632 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 6]
def baseStart_6804632 : Nat := 118140960795 + 6804632 * 2 ^ 59
def prefixEnd_6804632 : Nat := 4983230072969 + 3 ^ 40 * 6804632 * 2
def baseEnd_6804632 : Nat := 388227432551680675522897

theorem tailTrace_6804632 : CollatzResearch.WordTrace tailWord_6804632 prefixEnd_6804632 388227432551680675522897 := by
  unfold tailWord_6804632
  simp only [CollatzResearch.WordTrace]
  refine ⟨124092659141993938734064075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165456878855991918312085433 124092659141993938734064075)
  ·
    refine ⟨186138988712990908101096113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124092659141993938734064075 186138988712990908101096113)
    ·
      refine ⟨139604241534743181075822085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186138988712990908101096113 139604241534743181075822085)
      ·
        refine ⟨26175795287764346451716641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139604241534743181075822085 26175795287764346451716641)
        ·
          refine ⟨19631846465823259838787481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26175795287764346451716641 19631846465823259838787481)
          ·
            refine ⟨14723884849367444879090611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19631846465823259838787481 14723884849367444879090611)
            ·
              refine ⟨22085827274051167318635917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723884849367444879090611 22085827274051167318635917)
              ·
                refine ⟨8282185227769187744488469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22085827274051167318635917 8282185227769187744488469)
                ·
                  refine ⟨388227432551680675522897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8282185227769187744488469 388227432551680675522897)
                  ·
                    rfl

theorem cell23_6804632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_6804632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804632 prefixEnd_6804632 := by exact prefixLift 6804632
  have htrace : WordTrace (prefixWord ++ tailWord_6804632) baseStart_6804632 baseEnd_6804632 := by
    simpa [prefixWord, tailWord_6804632, baseEnd_6804632] using wordTrace_append hprefix tailTrace_6804632
  have hstable : (prefixWord ++ tailWord_6804632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804632).length < 2 ^ (prefixWord ++ tailWord_6804632).sum := by decide
  have hdescent : baseEnd_6804632 < baseStart_6804632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804669 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6804669 : Nat := 118140960795 + 6804669 * 2 ^ 59
def prefixEnd_6804669 : Nat := 4983230072969 + 3 ^ 40 * 6804669 * 2
def baseEnd_6804669 : Nat := 3494065891749342434943403

theorem tailTrace_6804669 : CollatzResearch.WordTrace tailWord_6804669 prefixEnd_6804669 3494065891749342434943403 := by
  unfold tailWord_6804669
  simp only [CollatzResearch.WordTrace]
  refine ⟨248186667784853832787225061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165457778523235888524816707 248186667784853832787225061)
  ·
    refine ⟨46535000209660093647604699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248186667784853832787225061 46535000209660093647604699)
    ·
      refine ⟨69802500314490140471407049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46535000209660093647604699 69802500314490140471407049)
      ·
        refine ⟨52351875235867605353555287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69802500314490140471407049 52351875235867605353555287)
        ·
          refine ⟨78527812853801408030332931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52351875235867605353555287 78527812853801408030332931)
          ·
            refine ⟨117791719280702112045499397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78527812853801408030332931 117791719280702112045499397)
            ·
              refine ⟨22085947365131646008531137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117791719280702112045499397 22085947365131646008531137)
              ·
                refine ⟨16564460523848734506398353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22085947365131646008531137 16564460523848734506398353)
                ·
                  refine ⟨12423345392886550879798765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16564460523848734506398353 12423345392886550879798765)
                  ·
                    refine ⟨4658754522332456579924537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12423345392886550879798765 4658754522332456579924537)
                    ·
                      refine ⟨3494065891749342434943403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658754522332456579924537 3494065891749342434943403)
                      ·
                        rfl

theorem cell23_6804669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6804669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804669 prefixEnd_6804669 := by exact prefixLift 6804669
  have htrace : WordTrace (prefixWord ++ tailWord_6804669) baseStart_6804669 baseEnd_6804669 := by
    simpa [prefixWord, tailWord_6804669, baseEnd_6804669] using wordTrace_append hprefix tailTrace_6804669
  have hstable : (prefixWord ++ tailWord_6804669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804669).length < 2 ^ (prefixWord ++ tailWord_6804669).sum := by decide
  have hdescent : baseEnd_6804669 < baseStart_6804669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804682 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_6804682 : Nat := 118140960795 + 6804682 * 2 ^ 59
def prefixEnd_6804682 : Nat := 4983230072969 + 3 ^ 40 * 6804682 * 2
def baseEnd_6804682 : Nat := 3494072566997850884080843

theorem tailTrace_6804682 : CollatzResearch.WordTrace tailWord_6804682 prefixEnd_6804682 3494072566997850884080843 := by
  unfold tailWord_6804682
  simp only [CollatzResearch.WordTrace]
  refine ⟨62046785483451684001862075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165458094622537824004965533 62046785483451684001862075)
  ·
    refine ⟨93070178225177526002793113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62046785483451684001862075 93070178225177526002793113)
    ·
      refine ⟨69802633668883144502094835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93070178225177526002793113 69802633668883144502094835)
      ·
        refine ⟨104703950503324716753142253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69802633668883144502094835 104703950503324716753142253)
        ·
          refine ⟨39263981438746768782428345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104703950503324716753142253 39263981438746768782428345)
          ·
            refine ⟨29447986079060076586821259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39263981438746768782428345 29447986079060076586821259)
            ·
              refine ⟨44171979118590114880231889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29447986079060076586821259 44171979118590114880231889)
              ·
                refine ⟨33128984338942586160173917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44171979118590114880231889 33128984338942586160173917)
                ·
                  refine ⟨12423369127103469810065219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33128984338942586160173917 12423369127103469810065219)
                  ·
                    refine ⟨18635053690655204715097829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12423369127103469810065219 18635053690655204715097829)
                    ·
                      refine ⟨3494072566997850884080843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18635053690655204715097829 3494072566997850884080843)
                      ·
                        rfl

theorem cell23_6804682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_6804682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804682 prefixEnd_6804682 := by exact prefixLift 6804682
  have htrace : WordTrace (prefixWord ++ tailWord_6804682) baseStart_6804682 baseEnd_6804682 := by
    simpa [prefixWord, tailWord_6804682, baseEnd_6804682] using wordTrace_append hprefix tailTrace_6804682
  have hstable : (prefixWord ++ tailWord_6804682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804682).length < 2 ^ (prefixWord ++ tailWord_6804682).sum := by decide
  have hdescent : baseEnd_6804682 < baseStart_6804682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804695 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_6804695 : Nat := 118140960795 + 6804695 * 2 ^ 59
def prefixEnd_6804695 : Nat := 4983230072969 + 3 ^ 40 * 6804695 * 2
def baseEnd_6804695 : Nat := 3494079242246359333218283

theorem tailTrace_6804695 : CollatzResearch.WordTrace tailWord_6804695 prefixEnd_6804695 3494079242246359333218283 := by
  unfold tailWord_6804695
  simp only [CollatzResearch.WordTrace]
  refine ⟨248187616082759639227671539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165458410721839759485114359 248187616082759639227671539)
  ·
    refine ⟨372281424124139458841507309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248187616082759639227671539 372281424124139458841507309)
    ·
      refine ⟨139605534046552297065565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372281424124139458841507309 139605534046552297065565241)
      ·
        refine ⟨104704150534914222799173931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139605534046552297065565241 104704150534914222799173931)
        ·
          refine ⟨157056225802371334198760897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104704150534914222799173931 157056225802371334198760897)
          ·
            refine ⟨117792169351778500649070673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157056225802371334198760897 117792169351778500649070673)
            ·
              refine ⟨88344127013833875486803005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117792169351778500649070673 88344127013833875486803005)
              ·
                refine ⟨33129047630187703307551127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88344127013833875486803005 33129047630187703307551127)
                ·
                  refine ⟨49693571445281554961326691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33129047630187703307551127 49693571445281554961326691)
                  ·
                    refine ⟨74540357167922332441990037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49693571445281554961326691 74540357167922332441990037)
                    ·
                      refine ⟨3494079242246359333218283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74540357167922332441990037 3494079242246359333218283)
                      ·
                        rfl

theorem cell23_6804695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_6804695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804695 prefixEnd_6804695 := by exact prefixLift 6804695
  have htrace : WordTrace (prefixWord ++ tailWord_6804695) baseStart_6804695 baseEnd_6804695 := by
    simpa [prefixWord, tailWord_6804695, baseEnd_6804695] using wordTrace_append hprefix tailTrace_6804695
  have hstable : (prefixWord ++ tailWord_6804695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804695).length < 2 ^ (prefixWord ++ tailWord_6804695).sum := by decide
  have hdescent : baseEnd_6804695 < baseStart_6804695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804712 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6804712 : Nat := 118140960795 + 6804712 * 2 ^ 59
def prefixEnd_6804712 : Nat := 4983230072969 + 3 ^ 40 * 6804712 * 2
def baseEnd_6804712 : Nat := 3494087971417485766705705

theorem tailTrace_6804712 : CollatzResearch.WordTrace tailWord_6804712 prefixEnd_6804712 3494087971417485766705705 := by
  unfold tailWord_6804712
  simp only [CollatzResearch.WordTrace]
  refine ⟨124094118061849025565520195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165458824082465367420693593 124094118061849025565520195)
  ·
    refine ⟨186141177092773538348280293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124094118061849025565520195 186141177092773538348280293)
    ·
      refine ⟨34901470704895038440302555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186141177092773538348280293 34901470704895038440302555)
      ·
        refine ⟨52352206057342557660453833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34901470704895038440302555 52352206057342557660453833)
        ·
          refine ⟨39264154543006918245340375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52352206057342557660453833 39264154543006918245340375)
          ·
            refine ⟨58896231814510377368010563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39264154543006918245340375 58896231814510377368010563)
            ·
              refine ⟨88344347721765566052015845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58896231814510377368010563 88344347721765566052015845)
              ·
                refine ⟨16564565197831043634752971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88344347721765566052015845 16564565197831043634752971)
                ·
                  refine ⟨24846847796746565452129457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16564565197831043634752971 24846847796746565452129457)
                  ·
                    refine ⟨18635135847559924089097093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24846847796746565452129457 18635135847559924089097093)
                    ·
                      refine ⟨3494087971417485766705705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18635135847559924089097093 3494087971417485766705705)
                      ·
                        rfl

theorem cell23_6804712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6804712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804712 prefixEnd_6804712 := by exact prefixLift 6804712
  have htrace : WordTrace (prefixWord ++ tailWord_6804712) baseStart_6804712 baseEnd_6804712 := by
    simpa [prefixWord, tailWord_6804712, baseEnd_6804712] using wordTrace_append hprefix tailTrace_6804712
  have hstable : (prefixWord ++ tailWord_6804712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804712).length < 2 ^ (prefixWord ++ tailWord_6804712).sum := by decide
  have hdescent : baseEnd_6804712 < baseStart_6804712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804716 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_6804716 : Nat := 118140960795 + 6804716 * 2 ^ 59
def prefixEnd_6804716 : Nat := 4983230072969 + 3 ^ 40 * 6804716 * 2
def baseEnd_6804716 : Nat := 3494090025340103751055687

theorem tailTrace_6804716 : CollatzResearch.WordTrace tailWord_6804716 prefixEnd_6804716 3494090025340103751055687 := by
  unfold tailWord_6804716
  simp only [CollatzResearch.WordTrace]
  refine ⟨124094191007841779907093001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165458921343789039876124001 124094191007841779907093001)
  ·
    refine ⟨93070643255881334930319751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124094191007841779907093001 93070643255881334930319751)
    ·
      refine ⟨139605964883822002395479627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93070643255881334930319751 139605964883822002395479627)
      ·
        refine ⟨209408947325733003593219441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139605964883822002395479627 209408947325733003593219441)
        ·
          refine ⟨157056710494299752694914581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209408947325733003593219441 157056710494299752694914581)
          ·
            refine ⟨7362033304420300907574121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157056710494299752694914581 7362033304420300907574121)
            ·
              refine ⟨5521524978315225680680591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362033304420300907574121 5521524978315225680680591)
              ·
                refine ⟨8282287467472838521020887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521524978315225680680591 8282287467472838521020887)
                ·
                  refine ⟨12423431201209257781531331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8282287467472838521020887 12423431201209257781531331)
                  ·
                    refine ⟨18635146801813886672296997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12423431201209257781531331 18635146801813886672296997)
                    ·
                      refine ⟨3494090025340103751055687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18635146801813886672296997 3494090025340103751055687)
                      ·
                        rfl

theorem cell23_6804716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_6804716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804716 prefixEnd_6804716 := by exact prefixLift 6804716
  have htrace : WordTrace (prefixWord ++ tailWord_6804716) baseStart_6804716 baseEnd_6804716 := by
    simpa [prefixWord, tailWord_6804716, baseEnd_6804716] using wordTrace_append hprefix tailTrace_6804716
  have hstable : (prefixWord ++ tailWord_6804716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804716).length < 2 ^ (prefixWord ++ tailWord_6804716).sum := by decide
  have hdescent : baseEnd_6804716 < baseStart_6804716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804722 : List Nat := [3, 2, 1, 3, 3, 1, 10]
def baseStart_6804722 : Nat := 118140960795 + 6804722 * 2 ^ 59
def prefixEnd_6804722 : Nat := 4983230072969 + 3 ^ 40 * 6804722 * 2
def baseEnd_6804722 : Nat := 43136951928691737377539

theorem tailTrace_6804722 : CollatzResearch.WordTrace tailWord_6804722 prefixEnd_6804722 43136951928691737377539 := by
  unfold tailWord_6804722
  simp only [CollatzResearch.WordTrace]
  refine ⟨62047150213415455709726105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165459067235774548559269613 62047150213415455709726105)
  ·
    refine ⟨46535362660061591782294579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62047150213415455709726105 46535362660061591782294579)
    ·
      refine ⟨69803043990092387673441869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46535362660061591782294579 69803043990092387673441869)
      ·
        refine ⟨26176141496284645377540701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69803043990092387673441869 26176141496284645377540701)
        ·
          refine ⟨9816053061106742016577763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26176141496284645377540701 9816053061106742016577763)
          ·
            refine ⟨14724079591660113024866645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816053061106742016577763 14724079591660113024866645)
            ·
              refine ⟨43136951928691737377539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14724079591660113024866645 43136951928691737377539)
              ·
                rfl

theorem cell23_6804722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 10].length) (baseStart_6804722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804722 prefixEnd_6804722 := by exact prefixLift 6804722
  have htrace : WordTrace (prefixWord ++ tailWord_6804722) baseStart_6804722 baseEnd_6804722 := by
    simpa [prefixWord, tailWord_6804722, baseEnd_6804722] using wordTrace_append hprefix tailTrace_6804722
  have hstable : (prefixWord ++ tailWord_6804722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804722).length < 2 ^ (prefixWord ++ tailWord_6804722).sum := by decide
  have hdescent : baseEnd_6804722 < baseStart_6804722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804762 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_6804762 : Nat := 118140960795 + 6804762 * 2 ^ 59
def prefixEnd_6804762 : Nat := 4983230072969 + 3 ^ 40 * 6804762 * 2
def baseEnd_6804762 : Nat := 3494113645450210571080475

theorem tailTrace_6804762 : CollatzResearch.WordTrace tailWord_6804762 prefixEnd_6804762 3494113645450210571080475 := by
  unfold tailWord_6804762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62047514943379227417590135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165460039849011273113573693 62047514943379227417590135)
  ·
    refine ⟨93071272415068841126385203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62047514943379227417590135 93071272415068841126385203)
    ·
      refine ⟨139606908622603261689577805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93071272415068841126385203 139606908622603261689577805)
      ·
        refine ⟨52352590733476223133591677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139606908622603261689577805 52352590733476223133591677)
        ·
          refine ⟨19632221525053583675096879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52352590733476223133591677 19632221525053583675096879)
          ·
            refine ⟨29448332287580375512645319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19632221525053583675096879 29448332287580375512645319)
            ·
              refine ⟨44172498431370563268967979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29448332287580375512645319 44172498431370563268967979)
              ·
                refine ⟨66258747647055844903451969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44172498431370563268967979 66258747647055844903451969)
                ·
                  refine ⟨49694060735291883677588977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66258747647055844903451969 49694060735291883677588977)
                  ·
                    refine ⟨37270545551468912758191733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49694060735291883677588977 37270545551468912758191733)
                    ·
                      refine ⟨3494113645450210571080475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37270545551468912758191733 3494113645450210571080475)
                      ·
                        rfl

theorem cell23_6804762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_6804762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804762 prefixEnd_6804762 := by exact prefixLift 6804762
  have htrace : WordTrace (prefixWord ++ tailWord_6804762) baseStart_6804762 baseEnd_6804762 := by
    simpa [prefixWord, tailWord_6804762, baseEnd_6804762] using wordTrace_append hprefix tailTrace_6804762
  have hstable : (prefixWord ++ tailWord_6804762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804762).length < 2 ^ (prefixWord ++ tailWord_6804762).sum := by decide
  have hdescent : baseEnd_6804762 < baseStart_6804762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804767 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 1, 2, 2]
def baseStart_6804767 : Nat := 118140960795 + 6804767 * 2 ^ 59
def prefixEnd_6804767 : Nat := 4983230072969 + 3 ^ 40 * 6804767 * 2
def baseEnd_6804767 : Nat := 3494116212853483051517953

theorem tailTrace_6804767 : CollatzResearch.WordTrace tailWord_6804767 prefixEnd_6804767 3494116212853483051517953 := by
  unfold tailWord_6804767
  simp only [CollatzResearch.WordTrace]
  refine ⟨248190242138498795524292555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165460161425665863682861703 248190242138498795524292555)
  ·
    refine ⟨372285363207748193286438833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248190242138498795524292555 372285363207748193286438833)
    ·
      refine ⟨279214022405811144964829125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372285363207748193286438833 279214022405811144964829125)
      ·
        refine ⟨52352629201089589680905461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279214022405811144964829125 52352629201089589680905461)
        ·
          refine ⟨4908058987602149032584887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52352629201089589680905461 4908058987602149032584887)
          ·
            refine ⟨7362088481403223548877331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908058987602149032584887 7362088481403223548877331)
            ·
              refine ⟨11043132722104835323315997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362088481403223548877331 11043132722104835323315997)
              ·
                refine ⟨4141174770789313246243499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043132722104835323315997 4141174770789313246243499)
                ·
                  refine ⟨6211762156183969869365249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141174770789313246243499 6211762156183969869365249)
                  ·
                    refine ⟨4658821617137977402023937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211762156183969869365249 4658821617137977402023937)
                    ·
                      refine ⟨3494116212853483051517953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658821617137977402023937 3494116212853483051517953)
                      ·
                        rfl

theorem cell23_6804767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_6804767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804767 prefixEnd_6804767 := by exact prefixLift 6804767
  have htrace : WordTrace (prefixWord ++ tailWord_6804767) baseStart_6804767 baseEnd_6804767 := by
    simpa [prefixWord, tailWord_6804767, baseEnd_6804767] using wordTrace_append hprefix tailTrace_6804767
  have hstable : (prefixWord ++ tailWord_6804767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804767).length < 2 ^ (prefixWord ++ tailWord_6804767).sum := by decide
  have hdescent : baseEnd_6804767 < baseStart_6804767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804792 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_6804792 : Nat := 118140960795 + 6804792 * 2 ^ 59
def prefixEnd_6804792 : Nat := 4983230072969 + 3 ^ 40 * 6804792 * 2
def baseEnd_6804792 : Nat := 3494129049869845453705337

theorem tailTrace_6804792 : CollatzResearch.WordTrace tailWord_6804792 prefixEnd_6804792 3494129049869845453705337 := by
  unfold tailWord_6804792
  simp only [CollatzResearch.WordTrace]
  refine ⟨124095576981704112396976315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165460769308938816529301753 124095576981704112396976315)
  ·
    refine ⟨186143365472556168595464473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124095576981704112396976315 186143365472556168595464473)
    ·
      refine ⟨139607524104417126446598355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186143365472556168595464473 139607524104417126446598355)
      ·
        refine ⟨209411286156625689669897533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139607524104417126446598355 209411286156625689669897533)
        ·
          refine ⟨78529232308734633626211575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209411286156625689669897533 78529232308734633626211575)
          ·
            refine ⟨117793848463101950439317363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78529232308734633626211575 117793848463101950439317363)
            ·
              refine ⟨176690772694652925658976045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117793848463101950439317363 176690772694652925658976045)
              ·
                refine ⟨66259039760494847122116017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176690772694652925658976045 66259039760494847122116017)
                ·
                  refine ⟨49694279820371135341587013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66259039760494847122116017 49694279820371135341587013)
                  ·
                    refine ⟨9317677466319587876547565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49694279820371135341587013 9317677466319587876547565)
                    ·
                      refine ⟨3494129049869845453705337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317677466319587876547565 3494129049869845453705337)
                      ·
                        rfl

theorem cell23_6804792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_6804792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804792 prefixEnd_6804792 := by exact prefixLift 6804792
  have htrace : WordTrace (prefixWord ++ tailWord_6804792) baseStart_6804792 baseEnd_6804792 := by
    simpa [prefixWord, tailWord_6804792, baseEnd_6804792] using wordTrace_append hprefix tailTrace_6804792
  have hstable : (prefixWord ++ tailWord_6804792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804792).length < 2 ^ (prefixWord ++ tailWord_6804792).sum := by decide
  have hdescent : baseEnd_6804792 < baseStart_6804792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804840 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6804840 : Nat := 118140960795 + 6804840 * 2 ^ 59
def prefixEnd_6804840 : Nat := 4983230072969 + 3 ^ 40 * 6804840 * 2
def baseEnd_6804840 : Nat := 3494153696941261265905117

theorem tailTrace_6804840 : CollatzResearch.WordTrace tailWord_6804840 prefixEnd_6804840 3494153696941261265905117 := by
  unfold tailWord_6804840
  simp only [CollatzResearch.WordTrace]
  refine ⟨124096452333617164495849987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165461936444822885994466649 124096452333617164495849987)
  ·
    refine ⟨186144678500425746743774981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124096452333617164495849987 186144678500425746743774981)
    ·
      refine ⟨34902127218829827514457809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186144678500425746743774981 34902127218829827514457809)
      ·
        refine ⟨26176595414122370635843357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34902127218829827514457809 26176595414122370635843357)
        ·
          refine ⟨9816223280295888988441259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26176595414122370635843357 9816223280295888988441259)
          ·
            refine ⟨14724334920443833482661889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816223280295888988441259 14724334920443833482661889)
            ·
              refine ⟨11043251190332875111996417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14724334920443833482661889 11043251190332875111996417)
              ·
                refine ⟨8282438392749656333997313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11043251190332875111996417 8282438392749656333997313)
                ·
                  refine ⟨6211828794562242250497985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282438392749656333997313 6211828794562242250497985)
                  ·
                    refine ⟨4658871595921681687873489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211828794562242250497985 4658871595921681687873489)
                    ·
                      refine ⟨3494153696941261265905117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658871595921681687873489 3494153696941261265905117)
                      ·
                        rfl

theorem cell23_6804840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6804840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804840 prefixEnd_6804840 := by exact prefixLift 6804840
  have htrace : WordTrace (prefixWord ++ tailWord_6804840) baseStart_6804840 baseEnd_6804840 := by
    simpa [prefixWord, tailWord_6804840, baseEnd_6804840] using wordTrace_append hprefix tailTrace_6804840
  have hstable : (prefixWord ++ tailWord_6804840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804840).length < 2 ^ (prefixWord ++ tailWord_6804840).sum := by decide
  have hdescent : baseEnd_6804840 < baseStart_6804840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804849 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_6804849 : Nat := 118140960795 + 6804849 * 2 ^ 59
def prefixEnd_6804849 : Nat := 4983230072969 + 3 ^ 40 * 6804849 * 2
def baseEnd_6804849 : Nat := 3494158318267151730692575

theorem tailTrace_6804849 : CollatzResearch.WordTrace tailWord_6804849 prefixEnd_6804849 3494158318267151730692575 := by
  unfold tailWord_6804849
  simp only [CollatzResearch.WordTrace]
  refine ⟨248193232924201723528777601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165462155282801149019185067 248193232924201723528777601)
  ·
    refine ⟨186144924693151292646583201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248193232924201723528777601 186144924693151292646583201)
    ·
      refine ⟨139608693519863469484937401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186144924693151292646583201 139608693519863469484937401)
      ·
        refine ⟨104706520139897602113703051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139608693519863469484937401 104706520139897602113703051)
        ·
          refine ⟨157059780209846403170554577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104706520139897602113703051 157059780209846403170554577)
          ·
            refine ⟨117794835157384802377915933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157059780209846403170554577 117794835157384802377915933)
            ·
              refine ⟨44173063184019300891718475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117794835157384802377915933 44173063184019300891718475)
              ·
                refine ⟨66259594776028951337577713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44173063184019300891718475 66259594776028951337577713)
                ·
                  refine ⟨49694696082021713503183285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66259594776028951337577713 49694696082021713503183285)
                  ·
                    refine ⟨4658877757689535640923433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49694696082021713503183285 4658877757689535640923433)
                    ·
                      refine ⟨3494158318267151730692575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4658877757689535640923433 3494158318267151730692575)
                      ·
                        rfl

theorem cell23_6804849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_6804849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804849 prefixEnd_6804849 := by exact prefixLift 6804849
  have htrace : WordTrace (prefixWord ++ tailWord_6804849) baseStart_6804849 baseEnd_6804849 := by
    simpa [prefixWord, tailWord_6804849, baseEnd_6804849] using wordTrace_append hprefix tailTrace_6804849
  have hstable : (prefixWord ++ tailWord_6804849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804849).length < 2 ^ (prefixWord ++ tailWord_6804849).sum := by decide
  have hdescent : baseEnd_6804849 < baseStart_6804849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804899 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3]
def baseStart_6804899 : Nat := 118140960795 + 6804899 * 2 ^ 59
def prefixEnd_6804899 : Nat := 4983230072969 + 3 ^ 40 * 6804899 * 2
def baseEnd_6804899 : Nat := 3494183992299876535067345

theorem tailTrace_6804899 : CollatzResearch.WordTrace tailWord_6804899 prefixEnd_6804899 3494183992299876535067345 := by
  unfold tailWord_6804899
  simp only [CollatzResearch.WordTrace]
  refine ⟨248195056574020582068097751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165463371049347054712065167 248195056574020582068097751)
  ·
    refine ⟨372292584861030873102146627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248195056574020582068097751 372292584861030873102146627)
    ·
      refine ⟨558438877291546309653219941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372292584861030873102146627 558438877291546309653219941)
      ·
        refine ⟨104707289492164933059978739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558438877291546309653219941 104707289492164933059978739)
        ·
          refine ⟨157060934238247399589968109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104707289492164933059978739 157060934238247399589968109)
          ·
            refine ⟨58897850339342774846238041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157060934238247399589968109 58897850339342774846238041)
            ·
              refine ⟨44173387754507081134678531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58897850339342774846238041 44173387754507081134678531)
              ·
                refine ⟨66260081631760621702017797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44173387754507081134678531 66260081631760621702017797)
                ·
                  refine ⟨12423765305955116569128337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66260081631760621702017797 12423765305955116569128337)
                  ·
                    refine ⟨9317823979466337426846253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12423765305955116569128337 9317823979466337426846253)
                    ·
                      refine ⟨3494183992299876535067345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317823979466337426846253 3494183992299876535067345)
                      ·
                        rfl

theorem cell23_6804899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_6804899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804899 prefixEnd_6804899 := by exact prefixLift 6804899
  have htrace : WordTrace (prefixWord ++ tailWord_6804899) baseStart_6804899 baseEnd_6804899 := by
    simpa [prefixWord, tailWord_6804899, baseEnd_6804899] using wordTrace_append hprefix tailTrace_6804899
  have hstable : (prefixWord ++ tailWord_6804899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804899).length < 2 ^ (prefixWord ++ tailWord_6804899).sum := by decide
  have hdescent : baseEnd_6804899 < baseStart_6804899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804940 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_6804940 : Nat := 118140960795 + 6804940 * 2 ^ 59
def prefixEnd_6804940 : Nat := 4983230072969 + 3 ^ 40 * 6804940 * 2
def baseEnd_6804940 : Nat := 1164735015002236958218219

theorem tailTrace_6804940 : CollatzResearch.WordTrace tailWord_6804940 prefixEnd_6804940 1164735015002236958218219 := by
  unfold tailWord_6804940
  simp only [CollatzResearch.WordTrace]
  refine ⟨124098275983436023035170137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165464367977914697380226849 124098275983436023035170137)
  ·
    refine ⟨93073706987577017276377603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124098275983436023035170137 93073706987577017276377603)
    ·
      refine ⟨139610560481365525914566405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93073706987577017276377603 139610560481365525914566405)
      ·
        refine ⟨26176980090256036108981201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139610560481365525914566405 26176980090256036108981201)
        ·
          refine ⟨19632735067692027081735901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26176980090256036108981201 19632735067692027081735901)
          ·
            refine ⟨7362275650384510155650963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19632735067692027081735901 7362275650384510155650963)
            ·
              refine ⟨11043413475576765233476445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362275650384510155650963 11043413475576765233476445)
              ·
                refine ⟨4141280053341286962553667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043413475576765233476445 4141280053341286962553667)
                ·
                  refine ⟨6211920080011930443830501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141280053341286962553667 6211920080011930443830501)
                  ·
                    refine ⟨1164735015002236958218219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211920080011930443830501 1164735015002236958218219)
                    ·
                      rfl

theorem cell23_6804940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_6804940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804940 prefixEnd_6804940 := by exact prefixLift 6804940
  have htrace : WordTrace (prefixWord ++ tailWord_6804940) baseStart_6804940 baseEnd_6804940 := by
    simpa [prefixWord, tailWord_6804940, baseEnd_6804940] using wordTrace_append hprefix tailTrace_6804940
  have hstable : (prefixWord ++ tailWord_6804940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804940).length < 2 ^ (prefixWord ++ tailWord_6804940).sum := by decide
  have hdescent : baseEnd_6804940 < baseStart_6804940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804963 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6804963 : Nat := 118140960795 + 6804963 * 2 ^ 59
def prefixEnd_6804963 : Nat := 4983230072969 + 3 ^ 40 * 6804963 * 2
def baseEnd_6804963 : Nat := 3494216855061764284667051

theorem tailTrace_6804963 : CollatzResearch.WordTrace tailWord_6804963 prefixEnd_6804963 3494216855061764284667051 := by
  unfold tailWord_6804963
  simp only [CollatzResearch.WordTrace]
  refine ⟨248197390845788720998427543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165464927230525813998951695 248197390845788720998427543)
  ·
    refine ⟨372296086268683081497641315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248197390845788720998427543 372296086268683081497641315)
    ·
      refine ⟨558444129403024622246461973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372296086268683081497641315 558444129403024622246461973)
      ·
        refine ⟨26177068565766779167802905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 558444129403024622246461973 26177068565766779167802905)
        ·
          refine ⟨19632801424325084375852179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26177068565766779167802905 19632801424325084375852179)
          ·
            refine ⟨29449202136487626563778269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19632801424325084375852179 29449202136487626563778269)
            ·
              refine ⟨11043450801182859961416851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29449202136487626563778269 11043450801182859961416851)
              ·
                refine ⟨16565176201774289942125277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11043450801182859961416851 16565176201774289942125277)
                ·
                  refine ⟨6211941075665358728296979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16565176201774289942125277 6211941075665358728296979)
                  ·
                    refine ⟨9317911613498038092445469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6211941075665358728296979 9317911613498038092445469)
                    ·
                      refine ⟨3494216855061764284667051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9317911613498038092445469 3494216855061764284667051)
                      ·
                        rfl

theorem cell23_6804963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6804963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804963 prefixEnd_6804963 := by exact prefixLift 6804963
  have htrace : WordTrace (prefixWord ++ tailWord_6804963) baseStart_6804963 baseEnd_6804963 := by
    simpa [prefixWord, tailWord_6804963, baseEnd_6804963] using wordTrace_append hprefix tailTrace_6804963
  have hstable : (prefixWord ++ tailWord_6804963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804963).length < 2 ^ (prefixWord ++ tailWord_6804963).sum := by decide
  have hdescent : baseEnd_6804963 < baseStart_6804963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804970 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_6804970 : Nat := 118140960795 + 6804970 * 2 ^ 59
def prefixEnd_6804970 : Nat := 4983230072969 + 3 ^ 40 * 6804970 * 2
def baseEnd_6804970 : Nat := 388246716602927306364391

theorem tailTrace_6804970 : CollatzResearch.WordTrace tailWord_6804970 prefixEnd_6804970 388246716602927306364391 := by
  unfold tailWord_6804970
  simp only [CollatzResearch.WordTrace]
  refine ⟨62049411539190840298483091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165465097437842240795954909 62049411539190840298483091)
  ·
    refine ⟨93074117308786260447724637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62049411539190840298483091 93074117308786260447724637)
    ·
      refine ⟨34902793990794847667896739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93074117308786260447724637 34902793990794847667896739)
      ·
        refine ⟨52354190986192271501845109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34902793990794847667896739 52354190986192271501845109)
        ·
          refine ⟨4908205404955525453297979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52354190986192271501845109 4908205404955525453297979)
          ·
            refine ⟨7362308107433288179946969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908205404955525453297979 7362308107433288179946969)
            ·
              refine ⟨5521731080574966134960227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362308107433288179946969 5521731080574966134960227)
              ·
                refine ⟨8282596620862449202440341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521731080574966134960227 8282596620862449202440341)
                ·
                  refine ⟨388246716602927306364391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8282596620862449202440341 388246716602927306364391)
                  ·
                    rfl

theorem cell23_6804970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_6804970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804970 prefixEnd_6804970 := by exact prefixLift 6804970
  have htrace : WordTrace (prefixWord ++ tailWord_6804970) baseStart_6804970 baseEnd_6804970 := by
    simpa [prefixWord, tailWord_6804970, baseEnd_6804970] using wordTrace_append hprefix tailTrace_6804970
  have hstable : (prefixWord ++ tailWord_6804970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804970).length < 2 ^ (prefixWord ++ tailWord_6804970).sum := by decide
  have hdescent : baseEnd_6804970 < baseStart_6804970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6804979 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 6, 4]
def baseStart_6804979 : Nat := 118140960795 + 6804979 * 2 ^ 59
def prefixEnd_6804979 : Nat := 4983230072969 + 3 ^ 40 * 6804979 * 2
def baseEnd_6804979 : Nat := 1164741690250745407355659

theorem tailTrace_6804979 : CollatzResearch.WordTrace tailWord_6804979 prefixEnd_6804979 1164741690250745407355659 := by
  unfold tailWord_6804979
  simp only [CollatzResearch.WordTrace]
  refine ⟨248197974413730755731009991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165465316275820503820673327 248197974413730755731009991)
  ·
    refine ⟨372296961620596133596514987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248197974413730755731009991 372296961620596133596514987)
    ·
      refine ⟨558445442430894200394772481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372296961620596133596514987 558445442430894200394772481)
      ·
        refine ⟨418834081823170650296079361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558445442430894200394772481 418834081823170650296079361)
        ·
          refine ⟨314125561367377987722059521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418834081823170650296079361 314125561367377987722059521)
          ·
            refine ⟨235594171025533490791544641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314125561367377987722059521 235594171025533490791544641)
            ·
              refine ⟨176695628269150118093658481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235594171025533490791544641 176695628269150118093658481)
              ·
                refine ⟨132521721201862588570243861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176695628269150118093658481 132521721201862588570243861)
                ·
                  refine ⟨6211955681337308839230181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132521721201862588570243861 6211955681337308839230181)
                  ·
                    refine ⟨1164741690250745407355659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211955681337308839230181 1164741690250745407355659)
                    ·
                      rfl

theorem cell23_6804979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 4].length) (baseStart_6804979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6804979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6804979 prefixEnd_6804979 := by exact prefixLift 6804979
  have htrace : WordTrace (prefixWord ++ tailWord_6804979) baseStart_6804979 baseEnd_6804979 := by
    simpa [prefixWord, tailWord_6804979, baseEnd_6804979] using wordTrace_append hprefix tailTrace_6804979
  have hstable : (prefixWord ++ tailWord_6804979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6804979).length < 2 ^ (prefixWord ++ tailWord_6804979).sum := by decide
  have hdescent : baseEnd_6804979 < baseStart_6804979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6804979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805013 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_6805013 : Nat := 118140960795 + 6805013 * 2 ^ 59
def prefixEnd_6805013 : Nat := 4983230072969 + 3 ^ 40 * 6805013 * 2
def baseEnd_6805013 : Nat := 1164747509698163029680607

theorem tailTrace_6805013 : CollatzResearch.WordTrace tailWord_6805013 prefixEnd_6805013 1164747509698163029680607 := by
  unfold tailWord_6805013
  simp only [CollatzResearch.WordTrace]
  refine ⟨248199214495607579537747693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165466142997071719691831795 248199214495607579537747693)
  ·
    refine ⟨93074705435852842326655385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248199214495607579537747693 93074705435852842326655385)
    ·
      refine ⟨69806029076889631744991539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93074705435852842326655385 69806029076889631744991539)
      ·
        refine ⟨104709043615334447617487309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69806029076889631744991539 104709043615334447617487309)
        ·
          refine ⟨39265891355750417856557741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104709043615334447617487309 39265891355750417856557741)
          ·
            refine ⟨14724709258406406696209153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39265891355750417856557741 14724709258406406696209153)
            ·
              refine ⟨11043531943804805022156865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14724709258406406696209153 11043531943804805022156865)
              ·
                refine ⟨8282648957853603766617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11043531943804805022156865 8282648957853603766617649)
                ·
                  refine ⟨6211986718390202824963237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282648957853603766617649 6211986718390202824963237)
                  ·
                    refine ⟨1164747509698163029680607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211986718390202824963237 1164747509698163029680607)
                    ·
                      rfl

theorem cell23_6805013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_6805013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805013 prefixEnd_6805013 := by exact prefixLift 6805013
  have htrace : WordTrace (prefixWord ++ tailWord_6805013) baseStart_6805013 baseEnd_6805013 := by
    simpa [prefixWord, tailWord_6805013, baseEnd_6805013] using wordTrace_append hprefix tailTrace_6805013
  have hstable : (prefixWord ++ tailWord_6805013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805013).length < 2 ^ (prefixWord ++ tailWord_6805013).sum := by decide
  have hdescent : baseEnd_6805013 < baseStart_6805013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805036 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_6805036 : Nat := 118140960795 + 6805036 * 2 ^ 59
def prefixEnd_6805036 : Nat := 4983230072969 + 3 ^ 40 * 6805036 * 2
def baseEnd_6805036 : Nat := 3494254339149542499054215

theorem tailTrace_6805036 : CollatzResearch.WordTrace tailWord_6805036 prefixEnd_6805036 3494254339149542499054215 := by
  unfold tailWord_6805036
  simp only [CollatzResearch.WordTrace]
  refine ⟨124100026687262127232917481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165466702249682836310556641 124100026687262127232917481)
  ·
    refine ⟨93075020015446595424688111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124100026687262127232917481 93075020015446595424688111)
    ·
      refine ⟨139612530023169893137032167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93075020015446595424688111 139612530023169893137032167)
      ·
        refine ⟨209418795034754839705548251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139612530023169893137032167 209418795034754839705548251)
        ·
          refine ⟨314128192552132259558322377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209418795034754839705548251 314128192552132259558322377)
          ·
            refine ⟨235596144414099194668741783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314128192552132259558322377 235596144414099194668741783)
            ·
              refine ⟨353394216621148792003112675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235596144414099194668741783 353394216621148792003112675)
              ·
                refine ⟨530091324931723188004669013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353394216621148792003112675 530091324931723188004669013)
                ·
                  refine ⟨6212007714043631109429715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 530091324931723188004669013 6212007714043631109429715)
                  ·
                    refine ⟨9318011571065446664144573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212007714043631109429715 9318011571065446664144573)
                    ·
                      refine ⟨3494254339149542499054215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318011571065446664144573 3494254339149542499054215)
                      ·
                        rfl

theorem cell23_6805036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_6805036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805036 prefixEnd_6805036 := by exact prefixLift 6805036
  have htrace : WordTrace (prefixWord ++ tailWord_6805036) baseStart_6805036 baseEnd_6805036 := by
    simpa [prefixWord, tailWord_6805036, baseEnd_6805036] using wordTrace_append hprefix tailTrace_6805036
  have hstable : (prefixWord ++ tailWord_6805036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805036).length < 2 ^ (prefixWord ++ tailWord_6805036).sum := by decide
  have hdescent : baseEnd_6805036 < baseStart_6805036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805144 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6805144 : Nat := 118140960795 + 6805144 * 2 ^ 59
def prefixEnd_6805144 : Nat := 4983230072969 + 3 ^ 40 * 6805144 * 2
def baseEnd_6805144 : Nat := 3494309795060228076503719

theorem tailTrace_6805144 : CollatzResearch.WordTrace tailWord_6805144 prefixEnd_6805144 3494309795060228076503719 := by
  unfold tailWord_6805144
  simp only [CollatzResearch.WordTrace]
  refine ⟨124101996229066494455383243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165469328305421992607177657 124101996229066494455383243)
  ·
    refine ⟨186152994343599741683074865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124101996229066494455383243 186152994343599741683074865)
    ·
      refine ⟨139614745757699806262306149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186152994343599741683074865 139614745757699806262306149)
      ·
        refine ⟨26177764829568713674182403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139614745757699806262306149 26177764829568713674182403)
        ·
          refine ⟨39266647244353070511273605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177764829568713674182403 39266647244353070511273605)
          ·
            refine ⟨7362496358316200720863801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39266647244353070511273605 7362496358316200720863801)
            ·
              refine ⟨5521872268737150540647851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362496358316200720863801 5521872268737150540647851)
              ·
                refine ⟨8282808403105725810971777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521872268737150540647851 8282808403105725810971777)
                ·
                  refine ⟨6212106302329294358228833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282808403105725810971777 6212106302329294358228833)
                  ·
                    refine ⟨4659079726746970768671625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212106302329294358228833 4659079726746970768671625)
                    ·
                      refine ⟨3494309795060228076503719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659079726746970768671625 3494309795060228076503719)
                      ·
                        rfl

theorem cell23_6805144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6805144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805144 prefixEnd_6805144 := by exact prefixLift 6805144
  have htrace : WordTrace (prefixWord ++ tailWord_6805144) baseStart_6805144 baseEnd_6805144 := by
    simpa [prefixWord, tailWord_6805144, baseEnd_6805144] using wordTrace_append hprefix tailTrace_6805144
  have hstable : (prefixWord ++ tailWord_6805144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805144).length < 2 ^ (prefixWord ++ tailWord_6805144).sum := by decide
  have hdescent : baseEnd_6805144 < baseStart_6805144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805183 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 4, 2]
def baseStart_6805183 : Nat := 118140960795 + 6805183 * 2 ^ 59
def prefixEnd_6805183 : Nat := 4983230072969 + 3 ^ 40 * 6805183 * 2
def baseEnd_6805183 : Nat := 3494329820805753423916039

theorem tailTrace_6805183 : CollatzResearch.WordTrace tailWord_6805183 prefixEnd_6805183 3494329820805753423916039 := by
  unfold tailWord_6805183
  simp only [CollatzResearch.WordTrace]
  refine ⟨248205414904991698571436203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165470276603327799047624135 248205414904991698571436203)
  ·
    refine ⟨372308122357487547857154305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248205414904991698571436203 372308122357487547857154305)
    ·
      refine ⟨279231091768115660892865729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372308122357487547857154305 279231091768115660892865729)
      ·
        refine ⟨209423318826086745669649297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279231091768115660892865729 209423318826086745669649297)
        ·
          refine ⟨157067489119565059252236973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209423318826086745669649297 157067489119565059252236973)
          ·
            refine ⟨58900308419836897219588865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157067489119565059252236973 58900308419836897219588865)
            ·
              refine ⟨44175231314877672914691649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58900308419836897219588865 44175231314877672914691649)
              ·
                refine ⟨33131423486158254686018737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44175231314877672914691649 33131423486158254686018737)
                ·
                  refine ⟨24848567614618691014514053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33131423486158254686018737 24848567614618691014514053)
                  ·
                    refine ⟨4659106427741004565221385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24848567614618691014514053 4659106427741004565221385)
                    ·
                      refine ⟨3494329820805753423916039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659106427741004565221385 3494329820805753423916039)
                      ·
                        rfl

theorem cell23_6805183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_6805183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805183 prefixEnd_6805183 := by exact prefixLift 6805183
  have htrace : WordTrace (prefixWord ++ tailWord_6805183) baseStart_6805183 baseEnd_6805183 := by
    simpa [prefixWord, tailWord_6805183, baseEnd_6805183] using wordTrace_append hprefix tailTrace_6805183
  have hstable : (prefixWord ++ tailWord_6805183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805183).length < 2 ^ (prefixWord ++ tailWord_6805183).sum := by decide
  have hdescent : baseEnd_6805183 < baseStart_6805183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805217 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_6805217 : Nat := 118140960795 + 6805217 * 2 ^ 59
def prefixEnd_6805217 : Nat := 4983230072969 + 3 ^ 40 * 6805217 * 2
def baseEnd_6805217 : Nat := 3494347279148006290890883

theorem tailTrace_6805217 : CollatzResearch.WordTrace tailWord_6805217 prefixEnd_6805217 3494347279148006290890883 := by
  unfold tailWord_6805217
  simp only [CollatzResearch.WordTrace]
  refine ⟨248206654986868522378173905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165471103324579014918782603 248206654986868522378173905)
  ·
    refine ⟨186154991240151391783630429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248206654986868522378173905 186154991240151391783630429)
    ·
      refine ⟨69808121715056771918861411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186154991240151391783630429 69808121715056771918861411)
      ·
        refine ⟨104712182572585157878292117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69808121715056771918861411 104712182572585157878292117)
        ·
          refine ⟨4908383558089929275544943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104712182572585157878292117 4908383558089929275544943)
          ·
            refine ⟨7362575337134893913317415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908383558089929275544943 7362575337134893913317415)
            ·
              refine ⟨11043863005702340869976123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362575337134893913317415 11043863005702340869976123)
              ·
                refine ⟨16565794508553511304964185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11043863005702340869976123 16565794508553511304964185)
                ·
                  refine ⟨12424345881415133478723139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16565794508553511304964185 12424345881415133478723139)
                  ·
                    refine ⟨18636518822122700218084709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12424345881415133478723139 18636518822122700218084709)
                    ·
                      refine ⟨3494347279148006290890883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18636518822122700218084709 3494347279148006290890883)
                      ·
                        rfl

theorem cell23_6805217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_6805217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805217 prefixEnd_6805217 := by exact prefixLift 6805217
  have htrace : WordTrace (prefixWord ++ tailWord_6805217) baseStart_6805217 baseEnd_6805217 := by
    simpa [prefixWord, tailWord_6805217, baseEnd_6805217] using wordTrace_append hprefix tailTrace_6805217
  have hstable : (prefixWord ++ tailWord_6805217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805217).length < 2 ^ (prefixWord ++ tailWord_6805217).sum := by decide
  have hdescent : baseEnd_6805217 < baseStart_6805217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805278 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6805278 : Nat := 118140960795 + 6805278 * 2 ^ 59
def prefixEnd_6805278 : Nat := 4983230072969 + 3 ^ 40 * 6805278 * 2
def baseEnd_6805278 : Nat := 1164792867155976850742701

theorem tailTrace_6805278 : CollatzResearch.WordTrace tailWord_6805278 prefixEnd_6805278 1164792867155976850742701 := by
  unfold tailWord_6805278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026109979955941224518061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165472586559765019864096325 31026109979955941224518061)
  ·
    refine ⟨11634791242483477959194273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31026109979955941224518061 11634791242483477959194273)
    ·
      refine ⟨8726093431862608469395705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11634791242483477959194273 8726093431862608469395705)
      ·
        refine ⟨6544570073896956352046779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726093431862608469395705 6544570073896956352046779)
        ·
          refine ⟨9816855110845434528070169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544570073896956352046779 9816855110845434528070169)
          ·
            refine ⟨7362641333134075896052627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9816855110845434528070169 7362641333134075896052627)
            ·
              refine ⟨11043961999701113844078941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362641333134075896052627 11043961999701113844078941)
              ·
                refine ⟨4141485749887917691529603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043961999701113844078941 4141485749887917691529603)
                ·
                  refine ⟨6212228624831876537294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141485749887917691529603 6212228624831876537294405)
                  ·
                    refine ⟨1164792867155976850742701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212228624831876537294405 1164792867155976850742701)
                    ·
                      rfl

theorem cell23_6805278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6805278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805278 prefixEnd_6805278 := by exact prefixLift 6805278
  have htrace : WordTrace (prefixWord ++ tailWord_6805278) baseStart_6805278 baseEnd_6805278 := by
    simpa [prefixWord, tailWord_6805278, baseEnd_6805278] using wordTrace_append hprefix tailTrace_6805278
  have hstable : (prefixWord ++ tailWord_6805278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805278).length < 2 ^ (prefixWord ++ tailWord_6805278).sum := by decide
  have hdescent : baseEnd_6805278 < baseStart_6805278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805283 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 4, 4]
def baseStart_6805283 : Nat := 118140960795 + 6805283 * 2 ^ 59
def prefixEnd_6805283 : Nat := 4983230072969 + 3 ^ 40 * 6805283 * 2
def baseEnd_6805283 : Nat := 1164793722957067677555193

theorem tailTrace_6805283 : CollatzResearch.WordTrace tailWord_6805283 prefixEnd_6805283 1164793722957067677555193 := by
  unfold tailWord_6805283
  simp only [CollatzResearch.WordTrace]
  refine ⟨248209062204629415650076503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165472708136419610433384335 248209062204629415650076503)
  ·
    refine ⟨372313593306944123475114755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248209062204629415650076503 372313593306944123475114755)
    ·
      refine ⟨558470389960416185212672133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372313593306944123475114755 558470389960416185212672133)
      ·
        refine ⟨104713198117578034727376025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558470389960416185212672133 104713198117578034727376025)
        ·
          refine ⟨78534898588183526045532019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104713198117578034727376025 78534898588183526045532019)
          ·
            refine ⟨117802347882275289068298029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78534898588183526045532019 117802347882275289068298029)
            ·
              refine ⟨44175880455853233400611761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117802347882275289068298029 44175880455853233400611761)
              ·
                refine ⟨33131910341889925050458821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44175880455853233400611761 33131910341889925050458821)
                ·
                  refine ⟨6212233189104360946961029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33131910341889925050458821 6212233189104360946961029)
                  ·
                    refine ⟨1164793722957067677555193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212233189104360946961029 1164793722957067677555193)
                    ·
                      rfl

theorem cell23_6805283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 4].length) (baseStart_6805283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805283 prefixEnd_6805283 := by exact prefixLift 6805283
  have htrace : WordTrace (prefixWord ++ tailWord_6805283) baseStart_6805283 baseEnd_6805283 := by
    simpa [prefixWord, tailWord_6805283, baseEnd_6805283] using wordTrace_append hprefix tailTrace_6805283
  have hstable : (prefixWord ++ tailWord_6805283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805283).length < 2 ^ (prefixWord ++ tailWord_6805283).sum := by decide
  have hdescent : baseEnd_6805283 < baseStart_6805283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805284 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_6805284 : Nat := 118140960795 + 6805284 * 2 ^ 59
def prefixEnd_6805284 : Nat := 4983230072969 + 3 ^ 40 * 6805284 * 2
def baseEnd_6805284 : Nat := 3494381682351857528753075

theorem tailTrace_6805284 : CollatzResearch.WordTrace tailWord_6805284 prefixEnd_6805284 3494381682351857528753075 := by
  unfold tailWord_6805284
  simp only [CollatzResearch.WordTrace]
  refine ⟨124104549338812896410431453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165472732451750528547241937 124104549338812896410431453)
  ·
    refine ⟨46539206002054836153911795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124104549338812896410431453 46539206002054836153911795)
    ·
      refine ⟨69808809003082254230867693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46539206002054836153911795 69808809003082254230867693)
      ·
        refine ⟨26178303376155845336575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69808809003082254230867693 26178303376155845336575385)
        ·
          refine ⟨19633727532116884002431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26178303376155845336575385 19633727532116884002431539)
          ·
            refine ⟨29450591298175326003647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19633727532116884002431539 29450591298175326003647309)
            ·
              refine ⟨11043971736815747251367741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29450591298175326003647309 11043971736815747251367741)
              ·
                refine ⟨4141489401305905219262903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043971736815747251367741 4141489401305905219262903)
                ·
                  refine ⟨6212234101958857828894355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141489401305905219262903 6212234101958857828894355)
                  ·
                    refine ⟨9318351152938286743341533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212234101958857828894355 9318351152938286743341533)
                    ·
                      refine ⟨3494381682351857528753075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318351152938286743341533 3494381682351857528753075)
                      ·
                        rfl

theorem cell23_6805284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_6805284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805284 prefixEnd_6805284 := by exact prefixLift 6805284
  have htrace : WordTrace (prefixWord ++ tailWord_6805284) baseStart_6805284 baseEnd_6805284 := by
    simpa [prefixWord, tailWord_6805284, baseEnd_6805284] using wordTrace_append hprefix tailTrace_6805284
  have hstable : (prefixWord ++ tailWord_6805284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805284).length < 2 ^ (prefixWord ++ tailWord_6805284).sum := by decide
  have hdescent : baseEnd_6805284 < baseStart_6805284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805294 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6805294 : Nat := 118140960795 + 6805294 * 2 ^ 59
def prefixEnd_6805294 : Nat := 4983230072969 + 3 ^ 40 * 6805294 * 2
def baseEnd_6805294 : Nat := 3494386817158402489628029

theorem tailTrace_6805294 : CollatzResearch.WordTrace tailWord_6805294 prefixEnd_6805294 3494386817158402489628029 := by
  unfold tailWord_6805294
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026182925948695566090867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165472975605059709685817957 31026182925948695566090867)
  ·
    refine ⟨46539274388923043349136301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31026182925948695566090867 46539274388923043349136301)
    ·
      refine ⟨17452227895846141255926113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46539274388923043349136301 17452227895846141255926113)
      ·
        refine ⟨13089170921884605941944585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17452227895846141255926113 13089170921884605941944585)
        ·
          refine ⟨9816878191413454456458439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13089170921884605941944585 9816878191413454456458439)
          ·
            refine ⟨14725317287120181684687659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816878191413454456458439 14725317287120181684687659)
            ·
              refine ⟨22087975930680272527031489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14725317287120181684687659 22087975930680272527031489)
              ·
                refine ⟨16565981948010204395273617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22087975930680272527031489 16565981948010204395273617)
                ·
                  refine ⟨12424486461007653296455213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16565981948010204395273617 12424486461007653296455213)
                  ·
                    refine ⟨4659182422877869986170705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12424486461007653296455213 4659182422877869986170705)
                    ·
                      refine ⟨3494386817158402489628029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659182422877869986170705 3494386817158402489628029)
                      ·
                        rfl

theorem cell23_6805294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6805294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805294 prefixEnd_6805294 := by exact prefixLift 6805294
  have htrace : WordTrace (prefixWord ++ tailWord_6805294) baseStart_6805294 baseEnd_6805294 := by
    simpa [prefixWord, tailWord_6805294, baseEnd_6805294] using wordTrace_append hprefix tailTrace_6805294
  have hstable : (prefixWord ++ tailWord_6805294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805294).length < 2 ^ (prefixWord ++ tailWord_6805294).sum := by decide
  have hdescent : baseEnd_6805294 < baseStart_6805294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805301 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_6805301 : Nat := 118140960795 + 6805301 * 2 ^ 59
def prefixEnd_6805301 : Nat := 4983230072969 + 3 ^ 40 * 6805301 * 2
def baseEnd_6805301 : Nat := 3494390411522983962240497

theorem tailTrace_6805301 : CollatzResearch.WordTrace tailWord_6805301 prefixEnd_6805301 3494390411522983962240497 := by
  unfold tailWord_6805301
  simp only [CollatzResearch.WordTrace]
  refine ⟨248209718718564204724231757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165473145812376136482821171 248209718718564204724231757)
  ·
    refine ⟨93078644519461576771586909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248209718718564204724231757 93078644519461576771586909)
    ·
      refine ⟨34904491694798091289345091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93078644519461576771586909 34904491694798091289345091)
      ·
        refine ⟨52356737542197136934017637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34904491694798091289345091 52356737542197136934017637)
        ·
          refine ⟨9816888289161963175128307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52356737542197136934017637 9816888289161963175128307)
          ·
            refine ⟨14725332433742944762692461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816888289161963175128307 14725332433742944762692461)
            ·
              refine ⟨5521999662653604286009673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14725332433742944762692461 5521999662653604286009673)
              ·
                refine ⟨4141499746990203214507255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521999662653604286009673 4141499746990203214507255)
                ·
                  refine ⟨6212249620485304821760883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141499746990203214507255 6212249620485304821760883)
                  ·
                    refine ⟨9318374430727957232641325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212249620485304821760883 9318374430727957232641325)
                    ·
                      refine ⟨3494390411522983962240497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318374430727957232641325 3494390411522983962240497)
                      ·
                        rfl

theorem cell23_6805301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_6805301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805301 prefixEnd_6805301 := by exact prefixLift 6805301
  have htrace : WordTrace (prefixWord ++ tailWord_6805301) baseStart_6805301 baseEnd_6805301 := by
    simpa [prefixWord, tailWord_6805301, baseEnd_6805301] using wordTrace_append hprefix tailTrace_6805301
  have hstable : (prefixWord ++ tailWord_6805301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805301).length < 2 ^ (prefixWord ++ tailWord_6805301).sum := by decide
  have hdescent : baseEnd_6805301 < baseStart_6805301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805310 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6805310 : Nat := 118140960795 + 6805310 * 2 ^ 59
def prefixEnd_6805310 : Nat := 4983230072969 + 3 ^ 40 * 6805310 * 2
def baseEnd_6805310 : Nat := 3494395032848874427027955

theorem tailTrace_6805310 : CollatzResearch.WordTrace tailWord_6805310 prefixEnd_6805310 3494395032848874427027955 := by
  unfold tailWord_6805310
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026255871941449907663673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165473364650354399507539589 31026255871941449907663673)
  ·
    refine ⟨23269691903956087430747755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31026255871941449907663673 23269691903956087430747755)
    ·
      refine ⟨34904537855934131146121633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23269691903956087430747755 34904537855934131146121633)
      ·
        refine ⟨26178403391950598359591225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34904537855934131146121633 26178403391950598359591225)
        ·
          refine ⟨19633802543962948769693419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26178403391950598359591225 19633802543962948769693419)
          ·
            refine ⟨29450703815944423154540129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19633802543962948769693419 29450703815944423154540129)
            ·
              refine ⟨22088027861958317365905097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29450703815944423154540129 22088027861958317365905097)
              ·
                refine ⟨16566020896468738024428823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22088027861958317365905097 16566020896468738024428823)
                ·
                  refine ⟨24849031344703107036643235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16566020896468738024428823 24849031344703107036643235)
                  ·
                    refine ⟨37273547017054660554964853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24849031344703107036643235 37273547017054660554964853)
                    ·
                      refine ⟨3494395032848874427027955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37273547017054660554964853 3494395032848874427027955)
                      ·
                        rfl

theorem cell23_6805310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6805310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805310 prefixEnd_6805310 := by exact prefixLift 6805310
  have htrace : WordTrace (prefixWord ++ tailWord_6805310) baseStart_6805310 baseEnd_6805310 := by
    simpa [prefixWord, tailWord_6805310, baseEnd_6805310] using wordTrace_append hprefix tailTrace_6805310
  have hstable : (prefixWord ++ tailWord_6805310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805310).length < 2 ^ (prefixWord ++ tailWord_6805310).sum := by decide
  have hdescent : baseEnd_6805310 < baseStart_6805310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805324 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6805324 : Nat := 118140960795 + 6805324 * 2 ^ 59
def prefixEnd_6805324 : Nat := 4983230072969 + 3 ^ 40 * 6805324 * 2
def baseEnd_6805324 : Nat := 3494402221578037372252891

theorem tailTrace_6805324 : CollatzResearch.WordTrace tailWord_6805324 prefixEnd_6805324 3494402221578037372252891 := by
  unfold tailWord_6805324
  simp only [CollatzResearch.WordTrace]
  refine ⟨124105278798740439826159513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165473705064987253101546017 124105278798740439826159513)
  ·
    refine ⟨93078959099055329869619635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124105278798740439826159513 93078959099055329869619635)
    ·
      refine ⟨139618438648582994804429453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93078959099055329869619635 139618438648582994804429453)
      ·
        refine ⟨52356914493218623051661045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139618438648582994804429453 52356914493218623051661045)
        ·
          refine ⟨4908460733739245911093223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52356914493218623051661045 4908460733739245911093223)
          ·
            refine ⟨7362691100608868866639835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908460733739245911093223 7362691100608868866639835)
            ·
              refine ⟨11044036650913303299959753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362691100608868866639835 11044036650913303299959753)
              ·
                refine ⟨8283027488184977474969815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11044036650913303299959753 8283027488184977474969815)
                ·
                  refine ⟨12424541232277466212454723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8283027488184977474969815 12424541232277466212454723)
                  ·
                    refine ⟨18636811848416199318682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12424541232277466212454723 18636811848416199318682085)
                    ·
                      refine ⟨3494402221578037372252891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18636811848416199318682085 3494402221578037372252891)
                      ·
                        rfl

theorem cell23_6805324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6805324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805324 prefixEnd_6805324 := by exact prefixLift 6805324
  have htrace : WordTrace (prefixWord ++ tailWord_6805324) baseStart_6805324 baseEnd_6805324 := by
    simpa [prefixWord, tailWord_6805324, baseEnd_6805324] using wordTrace_append hprefix tailTrace_6805324
  have hstable : (prefixWord ++ tailWord_6805324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805324).length < 2 ^ (prefixWord ++ tailWord_6805324).sum := by decide
  have hdescent : baseEnd_6805324 < baseStart_6805324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805357 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_6805357 : Nat := 118140960795 + 6805357 * 2 ^ 59
def prefixEnd_6805357 : Nat := 4983230072969 + 3 ^ 40 * 6805357 * 2
def baseEnd_6805357 : Nat := 3494419166439635743140239

theorem tailTrace_6805357 : CollatzResearch.WordTrace tailWord_6805357 prefixEnd_6805357 3494419166439635743140239 := by
  unfold tailWord_6805357
  simp only [CollatzResearch.WordTrace]
  refine ⟨248211761206361326288270325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165474507470907550858846883 248211761206361326288270325)
  ·
    refine ⟨23269852613096374339525343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248211761206361326288270325 23269852613096374339525343)
    ·
      refine ⟨34904778919644561509288015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23269852613096374339525343 34904778919644561509288015)
      ·
        refine ⟨52357168379466842263932023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34904778919644561509288015 52357168379466842263932023)
        ·
          refine ⟨78535752569200263395898035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52357168379466842263932023 78535752569200263395898035)
          ·
            refine ⟨117803628853800395093847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78535752569200263395898035 117803628853800395093847053)
            ·
              refine ⟨44176360820175148160192645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117803628853800395093847053 44176360820175148160192645)
              ·
                refine ⟨8283067653782840280036121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44176360820175148160192645 8283067653782840280036121)
                ·
                  refine ⟨6212300740337130210027091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283067653782840280036121 6212300740337130210027091)
                  ·
                    refine ⟨9318451110505695315040637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212300740337130210027091 9318451110505695315040637)
                    ·
                      refine ⟨3494419166439635743140239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318451110505695315040637 3494419166439635743140239)
                      ·
                        rfl

theorem cell23_6805357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_6805357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805357 prefixEnd_6805357 := by exact prefixLift 6805357
  have htrace : WordTrace (prefixWord ++ tailWord_6805357) baseStart_6805357 baseEnd_6805357 := by
    simpa [prefixWord, tailWord_6805357, baseEnd_6805357] using wordTrace_append hprefix tailTrace_6805357
  have hstable : (prefixWord ++ tailWord_6805357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805357).length < 2 ^ (prefixWord ++ tailWord_6805357).sum := by decide
  have hdescent : baseEnd_6805357 < baseStart_6805357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805358 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6805358 : Nat := 118140960795 + 6805358 * 2 ^ 59
def prefixEnd_6805358 : Nat := 4983230072969 + 3 ^ 40 * 6805358 * 2
def baseEnd_6805358 : Nat := 3494419679920290239227735

theorem tailTrace_6805358 : CollatzResearch.WordTrace tailWord_6805358 prefixEnd_6805358 3494419679920290239227735 := by
  unfold tailWord_6805358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026474709919712932382091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165474531786238468972704485 31026474709919712932382091)
  ·
    refine ⟨46539712064879569398573137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31026474709919712932382091 46539712064879569398573137)
    ·
      refine ⟨34904784048659677048929853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46539712064879569398573137 34904784048659677048929853)
      ·
        refine ⟨13089294018247378893348695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34904784048659677048929853 13089294018247378893348695)
        ·
          refine ⟨19633941027371068340023043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089294018247378893348695 19633941027371068340023043)
          ·
            refine ⟨29450911541056602510034565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19633941027371068340023043 29450911541056602510034565)
            ·
              refine ⟨5522045913948112970631481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29450911541056602510034565 5522045913948112970631481)
              ·
                refine ⟨4141534435461084727973611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522045913948112970631481 4141534435461084727973611)
                ·
                  refine ⟨6212301653191627091960417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141534435461084727973611 6212301653191627091960417)
                  ·
                    refine ⟨4659226239893720318970313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212301653191627091960417 4659226239893720318970313)
                    ·
                      refine ⟨3494419679920290239227735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659226239893720318970313 3494419679920290239227735)
                      ·
                        rfl

theorem cell23_6805358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6805358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805358 prefixEnd_6805358 := by exact prefixLift 6805358
  have htrace : WordTrace (prefixWord ++ tailWord_6805358) baseStart_6805358 baseEnd_6805358 := by
    simpa [prefixWord, tailWord_6805358, baseEnd_6805358] using wordTrace_append hprefix tailTrace_6805358
  have hstable : (prefixWord ++ tailWord_6805358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805358).length < 2 ^ (prefixWord ++ tailWord_6805358).sum := by decide
  have hdescent : baseEnd_6805358 < baseStart_6805358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805374 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6805374 : Nat := 118140960795 + 6805374 * 2 ^ 59
def prefixEnd_6805374 : Nat := 4983230072969 + 3 ^ 40 * 6805374 * 2
def baseEnd_6805374 : Nat := 3494427895610762176627661

theorem tailTrace_6805374 : CollatzResearch.WordTrace tailWord_6805374 prefixEnd_6805374 3494427895610762176627661 := by
  unfold tailWord_6805374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026547655912467273954897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165474920831533158794426117 31026547655912467273954897)
  ·
    refine ⟨23269910741934350455466173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31026547655912467273954897 23269910741934350455466173)
    ·
      refine ⟨8726216528225381420799815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23269910741934350455466173 8726216528225381420799815)
      ·
        refine ⟨13089324792338072131199723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8726216528225381420799815 13089324792338072131199723)
        ·
          refine ⟨19633987188507108196799585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089324792338072131199723 19633987188507108196799585)
          ·
            refine ⟨14725490391380331147599689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19633987188507108196799585 14725490391380331147599689)
            ·
              refine ⟨11044117793535248360699767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14725490391380331147599689 11044117793535248360699767)
              ·
                refine ⟨16566176690302872541049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11044117793535248360699767 16566176690302872541049651)
                ·
                  refine ⟨24849265035454308811574477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16566176690302872541049651 24849265035454308811574477)
                  ·
                    refine ⟨9318474388295365804340429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24849265035454308811574477 9318474388295365804340429)
                    ·
                      refine ⟨3494427895610762176627661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318474388295365804340429 3494427895610762176627661)
                      ·
                        rfl

theorem cell23_6805374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6805374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805374 prefixEnd_6805374 := by exact prefixLift 6805374
  have htrace : WordTrace (prefixWord ++ tailWord_6805374) baseStart_6805374 baseEnd_6805374 := by
    simpa [prefixWord, tailWord_6805374, baseEnd_6805374] using wordTrace_append hprefix tailTrace_6805374
  have hstable : (prefixWord ++ tailWord_6805374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805374).length < 2 ^ (prefixWord ++ tailWord_6805374).sum := by decide
  have hdescent : baseEnd_6805374 < baseStart_6805374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805397 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_6805397 : Nat := 118140960795 + 6805397 * 2 ^ 59
def prefixEnd_6805397 : Nat := 4983230072969 + 3 ^ 40 * 6805397 * 2
def baseEnd_6805397 : Nat := 3494439705665815586640055

theorem tailTrace_6805397 : CollatzResearch.WordTrace tailWord_6805397 prefixEnd_6805397 3494439705665815586640055 := by
  unfold tailWord_6805397
  simp only [CollatzResearch.WordTrace]
  refine ⟨248213220126216413119726445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165475480084144275413150963 248213220126216413119726445)
  ·
    refine ⟨93079957547331154919897417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248213220126216413119726445 93079957547331154919897417)
    ·
      refine ⟨69809968160498366189923063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93079957547331154919897417 69809968160498366189923063)
      ·
        refine ⟨104714952240747549284884595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69809968160498366189923063 104714952240747549284884595)
        ·
          refine ⟨157072428361121323927326893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104714952240747549284884595 157072428361121323927326893)
          ·
            refine ⟨58902160635420496472747585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157072428361121323927326893 58902160635420496472747585)
            ·
              refine ⟨44176620476565372354560689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58902160635420496472747585 44176620476565372354560689)
              ·
                refine ⟨33132465357424029265920517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44176620476565372354560689 33132465357424029265920517)
                ·
                  refine ⟨6212337254517005487360097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33132465357424029265920517 6212337254517005487360097)
                  ·
                    refine ⟨4659252940887754115520073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212337254517005487360097 4659252940887754115520073)
                    ·
                      refine ⟨3494439705665815586640055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659252940887754115520073 3494439705665815586640055)
                      ·
                        rfl

theorem cell23_6805397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_6805397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805397 prefixEnd_6805397 := by exact prefixLift 6805397
  have htrace : WordTrace (prefixWord ++ tailWord_6805397) baseStart_6805397 baseEnd_6805397 := by
    simpa [prefixWord, tailWord_6805397, baseEnd_6805397] using wordTrace_append hprefix tailTrace_6805397
  have hstable : (prefixWord ++ tailWord_6805397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805397).length < 2 ^ (prefixWord ++ tailWord_6805397).sum := by decide
  have hdescent : baseEnd_6805397 < baseStart_6805397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
