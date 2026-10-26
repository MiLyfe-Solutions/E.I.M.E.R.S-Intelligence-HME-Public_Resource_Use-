import V185TrunkScan20Chunk127

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_778834 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_778834 : Nat := 118140960795 + 778834 * 2 ^ 59
def prefixEnd_778834 : Nat := 4983230072969 + 3 ^ 40 * 778834 * 2
def baseEnd_778834 : Nat := 355481059612365370749523

theorem tailTrace_778834 : CollatzResearch.WordTrace tailWord_778834 prefixEnd_778834 355481059612365370749523 := by
  unfold tailWord_778834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101602415106226775625889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18937606440283271401669037 7101602415106226775625889)
  ·
    refine ⟨5326201811329670081719417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7101602415106226775625889 5326201811329670081719417)
    ·
      refine ⟨3994651358497252561289563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5326201811329670081719417 3994651358497252561289563)
      ·
        refine ⟨5991977037745878841934345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994651358497252561289563 5991977037745878841934345)
        ·
          refine ⟨4493982778309409131450759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5991977037745878841934345 4493982778309409131450759)
          ·
            refine ⟨6740974167464113697176139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493982778309409131450759 6740974167464113697176139)
            ·
              refine ⟨10111461251196170545764209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740974167464113697176139 10111461251196170545764209)
              ·
                refine ⟨7583595938397127909323157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10111461251196170545764209 7583595938397127909323157)
                ·
                  refine ⟨355481059612365370749523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7583595938397127909323157 355481059612365370749523)
                  ·
                    rfl

theorem cell20_778834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_778834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778834 prefixEnd_778834 := by exact prefixLift 778834
  have htrace : WordTrace (prefixWord ++ tailWord_778834) baseStart_778834 baseEnd_778834 := by
    simpa [prefixWord, tailWord_778834, baseEnd_778834] using wordTrace_append hprefix tailTrace_778834
  have hstable : (prefixWord ++ tailWord_778834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778834).length < 2 ^ (prefixWord ++ tailWord_778834).sum := by decide
  have hdescent : baseEnd_778834 < baseStart_778834 := by decide
  rcases family_descends (prefixWord ++ tailWord_778834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778844 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_778844 : Nat := 118140960795 + 778844 * 2 ^ 59
def prefixEnd_778844 : Nat := 4983230072969 + 3 ^ 40 * 778844 * 2
def baseEnd_778844 : Nat := 355485623884849780416149

theorem tailTrace_778844 : CollatzResearch.WordTrace tailWord_778844 prefixEnd_778844 355485623884849780416149 := by
  unfold tailWord_778844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203387195194339405183793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18937849593592452540245057 14203387195194339405183793)
  ·
    refine ⟨10652540396395754553887845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14203387195194339405183793 10652540396395754553887845)
    ·
      refine ⟨1997351324324203978853971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10652540396395754553887845 1997351324324203978853971)
      ·
        refine ⟨2996026986486305968280957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997351324324203978853971 2996026986486305968280957)
        ·
          refine ⟨1123510119932364738105359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2996026986486305968280957 1123510119932364738105359)
          ·
            refine ⟨1685265179898547107158039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123510119932364738105359 1685265179898547107158039)
            ·
              refine ⟨2527897769847820660737059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685265179898547107158039 2527897769847820660737059)
              ·
                refine ⟨3791846654771730991105589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527897769847820660737059 3791846654771730991105589)
                ·
                  refine ⟨355485623884849780416149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791846654771730991105589 355485623884849780416149)
                  ·
                    rfl

theorem cell20_778844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_778844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778844 prefixEnd_778844 := by exact prefixLift 778844
  have htrace : WordTrace (prefixWord ++ tailWord_778844) baseStart_778844 baseEnd_778844 := by
    simpa [prefixWord, tailWord_778844, baseEnd_778844] using wordTrace_append hprefix tailTrace_778844
  have hstable : (prefixWord ++ tailWord_778844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778844).length < 2 ^ (prefixWord ++ tailWord_778844).sum := by decide
  have hdescent : baseEnd_778844 < baseStart_778844 := by decide
  rcases family_descends (prefixWord ++ tailWord_778844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778851 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 2]
def baseStart_778851 : Nat := 118140960795 + 778851 * 2 ^ 59
def prefixEnd_778851 : Nat := 4983230072969 + 3 ^ 40 * 778851 * 2
def baseEnd_778851 : Nat := 355488818875588867182787

theorem tailTrace_778851 : CollatzResearch.WordTrace tailWord_778851 prefixEnd_778851 355488818875588867182787 := by
  unfold tailWord_778851
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407029701363319005872407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18938019800908879337248271 28407029701363319005872407)
  ·
    refine ⟨42610544552044978508808611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28407029701363319005872407 42610544552044978508808611)
    ·
      refine ⟨63915816828067467763212917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42610544552044978508808611 63915816828067467763212917)
      ·
        refine ⟨5992107827631325102801211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63915816828067467763212917 5992107827631325102801211)
        ·
          refine ⟨8988161741446987654201817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992107827631325102801211 8988161741446987654201817)
          ·
            refine ⟨6741121306085240740651363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988161741446987654201817 6741121306085240740651363)
            ·
              refine ⟨10111681959127861110977045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741121306085240740651363 10111681959127861110977045)
              ·
                refine ⟨473985091834118489577049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10111681959127861110977045 473985091834118489577049)
                ·
                  refine ⟨355488818875588867182787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473985091834118489577049 355488818875588867182787)
                  ·
                    rfl

theorem cell20_778851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2].length) (baseStart_778851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778851 prefixEnd_778851 := by exact prefixLift 778851
  have htrace : WordTrace (prefixWord ++ tailWord_778851) baseStart_778851 baseEnd_778851 := by
    simpa [prefixWord, tailWord_778851, baseEnd_778851] using wordTrace_append hprefix tailTrace_778851
  have hstable : (prefixWord ++ tailWord_778851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778851).length < 2 ^ (prefixWord ++ tailWord_778851).sum := by decide
  have hdescent : baseEnd_778851 < baseStart_778851 := by decide
  rcases family_descends (prefixWord ++ tailWord_778851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778861 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_778861 : Nat := 118140960795 + 778861 * 2 ^ 59
def prefixEnd_778861 : Nat := 4983230072969 + 3 ^ 40 * 778861 * 2
def baseEnd_778861 : Nat := 355493383148073276849413

theorem tailTrace_778861 : CollatzResearch.WordTrace tailWord_778861 prefixEnd_778861 355493383148073276849413 := by
  unfold tailWord_778861
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407394431327090713736437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18938262954218060475824291 28407394431327090713736437)
  ·
    refine ⟨2663193227936914754412791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28407394431327090713736437 2663193227936914754412791)
    ·
      refine ⟨3994789841905372131619187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663193227936914754412791 3994789841905372131619187)
      ·
        refine ⟨5992184762858058197428781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994789841905372131619187 5992184762858058197428781)
        ·
          refine ⟨2247069286071771824035793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5992184762858058197428781 2247069286071771824035793)
          ·
            refine ⟨1685301964553828868026845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2247069286071771824035793 1685301964553828868026845)
            ·
              refine ⟨631988236707685825510067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1685301964553828868026845 631988236707685825510067)
              ·
                refine ⟨947982355061528738265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631988236707685825510067 947982355061528738265101)
                ·
                  refine ⟨355493383148073276849413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947982355061528738265101 355493383148073276849413)
                  ·
                    rfl

theorem cell20_778861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_778861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778861 prefixEnd_778861 := by exact prefixLift 778861
  have htrace : WordTrace (prefixWord ++ tailWord_778861) baseStart_778861 baseEnd_778861 := by
    simpa [prefixWord, tailWord_778861, baseEnd_778861] using wordTrace_append hprefix tailTrace_778861
  have hstable : (prefixWord ++ tailWord_778861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778861).length < 2 ^ (prefixWord ++ tailWord_778861).sum := by decide
  have hdescent : baseEnd_778861 < baseStart_778861 := by decide
  rcases family_descends (prefixWord ++ tailWord_778861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778903 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_778903 : Nat := 118140960795 + 778903 * 2 ^ 59
def prefixEnd_778903 : Nat := 4983230072969 + 3 ^ 40 * 778903 * 2
def baseEnd_778903 : Nat := 355512553092507797449241

theorem tailTrace_778903 : CollatzResearch.WordTrace tailWord_778903 prefixEnd_778903 355512553092507797449241 := by
  unfold tailWord_778903
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408926297174931886765363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939284198116621257843575 28408926297174931886765363)
  ·
    refine ⟨42613389445762397830148045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28408926297174931886765363 42613389445762397830148045)
    ·
      refine ⟨15980021042160899186305517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42613389445762397830148045 15980021042160899186305517)
      ·
        refine ⟨5992507890810337194864569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15980021042160899186305517 5992507890810337194864569)
        ·
          refine ⟨4494380918107752896148427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5992507890810337194864569 4494380918107752896148427)
          ·
            refine ⟨6741571377161629344222641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494380918107752896148427 6741571377161629344222641)
            ·
              refine ⟨5056178532871222008166981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741571377161629344222641 5056178532871222008166981)
              ·
                refine ⟨948033474913354126531309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5056178532871222008166981 948033474913354126531309)
                ·
                  refine ⟨355512553092507797449241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948033474913354126531309 355512553092507797449241)
                  ·
                    rfl

theorem cell20_778903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_778903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778903 prefixEnd_778903 := by exact prefixLift 778903
  have htrace : WordTrace (prefixWord ++ tailWord_778903) baseStart_778903 baseEnd_778903 := by
    simpa [prefixWord, tailWord_778903, baseEnd_778903] using wordTrace_append hprefix tailTrace_778903
  have hstable : (prefixWord ++ tailWord_778903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778903).length < 2 ^ (prefixWord ++ tailWord_778903).sum := by decide
  have hdescent : baseEnd_778903 < baseStart_778903 := by decide
  rcases family_descends (prefixWord ++ tailWord_778903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778957 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 2]
def baseStart_778957 : Nat := 118140960795 + 778957 * 2 ^ 59
def prefixEnd_778957 : Nat := 4983230072969 + 3 ^ 40 * 778957 * 2
def baseEnd_778957 : Nat := 355537200163923609649021

theorem tailTrace_778957 : CollatzResearch.WordTrace tailWord_778957 prefixEnd_778957 355537200163923609649021 := by
  unfold tailWord_778957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28410895838979299109231125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18940597225986199406154083 28410895838979299109231125)
  ·
    refine ⟨1331760742452154645745209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28410895838979299109231125 1331760742452154645745209)
    ·
      refine ⟨998820556839115984308907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331760742452154645745209 998820556839115984308907)
      ·
        refine ⟨1498230835258673976463361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998820556839115984308907 1498230835258673976463361)
        ·
          refine ⟨1123673126444005482347521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498230835258673976463361 1123673126444005482347521)
          ·
            refine ⟨842754844833004111760641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123673126444005482347521 842754844833004111760641)
            ·
              refine ⟨632066133624753083820481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842754844833004111760641 632066133624753083820481)
              ·
                refine ⟨474049600218564812865361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632066133624753083820481 474049600218564812865361)
                ·
                  refine ⟨355537200163923609649021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474049600218564812865361 355537200163923609649021)
                  ·
                    rfl

theorem cell20_778957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_778957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778957 prefixEnd_778957 := by exact prefixLift 778957
  have htrace : WordTrace (prefixWord ++ tailWord_778957) baseStart_778957 baseEnd_778957 := by
    simpa [prefixWord, tailWord_778957, baseEnd_778957] using wordTrace_append hprefix tailTrace_778957
  have hstable : (prefixWord ++ tailWord_778957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778957).length < 2 ^ (prefixWord ++ tailWord_778957).sum := by decide
  have hdescent : baseEnd_778957 < baseStart_778957 := by decide
  rcases family_descends (prefixWord ++ tailWord_778957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778958 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_778958 : Nat := 118140960795 + 778958 * 2 ^ 59
def prefixEnd_778958 : Nat := 4983230072969 + 3 ^ 40 * 778958 * 2
def baseEnd_778958 : Nat := 355537656591172050615683

theorem tailTrace_778958 : CollatzResearch.WordTrace tailWord_778958 prefixEnd_778958 355537656591172050615683 := by
  unfold tailWord_778958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551366538996959535002191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18940621541317117520011685 3551366538996959535002191)
  ·
    refine ⟨5327049808495439302503287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551366538996959535002191 5327049808495439302503287)
    ·
      refine ⟨7990574712743158953754931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327049808495439302503287 7990574712743158953754931)
      ·
        refine ⟨11985862069114738430632397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7990574712743158953754931 11985862069114738430632397)
        ·
          refine ⟨4494698275918026911487149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11985862069114738430632397 4494698275918026911487149)
          ·
            refine ⟨1685511853469260091807681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4494698275918026911487149 1685511853469260091807681)
            ·
              refine ⟨1264133890101945068855761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685511853469260091807681 1264133890101945068855761)
              ·
                refine ⟨948100417576458801641821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264133890101945068855761 948100417576458801641821)
                ·
                  refine ⟨355537656591172050615683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948100417576458801641821 355537656591172050615683)
                  ·
                    rfl

theorem cell20_778958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_778958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778958 prefixEnd_778958 := by exact prefixLift 778958
  have htrace : WordTrace (prefixWord ++ tailWord_778958) baseStart_778958 baseEnd_778958 := by
    simpa [prefixWord, tailWord_778958, baseEnd_778958] using wordTrace_append hprefix tailTrace_778958
  have hstable : (prefixWord ++ tailWord_778958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778958).length < 2 ^ (prefixWord ++ tailWord_778958).sum := by decide
  have hdescent : baseEnd_778958 < baseStart_778958 := by decide
  rcases family_descends (prefixWord ++ tailWord_778958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779000 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_779000 : Nat := 118140960795 + 779000 * 2 ^ 59
def prefixEnd_779000 : Nat := 4983230072969 + 3 ^ 40 * 779000 * 2
def baseEnd_779000 : Nat := 355556826535606571215511

theorem tailTrace_779000 : CollatzResearch.WordTrace tailWord_779000 prefixEnd_779000 355556826535606571215511 := by
  unfold tailWord_779000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206232088911758726523227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18941642785215678302030969 14206232088911758726523227)
  ·
    refine ⟨21309348133367638089784841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14206232088911758726523227 21309348133367638089784841)
    ·
      refine ⟨15982011100025728567338631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21309348133367638089784841 15982011100025728567338631)
      ·
        refine ⟨23973016650038592851007947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15982011100025728567338631 23973016650038592851007947)
        ·
          refine ⟨35959524975057889276511921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23973016650038592851007947 35959524975057889276511921)
          ·
            refine ⟨26969643731293416957383941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35959524975057889276511921 26969643731293416957383941)
            ·
              refine ⟨5056808199617515679509489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26969643731293416957383941 5056808199617515679509489)
              ·
                refine ⟨3792606149713136759632117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056808199617515679509489 3792606149713136759632117)
                ·
                  refine ⟨355556826535606571215511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3792606149713136759632117 355556826535606571215511)
                  ·
                    rfl

theorem cell20_779000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_779000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779000 prefixEnd_779000 := by exact prefixLift 779000
  have htrace : WordTrace (prefixWord ++ tailWord_779000) baseStart_779000 baseEnd_779000 := by
    simpa [prefixWord, tailWord_779000, baseEnd_779000] using wordTrace_append hprefix tailTrace_779000
  have hstable : (prefixWord ++ tailWord_779000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779000).length < 2 ^ (prefixWord ++ tailWord_779000).sum := by decide
  have hdescent : baseEnd_779000 < baseStart_779000 := by decide
  rcases family_descends (prefixWord ++ tailWord_779000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779007 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_779007 : Nat := 118140960795 + 779007 * 2 ^ 59
def prefixEnd_779007 : Nat := 4983230072969 + 3 ^ 40 * 779007 * 2
def baseEnd_779007 : Nat := 355560021526345657982149

theorem tailTrace_779007 : CollatzResearch.WordTrace tailWord_779007 prefixEnd_779007 355560021526345657982149 := by
  unfold tailWord_779007
  simp only [CollatzResearch.WordTrace]
  refine ⟨28412719488798157648551275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18941812992532105099034183 28412719488798157648551275)
  ·
    refine ⟨42619079233197236472826913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28412719488798157648551275 42619079233197236472826913)
    ·
      refine ⟨31964309424897927354620185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42619079233197236472826913 31964309424897927354620185)
      ·
        refine ⟨23973232068673445515965139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31964309424897927354620185 23973232068673445515965139)
        ·
          refine ⟨35959848103010168273947709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23973232068673445515965139 35959848103010168273947709)
          ·
            refine ⟨13484943038628813102730391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35959848103010168273947709 13484943038628813102730391)
            ·
              refine ⟨20227414557943219654095587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13484943038628813102730391 20227414557943219654095587)
              ·
                refine ⟨30341121836914829481143381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20227414557943219654095587 30341121836914829481143381)
                ·
                  refine ⟨355560021526345657982149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30341121836914829481143381 355560021526345657982149)
                  ·
                    rfl

theorem cell20_779007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_779007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779007 prefixEnd_779007 := by exact prefixLift 779007
  have htrace : WordTrace (prefixWord ++ tailWord_779007) baseStart_779007 baseEnd_779007 := by
    simpa [prefixWord, tailWord_779007, baseEnd_779007] using wordTrace_append hprefix tailTrace_779007
  have hstable : (prefixWord ++ tailWord_779007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779007).length < 2 ^ (prefixWord ++ tailWord_779007).sum := by decide
  have hdescent : baseEnd_779007 < baseStart_779007 := by decide
  rcases family_descends (prefixWord ++ tailWord_779007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779010 : List Nat := [3, 4, 1, 1, 1, 3, 7]
def baseStart_779010 : Nat := 118140960795 + 779010 * 2 ^ 59
def prefixEnd_779010 : Nat := 4983230072969 + 3 ^ 40 * 779010 * 2
def baseEnd_779010 : Nat := 39506821200898997875793

theorem tailTrace_779010 : CollatzResearch.WordTrace tailWord_779010 prefixEnd_779010 39506821200898997875793 := by
  unfold tailWord_779010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103207226946822290227621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18941885938524859440606989 7103207226946822290227621)
  ·
    refine ⟨1331851355052529179417679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7103207226946822290227621 1331851355052529179417679)
    ·
      refine ⟨1997777032578793769126519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331851355052529179417679 1997777032578793769126519)
      ·
        refine ⟨2996665548868190653689779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997777032578793769126519 2996665548868190653689779)
        ·
          refine ⟨4494998323302285980534669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996665548868190653689779 4494998323302285980534669)
          ·
            refine ⟨1685624371238357242700501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4494998323302285980534669 1685624371238357242700501)
            ·
              refine ⟨39506821200898997875793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1685624371238357242700501 39506821200898997875793)
              ·
                rfl

theorem cell20_779010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_779010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779010 prefixEnd_779010 := by exact prefixLift 779010
  have htrace : WordTrace (prefixWord ++ tailWord_779010) baseStart_779010 baseEnd_779010 := by
    simpa [prefixWord, tailWord_779010, baseEnd_779010] using wordTrace_append hprefix tailTrace_779010
  have hstable : (prefixWord ++ tailWord_779010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779010).length < 2 ^ (prefixWord ++ tailWord_779010).sum := by decide
  have hdescent : baseEnd_779010 < baseStart_779010 := by decide
  rcases family_descends (prefixWord ++ tailWord_779010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779017 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_779017 : Nat := 118140960795 + 779017 * 2 ^ 59
def prefixEnd_779017 : Nat := 4983230072969 + 3 ^ 40 * 779017 * 2
def baseEnd_779017 : Nat := 355564585798830067648775

theorem tailTrace_779017 : CollatzResearch.WordTrace tailWord_779017 prefixEnd_779017 355564585798830067648775 := by
  unfold tailWord_779017
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413084218761929356415305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18942056145841286237610203 28413084218761929356415305)
  ·
    refine ⟨21309813164071447017311479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28413084218761929356415305 21309813164071447017311479)
    ·
      refine ⟨31964719746107170525967219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21309813164071447017311479 31964719746107170525967219)
      ·
        refine ⟨47947079619160755788950829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31964719746107170525967219 47947079619160755788950829)
        ·
          refine ⟨17980154857185283420856561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47947079619160755788950829 17980154857185283420856561)
          ·
            refine ⟨13485116142888962565642421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17980154857185283420856561 13485116142888962565642421)
            ·
              refine ⟨1264229638395840240528977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13485116142888962565642421 1264229638395840240528977)
              ·
                refine ⟨948172228796880180396733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264229638395840240528977 948172228796880180396733)
                ·
                  refine ⟨355564585798830067648775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948172228796880180396733 355564585798830067648775)
                  ·
                    rfl

theorem cell20_779017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_779017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779017 prefixEnd_779017 := by exact prefixLift 779017
  have htrace : WordTrace (prefixWord ++ tailWord_779017) baseStart_779017 baseEnd_779017 := by
    simpa [prefixWord, tailWord_779017, baseEnd_779017] using wordTrace_append hprefix tailTrace_779017
  have hstable : (prefixWord ++ tailWord_779017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779017).length < 2 ^ (prefixWord ++ tailWord_779017).sum := by decide
  have hdescent : baseEnd_779017 < baseStart_779017 := by decide
  rcases family_descends (prefixWord ++ tailWord_779017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779034 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_779034 : Nat := 118140960795 + 779034 * 2 ^ 59
def prefixEnd_779034 : Nat := 4983230072969 + 3 ^ 40 * 779034 * 2
def baseEnd_779034 : Nat := 355572345062053564082039

theorem tailTrace_779034 : CollatzResearch.WordTrace tailWord_779034 prefixEnd_779034 355572345062053564082039 := by
  unfold tailWord_779034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103426064925085314946039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18942469506466894173189437 7103426064925085314946039)
  ·
    refine ⟨10655139097387627972419059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103426064925085314946039 10655139097387627972419059)
    ·
      refine ⟨15982708646081441958628589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655139097387627972419059 15982708646081441958628589)
      ·
        refine ⟨5993515742280540734485721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15982708646081441958628589 5993515742280540734485721)
        ·
          refine ⟨4495136806710405550864291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993515742280540734485721 4495136806710405550864291)
          ·
            refine ⟨6742705210065608326296437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495136806710405550864291 6742705210065608326296437)
            ·
              refine ⟨632128613443650780590291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6742705210065608326296437 632128613443650780590291)
              ·
                refine ⟨948192920165476170885437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632128613443650780590291 948192920165476170885437)
                ·
                  refine ⟨355572345062053564082039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948192920165476170885437 355572345062053564082039)
                  ·
                    rfl

theorem cell20_779034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_779034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779034 prefixEnd_779034 := by exact prefixLift 779034
  have htrace : WordTrace (prefixWord ++ tailWord_779034) baseStart_779034 baseEnd_779034 := by
    simpa [prefixWord, tailWord_779034, baseEnd_779034] using wordTrace_append hprefix tailTrace_779034
  have hstable : (prefixWord ++ tailWord_779034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779034).length < 2 ^ (prefixWord ++ tailWord_779034).sum := by decide
  have hdescent : baseEnd_779034 < baseStart_779034 := by decide
  rcases family_descends (prefixWord ++ tailWord_779034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779044 : List Nat := [2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_779044 : Nat := 118140960795 + 779044 * 2 ^ 59
def prefixEnd_779044 : Nat := 4983230072969 + 3 ^ 40 * 779044 * 2
def baseEnd_779044 : Nat := 118525636444845991249555

theorem tailTrace_779044 : CollatzResearch.WordTrace tailWord_779044 prefixEnd_779044 118525636444845991249555 := by
  unfold tailWord_779044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14207034494832056483824093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18942712659776075311765457 14207034494832056483824093)
  ·
    refine ⟨5327637935562021181434035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14207034494832056483824093 5327637935562021181434035)
    ·
      refine ⟨7991456903343031772151053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327637935562021181434035 7991456903343031772151053)
      ·
        refine ⟨2996796338753636914556645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7991456903343031772151053 2996796338753636914556645)
        ·
          refine ⟨561899313516306921479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2996796338753636914556645 561899313516306921479371)
          ·
            refine ⟨842848970274460382219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561899313516306921479371 842848970274460382219057)
            ·
              refine ⟨632136727705845286664293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842848970274460382219057 632136727705845286664293)
              ·
                refine ⟨118525636444845991249555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632136727705845286664293 118525636444845991249555)
                ·
                  rfl

theorem cell20_779044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_779044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779044 prefixEnd_779044 := by exact prefixLift 779044
  have htrace : WordTrace (prefixWord ++ tailWord_779044) baseStart_779044 baseEnd_779044 := by
    simpa [prefixWord, tailWord_779044, baseEnd_779044] using wordTrace_append hprefix tailTrace_779044
  have hstable : (prefixWord ++ tailWord_779044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779044).length < 2 ^ (prefixWord ++ tailWord_779044).sum := by decide
  have hdescent : baseEnd_779044 < baseStart_779044 := by decide
  rcases family_descends (prefixWord ++ tailWord_779044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779085 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 3]
def baseStart_779085 : Nat := 118140960795 + 779085 * 2 ^ 59
def prefixEnd_779085 : Nat := 4983230072969 + 3 ^ 40 * 779085 * 2
def baseEnd_779085 : Nat := 355595622851724053381831

theorem tailTrace_779085 : CollatzResearch.WordTrace tailWord_779085 prefixEnd_779085 355595622851724053381831 := by
  unfold tailWord_779085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415564382515576969890709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943709588343717979927139 28415564382515576969890709)
  ·
    refine ⟨1331979580430417670463627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28415564382515576969890709 1331979580430417670463627)
    ·
      refine ⟨1997969370645626505695441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331979580430417670463627 1997969370645626505695441)
      ·
        refine ⟨1498477027984219879271581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1997969370645626505695441 1498477027984219879271581)
        ·
          refine ⟨561928885494082454726843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1498477027984219879271581 561928885494082454726843)
          ·
            refine ⟨842893328241123682090265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561928885494082454726843 842893328241123682090265)
            ·
              refine ⟨632169996180842761567699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842893328241123682090265 632169996180842761567699)
              ·
                refine ⟨948254994271264142351549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632169996180842761567699 948254994271264142351549)
                ·
                  refine ⟨355595622851724053381831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948254994271264142351549 355595622851724053381831)
                  ·
                    rfl

theorem cell20_779085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_779085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779085 prefixEnd_779085 := by exact prefixLift 779085
  have htrace : WordTrace (prefixWord ++ tailWord_779085) baseStart_779085 baseEnd_779085 := by
    simpa [prefixWord, tailWord_779085, baseEnd_779085] using wordTrace_append hprefix tailTrace_779085
  have hstable : (prefixWord ++ tailWord_779085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779085).length < 2 ^ (prefixWord ++ tailWord_779085).sum := by decide
  have hdescent : baseEnd_779085 < baseStart_779085 := by decide
  rcases family_descends (prefixWord ++ tailWord_779085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779089 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_779089 : Nat := 118140960795 + 779089 * 2 ^ 59
def prefixEnd_779089 : Nat := 4983230072969 + 3 ^ 40 * 779089 * 2
def baseEnd_779089 : Nat := 355597448560717817248481

theorem tailTrace_779089 : CollatzResearch.WordTrace tailWord_779089 prefixEnd_779089 355597448560717817248481 := by
  unfold tailWord_779089
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415710274501085653036321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943806849667390435357547 28415710274501085653036321)
  ·
    refine ⟨21311782705875814239777241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28415710274501085653036321 21311782705875814239777241)
    ·
      refine ⟨15983837029406860679832931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21311782705875814239777241 15983837029406860679832931)
      ·
        refine ⟨23975755544110291019749397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15983837029406860679832931 23975755544110291019749397)
        ·
          refine ⟨1123863541130169891550753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23975755544110291019749397 1123863541130169891550753)
          ·
            refine ⟨842897655847627418663065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123863541130169891550753 842897655847627418663065)
            ·
              refine ⟨632173241885720563997299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842897655847627418663065 632173241885720563997299)
              ·
                refine ⟨948259862828580845995949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632173241885720563997299 948259862828580845995949)
                ·
                  refine ⟨355597448560717817248481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948259862828580845995949 355597448560717817248481)
                  ·
                    rfl

theorem cell20_779089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_779089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779089 prefixEnd_779089 := by exact prefixLift 779089
  have htrace : WordTrace (prefixWord ++ tailWord_779089) baseStart_779089 baseEnd_779089 := by
    simpa [prefixWord, tailWord_779089, baseEnd_779089] using wordTrace_append hprefix tailTrace_779089
  have hstable : (prefixWord ++ tailWord_779089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779089).length < 2 ^ (prefixWord ++ tailWord_779089).sum := by decide
  have hdescent : baseEnd_779089 < baseStart_779089 := by decide
  rcases family_descends (prefixWord ++ tailWord_779089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779093 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_779093 : Nat := 118140960795 + 779093 * 2 ^ 59
def prefixEnd_779093 : Nat := 4983230072969 + 3 ^ 40 * 779093 * 2
def baseEnd_779093 : Nat := 355599274269711581115131

theorem tailTrace_779093 : CollatzResearch.WordTrace tailWord_779093 prefixEnd_779093 355599274269711581115131 := by
  unfold tailWord_779093
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415856166486594336181933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943904110991062890787955 28415856166486594336181933)
  ·
    refine ⟨10655946062432472876068225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28415856166486594336181933 10655946062432472876068225)
    ·
      refine ⟨7991959546824354657051169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10655946062432472876068225 7991959546824354657051169)
      ·
        refine ⟨5993969660118265992788377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7991959546824354657051169 5993969660118265992788377)
        ·
          refine ⟨4495477245088699494591283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993969660118265992788377 4495477245088699494591283)
          ·
            refine ⟨6743215867633049241886925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495477245088699494591283 6743215867633049241886925)
            ·
              refine ⟨2528705950362393465707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6743215867633049241886925 2528705950362393465707597)
              ·
                refine ⟨948264731385897549640349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2528705950362393465707597 948264731385897549640349)
                ·
                  refine ⟨355599274269711581115131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948264731385897549640349 355599274269711581115131)
                  ·
                    rfl

theorem cell20_779093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_779093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779093 prefixEnd_779093 := by exact prefixLift 779093
  have htrace : WordTrace (prefixWord ++ tailWord_779093) baseStart_779093 baseEnd_779093 := by
    simpa [prefixWord, tailWord_779093, baseEnd_779093] using wordTrace_append hprefix tailTrace_779093
  have hstable : (prefixWord ++ tailWord_779093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779093).length < 2 ^ (prefixWord ++ tailWord_779093).sum := by decide
  have hdescent : baseEnd_779093 < baseStart_779093 := by decide
  rcases family_descends (prefixWord ++ tailWord_779093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779107 : List Nat := [1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_779107 : Nat := 118140960795 + 779107 * 2 ^ 59
def prefixEnd_779107 : Nat := 4983230072969 + 3 ^ 40 * 779107 * 2
def baseEnd_779107 : Nat := 118535221417063251549469

theorem tailTrace_779107 : CollatzResearch.WordTrace tailWord_779107 prefixEnd_779107 118535221417063251549469 := by
  unfold tailWord_779107
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416366788435874727191575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18944244525623916484794383 28416366788435874727191575)
  ·
    refine ⟨42624550182653812090787363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28416366788435874727191575 42624550182653812090787363)
    ·
      refine ⟨63936825273980718136181045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42624550182653812090787363 63936825273980718136181045)
      ·
        refine ⟨5994077369435692325266973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63936825273980718136181045 5994077369435692325266973)
        ·
          refine ⟨2247779013538384621975115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5994077369435692325266973 2247779013538384621975115)
          ·
            refine ⟨3371668520307576932962673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247779013538384621975115 3371668520307576932962673)
            ·
              refine ⟨2528751390230682699722005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371668520307576932962673 2528751390230682699722005)
              ·
                refine ⟨118535221417063251549469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2528751390230682699722005 118535221417063251549469)
                ·
                  rfl

theorem cell20_779107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_779107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779107 prefixEnd_779107 := by exact prefixLift 779107
  have htrace : WordTrace (prefixWord ++ tailWord_779107) baseStart_779107 baseEnd_779107 := by
    simpa [prefixWord, tailWord_779107, baseEnd_779107] using wordTrace_append hprefix tailTrace_779107
  have hstable : (prefixWord ++ tailWord_779107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779107).length < 2 ^ (prefixWord ++ tailWord_779107).sum := by decide
  have hdescent : baseEnd_779107 < baseStart_779107 := by decide
  rcases family_descends (prefixWord ++ tailWord_779107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779117 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 2]
def baseStart_779117 : Nat := 118140960795 + 779117 * 2 ^ 59
def prefixEnd_779117 : Nat := 4983230072969 + 3 ^ 40 * 779117 * 2
def baseEnd_779117 : Nat := 355610228523674164315033

theorem tailTrace_779117 : CollatzResearch.WordTrace tailWord_779117 prefixEnd_779117 355610228523674164315033 := by
  unfold tailWord_779117
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416731518399646435055605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18944487678933097623370403 28416731518399646435055605)
  ·
    refine ⟨2664068579849966853286463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28416731518399646435055605 2664068579849966853286463)
    ·
      refine ⟨3996102869774950279929695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664068579849966853286463 3996102869774950279929695)
      ·
        refine ⟨5994154304662425419894543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996102869774950279929695 5994154304662425419894543)
        ·
          refine ⟨8991231456993638129841815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5994154304662425419894543 8991231456993638129841815)
          ·
            refine ⟨13486847185490457194762723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991231456993638129841815 13486847185490457194762723)
            ·
              refine ⟨20230270778235685792144085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13486847185490457194762723 20230270778235685792144085)
              ·
                refine ⟨474146971364898885753377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20230270778235685792144085 474146971364898885753377)
                ·
                  refine ⟨355610228523674164315033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474146971364898885753377 355610228523674164315033)
                  ·
                    rfl

theorem cell20_779117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_779117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779117 prefixEnd_779117 := by exact prefixLift 779117
  have htrace : WordTrace (prefixWord ++ tailWord_779117) baseStart_779117 baseEnd_779117 := by
    simpa [prefixWord, tailWord_779117, baseEnd_779117] using wordTrace_append hprefix tailTrace_779117
  have hstable : (prefixWord ++ tailWord_779117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779117).length < 2 ^ (prefixWord ++ tailWord_779117).sum := by decide
  have hdescent : baseEnd_779117 < baseStart_779117 := by decide
  rcases family_descends (prefixWord ++ tailWord_779117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779145 : List Nat := [1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_779145 : Nat := 118140960795 + 779145 * 2 ^ 59
def prefixEnd_779145 : Nat := 4983230072969 + 3 ^ 40 * 779145 * 2
def baseEnd_779145 : Nat := 118541002828876837127195

theorem tailTrace_779145 : CollatzResearch.WordTrace tailWord_779145 prefixEnd_779145 118541002828876837127195 := by
  unfold tailWord_779145
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417752762298207217074889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18945168508198804811383259 28417752762298207217074889)
  ·
    refine ⟨21313314571723655412806167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28417752762298207217074889 21313314571723655412806167)
    ·
      refine ⟨31969971857585483119209251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21313314571723655412806167 31969971857585483119209251)
      ·
        refine ⟨47954957786378224678813877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31969971857585483119209251 47954957786378224678813877)
        ·
          refine ⟨4495777292472958563638801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47954957786378224678813877 4495777292472958563638801)
          ·
            refine ⟨3371832969354718922729101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495777292472958563638801 3371832969354718922729101)
            ·
              refine ⟨1264437363508019596023413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371832969354718922729101 1264437363508019596023413)
              ·
                refine ⟨118541002828876837127195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1264437363508019596023413 118541002828876837127195)
                ·
                  rfl

theorem cell20_779145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_779145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779145 prefixEnd_779145 := by exact prefixLift 779145
  have htrace : WordTrace (prefixWord ++ tailWord_779145) baseStart_779145 baseEnd_779145 := by
    simpa [prefixWord, tailWord_779145, baseEnd_779145] using wordTrace_append hprefix tailTrace_779145
  have hstable : (prefixWord ++ tailWord_779145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779145).length < 2 ^ (prefixWord ++ tailWord_779145).sum := by decide
  have hdescent : baseEnd_779145 < baseStart_779145 := by decide
  rcases family_descends (prefixWord ++ tailWord_779145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779193 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 2]
def baseStart_779193 : Nat := 118140960795 + 779193 * 2 ^ 59
def prefixEnd_779193 : Nat := 4983230072969 + 3 ^ 40 * 779193 * 2
def baseEnd_779193 : Nat := 355644916994555677781389

theorem tailTrace_779193 : CollatzResearch.WordTrace tailWord_779193 prefixEnd_779193 355644916994555677781389 := by
  unfold tailWord_779193
  simp only [CollatzResearch.WordTrace]
  refine ⟨28419503466124311414822233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18946335644082874276548155 28419503466124311414822233)
  ·
    refine ⟨21314627599593233561116675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28419503466124311414822233 21314627599593233561116675)
    ·
      refine ⟨31971941399389850341675013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21314627599593233561116675 31971941399389850341675013)
      ·
        refine ⟨5994739012385596939064065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31971941399389850341675013 5994739012385596939064065)
        ·
          refine ⟨4496054259289197704298049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994739012385596939064065 4496054259289197704298049)
          ·
            refine ⟨3372040694466898278223537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496054259289197704298049 3372040694466898278223537)
            ·
              refine ⟨2529030520850173708667653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372040694466898278223537 2529030520850173708667653)
              ·
                refine ⟨474193222659407570375185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2529030520850173708667653 474193222659407570375185)
                ·
                  refine ⟨355644916994555677781389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474193222659407570375185 355644916994555677781389)
                  ·
                    rfl

theorem cell20_779193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_779193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779193 prefixEnd_779193 := by exact prefixLift 779193
  have htrace : WordTrace (prefixWord ++ tailWord_779193) baseStart_779193 baseEnd_779193 := by
    simpa [prefixWord, tailWord_779193, baseEnd_779193] using wordTrace_append hprefix tailTrace_779193
  have hstable : (prefixWord ++ tailWord_779193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779193).length < 2 ^ (prefixWord ++ tailWord_779193).sum := by decide
  have hdescent : baseEnd_779193 < baseStart_779193 := by decide
  rcases family_descends (prefixWord ++ tailWord_779193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779214 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_779214 : Nat := 118140960795 + 779214 * 2 ^ 59
def prefixEnd_779214 : Nat := 4983230072969 + 3 ^ 40 * 779214 * 2
def baseEnd_779214 : Nat := 355654501966772938081303

theorem tailTrace_779214 : CollatzResearch.WordTrace tailWord_779214 prefixEnd_779214 355654501966772938081303 := by
  unfold tailWord_779214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552533674881029000167087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18946846266032154667557797 3552533674881029000167087)
  ·
    refine ⟨5328800512321543500250631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552533674881029000167087 5328800512321543500250631)
    ·
      refine ⟨7993200768482315250375947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328800512321543500250631 7993200768482315250375947)
      ·
        refine ⟨11989801152723472875563921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993200768482315250375947 11989801152723472875563921)
        ·
          refine ⟨8992350864542604656672941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11989801152723472875563921 8992350864542604656672941)
          ·
            refine ⟨3372131574203476746252353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8992350864542604656672941 3372131574203476746252353)
            ·
              refine ⟨2529098680652607559689265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372131574203476746252353 2529098680652607559689265)
              ·
                refine ⟨1896824010489455669766949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529098680652607559689265 1896824010489455669766949)
                ·
                  refine ⟨355654501966772938081303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896824010489455669766949 355654501966772938081303)
                  ·
                    rfl

theorem cell20_779214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_779214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779214 prefixEnd_779214 := by exact prefixLift 779214
  have htrace : WordTrace (prefixWord ++ tailWord_779214) baseStart_779214 baseEnd_779214 := by
    simpa [prefixWord, tailWord_779214, baseEnd_779214] using wordTrace_append hprefix tailTrace_779214
  have hstable : (prefixWord ++ tailWord_779214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779214).length < 2 ^ (prefixWord ++ tailWord_779214).sum := by decide
  have hdescent : baseEnd_779214 < baseStart_779214 := by decide
  rcases family_descends (prefixWord ++ tailWord_779214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779273 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_779273 : Nat := 118140960795 + 779273 * 2 ^ 59
def prefixEnd_779273 : Nat := 4983230072969 + 3 ^ 40 * 779273 * 2
def baseEnd_779273 : Nat := 355681431174430955114395

theorem tailTrace_779273 : CollatzResearch.WordTrace tailWord_779273 prefixEnd_779273 355681431174430955114395 := by
  unfold tailWord_779273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28422421305834485077734473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18948280870556323385156315 28422421305834485077734473)
  ·
    refine ⟨21316815979375863808300855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28422421305834485077734473 21316815979375863808300855)
    ·
      refine ⟨31975223969063795712451283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21316815979375863808300855 31975223969063795712451283)
      ·
        refine ⟨47962835953595693568676925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31975223969063795712451283 47962835953595693568676925)
        ·
          refine ⟨17986063482598385088253847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47962835953595693568676925 17986063482598385088253847)
          ·
            refine ⟨26979095223897577632380771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986063482598385088253847 26979095223897577632380771)
            ·
              refine ⟨40468642835846366448571157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26979095223897577632380771 40468642835846366448571157)
              ·
                refine ⟨1896967632930298427276773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40468642835846366448571157 1896967632930298427276773)
                ·
                  refine ⟨355681431174430955114395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896967632930298427276773 355681431174430955114395)
                  ·
                    rfl

theorem cell20_779273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_779273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779273 prefixEnd_779273 := by exact prefixLift 779273
  have htrace : WordTrace (prefixWord ++ tailWord_779273) baseStart_779273 baseEnd_779273 := by
    simpa [prefixWord, tailWord_779273, baseEnd_779273] using wordTrace_append hprefix tailTrace_779273
  have hstable : (prefixWord ++ tailWord_779273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779273).length < 2 ^ (prefixWord ++ tailWord_779273).sum := by decide
  have hdescent : baseEnd_779273 < baseStart_779273 := by decide
  rcases family_descends (prefixWord ++ tailWord_779273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779300 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_779300 : Nat := 118140960795 + 779300 * 2 ^ 59
def prefixEnd_779300 : Nat := 4983230072969 + 3 ^ 40 * 779300 * 2
def baseEnd_779300 : Nat := 355693754710138861214285

theorem tailTrace_779300 : CollatzResearch.WordTrace tailWord_779300 prefixEnd_779300 355693754710138861214285 := by
  unfold tailWord_779300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211703038368334344483677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18948937384491112459311569 14211703038368334344483677)
  ·
    refine ⟨5329388639388125379181379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14211703038368334344483677 5329388639388125379181379)
    ·
      refine ⟨7994082959082188068772069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329388639388125379181379 7994082959082188068772069)
      ·
        refine ⟨1498890554827910262894763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7994082959082188068772069 1498890554827910262894763)
        ·
          refine ⟨2248335832241865394342145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498890554827910262894763 2248335832241865394342145)
          ·
            refine ⟨1686251874181399045756609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248335832241865394342145 1686251874181399045756609)
            ·
              refine ⟨1264688905636049284317457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686251874181399045756609 1264688905636049284317457)
              ·
                refine ⟨948516679227036963238093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264688905636049284317457 948516679227036963238093)
                ·
                  refine ⟨355693754710138861214285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948516679227036963238093 355693754710138861214285)
                  ·
                    rfl

theorem cell20_779300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_779300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779300 prefixEnd_779300 := by exact prefixLift 779300
  have htrace : WordTrace (prefixWord ++ tailWord_779300) baseStart_779300 baseEnd_779300 := by
    simpa [prefixWord, tailWord_779300, baseEnd_779300] using wordTrace_append hprefix tailTrace_779300
  have hstable : (prefixWord ++ tailWord_779300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779300).length < 2 ^ (prefixWord ++ tailWord_779300).sum := by decide
  have hdescent : baseEnd_779300 < baseStart_779300 := by decide
  rcases family_descends (prefixWord ++ tailWord_779300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779303 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 2]
def baseStart_779303 : Nat := 118140960795 + 779303 * 2 ^ 59
def prefixEnd_779303 : Nat := 4983230072969 + 3 ^ 40 * 779303 * 2
def baseEnd_779303 : Nat := 355695123991884184114273

theorem tailTrace_779303 : CollatzResearch.WordTrace tailWord_779303 prefixEnd_779303 355695123991884184114273 := by
  unfold tailWord_779303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423515495725800201326563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18949010330483866800884375 28423515495725800201326563)
  ·
    refine ⟨42635273243588700301989845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28423515495725800201326563 42635273243588700301989845)
    ·
      refine ⟨999264216646610163327887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42635273243588700301989845 999264216646610163327887)
      ·
        refine ⟨1498896324969915244991831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999264216646610163327887 1498896324969915244991831)
        ·
          refine ⟨2248344487454872867487747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498896324969915244991831 2248344487454872867487747)
          ·
            refine ⟨3372516731182309301231621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248344487454872867487747 3372516731182309301231621)
            ·
              refine ⟨632346887096682993980929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3372516731182309301231621 632346887096682993980929)
              ·
                refine ⟨474260165322512245485697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632346887096682993980929 474260165322512245485697)
                ·
                  refine ⟨355695123991884184114273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474260165322512245485697 355695123991884184114273)
                  ·
                    rfl

theorem cell20_779303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2].length) (baseStart_779303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779303 prefixEnd_779303 := by exact prefixLift 779303
  have htrace : WordTrace (prefixWord ++ tailWord_779303) baseStart_779303 baseEnd_779303 := by
    simpa [prefixWord, tailWord_779303, baseEnd_779303] using wordTrace_append hprefix tailTrace_779303
  have hstable : (prefixWord ++ tailWord_779303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779303).length < 2 ^ (prefixWord ++ tailWord_779303).sum := by decide
  have hdescent : baseEnd_779303 < baseStart_779303 := by decide
  rcases family_descends (prefixWord ++ tailWord_779303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779321 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_779321 : Nat := 118140960795 + 779321 * 2 ^ 59
def prefixEnd_779321 : Nat := 4983230072969 + 3 ^ 40 * 779321 * 2
def baseEnd_779321 : Nat := 355703339682356121514199

theorem tailTrace_779321 : CollatzResearch.WordTrace tailWord_779321 prefixEnd_779321 355703339682356121514199 := by
  unfold tailWord_779321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28424172009660589275481817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18949448006440392850321211 28424172009660589275481817)
  ·
    refine ⟨21318129007245441956611363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28424172009660589275481817 21318129007245441956611363)
    ·
      refine ⟨31977193510868162934917045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21318129007245441956611363 31977193510868162934917045)
      ·
        refine ⟨2997861891643890275148473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31977193510868162934917045 2997861891643890275148473)
        ·
          refine ⟨2248396418732917706361355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997861891643890275148473 2248396418732917706361355)
          ·
            refine ⟨3372594628099376559542033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248396418732917706361355 3372594628099376559542033)
            ·
              refine ⟨2529445971074532419656525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372594628099376559542033 2529445971074532419656525)
              ·
                refine ⟨948542239152949657371197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529445971074532419656525 948542239152949657371197)
                ·
                  refine ⟨355703339682356121514199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948542239152949657371197 355703339682356121514199)
                  ·
                    rfl

theorem cell20_779321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_779321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779321 prefixEnd_779321 := by exact prefixLift 779321
  have htrace : WordTrace (prefixWord ++ tailWord_779321) baseStart_779321 baseEnd_779321 := by
    simpa [prefixWord, tailWord_779321, baseEnd_779321] using wordTrace_append hprefix tailTrace_779321
  have hstable : (prefixWord ++ tailWord_779321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779321).length < 2 ^ (prefixWord ++ tailWord_779321).sum := by decide
  have hdescent : baseEnd_779321 < baseStart_779321 := by decide
  rcases family_descends (prefixWord ++ tailWord_779321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779342 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_779342 : Nat := 118140960795 + 779342 * 2 ^ 59
def prefixEnd_779342 : Nat := 4983230072969 + 3 ^ 40 * 779342 * 2
def baseEnd_779342 : Nat := 355712924654573381814113

theorem tailTrace_779342 : CollatzResearch.WordTrace tailWord_779342 prefixEnd_779342 355712924654573381814113 := by
  unfold tailWord_779342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553117242823063732749535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18949958628389673241330853 3553117242823063732749535)
  ·
    refine ⟨5329675864234595599124303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553117242823063732749535 5329675864234595599124303)
    ·
      refine ⟨7994513796351893398686455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329675864234595599124303 7994513796351893398686455)
      ·
        refine ⟨11991770694527840098029683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994513796351893398686455 11991770694527840098029683)
        ·
          refine ⟨17987656041791760147044525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991770694527840098029683 17987656041791760147044525)
          ·
            refine ⟨6745371015671910055141697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17987656041791760147044525 6745371015671910055141697)
            ·
              refine ⟨5059028261753932541356273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745371015671910055141697 5059028261753932541356273)
              ·
                refine ⟨3794271196315449406017205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059028261753932541356273 3794271196315449406017205)
                ·
                  refine ⟨355712924654573381814113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3794271196315449406017205 355712924654573381814113)
                  ·
                    rfl

theorem cell20_779342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_779342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779342 prefixEnd_779342 := by exact prefixLift 779342
  have htrace : WordTrace (prefixWord ++ tailWord_779342) baseStart_779342 baseEnd_779342 := by
    simpa [prefixWord, tailWord_779342, baseEnd_779342] using wordTrace_append hprefix tailTrace_779342
  have hstable : (prefixWord ++ tailWord_779342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779342).length < 2 ^ (prefixWord ++ tailWord_779342).sum := by decide
  have hdescent : baseEnd_779342 < baseStart_779342 := by decide
  rcases family_descends (prefixWord ++ tailWord_779342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779349 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_779349 : Nat := 118140960795 + 779349 * 2 ^ 59
def prefixEnd_779349 : Nat := 4983230072969 + 3 ^ 40 * 779349 * 2
def baseEnd_779349 : Nat := 355716119645312468580751

theorem tailTrace_779349 : CollatzResearch.WordTrace tailWord_779349 prefixEnd_779349 355716119645312468580751 := by
  unfold tailWord_779349
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425193253559150057501101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950128835706100038334067 28425193253559150057501101)
  ·
    refine ⟨10659447470084681271562913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28425193253559150057501101 10659447470084681271562913)
    ·
      refine ⟨7994585602563510953672185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10659447470084681271562913 7994585602563510953672185)
      ·
        refine ⟨5995939201922633215254139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7994585602563510953672185 5995939201922633215254139)
        ·
          refine ⟨8993908802883949822881209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995939201922633215254139 8993908802883949822881209)
          ·
            refine ⟨6745431602162962367160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8993908802883949822881209 6745431602162962367160907)
            ·
              refine ⟨10118147403244443550741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745431602162962367160907 10118147403244443550741361)
              ·
                refine ⟨7588610552433332663056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10118147403244443550741361 7588610552433332663056021)
                ·
                  refine ⟨355716119645312468580751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7588610552433332663056021 355716119645312468580751)
                  ·
                    rfl

theorem cell20_779349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_779349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779349 prefixEnd_779349 := by exact prefixLift 779349
  have htrace : WordTrace (prefixWord ++ tailWord_779349) baseStart_779349 baseEnd_779349 := by
    simpa [prefixWord, tailWord_779349, baseEnd_779349] using wordTrace_append hprefix tailTrace_779349
  have hstable : (prefixWord ++ tailWord_779349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779349).length < 2 ^ (prefixWord ++ tailWord_779349).sum := by decide
  have hdescent : baseEnd_779349 < baseStart_779349 := by decide
  rcases family_descends (prefixWord ++ tailWord_779349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779362 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_779362 : Nat := 118140960795 + 779362 * 2 ^ 59
def prefixEnd_779362 : Nat := 4983230072969 + 3 ^ 40 * 779362 * 2
def baseEnd_779362 : Nat := 355722053199542201147365

theorem tailTrace_779362 : CollatzResearch.WordTrace tailWord_779362 prefixEnd_779362 355722053199542201147365 := by
  unfold tailWord_779362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106416850628013319431085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18950444935008035518482893 7106416850628013319431085)
  ·
    refine ⟨2664906318985504994786657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7106416850628013319431085 2664906318985504994786657)
    ·
      refine ⟨1998679739239128746089993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664906318985504994786657 1998679739239128746089993)
      ·
        refine ⟨1499009804429346559567495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998679739239128746089993 1499009804429346559567495)
        ·
          refine ⟨2248514706644019839351243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499009804429346559567495 2248514706644019839351243)
          ·
            refine ⟨3372772059966029759026865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248514706644019839351243 3372772059966029759026865)
            ·
              refine ⟨2529579044974522319270149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372772059966029759026865 2529579044974522319270149)
              ·
                refine ⟨474296070932722934863153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2529579044974522319270149 474296070932722934863153)
                ·
                  refine ⟨355722053199542201147365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474296070932722934863153 355722053199542201147365)
                  ·
                    rfl

theorem cell20_779362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_779362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779362 prefixEnd_779362 := by exact prefixLift 779362
  have htrace : WordTrace (prefixWord ++ tailWord_779362) baseStart_779362 baseEnd_779362 := by
    simpa [prefixWord, tailWord_779362, baseEnd_779362] using wordTrace_append hprefix tailTrace_779362
  have hstable : (prefixWord ++ tailWord_779362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779362).length < 2 ^ (prefixWord ++ tailWord_779362).sum := by decide
  have hdescent : baseEnd_779362 < baseStart_779362 := by decide
  rcases family_descends (prefixWord ++ tailWord_779362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779431 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_779431 : Nat := 118140960795 + 779431 * 2 ^ 59
def prefixEnd_779431 : Nat := 4983230072969 + 3 ^ 40 * 779431 * 2
def baseEnd_779431 : Nat := 355753546679684627847083

theorem tailTrace_779431 : CollatzResearch.WordTrace tailWord_779431 prefixEnd_779431 355753546679684627847083 := by
  unfold tailWord_779431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428184039262078061986147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18952122692841385374657431 28428184039262078061986147)
  ·
    refine ⟨42642276058893117092979221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28428184039262078061986147 42642276058893117092979221)
    ·
      refine ⟨1998856690260614863733401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42642276058893117092979221 1998856690260614863733401)
      ·
        refine ⟨1499142517695461147800051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998856690260614863733401 1499142517695461147800051)
        ·
          refine ⟨2248713776543191721700077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499142517695461147800051 2248713776543191721700077)
          ·
            refine ⟨843267666203696895637529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2248713776543191721700077 843267666203696895637529)
            ·
              refine ⟨632450749652772671728147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843267666203696895637529 632450749652772671728147)
              ·
                refine ⟨948676124479159007592221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632450749652772671728147 948676124479159007592221)
                ·
                  refine ⟨355753546679684627847083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948676124479159007592221 355753546679684627847083)
                  ·
                    rfl

theorem cell20_779431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_779431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779431 prefixEnd_779431 := by exact prefixLift 779431
  have htrace : WordTrace (prefixWord ++ tailWord_779431) baseStart_779431 baseEnd_779431 := by
    simpa [prefixWord, tailWord_779431, baseEnd_779431] using wordTrace_append hprefix tailTrace_779431
  have hstable : (prefixWord ++ tailWord_779431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779431).length < 2 ^ (prefixWord ++ tailWord_779431).sum := by decide
  have hdescent : baseEnd_779431 < baseStart_779431 := by decide
  rcases family_descends (prefixWord ++ tailWord_779431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779462 : List Nat := [6, 1, 2, 2, 2, 7]
def baseStart_779462 : Nat := 118140960795 + 779462 * 2 ^ 59
def prefixEnd_779462 : Nat := 4983230072969 + 3 ^ 40 * 779462 * 2
def baseEnd_779462 : Nat := 13176581330532825844949

theorem tailTrace_779462 : CollatzResearch.WordTrace tailWord_779462 prefixEnd_779462 13176581330532825844949 := by
  unfold tailWord_779462
  simp only [CollatzResearch.WordTrace]
  refine ⟨888416084442180323636395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18952876468099846904243093 888416084442180323636395)
  ·
    refine ⟨1332624126663270485454593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 888416084442180323636395 1332624126663270485454593)
    ·
      refine ⟨999468094997452864090945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1332624126663270485454593 999468094997452864090945)
      ·
        refine ⟨749601071248089648068209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 999468094997452864090945 749601071248089648068209)
        ·
          refine ⟨562200803436067236051157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749601071248089648068209 562200803436067236051157)
          ·
            refine ⟨13176581330532825844949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 562200803436067236051157 13176581330532825844949)
            ·
              rfl

theorem cell20_779462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 7].length) (baseStart_779462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779462 prefixEnd_779462 := by exact prefixLift 779462
  have htrace : WordTrace (prefixWord ++ tailWord_779462) baseStart_779462 baseEnd_779462 := by
    simpa [prefixWord, tailWord_779462, baseEnd_779462] using wordTrace_append hprefix tailTrace_779462
  have hstable : (prefixWord ++ tailWord_779462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779462).length < 2 ^ (prefixWord ++ tailWord_779462).sum := by decide
  have hdescent : baseEnd_779462 < baseStart_779462 := by decide
  rcases family_descends (prefixWord ++ tailWord_779462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779470 : List Nat := [4, 1, 1, 1, 13]
def baseStart_779470 : Nat := 118140960795 + 779470 * 2 ^ 59
def prefixEnd_779470 : Nat := 4983230072969 + 3 ^ 40 * 779470 * 2
def baseEnd_779470 : Nat := 4392238856078689204283

theorem tailTrace_779470 : CollatzResearch.WordTrace tailWord_779470 prefixEnd_779470 4392238856078689204283 := by
  unfold tailWord_779470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553700810765098465331983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18953070990747191815103909 3553700810765098465331983)
  ·
    refine ⟨5330551216147647697997975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553700810765098465331983 5330551216147647697997975)
    ·
      refine ⟨7995826824221471546996963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330551216147647697997975 7995826824221471546996963)
      ·
        refine ⟨11993740236332207320495445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995826824221471546996963 11993740236332207320495445)
        ·
          refine ⟨4392238856078689204283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11993740236332207320495445 4392238856078689204283)
          ·
            rfl

theorem cell20_779470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 13].length) (baseStart_779470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779470 prefixEnd_779470 := by exact prefixLift 779470
  have htrace : WordTrace (prefixWord ++ tailWord_779470) baseStart_779470 baseEnd_779470 := by
    simpa [prefixWord, tailWord_779470, baseEnd_779470] using wordTrace_append hprefix tailTrace_779470
  have hstable : (prefixWord ++ tailWord_779470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779470).length < 2 ^ (prefixWord ++ tailWord_779470).sum := by decide
  have hdescent : baseEnd_779470 < baseStart_779470 := by decide
  rcases family_descends (prefixWord ++ tailWord_779470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779528 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_779528 : Nat := 118140960795 + 779528 * 2 ^ 59
def prefixEnd_779528 : Nat := 4983230072969 + 3 ^ 40 * 779528 * 2
def baseEnd_779528 : Nat := 355797820122783401613353

theorem tailTrace_779528 : CollatzResearch.WordTrace tailWord_779528 prefixEnd_779528 355797820122783401613353 := by
  unfold tailWord_779528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14215860959955331814133619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18954481279940442418844825 14215860959955331814133619)
  ·
    refine ⟨21323791439932997721200429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14215860959955331814133619 21323791439932997721200429)
    ·
      refine ⟨7996421789974874145450161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21323791439932997721200429 7996421789974874145450161)
      ·
        refine ⟨5997316342481155609087621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7996421789974874145450161 5997316342481155609087621)
        ·
          refine ⟨1124496814215216676703929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5997316342481155609087621 1124496814215216676703929)
          ·
            refine ⟨843372610661412507527947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124496814215216676703929 843372610661412507527947)
            ·
              refine ⟨1265058915992118761291921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843372610661412507527947 1265058915992118761291921)
              ·
                refine ⟨948794186994089070968941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265058915992118761291921 948794186994089070968941)
                ·
                  refine ⟨355797820122783401613353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948794186994089070968941 355797820122783401613353)
                  ·
                    rfl

theorem cell20_779528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_779528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779528 prefixEnd_779528 := by exact prefixLift 779528
  have htrace : WordTrace (prefixWord ++ tailWord_779528) baseStart_779528 baseEnd_779528 := by
    simpa [prefixWord, tailWord_779528, baseEnd_779528] using wordTrace_append hprefix tailTrace_779528
  have hstable : (prefixWord ++ tailWord_779528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779528).length < 2 ^ (prefixWord ++ tailWord_779528).sum := by decide
  have hdescent : baseEnd_779528 < baseStart_779528 := by decide
  rcases family_descends (prefixWord ++ tailWord_779528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779532 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_779532 : Nat := 118140960795 + 779532 * 2 ^ 59
def prefixEnd_779532 : Nat := 4983230072969 + 3 ^ 40 * 779532 * 2
def baseEnd_779532 : Nat := 355799645831777165480003

theorem tailTrace_779532 : CollatzResearch.WordTrace tailWord_779532 prefixEnd_779532 355799645831777165480003 := by
  unfold tailWord_779532
  simp only [CollatzResearch.WordTrace]
  refine ⟨14215933905948086155706425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18954578541264114874275233 14215933905948086155706425)
  ·
    refine ⟨10661950429461064616779819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14215933905948086155706425 10661950429461064616779819)
    ·
      refine ⟨15992925644191596925169729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661950429461064616779819 15992925644191596925169729)
      ·
        refine ⟨11994694233143697693877297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15992925644191596925169729 11994694233143697693877297)
        ·
          refine ⟨8996020674857773270407973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11994694233143697693877297 8996020674857773270407973)
          ·
            refine ⟨1686753876535832488201495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8996020674857773270407973 1686753876535832488201495)
            ·
              refine ⟨2530130814803748732302243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686753876535832488201495 2530130814803748732302243)
              ·
                refine ⟨3795196222205623098453365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530130814803748732302243 3795196222205623098453365)
                ·
                  refine ⟨355799645831777165480003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3795196222205623098453365 355799645831777165480003)
                  ·
                    rfl

theorem cell20_779532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_779532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779532 prefixEnd_779532 := by exact prefixLift 779532
  have htrace : WordTrace (prefixWord ++ tailWord_779532) baseStart_779532 baseEnd_779532 := by
    simpa [prefixWord, tailWord_779532, baseEnd_779532] using wordTrace_append hprefix tailTrace_779532
  have hstable : (prefixWord ++ tailWord_779532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779532).length < 2 ^ (prefixWord ++ tailWord_779532).sum := by decide
  have hdescent : baseEnd_779532 < baseStart_779532 := by decide
  rcases family_descends (prefixWord ++ tailWord_779532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779570 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_779570 : Nat := 118140960795 + 779570 * 2 ^ 59
def prefixEnd_779570 : Nat := 4983230072969 + 3 ^ 40 * 779570 * 2
def baseEnd_779570 : Nat := 355816990067217922213181

theorem tailTrace_779570 : CollatzResearch.WordTrace tailWord_779570 prefixEnd_779570 355816990067217922213181 := by
  unfold tailWord_779570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7108313446439626200324041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18955502523839003200864109 7108313446439626200324041)
  ·
    refine ⟨5331235084829719650243031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7108313446439626200324041 5331235084829719650243031)
    ·
      refine ⟨7996852627244579475364547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331235084829719650243031 7996852627244579475364547)
      ·
        refine ⟨11995278940866869213046821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996852627244579475364547 11995278940866869213046821)
        ·
          refine ⟨2249114801412537977446279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11995278940866869213046821 2249114801412537977446279)
          ·
            refine ⟨3373672202118806966169419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249114801412537977446279 3373672202118806966169419)
            ·
              refine ⟨5060508303178210449254129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373672202118806966169419 5060508303178210449254129)
              ·
                refine ⟨3795381227383657836940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060508303178210449254129 3795381227383657836940597)
                ·
                  refine ⟨355816990067217922213181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3795381227383657836940597 355816990067217922213181)
                  ·
                    rfl

theorem cell20_779570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_779570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779570 prefixEnd_779570 := by exact prefixLift 779570
  have htrace : WordTrace (prefixWord ++ tailWord_779570) baseStart_779570 baseEnd_779570 := by
    simpa [prefixWord, tailWord_779570, baseEnd_779570] using wordTrace_append hprefix tailTrace_779570
  have hstable : (prefixWord ++ tailWord_779570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779570).length < 2 ^ (prefixWord ++ tailWord_779570).sum := by decide
  have hdescent : baseEnd_779570 < baseStart_779570 := by decide
  rcases family_descends (prefixWord ++ tailWord_779570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779573 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 2]
def baseStart_779573 : Nat := 118140960795 + 779573 * 2 ^ 59
def prefixEnd_779573 : Nat := 4983230072969 + 3 ^ 40 * 779573 * 2
def baseEnd_779573 : Nat := 355818359348963245113169

theorem tailTrace_779573 : CollatzResearch.WordTrace tailWord_779573 prefixEnd_779573 355818359348963245113169 := by
  unfold tailWord_779573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433363204747636313655373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18955575469831757542436915 28433363204747636313655373)
  ·
    refine ⟨10662511201780363617620765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28433363204747636313655373 10662511201780363617620765)
    ·
      refine ⟨3998441700667636356607787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10662511201780363617620765 3998441700667636356607787)
      ·
        refine ⟨5997662551001454534911681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998441700667636356607787 5997662551001454534911681)
        ·
          refine ⟨4498246913251090901183761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5997662551001454534911681 4498246913251090901183761)
          ·
            refine ⟨3373685184938318175887821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498246913251090901183761 3373685184938318175887821)
            ·
              refine ⟨1265131944351869315957933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3373685184938318175887821 1265131944351869315957933)
              ·
                refine ⟨474424479131950993484225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265131944351869315957933 474424479131950993484225)
                ·
                  refine ⟨355818359348963245113169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474424479131950993484225 355818359348963245113169)
                  ·
                    rfl

theorem cell20_779573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_779573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779573 prefixEnd_779573 := by exact prefixLift 779573
  have htrace : WordTrace (prefixWord ++ tailWord_779573) baseStart_779573 baseEnd_779573 := by
    simpa [prefixWord, tailWord_779573, baseEnd_779573] using wordTrace_append hprefix tailTrace_779573
  have hstable : (prefixWord ++ tailWord_779573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779573).length < 2 ^ (prefixWord ++ tailWord_779573).sum := by decide
  have hdescent : baseEnd_779573 < baseStart_779573 := by decide
  rcases family_descends (prefixWord ++ tailWord_779573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779594 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_779594 : Nat := 118140960795 + 779594 * 2 ^ 59
def prefixEnd_779594 : Nat := 4983230072969 + 3 ^ 40 * 779594 * 2
def baseEnd_779594 : Nat := 355827944321180505413083

theorem tailTrace_779594 : CollatzResearch.WordTrace tailWord_779594 prefixEnd_779594 355827944321180505413083 := by
  unfold tailWord_779594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7108532284417889225042459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18956086091781037933446557 7108532284417889225042459)
  ·
    refine ⟨10662798426626833837563689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7108532284417889225042459 10662798426626833837563689)
    ·
      refine ⟨7997098819970125378172767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10662798426626833837563689 7997098819970125378172767)
      ·
        refine ⟨11995648229955188067259151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997098819970125378172767 11995648229955188067259151)
        ·
          refine ⟨17993472344932782100888727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11995648229955188067259151 17993472344932782100888727)
          ·
            refine ⟨26990208517399173151333091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993472344932782100888727 26990208517399173151333091)
            ·
              refine ⟨40485312776098759726999637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26990208517399173151333091 40485312776098759726999637)
              ·
                refine ⟨474437259094907340550777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40485312776098759726999637 474437259094907340550777)
                ·
                  refine ⟨355827944321180505413083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474437259094907340550777 355827944321180505413083)
                  ·
                    rfl

theorem cell20_779594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_779594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779594 prefixEnd_779594 := by exact prefixLift 779594
  have htrace : WordTrace (prefixWord ++ tailWord_779594) baseStart_779594 baseEnd_779594 := by
    simpa [prefixWord, tailWord_779594, baseEnd_779594] using wordTrace_append hprefix tailTrace_779594
  have hstable : (prefixWord ++ tailWord_779594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779594).length < 2 ^ (prefixWord ++ tailWord_779594).sum := by decide
  have hdescent : baseEnd_779594 < baseStart_779594 := by decide
  rcases family_descends (prefixWord ++ tailWord_779594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779597 : List Nat := [1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_779597 : Nat := 118140960795 + 779597 * 2 ^ 59
def prefixEnd_779597 : Nat := 4983230072969 + 3 ^ 40 * 779597 * 2
def baseEnd_779597 : Nat := 118609771200975276104357

theorem tailTrace_779597 : CollatzResearch.WordTrace tailWord_779597 prefixEnd_779597 118609771200975276104357 := by
  unfold tailWord_779597
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434238556660688412529045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18956159037773792275019363 28434238556660688412529045)
  ·
    refine ⟨1332854932343469769337299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28434238556660688412529045 1332854932343469769337299)
    ·
      refine ⟨1999282398515204654005949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332854932343469769337299 1999282398515204654005949)
      ·
        refine ⟨749730899443201745252231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1999282398515204654005949 749730899443201745252231)
        ·
          refine ⟨1124596349164802617878347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749730899443201745252231 1124596349164802617878347)
          ·
            refine ⟨1686894523747203926817521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124596349164802617878347 1686894523747203926817521)
            ·
              refine ⟨1265170892810402945113141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686894523747203926817521 1265170892810402945113141)
              ·
                refine ⟨118609771200975276104357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265170892810402945113141 118609771200975276104357)
                ·
                  rfl

theorem cell20_779597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_779597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779597 prefixEnd_779597 := by exact prefixLift 779597
  have htrace : WordTrace (prefixWord ++ tailWord_779597) baseStart_779597 baseEnd_779597 := by
    simpa [prefixWord, tailWord_779597, baseEnd_779597] using wordTrace_append hprefix tailTrace_779597
  have hstable : (prefixWord ++ tailWord_779597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779597).length < 2 ^ (prefixWord ++ tailWord_779597).sum := by decide
  have hdescent : baseEnd_779597 < baseStart_779597 := by decide
  rcases family_descends (prefixWord ++ tailWord_779597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779608 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_779608 : Nat := 118140960795 + 779608 * 2 ^ 59
def prefixEnd_779608 : Nat := 4983230072969 + 3 ^ 40 * 779608 * 2
def baseEnd_779608 : Nat := 355834334302658678946359

theorem tailTrace_779608 : CollatzResearch.WordTrace tailWord_779608 prefixEnd_779608 355834334302658678946359 := by
  unfold tailWord_779608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217319879810418645589739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18956426506413891527452985 14217319879810418645589739)
  ·
    refine ⟨21325979819715627968384609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14217319879810418645589739 21325979819715627968384609)
    ·
      refine ⟨15994484864786720976288457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21325979819715627968384609 15994484864786720976288457)
      ·
        refine ⟨11995863648590040732216343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15994484864786720976288457 11995863648590040732216343)
        ·
          refine ⟨17993795472885061098324515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11995863648590040732216343 17993795472885061098324515)
          ·
            refine ⟨26990693209327591647486773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993795472885061098324515 26990693209327591647486773)
            ·
              refine ⟨2530377488374461716951885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26990693209327591647486773 2530377488374461716951885)
              ·
                refine ⟨948891558140423143856957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530377488374461716951885 948891558140423143856957)
                ·
                  refine ⟨355834334302658678946359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948891558140423143856957 355834334302658678946359)
                  ·
                    rfl

theorem cell20_779608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_779608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779608 prefixEnd_779608 := by exact prefixLift 779608
  have htrace : WordTrace (prefixWord ++ tailWord_779608) baseStart_779608 baseEnd_779608 := by
    simpa [prefixWord, tailWord_779608, baseEnd_779608] using wordTrace_append hprefix tailTrace_779608
  have hstable : (prefixWord ++ tailWord_779608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779608).length < 2 ^ (prefixWord ++ tailWord_779608).sum := by decide
  have hdescent : baseEnd_779608 < baseStart_779608 := by decide
  rcases family_descends (prefixWord ++ tailWord_779608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779632 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_779632 : Nat := 118140960795 + 779632 * 2 ^ 59
def prefixEnd_779632 : Nat := 4983230072969 + 3 ^ 40 * 779632 * 2
def baseEnd_779632 : Nat := 355845288556621262146261

theorem tailTrace_779632 : CollatzResearch.WordTrace tailWord_779632 prefixEnd_779632 355845288556621262146261 := by
  unfold tailWord_779632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217757555766944695026575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18957010074355926260035433 14217757555766944695026575)
  ·
    refine ⟨21326636333650417042539863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14217757555766944695026575 21326636333650417042539863)
    ·
      refine ⟨31989954500475625563809795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326636333650417042539863 31989954500475625563809795)
      ·
        refine ⟨47984931750713438345714693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31989954500475625563809795 47984931750713438345714693)
        ·
          refine ⟨8997174703258769689821505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47984931750713438345714693 8997174703258769689821505)
          ·
            refine ⟨6747881027444077267366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8997174703258769689821505 6747881027444077267366129)
            ·
              refine ⟨5060910770583057950524597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747881027444077267366129 5060910770583057950524597)
              ·
                refine ⟨474460384742161682861681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5060910770583057950524597 474460384742161682861681)
                ·
                  refine ⟨355845288556621262146261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474460384742161682861681 355845288556621262146261)
                  ·
                    rfl

theorem cell20_779632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_779632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779632 prefixEnd_779632 := by exact prefixLift 779632
  have htrace : WordTrace (prefixWord ++ tailWord_779632) baseStart_779632 baseEnd_779632 := by
    simpa [prefixWord, tailWord_779632, baseEnd_779632] using wordTrace_append hprefix tailTrace_779632
  have hstable : (prefixWord ++ tailWord_779632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779632).length < 2 ^ (prefixWord ++ tailWord_779632).sum := by decide
  have hdescent : baseEnd_779632 < baseStart_779632 := by decide
  rcases family_descends (prefixWord ++ tailWord_779632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779687 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 2]
def baseStart_779687 : Nat := 118140960795 + 779687 * 2 ^ 59
def prefixEnd_779687 : Nat := 4983230072969 + 3 ^ 40 * 779687 * 2
def baseEnd_779687 : Nat := 355870392055285515312703

theorem tailTrace_779687 : CollatzResearch.WordTrace tailWord_779687 prefixEnd_779687 355870392055285515312703 := by
  unfold tailWord_779687
  simp only [CollatzResearch.WordTrace]
  refine ⟨28437521126334633783305315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18958347417556422522203543 28437521126334633783305315)
  ·
    refine ⟨42656281689501950674957973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28437521126334633783305315 42656281689501950674957973)
    ·
      refine ⟨1999513204195403937888655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42656281689501950674957973 1999513204195403937888655)
      ·
        refine ⟨2999269806293105906832983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999513204195403937888655 2999269806293105906832983)
        ·
          refine ⟨4498904709439658860249475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999269806293105906832983 4498904709439658860249475)
          ·
            refine ⟨6748357064159488290374213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498904709439658860249475 6748357064159488290374213)
            ·
              refine ⟨1265316949529904054445165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6748357064159488290374213 1265316949529904054445165)
              ·
                refine ⟨474493856073714020416937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265316949529904054445165 474493856073714020416937)
                ·
                  refine ⟨355870392055285515312703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474493856073714020416937 355870392055285515312703)
                  ·
                    rfl

theorem cell20_779687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2].length) (baseStart_779687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779687 prefixEnd_779687 := by exact prefixLift 779687
  have htrace : WordTrace (prefixWord ++ tailWord_779687) baseStart_779687 baseEnd_779687 := by
    simpa [prefixWord, tailWord_779687, baseEnd_779687] using wordTrace_append hprefix tailTrace_779687
  have hstable : (prefixWord ++ tailWord_779687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779687).length < 2 ^ (prefixWord ++ tailWord_779687).sum := by decide
  have hdescent : baseEnd_779687 < baseStart_779687 := by decide
  rcases family_descends (prefixWord ++ tailWord_779687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779701 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_779701 : Nat := 118140960795 + 779701 * 2 ^ 59
def prefixEnd_779701 : Nat := 4983230072969 + 3 ^ 40 * 779701 * 2
def baseEnd_779701 : Nat := 355876782036763688845979

theorem tailTrace_779701 : CollatzResearch.WordTrace tailWord_779701 prefixEnd_779701 355876782036763688845979 := by
  unfold tailWord_779701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28438031748283914174314957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18958687832189276116209971 28438031748283914174314957)
  ·
    refine ⟨10664261905606467815368109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28438031748283914174314957 10664261905606467815368109)
    ·
      refine ⟨3999098214602425430763041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10664261905606467815368109 3999098214602425430763041)
      ·
        refine ⟨2999323660951819073072281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3999098214602425430763041 2999323660951819073072281)
        ·
          refine ⟨2249492745713864304804211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2999323660951819073072281 2249492745713864304804211)
          ·
            refine ⟨3374239118570796457206317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249492745713864304804211 3374239118570796457206317)
            ·
              refine ⟨1265339669464048671452369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3374239118570796457206317 1265339669464048671452369)
              ·
                refine ⟨949004752098036503589277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265339669464048671452369 949004752098036503589277)
                ·
                  refine ⟨355876782036763688845979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949004752098036503589277 355876782036763688845979)
                  ·
                    rfl

theorem cell20_779701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_779701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779701 prefixEnd_779701 := by exact prefixLift 779701
  have htrace : WordTrace (prefixWord ++ tailWord_779701) baseStart_779701 baseEnd_779701 := by
    simpa [prefixWord, tailWord_779701, baseEnd_779701] using wordTrace_append hprefix tailTrace_779701
  have hstable : (prefixWord ++ tailWord_779701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779701).length < 2 ^ (prefixWord ++ tailWord_779701).sum := by decide
  have hdescent : baseEnd_779701 < baseStart_779701 := by decide
  rcases family_descends (prefixWord ++ tailWord_779701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779743 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_779743 : Nat := 118140960795 + 779743 * 2 ^ 59
def prefixEnd_779743 : Nat := 4983230072969 + 3 ^ 40 * 779743 * 2
def baseEnd_779743 : Nat := 355895951981198209445807

theorem tailTrace_779743 : CollatzResearch.WordTrace tailWord_779743 prefixEnd_779743 355895951981198209445807 := by
  unfold tailWord_779743
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439563614131755347343883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18959709076087836898229255 28439563614131755347343883)
  ·
    refine ⟨42659345421197633021015825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28439563614131755347343883 42659345421197633021015825)
    ·
      refine ⟨31994509065898224765761869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42659345421197633021015825 31994509065898224765761869)
      ·
        refine ⟨11997940899711834287160701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31994509065898224765761869 11997940899711834287160701)
        ·
          refine ⟨4499227837391937857685263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11997940899711834287160701 4499227837391937857685263)
          ·
            refine ⟨6748841756087906786527895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499227837391937857685263 6748841756087906786527895)
            ·
              refine ⟨10123262634131860179791843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748841756087906786527895 10123262634131860179791843)
              ·
                refine ⟨15184893951197790269687765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10123262634131860179791843 15184893951197790269687765)
                ·
                  refine ⟨355895951981198209445807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15184893951197790269687765 355895951981198209445807)
                  ·
                    rfl

theorem cell20_779743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_779743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779743 prefixEnd_779743 := by exact prefixLift 779743
  have htrace : WordTrace (prefixWord ++ tailWord_779743) baseStart_779743 baseEnd_779743 := by
    simpa [prefixWord, tailWord_779743, baseEnd_779743] using wordTrace_append hprefix tailTrace_779743
  have hstable : (prefixWord ++ tailWord_779743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779743).length < 2 ^ (prefixWord ++ tailWord_779743).sum := by decide
  have hdescent : baseEnd_779743 < baseStart_779743 := by decide
  rcases family_descends (prefixWord ++ tailWord_779743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779777 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_779777 : Nat := 118140960795 + 779777 * 2 ^ 59
def prefixEnd_779777 : Nat := 4983230072969 + 3 ^ 40 * 779777 * 2
def baseEnd_779777 : Nat := 355911470507645202312335

theorem tailTrace_779777 : CollatzResearch.WordTrace tailWord_779777 prefixEnd_779777 355911470507645202312335 := by
  unfold tailWord_779777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28440803696008579154081585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18960535797339052769387723 28440803696008579154081585)
  ·
    refine ⟨21330602772006434365561189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28440803696008579154081585 21330602772006434365561189)
    ·
      refine ⟨3999488019751206443542723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21330602772006434365561189 3999488019751206443542723)
      ·
        refine ⟨5999232029626809665314085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999488019751206443542723 5999232029626809665314085)
        ·
          refine ⟨1124856005555026812246391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5999232029626809665314085 1124856005555026812246391)
          ·
            refine ⟨1687284008332540218369587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124856005555026812246391 1687284008332540218369587)
            ·
              refine ⟨2530926012498810327554381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687284008332540218369587 2530926012498810327554381)
              ·
                refine ⟨949097254687053872832893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530926012498810327554381 949097254687053872832893)
                ·
                  refine ⟨355911470507645202312335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949097254687053872832893 355911470507645202312335)
                  ·
                    rfl

theorem cell20_779777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_779777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779777 prefixEnd_779777 := by exact prefixLift 779777
  have htrace : WordTrace (prefixWord ++ tailWord_779777) baseStart_779777 baseEnd_779777 := by
    simpa [prefixWord, tailWord_779777, baseEnd_779777] using wordTrace_append hprefix tailTrace_779777
  have hstable : (prefixWord ++ tailWord_779777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779777).length < 2 ^ (prefixWord ++ tailWord_779777).sum := by decide
  have hdescent : baseEnd_779777 < baseStart_779777 := by decide
  rcases family_descends (prefixWord ++ tailWord_779777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779829 : List Nat := [1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_779829 : Nat := 118140960795 + 779829 * 2 ^ 59
def prefixEnd_779829 : Nat := 4983230072969 + 3 ^ 40 * 779829 * 2
def baseEnd_779829 : Nat := 118645068241521377526263

theorem tailTrace_779829 : CollatzResearch.WordTrace tailWord_779829 prefixEnd_779829 118645068241521377526263 := by
  unfold tailWord_779829
  simp only [CollatzResearch.WordTrace]
  refine ⟨28442700291820192034974541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18961800194546794689983027 28442700291820192034974541)
  ·
    refine ⟨10666012609432572013115453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28442700291820192034974541 10666012609432572013115453)
    ·
      refine ⟨3999754728537214504918295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10666012609432572013115453 3999754728537214504918295)
      ·
        refine ⟨5999632092805821757377443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999754728537214504918295 5999632092805821757377443)
        ·
          refine ⟨8999448139208732636066165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999632092805821757377443 8999448139208732636066165)
          ·
            refine ⟨843698263050818684631203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8999448139208732636066165 843698263050818684631203)
            ·
              refine ⟨1265547394576228026946805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843698263050818684631203 1265547394576228026946805)
              ·
                refine ⟨118645068241521377526263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265547394576228026946805 118645068241521377526263)
                ·
                  rfl

theorem cell20_779829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_779829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779829 prefixEnd_779829 := by exact prefixLift 779829
  have htrace : WordTrace (prefixWord ++ tailWord_779829) baseStart_779829 baseEnd_779829 := by
    simpa [prefixWord, tailWord_779829, baseEnd_779829] using wordTrace_append hprefix tailTrace_779829
  have hstable : (prefixWord ++ tailWord_779829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779829).length < 2 ^ (prefixWord ++ tailWord_779829).sum := by decide
  have hdescent : baseEnd_779829 < baseStart_779829 := by decide
  rcases family_descends (prefixWord ++ tailWord_779829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779857 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_779857 : Nat := 118140960795 + 779857 * 2 ^ 59
def prefixEnd_779857 : Nat := 4983230072969 + 3 ^ 40 * 779857 * 2
def baseEnd_779857 : Nat := 355947984687520479645341

theorem tailTrace_779857 : CollatzResearch.WordTrace tailWord_779857 prefixEnd_779857 355947984687520479645341 := by
  unfold tailWord_779857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443721535718752816993825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18962481023812501877995883 28443721535718752816993825)
  ·
    refine ⟨21332791151789064612745369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28443721535718752816993825 21332791151789064612745369)
    ·
      refine ⟨15999593363841798459559027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21332791151789064612745369 15999593363841798459559027)
      ·
        refine ⟨23999390045762697689338541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999593363841798459559027 23999390045762697689338541)
        ·
          refine ⟨8999771267161011633501953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23999390045762697689338541 8999771267161011633501953)
          ·
            refine ⟨6749828450370758725126465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8999771267161011633501953 6749828450370758725126465)
            ·
              refine ⟨5062371337778069043844849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6749828450370758725126465 5062371337778069043844849)
              ·
                refine ⟨3796778503333551782883637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5062371337778069043844849 3796778503333551782883637)
                ·
                  refine ⟨355947984687520479645341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3796778503333551782883637 355947984687520479645341)
                  ·
                    rfl

theorem cell20_779857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_779857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779857 prefixEnd_779857 := by exact prefixLift 779857
  have htrace : WordTrace (prefixWord ++ tailWord_779857) baseStart_779857 baseEnd_779857 := by
    simpa [prefixWord, tailWord_779857, baseEnd_779857] using wordTrace_append hprefix tailTrace_779857
  have hstable : (prefixWord ++ tailWord_779857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779857).length < 2 ^ (prefixWord ++ tailWord_779857).sum := by decide
  have hdescent : baseEnd_779857 < baseStart_779857 := by decide
  rcases family_descends (prefixWord ++ tailWord_779857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779864 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_779864 : Nat := 118140960795 + 779864 * 2 ^ 59
def prefixEnd_779864 : Nat := 4983230072969 + 3 ^ 40 * 779864 * 2
def baseEnd_779864 : Nat := 355951179678259566411979

theorem tailTrace_779864 : CollatzResearch.WordTrace tailWord_779864 prefixEnd_779864 355951179678259566411979 := by
  unfold tailWord_779864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221988423346696506249323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18962651231128928674999097 14221988423346696506249323)
  ·
    refine ⟨21332982635020044759373985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221988423346696506249323 21332982635020044759373985)
    ·
      refine ⟨15999736976265033569530489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21332982635020044759373985 15999736976265033569530489)
      ·
        refine ⟨11999802732198775177147867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15999736976265033569530489 11999802732198775177147867)
        ·
          refine ⟨17999704098298162765721801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999802732198775177147867 17999704098298162765721801)
          ·
            refine ⟨13499778073723622074291351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17999704098298162765721801 13499778073723622074291351)
            ·
              refine ⟨20249667110585433111437027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13499778073723622074291351 20249667110585433111437027)
              ·
                refine ⟨30374500665878149667155541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20249667110585433111437027 30374500665878149667155541)
                ·
                  refine ⟨355951179678259566411979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30374500665878149667155541 355951179678259566411979)
                  ·
                    rfl

theorem cell20_779864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_779864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779864 prefixEnd_779864 := by exact prefixLift 779864
  have htrace : WordTrace (prefixWord ++ tailWord_779864) baseStart_779864 baseEnd_779864 := by
    simpa [prefixWord, tailWord_779864, baseEnd_779864] using wordTrace_append hprefix tailTrace_779864
  have hstable : (prefixWord ++ tailWord_779864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779864).length < 2 ^ (prefixWord ++ tailWord_779864).sum := by decide
  have hdescent : baseEnd_779864 < baseStart_779864 := by decide
  rcases family_descends (prefixWord ++ tailWord_779864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779905 : List Nat := [1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_779905 : Nat := 118140960795 + 779905 * 2 ^ 59
def prefixEnd_779905 : Nat := 4983230072969 + 3 ^ 40 * 779905 * 2
def baseEnd_779905 : Nat := 118656631065148548681715

theorem tailTrace_779905 : CollatzResearch.WordTrace tailWord_779905 prefixEnd_779905 118656631065148548681715 := by
  unfold tailWord_779905
  simp only [CollatzResearch.WordTrace]
  refine ⟨28445472239544857014741169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18963648159696571343160779 28445472239544857014741169)
  ·
    refine ⟨21334104179658642761055877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28445472239544857014741169 21334104179658642761055877)
    ·
      refine ⟨4000144533685995517697977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21334104179658642761055877 4000144533685995517697977)
      ·
        refine ⟨3000108400264496638273483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000144533685995517697977 3000108400264496638273483)
        ·
          refine ⟨4500162600396744957410225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000108400264496638273483 4500162600396744957410225)
          ·
            refine ⟨3375121950297558718057669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500162600396744957410225 3375121950297558718057669)
            ·
              refine ⟨632835365680792259635813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3375121950297558718057669 632835365680792259635813)
              ·
                refine ⟨118656631065148548681715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632835365680792259635813 118656631065148548681715)
                ·
                  rfl

theorem cell20_779905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_779905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779905 prefixEnd_779905 := by exact prefixLift 779905
  have htrace : WordTrace (prefixWord ++ tailWord_779905) baseStart_779905 baseEnd_779905 := by
    simpa [prefixWord, tailWord_779905, baseEnd_779905] using wordTrace_append hprefix tailTrace_779905
  have hstable : (prefixWord ++ tailWord_779905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779905).length < 2 ^ (prefixWord ++ tailWord_779905).sum := by decide
  have hdescent : baseEnd_779905 < baseStart_779905 := by decide
  rcases family_descends (prefixWord ++ tailWord_779905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779922 : List Nat := [3, 2, 3, 1, 4, 1, 6]
def baseStart_779922 : Nat := 118140960795 + 779922 * 2 ^ 59
def prefixEnd_779922 : Nat := 4983230072969 + 3 ^ 40 * 779922 * 2
def baseEnd_779922 : Nat := 39553072495407682497601

theorem tailTrace_779922 : CollatzResearch.WordTrace tailWord_779922 prefixEnd_779922 39553072495407682497601 := by
  unfold tailWord_779922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111523070120817229527505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18964061520322179278740013 7111523070120817229527505)
  ·
    refine ⟨5333642302590612922145629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7111523070120817229527505 5333642302590612922145629)
    ·
      refine ⟨2000115863471479845804611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5333642302590612922145629 2000115863471479845804611)
      ·
        refine ⟨3000173795207219768706917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000115863471479845804611 3000173795207219768706917)
        ·
          refine ⟨562532586601353706632547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3000173795207219768706917 562532586601353706632547)
          ·
            refine ⟨843798879902030559948821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562532586601353706632547 843798879902030559948821)
            ·
              refine ⟨39553072495407682497601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 843798879902030559948821 39553072495407682497601)
              ·
                rfl

theorem cell20_779922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_779922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779922 prefixEnd_779922 := by exact prefixLift 779922
  have htrace : WordTrace (prefixWord ++ tailWord_779922) baseStart_779922 baseEnd_779922 := by
    simpa [prefixWord, tailWord_779922, baseEnd_779922] using wordTrace_append hprefix tailTrace_779922
  have hstable : (prefixWord ++ tailWord_779922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779922).length < 2 ^ (prefixWord ++ tailWord_779922).sum := by decide
  have hdescent : baseEnd_779922 < baseStart_779922 := by decide
  rcases family_descends (prefixWord ++ tailWord_779922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779932 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_779932 : Nat := 118140960795 + 779932 * 2 ^ 59
def prefixEnd_779932 : Nat := 4983230072969 + 3 ^ 40 * 779932 * 2
def baseEnd_779932 : Nat := 355982216731153552145035

theorem tailTrace_779932 : CollatzResearch.WordTrace tailWord_779932 prefixEnd_779932 355982216731153552145035 := by
  unfold tailWord_779932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223228505223520312987025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18964304673631360417316033 14223228505223520312987025)
  ·
    refine ⟨10667421378917640234740269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14223228505223520312987025 10667421378917640234740269)
    ·
      refine ⟨4000283017094115088027601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10667421378917640234740269 4000283017094115088027601)
      ·
        refine ⟨3000212262820586316020701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000283017094115088027601 3000212262820586316020701)
        ·
          refine ⟨1125079598557719868507763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3000212262820586316020701 1125079598557719868507763)
          ·
            refine ⟨1687619397836579802761645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125079598557719868507763 1687619397836579802761645)
            ·
              refine ⟨632857274188717426035617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1687619397836579802761645 632857274188717426035617)
              ·
                refine ⟨474642955641538069526713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632857274188717426035617 474642955641538069526713)
                ·
                  refine ⟨355982216731153552145035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474642955641538069526713 355982216731153552145035)
                  ·
                    rfl

theorem cell20_779932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_779932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779932 prefixEnd_779932 := by exact prefixLift 779932
  have htrace : WordTrace (prefixWord ++ tailWord_779932) baseStart_779932 baseEnd_779932 := by
    simpa [prefixWord, tailWord_779932, baseEnd_779932] using wordTrace_append hprefix tailTrace_779932
  have hstable : (prefixWord ++ tailWord_779932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779932).length < 2 ^ (prefixWord ++ tailWord_779932).sum := by decide
  have hdescent : baseEnd_779932 < baseStart_779932 := by decide
  rcases family_descends (prefixWord ++ tailWord_779932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779936 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_779936 : Nat := 118140960795 + 779936 * 2 ^ 59
def prefixEnd_779936 : Nat := 4983230072969 + 3 ^ 40 * 779936 * 2
def baseEnd_779936 : Nat := 355984042440147316011685

theorem tailTrace_779936 : CollatzResearch.WordTrace tailWord_779936 prefixEnd_779936 355984042440147316011685 := by
  unfold tailWord_779936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223301451216274654559831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18964401934955032872746441 14223301451216274654559831)
  ·
    refine ⟨21334952176824411981839747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14223301451216274654559831 21334952176824411981839747)
    ·
      refine ⟨32002428265236617972759621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21334952176824411981839747 32002428265236617972759621)
      ·
        refine ⟨6000455299731865869892429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32002428265236617972759621 6000455299731865869892429)
        ·
          refine ⟨2250170737399449701209661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6000455299731865869892429 2250170737399449701209661)
          ·
            refine ⟨843814026524793637953623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2250170737399449701209661 843814026524793637953623)
            ·
              refine ⟨1265721039787190456930435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843814026524793637953623 1265721039787190456930435)
              ·
                refine ⟨1898581559680785685395653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265721039787190456930435 1898581559680785685395653)
                ·
                  refine ⟨355984042440147316011685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898581559680785685395653 355984042440147316011685)
                  ·
                    rfl

theorem cell20_779936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_779936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779936 prefixEnd_779936 := by exact prefixLift 779936
  have htrace : WordTrace (prefixWord ++ tailWord_779936) baseStart_779936 baseEnd_779936 := by
    simpa [prefixWord, tailWord_779936, baseEnd_779936] using wordTrace_append hprefix tailTrace_779936
  have hstable : (prefixWord ++ tailWord_779936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779936).length < 2 ^ (prefixWord ++ tailWord_779936).sum := by decide
  have hdescent : baseEnd_779936 < baseStart_779936 := by decide
  rcases family_descends (prefixWord ++ tailWord_779936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779964 : List Nat := [2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_779964 : Nat := 118140960795 + 779964 * 2 ^ 59
def prefixEnd_779964 : Nat := 4983230072969 + 3 ^ 40 * 779964 * 2
def baseEnd_779964 : Nat := 118665607467701221026079

theorem tailTrace_779964 : CollatzResearch.WordTrace tailWord_779964 prefixEnd_779964 118665607467701221026079 := by
  unfold tailWord_779964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223812073165555045569473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18965082764220740060759297 14223812073165555045569473)
  ·
    refine ⟨10667859054874166284177105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14223812073165555045569473 10667859054874166284177105)
    ·
      refine ⟨8000894291155624713132829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10667859054874166284177105 8000894291155624713132829)
      ·
        refine ⟨3000335359183359267424811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8000894291155624713132829 3000335359183359267424811)
        ·
          refine ⟨4500503038775038901137217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000335359183359267424811 4500503038775038901137217)
          ·
            refine ⟨3375377279081279175852913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500503038775038901137217 3375377279081279175852913)
            ·
              refine ⟨2531532959310959381889685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375377279081279175852913 2531532959310959381889685)
              ·
                refine ⟨118665607467701221026079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2531532959310959381889685 118665607467701221026079)
                ·
                  rfl

theorem cell20_779964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_779964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779964 prefixEnd_779964 := by exact prefixLift 779964
  have htrace : WordTrace (prefixWord ++ tailWord_779964) baseStart_779964 baseEnd_779964 := by
    simpa [prefixWord, tailWord_779964, baseEnd_779964] using wordTrace_append hprefix tailTrace_779964
  have hstable : (prefixWord ++ tailWord_779964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779964).length < 2 ^ (prefixWord ++ tailWord_779964).sum := by decide
  have hdescent : baseEnd_779964 < baseStart_779964 := by decide
  rcases family_descends (prefixWord ++ tailWord_779964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779981 : List Nat := [1, 6, 2, 1, 1, 9]
def baseStart_779981 : Nat := 118140960795 + 779981 * 2 ^ 59
def prefixEnd_779981 : Nat := 4983230072969 + 3 ^ 40 * 779981 * 2
def baseEnd_779981 : Nat := 13185354876530635537463

theorem tailTrace_779981 : CollatzResearch.WordTrace tailWord_779981 prefixEnd_779981 13185354876530635537463 := by
  unfold tailWord_779981
  simp only [CollatzResearch.WordTrace]
  refine ⟨28448244187269521994507797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18965496124846347996338531 28448244187269521994507797)
  ·
    refine ⟨1333511446278258843492553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28448244187269521994507797 1333511446278258843492553)
    ·
      refine ⟨1000133584708694132619415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1333511446278258843492553 1000133584708694132619415)
      ·
        refine ⟨1500200377063041198929123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000133584708694132619415 1500200377063041198929123)
        ·
          refine ⟨2250300565594561798393685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500200377063041198929123 2250300565594561798393685)
          ·
            refine ⟨13185354876530635537463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2250300565594561798393685 13185354876530635537463)
            ·
              rfl

theorem cell20_779981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_779981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779981 prefixEnd_779981 := by exact prefixLift 779981
  have htrace : WordTrace (prefixWord ++ tailWord_779981) baseStart_779981 baseEnd_779981 := by
    simpa [prefixWord, tailWord_779981, baseEnd_779981] using wordTrace_append hprefix tailTrace_779981
  have hstable : (prefixWord ++ tailWord_779981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779981).length < 2 ^ (prefixWord ++ tailWord_779981).sum := by decide
  have hdescent : baseEnd_779981 < baseStart_779981 := by decide
  rcases family_descends (prefixWord ++ tailWord_779981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779985 : List Nat := [1, 2, 2, 1, 2, 12]
def baseStart_779985 : Nat := 118140960795 + 779985 * 2 ^ 59
def prefixEnd_779985 : Nat := 4983230072969 + 3 ^ 40 * 779985 * 2
def baseEnd_779985 : Nat := 13185422495382256421413

theorem tailTrace_779985 : CollatzResearch.WordTrace tailWord_779985 prefixEnd_779985 13185422495382256421413 := by
  unfold tailWord_779985
  simp only [CollatzResearch.WordTrace]
  refine ⟨28448390079255030677653409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18965593386170020451768939 28448390079255030677653409)
  ·
    refine ⟨21336292559441273008240057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28448390079255030677653409 21336292559441273008240057)
    ·
      refine ⟨16002219419580954756180043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21336292559441273008240057 16002219419580954756180043)
      ·
        refine ⟨24003329129371432134270065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16002219419580954756180043 24003329129371432134270065)
        ·
          refine ⟨18002496847028574100702549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24003329129371432134270065 18002496847028574100702549)
          ·
            refine ⟨13185422495382256421413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18002496847028574100702549 13185422495382256421413)
            ·
              rfl

theorem cell20_779985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_779985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_779985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_779985 prefixEnd_779985 := by exact prefixLift 779985
  have htrace : WordTrace (prefixWord ++ tailWord_779985) baseStart_779985 baseEnd_779985 := by
    simpa [prefixWord, tailWord_779985, baseEnd_779985] using wordTrace_append hprefix tailTrace_779985
  have hstable : (prefixWord ++ tailWord_779985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779985).length < 2 ^ (prefixWord ++ tailWord_779985).sum := by decide
  have hdescent : baseEnd_779985 < baseStart_779985 := by decide
  rcases family_descends (prefixWord ++ tailWord_779985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780023 : List Nat := [1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_780023 : Nat := 118140960795 + 780023 * 2 ^ 59
def prefixEnd_780023 : Nat := 4983230072969 + 3 ^ 40 * 780023 * 2
def baseEnd_780023 : Nat := 118674583870253893370443

theorem tailTrace_780023 : CollatzResearch.WordTrace tailWord_780023 prefixEnd_780023 118674583870253893370443 := by
  unfold tailWord_780023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449776053117363167536723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18966517368744908778357815 28449776053117363167536723)
  ·
    refine ⟨42674664079676044751305085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28449776053117363167536723 42674664079676044751305085)
    ·
      refine ⟨16002999029878516781739407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42674664079676044751305085 16002999029878516781739407)
      ·
        refine ⟨24004498544817775172609111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16002999029878516781739407 24004498544817775172609111)
        ·
          refine ⟨36006747817226662758913667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24004498544817775172609111 36006747817226662758913667)
          ·
            refine ⟨54010121725839994138370501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36006747817226662758913667 54010121725839994138370501)
            ·
              refine ⟨10126897823594998900944469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54010121725839994138370501 10126897823594998900944469)
              ·
                refine ⟨118674583870253893370443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10126897823594998900944469 118674583870253893370443)
                ·
                  rfl

theorem cell20_780023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_780023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780023 prefixEnd_780023 := by exact prefixLift 780023
  have htrace : WordTrace (prefixWord ++ tailWord_780023) baseStart_780023 baseEnd_780023 := by
    simpa [prefixWord, tailWord_780023, baseEnd_780023] using wordTrace_append hprefix tailTrace_780023
  have hstable : (prefixWord ++ tailWord_780023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780023).length < 2 ^ (prefixWord ++ tailWord_780023).sum := by decide
  have hdescent : baseEnd_780023 < baseStart_780023 := by decide
  rcases family_descends (prefixWord ++ tailWord_780023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780047 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_780047 : Nat := 118140960795 + 780047 * 2 ^ 59
def prefixEnd_780047 : Nat := 4983230072969 + 3 ^ 40 * 780047 * 2
def baseEnd_780047 : Nat := 356034705864724263311231

theorem tailTrace_780047 : CollatzResearch.WordTrace tailWord_780047 prefixEnd_780047 356034705864724263311231 := by
  unfold tailWord_780047
  simp only [CollatzResearch.WordTrace]
  refine ⟨28450651405030415266410395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18967100936686943510940263 28450651405030415266410395)
  ·
    refine ⟨42675977107545622899615593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28450651405030415266410395 42675977107545622899615593)
    ·
      refine ⟨32006982830659217174711695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42675977107545622899615593 32006982830659217174711695)
      ·
        refine ⟨48010474245988825762067543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32006982830659217174711695 48010474245988825762067543)
        ·
          refine ⟨72015711368983238643101315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48010474245988825762067543 72015711368983238643101315)
          ·
            refine ⟨108023567053474857964651973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72015711368983238643101315 108023567053474857964651973)
            ·
              refine ⟨20254418822526535868372245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108023567053474857964651973 20254418822526535868372245)
              ·
                refine ⟨949425882305931368829949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20254418822526535868372245 949425882305931368829949)
                ·
                  refine ⟨356034705864724263311231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949425882305931368829949 356034705864724263311231)
                  ·
                    rfl

theorem cell20_780047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_780047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780047 prefixEnd_780047 := by exact prefixLift 780047
  have htrace : WordTrace (prefixWord ++ tailWord_780047) baseStart_780047 baseEnd_780047 := by
    simpa [prefixWord, tailWord_780047, baseEnd_780047] using wordTrace_append hprefix tailTrace_780047
  have hstable : (prefixWord ++ tailWord_780047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780047).length < 2 ^ (prefixWord ++ tailWord_780047).sum := by decide
  have hdescent : baseEnd_780047 < baseStart_780047 := by decide
  rcases family_descends (prefixWord ++ tailWord_780047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780050 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_780050 : Nat := 118140960795 + 780050 * 2 ^ 59
def prefixEnd_780050 : Nat := 4983230072969 + 3 ^ 40 * 780050 * 2
def baseEnd_780050 : Nat := 356036075146469586211219

theorem tailTrace_780050 : CollatzResearch.WordTrace tailWord_780050 prefixEnd_780050 356036075146469586211219 := by
  unfold tailWord_780050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112690206004886694692401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18967173882679697852513069 7112690206004886694692401)
  ·
    refine ⟨5334517654503665021019301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7112690206004886694692401 5334517654503665021019301)
    ·
      refine ⟨1000222060219437191441119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5334517654503665021019301 1000222060219437191441119)
      ·
        refine ⟨1500333090329155787161679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000222060219437191441119 1500333090329155787161679)
        ·
          refine ⟨2250499635493733680742519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500333090329155787161679 2250499635493733680742519)
          ·
            refine ⟨3375749453240600521113779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250499635493733680742519 3375749453240600521113779)
            ·
              refine ⟨5063624179860900781670669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375749453240600521113779 5063624179860900781670669)
              ·
                refine ⟨1898859067447837793126501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063624179860900781670669 1898859067447837793126501)
                ·
                  refine ⟨356036075146469586211219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898859067447837793126501 356036075146469586211219)
                  ·
                    rfl

theorem cell20_780050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_780050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780050 prefixEnd_780050 := by exact prefixLift 780050
  have htrace : WordTrace (prefixWord ++ tailWord_780050) baseStart_780050 baseEnd_780050 := by
    simpa [prefixWord, tailWord_780050, baseEnd_780050] using wordTrace_append hprefix tailTrace_780050
  have hstable : (prefixWord ++ tailWord_780050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780050).length < 2 ^ (prefixWord ++ tailWord_780050).sum := by decide
  have hdescent : baseEnd_780050 < baseStart_780050 := by decide
  rcases family_descends (prefixWord ++ tailWord_780050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780084 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_780084 : Nat := 118140960795 + 780084 * 2 ^ 59
def prefixEnd_780084 : Nat := 4983230072969 + 3 ^ 40 * 780084 * 2
def baseEnd_780084 : Nat := 356051593672916579077747

theorem tailTrace_780084 : CollatzResearch.WordTrace tailWord_780084 prefixEnd_780084 356051593672916579077747 := by
  unfold tailWord_780084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226000452948185292753653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968000603930913723671537 14226000452948185292753653)
  ·
    refine ⟨1333687542463892371195655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14226000452948185292753653 1333687542463892371195655)
    ·
      refine ⟨2000531313695838556793483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333687542463892371195655 2000531313695838556793483)
      ·
        refine ⟨3000796970543757835190225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000531313695838556793483 3000796970543757835190225)
        ·
          refine ⟨2250597727907818376392669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000796970543757835190225 2250597727907818376392669)
          ·
            refine ⟨843974147965431891147251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2250597727907818376392669 843974147965431891147251)
            ·
              refine ⟨1265961221948147836720877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843974147965431891147251 1265961221948147836720877)
              ·
                refine ⟨474735458230555438770329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265961221948147836720877 474735458230555438770329)
                ·
                  refine ⟨356051593672916579077747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474735458230555438770329 356051593672916579077747)
                  ·
                    rfl

theorem cell20_780084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_780084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780084 prefixEnd_780084 := by exact prefixLift 780084
  have htrace : WordTrace (prefixWord ++ tailWord_780084) baseStart_780084 baseEnd_780084 := by
    simpa [prefixWord, tailWord_780084, baseEnd_780084] using wordTrace_append hprefix tailTrace_780084
  have hstable : (prefixWord ++ tailWord_780084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780084).length < 2 ^ (prefixWord ++ tailWord_780084).sum := by decide
  have hdescent : baseEnd_780084 < baseStart_780084 := by decide
  rcases family_descends (prefixWord ++ tailWord_780084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780088 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_780088 : Nat := 118140960795 + 780088 * 2 ^ 59
def prefixEnd_780088 : Nat := 4983230072969 + 3 ^ 40 * 780088 * 2
def baseEnd_780088 : Nat := 356053419381910342944397

theorem tailTrace_780088 : CollatzResearch.WordTrace tailWord_780088 prefixEnd_780088 356053419381910342944397 := by
  unfold tailWord_780088
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226073398940939634326459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968097865254586179101945 14226073398940939634326459)
  ·
    refine ⟨21339110098411409451489689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14226073398940939634326459 21339110098411409451489689)
    ·
      refine ⟨16004332573808557088617267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21339110098411409451489689 16004332573808557088617267)
      ·
        refine ⟨24006498860712835632925901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16004332573808557088617267 24006498860712835632925901)
        ·
          refine ⟨9002437072767313362347213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24006498860712835632925901 9002437072767313362347213)
          ·
            refine ⟨3375913902287742510880205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9002437072767313362347213 3375913902287742510880205)
            ·
              refine ⟨1265967713357903441580077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375913902287742510880205 1265967713357903441580077)
              ·
                refine ⟨474737892509213790592529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265967713357903441580077 474737892509213790592529)
                ·
                  refine ⟨356053419381910342944397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474737892509213790592529 356053419381910342944397)
                  ·
                    rfl

theorem cell20_780088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_780088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780088 prefixEnd_780088 := by exact prefixLift 780088
  have htrace : WordTrace (prefixWord ++ tailWord_780088) baseStart_780088 baseEnd_780088 := by
    simpa [prefixWord, tailWord_780088, baseEnd_780088] using wordTrace_append hprefix tailTrace_780088
  have hstable : (prefixWord ++ tailWord_780088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780088).length < 2 ^ (prefixWord ++ tailWord_780088).sum := by decide
  have hdescent : baseEnd_780088 < baseStart_780088 := by decide
  rcases family_descends (prefixWord ++ tailWord_780088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780092 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_780092 : Nat := 118140960795 + 780092 * 2 ^ 59
def prefixEnd_780092 : Nat := 4983230072969 + 3 ^ 40 * 780092 * 2
def baseEnd_780092 : Nat := 356055245090904106811047

theorem tailTrace_780092 : CollatzResearch.WordTrace tailWord_780092 prefixEnd_780092 356055245090904106811047 := by
  unfold tailWord_780092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226146344933693975899265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968195126578258634532353 14226146344933693975899265)
  ·
    refine ⟨10669609758700270481924449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14226146344933693975899265 10669609758700270481924449)
    ·
      refine ⟨8002207319025202861443337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10669609758700270481924449 8002207319025202861443337)
      ·
        refine ⟨6001655489268902146082503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8002207319025202861443337 6001655489268902146082503)
        ·
          refine ⟨9002483233903353219123755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001655489268902146082503 9002483233903353219123755)
          ·
            refine ⟨13503724850855029828685633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002483233903353219123755 13503724850855029828685633)
            ·
              refine ⟨10127793638141272371514225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13503724850855029828685633 10127793638141272371514225)
              ·
                refine ⟨7595845228605954278635669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10127793638141272371514225 7595845228605954278635669)
                ·
                  refine ⟨356055245090904106811047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7595845228605954278635669 356055245090904106811047)
                  ·
                    rfl

theorem cell20_780092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_780092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780092 prefixEnd_780092 := by exact prefixLift 780092
  have htrace : WordTrace (prefixWord ++ tailWord_780092) baseStart_780092 baseEnd_780092 := by
    simpa [prefixWord, tailWord_780092, baseEnd_780092] using wordTrace_append hprefix tailTrace_780092
  have hstable : (prefixWord ++ tailWord_780092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780092).length < 2 ^ (prefixWord ++ tailWord_780092).sum := by decide
  have hdescent : baseEnd_780092 < baseStart_780092 := by decide
  rcases family_descends (prefixWord ++ tailWord_780092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780095 : List Nat := [1, 1, 2, 2, 7, 1, 6]
def baseStart_780095 : Nat := 118140960795 + 780095 * 2 ^ 59
def prefixEnd_780095 : Nat := 4983230072969 + 3 ^ 40 * 780095 * 2
def baseEnd_780095 : Nat := 39561846041405492190115

theorem tailTrace_780095 : CollatzResearch.WordTrace tailWord_780095 prefixEnd_780095 39561846041405492190115 := by
  unfold tailWord_780095
  simp only [CollatzResearch.WordTrace]
  refine ⟨28452402108856519464157739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18968268072571012976105159 28452402108856519464157739)
  ·
    refine ⟨42678603163284779196236609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28452402108856519464157739 42678603163284779196236609)
    ·
      refine ⟨32008952372463584397177457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42678603163284779196236609 32008952372463584397177457)
      ·
        refine ⟨24006714279347688297883093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32008952372463584397177457 24006714279347688297883093)
        ·
          refine ⟨562657365922211444481635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24006714279347688297883093 562657365922211444481635)
          ·
            refine ⟨843986048883317166722453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562657365922211444481635 843986048883317166722453)
            ·
              refine ⟨39561846041405492190115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 843986048883317166722453 39561846041405492190115)
              ·
                rfl

theorem cell20_780095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_780095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780095 prefixEnd_780095 := by exact prefixLift 780095
  have htrace : WordTrace (prefixWord ++ tailWord_780095) baseStart_780095 baseEnd_780095 := by
    simpa [prefixWord, tailWord_780095, baseEnd_780095] using wordTrace_append hprefix tailTrace_780095
  have hstable : (prefixWord ++ tailWord_780095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780095).length < 2 ^ (prefixWord ++ tailWord_780095).sum := by decide
  have hdescent : baseEnd_780095 < baseStart_780095 := by decide
  rcases family_descends (prefixWord ++ tailWord_780095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780099 : List Nat := [1, 1, 1, 3, 1, 5, 8]
def baseStart_780099 : Nat := 118140960795 + 780099 * 2 ^ 59
def prefixEnd_780099 : Nat := 4983230072969 + 3 ^ 40 * 780099 * 2
def baseEnd_780099 : Nat := 39562048897960354841965

theorem tailTrace_780099 : CollatzResearch.WordTrace tailWord_780099 prefixEnd_780099 39562048897960354841965 := by
  unfold tailWord_780099
  simp only [CollatzResearch.WordTrace]
  refine ⟨28452548000842028147303351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18968365333894685431535567 28452548000842028147303351)
  ·
    refine ⟨42678822001263042220955027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28452548000842028147303351 42678822001263042220955027)
    ·
      refine ⟨64018233001894563331432541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42678822001263042220955027 64018233001894563331432541)
      ·
        refine ⟨24006837375710461249287203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64018233001894563331432541 24006837375710461249287203)
        ·
          refine ⟨36010256063565691873930805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24006837375710461249287203 36010256063565691873930805)
          ·
            refine ⟨3375961505959283613181013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36010256063565691873930805 3375961505959283613181013)
            ·
              refine ⟨39562048897960354841965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3375961505959283613181013 39562048897960354841965)
              ·
                rfl

theorem cell20_780099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_780099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780099 prefixEnd_780099 := by exact prefixLift 780099
  have htrace : WordTrace (prefixWord ++ tailWord_780099) baseStart_780099 baseEnd_780099 := by
    simpa [prefixWord, tailWord_780099, baseEnd_780099] using wordTrace_append hprefix tailTrace_780099
  have hstable : (prefixWord ++ tailWord_780099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780099).length < 2 ^ (prefixWord ++ tailWord_780099).sum := by decide
  have hdescent : baseEnd_780099 < baseStart_780099 := by decide
  rcases family_descends (prefixWord ++ tailWord_780099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780116 : List Nat := [2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_780116 : Nat := 118140960795 + 780116 * 2 ^ 59
def prefixEnd_780116 : Nat := 4983230072969 + 3 ^ 40 * 780116 * 2
def baseEnd_780116 : Nat := 118688733114955563336983

theorem tailTrace_780116 : CollatzResearch.WordTrace tailWord_780116 prefixEnd_780116 118688733114955563336983 := by
  unfold tailWord_780116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226584020890220025336101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968778694520293367114801 14226584020890220025336101)
  ·
    refine ⟨2667484503916916254750519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14226584020890220025336101 2667484503916916254750519)
    ·
      refine ⟨4001226755875374382125779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667484503916916254750519 4001226755875374382125779)
      ·
        refine ⟨6001840133813061573188669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001226755875374382125779 6001840133813061573188669)
        ·
          refine ⟨2250690050179898089945751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6001840133813061573188669 2250690050179898089945751)
          ·
            refine ⟨3376035075269847134918627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250690050179898089945751 3376035075269847134918627)
            ·
              refine ⟨5064052612904770702377941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376035075269847134918627 5064052612904770702377941)
              ·
                refine ⟨118688733114955563336983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5064052612904770702377941 118688733114955563336983)
                ·
                  rfl

theorem cell20_780116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_780116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780116 prefixEnd_780116 := by exact prefixLift 780116
  have htrace : WordTrace (prefixWord ++ tailWord_780116) baseStart_780116 baseEnd_780116 := by
    simpa [prefixWord, tailWord_780116, baseEnd_780116] using wordTrace_append hprefix tailTrace_780116
  have hstable : (prefixWord ++ tailWord_780116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780116).length < 2 ^ (prefixWord ++ tailWord_780116).sum := by decide
  have hdescent : baseEnd_780116 < baseStart_780116 := by decide
  rcases family_descends (prefixWord ++ tailWord_780116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780147 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 2]
def baseStart_780147 : Nat := 118140960795 + 780147 * 2 ^ 59
def prefixEnd_780147 : Nat := 4983230072969 + 3 ^ 40 * 780147 * 2
def baseEnd_780147 : Nat := 356080348589568359977489

theorem tailTrace_780147 : CollatzResearch.WordTrace tailWord_780147 prefixEnd_780147 356080348589568359977489 := by
  unfold tailWord_780147
  simp only [CollatzResearch.WordTrace]
  refine ⟨28454298704668132345050695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18969532469778754896700463 28454298704668132345050695)
  ·
    refine ⟨42681448057002198517576043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28454298704668132345050695 42681448057002198517576043)
    ·
      refine ⟨64022172085503297776364065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42681448057002198517576043 64022172085503297776364065)
      ·
        refine ⟨48016629064127473332273049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64022172085503297776364065 48016629064127473332273049)
        ·
          refine ⟨36012471798095604999204787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48016629064127473332273049 36012471798095604999204787)
          ·
            refine ⟨54018707697143407498807181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36012471798095604999204787 54018707697143407498807181)
            ·
              refine ⟨20257015386428777812052693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54018707697143407498807181 20257015386428777812052693)
              ·
                refine ⟨474773798119424479969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20257015386428777812052693 474773798119424479969985)
                ·
                  refine ⟨356080348589568359977489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474773798119424479969985 356080348589568359977489)
                  ·
                    rfl

theorem cell20_780147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2].length) (baseStart_780147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780147 prefixEnd_780147 := by exact prefixLift 780147
  have htrace : WordTrace (prefixWord ++ tailWord_780147) baseStart_780147 baseEnd_780147 := by
    simpa [prefixWord, tailWord_780147, baseEnd_780147] using wordTrace_append hprefix tailTrace_780147
  have hstable : (prefixWord ++ tailWord_780147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780147).length < 2 ^ (prefixWord ++ tailWord_780147).sum := by decide
  have hdescent : baseEnd_780147 < baseStart_780147 := by decide
  rcases family_descends (prefixWord ++ tailWord_780147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780223 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 2]
def baseStart_780223 : Nat := 118140960795 + 780223 * 2 ^ 59
def prefixEnd_780223 : Nat := 4983230072969 + 3 ^ 40 * 780223 * 2
def baseEnd_780223 : Nat := 356115037060449873443845

theorem tailTrace_780223 : CollatzResearch.WordTrace tailWord_780223 prefixEnd_780223 356115037060449873443845 := by
  unfold tailWord_780223
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457070652392797324817323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18971380434928531549878215 28457070652392797324817323)
  ·
    refine ⟨42685605978589195987225985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457070652392797324817323 42685605978589195987225985)
    ·
      refine ⟨32014204483941896990419489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42685605978589195987225985 32014204483941896990419489)
      ·
        refine ⟨24010653362956422742814617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32014204483941896990419489 24010653362956422742814617)
        ·
          refine ⟨18007990022217317057110963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24010653362956422742814617 18007990022217317057110963)
          ·
            refine ⟨27011985033325975585666445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007990022217317057110963 27011985033325975585666445)
            ·
              refine ⟨10129494387497240844624917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27011985033325975585666445 10129494387497240844624917)
              ·
                refine ⟨474820049413933164591793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10129494387497240844624917 474820049413933164591793)
                ·
                  refine ⟨356115037060449873443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474820049413933164591793 356115037060449873443845)
                  ·
                    rfl

theorem cell20_780223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2].length) (baseStart_780223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780223 prefixEnd_780223 := by exact prefixLift 780223
  have htrace : WordTrace (prefixWord ++ tailWord_780223) baseStart_780223 baseEnd_780223 := by
    simpa [prefixWord, tailWord_780223, baseEnd_780223] using wordTrace_append hprefix tailTrace_780223
  have hstable : (prefixWord ++ tailWord_780223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780223).length < 2 ^ (prefixWord ++ tailWord_780223).sum := by decide
  have hdescent : baseEnd_780223 < baseStart_780223 := by decide
  rcases family_descends (prefixWord ++ tailWord_780223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780330 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_780330 : Nat := 118140960795 + 780330 * 2 ^ 59
def prefixEnd_780330 : Nat := 4983230072969 + 3 ^ 40 * 780330 * 2
def baseEnd_780330 : Nat := 356163874776033056876741

theorem tailTrace_780330 : CollatzResearch.WordTrace tailWord_780330 prefixEnd_780330 356163874776033056876741 := by
  unfold tailWord_780330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115243315751288649740611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18973982175336769732641629 7115243315751288649740611)
  ·
    refine ⟨10672864973626932974610917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115243315751288649740611 10672864973626932974610917)
    ·
      refine ⟨2001162182555049932739547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10672864973626932974610917 2001162182555049932739547)
      ·
        refine ⟨3001743273832574899109321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001162182555049932739547 3001743273832574899109321)
        ·
          refine ⟨2251307455374431174331991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001743273832574899109321 2251307455374431174331991)
          ·
            refine ⟨3376961183061646761497987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251307455374431174331991 3376961183061646761497987)
            ·
              refine ⟨5065441774592470142246981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376961183061646761497987 5065441774592470142246981)
              ·
                refine ⟨949770332736088151671309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5065441774592470142246981 949770332736088151671309)
                ·
                  refine ⟨356163874776033056876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949770332736088151671309 356163874776033056876741)
                  ·
                    rfl

theorem cell20_780330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_780330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780330 prefixEnd_780330 := by exact prefixLift 780330
  have htrace : WordTrace (prefixWord ++ tailWord_780330) baseStart_780330 baseEnd_780330 := by
    simpa [prefixWord, tailWord_780330, baseEnd_780330] using wordTrace_append hprefix tailTrace_780330
  have hstable : (prefixWord ++ tailWord_780330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780330).length < 2 ^ (prefixWord ++ tailWord_780330).sum := by decide
  have hdescent : baseEnd_780330 < baseStart_780330 := by decide
  rcases family_descends (prefixWord ++ tailWord_780330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780340 : List Nat := [2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_780340 : Nat := 118140960795 + 780340 * 2 ^ 59
def prefixEnd_780340 : Nat := 4983230072969 + 3 ^ 40 * 780340 * 2
def baseEnd_780340 : Nat := 118722813016172488847789

theorem tailTrace_780340 : CollatzResearch.WordTrace tailWord_780340 prefixEnd_780340 118722813016172488847789 := by
  unfold tailWord_780340
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230668996484463153413237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18974225328645950871217649 14230668996484463153413237)
  ·
    refine ⟨1334125218420418420632491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14230668996484463153413237 1334125218420418420632491)
    ·
      refine ⟨2001187827630627630948737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334125218420418420632491 2001187827630627630948737)
      ·
        refine ⟨1500890870722970723211553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001187827630627630948737 1500890870722970723211553)
        ·
          refine ⟨1125668153042228042408665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1500890870722970723211553 1125668153042228042408665)
          ·
            refine ⟨844251114781671031806499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125668153042228042408665 844251114781671031806499)
            ·
              refine ⟨1266376672172506547709749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844251114781671031806499 1266376672172506547709749)
              ·
                refine ⟨118722813016172488847789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266376672172506547709749 118722813016172488847789)
                ·
                  rfl

theorem cell20_780340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_780340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780340 prefixEnd_780340 := by exact prefixLift 780340
  have htrace : WordTrace (prefixWord ++ tailWord_780340) baseStart_780340 baseEnd_780340 := by
    simpa [prefixWord, tailWord_780340, baseEnd_780340] using wordTrace_append hprefix tailTrace_780340
  have hstable : (prefixWord ++ tailWord_780340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780340).length < 2 ^ (prefixWord ++ tailWord_780340).sum := by decide
  have hdescent : baseEnd_780340 < baseStart_780340 := by decide
  rcases family_descends (prefixWord ++ tailWord_780340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780351 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_780351 : Nat := 118140960795 + 780351 * 2 ^ 59
def prefixEnd_780351 : Nat := 4983230072969 + 3 ^ 40 * 780351 * 2
def baseEnd_780351 : Nat := 356173459748250317176655

theorem tailTrace_780351 : CollatzResearch.WordTrace tailWord_780351 prefixEnd_780351 356173459748250317176655 := by
  unfold tailWord_780351
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461739195929075185476907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18974492797286050123651271 28461739195929075185476907)
  ·
    refine ⟨42692608793893612778215361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28461739195929075185476907 42692608793893612778215361)
    ·
      refine ⟨32019456595420209583661521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42692608793893612778215361 32019456595420209583661521)
      ·
        refine ⟨24014592446565157187746141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32019456595420209583661521 24014592446565157187746141)
        ·
          refine ⟨9005472167461933945404803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24014592446565157187746141 9005472167461933945404803)
          ·
            refine ⟨13508208251192900918107205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005472167461933945404803 13508208251192900918107205)
            ·
              refine ⟨2532789047098668922145101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13508208251192900918107205 2532789047098668922145101)
              ·
                refine ⟨949795892662000845804413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2532789047098668922145101 949795892662000845804413)
                ·
                  refine ⟨356173459748250317176655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949795892662000845804413 356173459748250317176655)
                  ·
                    rfl

theorem cell20_780351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_780351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780351 prefixEnd_780351 := by exact prefixLift 780351
  have htrace : WordTrace (prefixWord ++ tailWord_780351) baseStart_780351 baseEnd_780351 := by
    simpa [prefixWord, tailWord_780351, baseEnd_780351] using wordTrace_append hprefix tailTrace_780351
  have hstable : (prefixWord ++ tailWord_780351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780351).length < 2 ^ (prefixWord ++ tailWord_780351).sum := by decide
  have hdescent : baseEnd_780351 < baseStart_780351 := by decide
  rcases family_descends (prefixWord ++ tailWord_780351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780375 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 2]
def baseStart_780375 : Nat := 118140960795 + 780375 * 2 ^ 59
def prefixEnd_780375 : Nat := 4983230072969 + 3 ^ 40 * 780375 * 2
def baseEnd_780375 : Nat := 356184414002212900376557

theorem tailTrace_780375 : CollatzResearch.WordTrace tailWord_780375 prefixEnd_780375 356184414002212900376557 := by
  unfold tailWord_780375
  simp only [CollatzResearch.WordTrace]
  refine ⟨28462614547842127284350579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18975076365228084856233719 28462614547842127284350579)
  ·
    refine ⟨42693921821763190926525869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28462614547842127284350579 42693921821763190926525869)
    ·
      refine ⟨16010220683161196597447201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42693921821763190926525869 16010220683161196597447201)
      ·
        refine ⟨12007665512370897448085401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16010220683161196597447201 12007665512370897448085401)
        ·
          refine ⟨9005749134278173086064051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12007665512370897448085401 9005749134278173086064051)
          ·
            refine ⟨13508623701417259629096077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005749134278173086064051 13508623701417259629096077)
            ·
              refine ⟨5065733888031472360911029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13508623701417259629096077 5065733888031472360911029)
              ·
                refine ⟨474912552002950533835409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5065733888031472360911029 474912552002950533835409)
                ·
                  refine ⟨356184414002212900376557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474912552002950533835409 356184414002212900376557)
                  ·
                    rfl

theorem cell20_780375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2].length) (baseStart_780375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780375 prefixEnd_780375 := by exact prefixLift 780375
  have htrace : WordTrace (prefixWord ++ tailWord_780375) baseStart_780375 baseEnd_780375 := by
    simpa [prefixWord, tailWord_780375, baseEnd_780375] using wordTrace_append hprefix tailTrace_780375
  have hstable : (prefixWord ++ tailWord_780375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780375).length < 2 ^ (prefixWord ++ tailWord_780375).sum := by decide
  have hdescent : baseEnd_780375 < baseStart_780375 := by decide
  rcases family_descends (prefixWord ++ tailWord_780375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780389 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_780389 : Nat := 118140960795 + 780389 * 2 ^ 59
def prefixEnd_780389 : Nat := 4983230072969 + 3 ^ 40 * 780389 * 2
def baseEnd_780389 : Nat := 356190803983691073909833

theorem tailTrace_780389 : CollatzResearch.WordTrace tailWord_780389 prefixEnd_780389 356190803983691073909833 := by
  unfold tailWord_780389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28463125169791407675360221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18975416779860938450240147 28463125169791407675360221)
  ·
    refine ⟨10673671938671777878260083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28463125169791407675360221 10673671938671777878260083)
    ·
      refine ⟨16010507908007666817390125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673671938671777878260083 16010507908007666817390125)
      ·
        refine ⟨6003940465502875056521297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16010507908007666817390125 6003940465502875056521297)
        ·
          refine ⟨4502955349127156292390973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6003940465502875056521297 4502955349127156292390973)
          ·
            refine ⟨1688608255922683609646615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4502955349127156292390973 1688608255922683609646615)
            ·
              refine ⟨2532912383884025414469923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688608255922683609646615 2532912383884025414469923)
              ·
                refine ⟨3799368575826038121704885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532912383884025414469923 3799368575826038121704885)
                ·
                  refine ⟨356190803983691073909833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799368575826038121704885 356190803983691073909833)
                  ·
                    rfl

theorem cell20_780389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_780389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780389 prefixEnd_780389 := by exact prefixLift 780389
  have htrace : WordTrace (prefixWord ++ tailWord_780389) baseStart_780389 baseEnd_780389 := by
    simpa [prefixWord, tailWord_780389, baseEnd_780389] using wordTrace_append hprefix tailTrace_780389
  have hstable : (prefixWord ++ tailWord_780389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780389).length < 2 ^ (prefixWord ++ tailWord_780389).sum := by decide
  have hdescent : baseEnd_780389 < baseStart_780389 := by decide
  rcases family_descends (prefixWord ++ tailWord_780389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780396 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_780396 : Nat := 118140960795 + 780396 * 2 ^ 59
def prefixEnd_780396 : Nat := 4983230072969 + 3 ^ 40 * 780396 * 2
def baseEnd_780396 : Nat := 356193998974430160676471

theorem tailTrace_780396 : CollatzResearch.WordTrace tailWord_780396 prefixEnd_780396 356193998974430160676471 := by
  unfold tailWord_780396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231690240383023935432521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18975586987177365247243361 14231690240383023935432521)
  ·
    refine ⟨10673767680287267951574391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14231690240383023935432521 10673767680287267951574391)
    ·
      refine ⟨16010651520430901927361587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673767680287267951574391 16010651520430901927361587)
      ·
        refine ⟨24015977280646352891042381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16010651520430901927361587 24015977280646352891042381)
        ·
          refine ⟨9005991480242382334140893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24015977280646352891042381 9005991480242382334140893)
          ·
            refine ⟨3377246805090893375302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9005991480242382334140893 3377246805090893375302835)
            ·
              refine ⟨5065870207636340062954253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377246805090893375302835 5065870207636340062954253)
              ·
                refine ⟨1899701327863627523607845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5065870207636340062954253 1899701327863627523607845)
                ·
                  refine ⟨356193998974430160676471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899701327863627523607845 356193998974430160676471)
                  ·
                    rfl

theorem cell20_780396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_780396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780396 prefixEnd_780396 := by exact prefixLift 780396
  have htrace : WordTrace (prefixWord ++ tailWord_780396) baseStart_780396 baseEnd_780396 := by
    simpa [prefixWord, tailWord_780396, baseEnd_780396] using wordTrace_append hprefix tailTrace_780396
  have hstable : (prefixWord ++ tailWord_780396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780396).length < 2 ^ (prefixWord ++ tailWord_780396).sum := by decide
  have hdescent : baseEnd_780396 < baseStart_780396 := by decide
  rcases family_descends (prefixWord ++ tailWord_780396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780447 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 2]
def baseStart_780447 : Nat := 118140960795 + 780447 * 2 ^ 59
def prefixEnd_780447 : Nat := 4983230072969 + 3 ^ 40 * 780447 * 2
def baseEnd_780447 : Nat := 356217276764100649976263

theorem tailTrace_780447 : CollatzResearch.WordTrace tailWord_780447 prefixEnd_780447 356217276764100649976263 := by
  unfold tailWord_780447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28465240603581283580971595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18976827069054189053981063 28465240603581283580971595)
  ·
    refine ⟨42697860905371925371457393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28465240603581283580971595 42697860905371925371457393)
    ·
      refine ⟨32023395679028944028593045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42697860905371925371457393 32023395679028944028593045)
      ·
        refine ⟨1501096672454481751340299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32023395679028944028593045 1501096672454481751340299)
        ·
          refine ⟨2251645008681722627010449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501096672454481751340299 2251645008681722627010449)
          ·
            refine ⟨1688733756511291970257837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2251645008681722627010449 1688733756511291970257837)
            ·
              refine ⟨633275158691734488846689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1688733756511291970257837 633275158691734488846689)
              ·
                refine ⟨474956369018800866635017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633275158691734488846689 474956369018800866635017)
                ·
                  refine ⟨356217276764100649976263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474956369018800866635017 356217276764100649976263)
                  ·
                    rfl

theorem cell20_780447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2].length) (baseStart_780447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780447 prefixEnd_780447 := by exact prefixLift 780447
  have htrace : WordTrace (prefixWord ++ tailWord_780447) baseStart_780447 baseEnd_780447 := by
    simpa [prefixWord, tailWord_780447, baseEnd_780447] using wordTrace_append hprefix tailTrace_780447
  have hstable : (prefixWord ++ tailWord_780447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780447).length < 2 ^ (prefixWord ++ tailWord_780447).sum := by decide
  have hdescent : baseEnd_780447 < baseStart_780447 := by decide
  rcases family_descends (prefixWord ++ tailWord_780447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780461 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_780461 : Nat := 118140960795 + 780461 * 2 ^ 59
def prefixEnd_780461 : Nat := 4983230072969 + 3 ^ 40 * 780461 * 2
def baseEnd_780461 : Nat := 356223666745578823509539

theorem tailTrace_780461 : CollatzResearch.WordTrace tailWord_780461 prefixEnd_780461 356223666745578823509539 := by
  unfold tailWord_780461
  simp only [CollatzResearch.WordTrace]
  refine ⟨28465751225530563971981237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18977167483687042647987491 28465751225530563971981237)
  ·
    refine ⟨2668664177393490372373241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28465751225530563971981237 2668664177393490372373241)
    ·
      refine ⟨2001498133045117779279931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2668664177393490372373241 2001498133045117779279931)
      ·
        refine ⟨3002247199567676668919897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001498133045117779279931 3002247199567676668919897)
        ·
          refine ⟨2251685399675757501689923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002247199567676668919897 2251685399675757501689923)
          ·
            refine ⟨3377528099513636252534885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251685399675757501689923 3377528099513636252534885)
            ·
              refine ⟨633286518658806797350291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3377528099513636252534885 633286518658806797350291)
              ·
                refine ⟨949929777988210196025437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633286518658806797350291 949929777988210196025437)
                ·
                  refine ⟨356223666745578823509539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949929777988210196025437 356223666745578823509539)
                  ·
                    rfl

theorem cell20_780461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_780461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780461 prefixEnd_780461 := by exact prefixLift 780461
  have htrace : WordTrace (prefixWord ++ tailWord_780461) baseStart_780461 baseEnd_780461 := by
    simpa [prefixWord, tailWord_780461, baseEnd_780461] using wordTrace_append hprefix tailTrace_780461
  have hstable : (prefixWord ++ tailWord_780461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780461).length < 2 ^ (prefixWord ++ tailWord_780461).sum := by decide
  have hdescent : baseEnd_780461 < baseStart_780461 := by decide
  rcases family_descends (prefixWord ++ tailWord_780461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780502 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_780502 : Nat := 118140960795 + 780502 * 2 ^ 59
def prefixEnd_780502 : Nat := 4983230072969 + 3 ^ 40 * 780502 * 2
def baseEnd_780502 : Nat := 356242380262764903142705

theorem tailTrace_780502 : CollatzResearch.WordTrace tailWord_780502 prefixEnd_780502 356242380262764903142705 := by
  unfold tailWord_780502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779202913648876748388985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18978164412254685316149173 1779202913648876748388985)
  ·
    refine ⟨1334402185236657561291739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1779202913648876748388985 1334402185236657561291739)
    ·
      refine ⟨2001603277854986341937609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334402185236657561291739 2001603277854986341937609)
      ·
        refine ⟨1501202458391239756453207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001603277854986341937609 1501202458391239756453207)
        ·
          refine ⟨2251803687586859634679811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501202458391239756453207 2251803687586859634679811)
          ·
            refine ⟨3377705531380289452019717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251803687586859634679811 3377705531380289452019717)
            ·
              refine ⟨633319787133804272253697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3377705531380289452019717 633319787133804272253697)
              ·
                refine ⟨474989840350353204190273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633319787133804272253697 474989840350353204190273)
                ·
                  refine ⟨356242380262764903142705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474989840350353204190273 356242380262764903142705)
                  ·
                    rfl

theorem cell20_780502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_780502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780502 prefixEnd_780502 := by exact prefixLift 780502
  have htrace : WordTrace (prefixWord ++ tailWord_780502) baseStart_780502 baseEnd_780502 := by
    simpa [prefixWord, tailWord_780502, baseEnd_780502] using wordTrace_append hprefix tailTrace_780502
  have hstable : (prefixWord ++ tailWord_780502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780502).length < 2 ^ (prefixWord ++ tailWord_780502).sum := by decide
  have hdescent : baseEnd_780502 < baseStart_780502 := by decide
  rcases family_descends (prefixWord ++ tailWord_780502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780506 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_780506 : Nat := 118140960795 + 780506 * 2 ^ 59
def prefixEnd_780506 : Nat := 4983230072969 + 3 ^ 40 * 780506 * 2
def baseEnd_780506 : Nat := 356244205971758667009355

theorem tailTrace_780506 : CollatzResearch.WordTrace tailWord_780506 prefixEnd_780506 356244205971758667009355 := by
  unfold tailWord_780506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116848127591884164342343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18978261673578357771579581 7116848127591884164342343)
  ·
    refine ⟨10675272191387826246513515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116848127591884164342343 10675272191387826246513515)
    ·
      refine ⟨16012908287081739369770273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10675272191387826246513515 16012908287081739369770273)
      ·
        refine ⟨12009681215311304527327705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16012908287081739369770273 12009681215311304527327705)
        ·
          refine ⟨9007260911483478395495779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12009681215311304527327705 9007260911483478395495779)
          ·
            refine ⟨13510891367225217593243669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007260911483478395495779 13510891367225217593243669)
            ·
              refine ⟨633323032838682074683297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13510891367225217593243669 633323032838682074683297)
              ·
                refine ⟨474992274629011556012473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633323032838682074683297 474992274629011556012473)
                ·
                  refine ⟨356244205971758667009355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474992274629011556012473 356244205971758667009355)
                  ·
                    rfl

theorem cell20_780506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_780506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780506 prefixEnd_780506 := by exact prefixLift 780506
  have htrace : WordTrace (prefixWord ++ tailWord_780506) baseStart_780506 baseEnd_780506 := by
    simpa [prefixWord, tailWord_780506, baseEnd_780506] using wordTrace_append hprefix tailTrace_780506
  have hstable : (prefixWord ++ tailWord_780506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780506).length < 2 ^ (prefixWord ++ tailWord_780506).sum := by decide
  have hdescent : baseEnd_780506 < baseStart_780506 := by decide
  rcases family_descends (prefixWord ++ tailWord_780506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780565 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 2]
def baseStart_780565 : Nat := 118140960795 + 780565 * 2 ^ 59
def prefixEnd_780565 : Nat := 4983230072969 + 3 ^ 40 * 780565 * 2
def baseEnd_780565 : Nat := 356271135179416684042447

theorem tailTrace_780565 : CollatzResearch.WordTrace tailWord_780565 prefixEnd_780565 356271135179416684042447 := by
  unfold tailWord_780565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469544417153789733767149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18979696278102526489178099 28469544417153789733767149)
  ·
    refine ⟨10676079156432671150162681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28469544417153789733767149 10676079156432671150162681)
    ·
      refine ⟨8007059367324503362622011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10676079156432671150162681 8007059367324503362622011)
      ·
        refine ⟨12010589050986755043933017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007059367324503362622011 12010589050986755043933017)
        ·
          refine ⟨9007941788240066282949763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12010589050986755043933017 9007941788240066282949763)
          ·
            refine ⟨13511912682360099424424645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007941788240066282949763 13511912682360099424424645)
            ·
              refine ⟨2533483627942518642079621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13511912682360099424424645 2533483627942518642079621)
              ·
                refine ⟨475028180239222245389929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2533483627942518642079621 475028180239222245389929)
                ·
                  refine ⟨356271135179416684042447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475028180239222245389929 356271135179416684042447)
                  ·
                    rfl

theorem cell20_780565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_780565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780565 prefixEnd_780565 := by exact prefixLift 780565
  have htrace : WordTrace (prefixWord ++ tailWord_780565) baseStart_780565 baseEnd_780565 := by
    simpa [prefixWord, tailWord_780565, baseEnd_780565] using wordTrace_append hprefix tailTrace_780565
  have hstable : (prefixWord ++ tailWord_780565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780565).length < 2 ^ (prefixWord ++ tailWord_780565).sum := by decide
  have hdescent : baseEnd_780565 < baseStart_780565 := by decide
  rcases family_descends (prefixWord ++ tailWord_780565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780589 : List Nat := [1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_780589 : Nat := 118140960795 + 780589 * 2 ^ 59
def prefixEnd_780589 : Nat := 4983230072969 + 3 ^ 40 * 780589 * 2
def baseEnd_780589 : Nat := 118760696477793089080783

theorem tailTrace_780589 : CollatzResearch.WordTrace tailWord_780589 prefixEnd_780589 118760696477793089080783 := by
  unfold tailWord_780589
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470419769066841832640821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18980279846044561221760547 28470419769066841832640821)
  ·
    refine ⟨2669101853350016421810077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28470419769066841832640821 2669101853350016421810077)
    ·
      refine ⟨1000913195006256158178779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2669101853350016421810077 1000913195006256158178779)
      ·
        refine ⟨1501369792509384237268169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000913195006256158178779 1501369792509384237268169)
        ·
          refine ⟨1126027344382038177951127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1501369792509384237268169 1126027344382038177951127)
          ·
            refine ⟨1689041016573057266926691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126027344382038177951127 1689041016573057266926691)
            ·
              refine ⟨2533561524859585900390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689041016573057266926691 2533561524859585900390037)
              ·
                refine ⟨118760696477793089080783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2533561524859585900390037 118760696477793089080783)
                ·
                  rfl

theorem cell20_780589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_780589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780589 prefixEnd_780589 := by exact prefixLift 780589
  have htrace : WordTrace (prefixWord ++ tailWord_780589) baseStart_780589 baseEnd_780589 := by
    simpa [prefixWord, tailWord_780589, baseEnd_780589] using wordTrace_append hprefix tailTrace_780589
  have hstable : (prefixWord ++ tailWord_780589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780589).length < 2 ^ (prefixWord ++ tailWord_780589).sum := by decide
  have hdescent : baseEnd_780589 < baseStart_780589 := by decide
  rcases family_descends (prefixWord ++ tailWord_780589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780600 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_780600 : Nat := 118140960795 + 780600 * 2 ^ 59
def prefixEnd_780600 : Nat := 4983230072969 + 3 ^ 40 * 780600 * 2
def baseEnd_780600 : Nat := 356287110133112117875637

theorem tailTrace_780600 : CollatzResearch.WordTrace tailWord_780600 prefixEnd_780600 356287110133112117875637 := by
  unfold tailWord_780600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235410486013495355645627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18980547314684660474194169 14235410486013495355645627)
  ·
    refine ⟨21353115729020243033468441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14235410486013495355645627 21353115729020243033468441)
    ·
      refine ⟨16014836796765182275101331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21353115729020243033468441 16014836796765182275101331)
      ·
        refine ⟨24022255195147773412651997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014836796765182275101331 24022255195147773412651997)
        ·
          refine ⟨9008345698180415029744499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24022255195147773412651997 9008345698180415029744499)
          ·
            refine ⟨13512518547270622544616749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008345698180415029744499 13512518547270622544616749)
            ·
              refine ⟨5067194455226483454231281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13512518547270622544616749 5067194455226483454231281)
              ·
                refine ⟨3800395841419862590673461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5067194455226483454231281 3800395841419862590673461)
                ·
                  refine ⟨356287110133112117875637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800395841419862590673461 356287110133112117875637)
                  ·
                    rfl

theorem cell20_780600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_780600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780600 prefixEnd_780600 := by exact prefixLift 780600
  have htrace : WordTrace (prefixWord ++ tailWord_780600) baseStart_780600 baseEnd_780600 := by
    simpa [prefixWord, tailWord_780600, baseEnd_780600] using wordTrace_append hprefix tailTrace_780600
  have hstable : (prefixWord ++ tailWord_780600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780600).length < 2 ^ (prefixWord ++ tailWord_780600).sum := by decide
  have hdescent : baseEnd_780600 < baseStart_780600 := by decide
  rcases family_descends (prefixWord ++ tailWord_780600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780620 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_780620 : Nat := 118140960795 + 780620 * 2 ^ 59
def prefixEnd_780620 : Nat := 4983230072969 + 3 ^ 40 * 780620 * 2
def baseEnd_780620 : Nat := 356296238678080937208889

theorem tailTrace_780620 : CollatzResearch.WordTrace tailWord_780620 prefixEnd_780620 356296238678080937208889 := by
  unfold tailWord_780620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235775215977267063509657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18981033621303022751346209 14235775215977267063509657)
  ·
    refine ⟨10676831411982950297632243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14235775215977267063509657 10676831411982950297632243)
    ·
      refine ⟨16015247117974425446448365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10676831411982950297632243 16015247117974425446448365)
      ·
        refine ⟨6005717669240409542418137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16015247117974425446448365 6005717669240409542418137)
        ·
          refine ⟨4504288251930307156813603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005717669240409542418137 4504288251930307156813603)
          ·
            refine ⟨6756432377895460735220405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504288251930307156813603 6756432377895460735220405)
            ·
              refine ⟨633415535427699443926913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6756432377895460735220405 633415535427699443926913)
              ·
                refine ⟨475061651570774582945185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633415535427699443926913 475061651570774582945185)
                ·
                  refine ⟨356296238678080937208889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475061651570774582945185 356296238678080937208889)
                  ·
                    rfl

theorem cell20_780620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_780620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780620 prefixEnd_780620 := by exact prefixLift 780620
  have htrace : WordTrace (prefixWord ++ tailWord_780620) baseStart_780620 baseEnd_780620 := by
    simpa [prefixWord, tailWord_780620, baseEnd_780620] using wordTrace_append hprefix tailTrace_780620
  have hstable : (prefixWord ++ tailWord_780620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780620).length < 2 ^ (prefixWord ++ tailWord_780620).sum := by decide
  have hdescent : baseEnd_780620 < baseStart_780620 := by decide
  rcases family_descends (prefixWord ++ tailWord_780620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780624 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_780624 : Nat := 118140960795 + 780624 * 2 ^ 59
def prefixEnd_780624 : Nat := 4983230072969 + 3 ^ 40 * 780624 * 2
def baseEnd_780624 : Nat := 356298064387074701075539

theorem tailTrace_780624 : CollatzResearch.WordTrace tailWord_780624 prefixEnd_780624 356298064387074701075539 := by
  unfold tailWord_780624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235848161970021405082463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18981130882626695206776617 14235848161970021405082463)
  ·
    refine ⟨21353772242955032107623695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14235848161970021405082463 21353772242955032107623695)
    ·
      refine ⟨32030658364432548161435543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21353772242955032107623695 32030658364432548161435543)
      ·
        refine ⟨48045987546648822242153315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32030658364432548161435543 48045987546648822242153315)
        ·
          refine ⟨72068981319973233363229973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48045987546648822242153315 72068981319973233363229973)
          ·
            refine ⟨3378233499373745313901405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72068981319973233363229973 3378233499373745313901405)
            ·
              refine ⟨1266837562265154492713027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378233499373745313901405 1266837562265154492713027)
              ·
                refine ⟨1900256343397731739069541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266837562265154492713027 1900256343397731739069541)
                ·
                  refine ⟨356298064387074701075539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900256343397731739069541 356298064387074701075539)
                  ·
                    rfl

theorem cell20_780624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_780624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780624 prefixEnd_780624 := by exact prefixLift 780624
  have htrace : WordTrace (prefixWord ++ tailWord_780624) baseStart_780624 baseEnd_780624 := by
    simpa [prefixWord, tailWord_780624, baseEnd_780624] using wordTrace_append hprefix tailTrace_780624
  have hstable : (prefixWord ++ tailWord_780624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780624).length < 2 ^ (prefixWord ++ tailWord_780624).sum := by decide
  have hdescent : baseEnd_780624 < baseStart_780624 := by decide
  rcases family_descends (prefixWord ++ tailWord_780624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780631 : List Nat := [1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_780631 : Nat := 118140960795 + 780631 * 2 ^ 59
def prefixEnd_780631 : Nat := 4983230072969 + 3 ^ 40 * 780631 * 2
def baseEnd_780631 : Nat := 118767086459271262614059

theorem tailTrace_780631 : CollatzResearch.WordTrace tailWord_780631 prefixEnd_780631 118767086459271262614059 := by
  unfold tailWord_780631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471951634914683005669747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18981301089943122003779831 28471951634914683005669747)
  ·
    refine ⟨42707927452372024508504621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28471951634914683005669747 42707927452372024508504621)
    ·
      refine ⟨16015472794639509190689233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42707927452372024508504621 16015472794639509190689233)
      ·
        refine ⟨12011604595979631893016925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015472794639509190689233 12011604595979631893016925)
        ·
          refine ⟨4504351723492361959881347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12011604595979631893016925 4504351723492361959881347)
          ·
            refine ⟨6756527585238542939822021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504351723492361959881347 6756527585238542939822021)
            ·
              refine ⟨1266848922232226801216629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6756527585238542939822021 1266848922232226801216629)
              ·
                refine ⟨118767086459271262614059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266848922232226801216629 118767086459271262614059)
                ·
                  rfl

theorem cell20_780631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_780631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780631 prefixEnd_780631 := by exact prefixLift 780631
  have htrace : WordTrace (prefixWord ++ tailWord_780631) baseStart_780631 baseEnd_780631 := by
    simpa [prefixWord, tailWord_780631, baseEnd_780631] using wordTrace_append hprefix tailTrace_780631
  have hstable : (prefixWord ++ tailWord_780631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780631).length < 2 ^ (prefixWord ++ tailWord_780631).sum := by decide
  have hdescent : baseEnd_780631 < baseStart_780631 := by decide
  rcases family_descends (prefixWord ++ tailWord_780631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780675 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 2]
def baseStart_780675 : Nat := 118140960795 + 780675 * 2 ^ 59
def prefixEnd_780675 : Nat := 4983230072969 + 3 ^ 40 * 780675 * 2
def baseEnd_780675 : Nat := 356321342176745190375331

theorem tailTrace_780675 : CollatzResearch.WordTrace tailWord_780675 prefixEnd_780675 356321342176745190375331 := by
  unfold tailWord_780675
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473556446755278520271479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18982370964503519013514319 28473556446755278520271479)
  ·
    refine ⟨42710334670132917780407219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28473556446755278520271479 42710334670132917780407219)
    ·
      refine ⟨64065502005199376670610829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42710334670132917780407219 64065502005199376670610829)
      ·
        refine ⟨24024563251949766251479061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64065502005199376670610829 24024563251949766251479061)
        ·
          refine ⟨1126151402435145293038081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24024563251949766251479061 1126151402435145293038081)
          ·
            refine ⟨844613551826358969778561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126151402435145293038081 844613551826358969778561)
            ·
              refine ⟨633460163869769227333921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844613551826358969778561 633460163869769227333921)
              ·
                refine ⟨475095122902326920500441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633460163869769227333921 475095122902326920500441)
                ·
                  refine ⟨356321342176745190375331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475095122902326920500441 356321342176745190375331)
                  ·
                    rfl

theorem cell20_780675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2].length) (baseStart_780675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780675 prefixEnd_780675 := by exact prefixLift 780675
  have htrace : WordTrace (prefixWord ++ tailWord_780675) baseStart_780675 baseEnd_780675 := by
    simpa [prefixWord, tailWord_780675, baseEnd_780675] using wordTrace_append hprefix tailTrace_780675
  have hstable : (prefixWord ++ tailWord_780675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780675).length < 2 ^ (prefixWord ++ tailWord_780675).sum := by decide
  have hdescent : baseEnd_780675 < baseStart_780675 := by decide
  rcases family_descends (prefixWord ++ tailWord_780675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780679 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 2]
def baseStart_780679 : Nat := 118140960795 + 780679 * 2 ^ 59
def prefixEnd_780679 : Nat := 4983230072969 + 3 ^ 40 * 780679 * 2
def baseEnd_780679 : Nat := 356323167885738954241981

theorem tailTrace_780679 : CollatzResearch.WordTrace tailWord_780679 prefixEnd_780679 356323167885738954241981 := by
  unfold tailWord_780679
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473702338740787203417091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18982468225827191468944727 28473702338740787203417091)
  ·
    refine ⟨42710553508111180805125637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28473702338740787203417091 42710553508111180805125637)
    ·
      refine ⟨8008228782770846400961057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42710553508111180805125637 8008228782770846400961057)
      ·
        refine ⟨6006171587078134800720793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008228782770846400961057 6006171587078134800720793)
        ·
          refine ⟨4504628690308601100540595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006171587078134800720793 4504628690308601100540595)
          ·
            refine ⟨6756943035462901650810893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504628690308601100540595 6756943035462901650810893)
            ·
              refine ⟨2533853638298588119054085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6756943035462901650810893 2533853638298588119054085)
              ·
                refine ⟨475097557180985272322641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2533853638298588119054085 475097557180985272322641)
                ·
                  refine ⟨356323167885738954241981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475097557180985272322641 356323167885738954241981)
                  ·
                    rfl

theorem cell20_780679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2].length) (baseStart_780679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780679 prefixEnd_780679 := by exact prefixLift 780679
  have htrace : WordTrace (prefixWord ++ tailWord_780679) baseStart_780679 baseEnd_780679 := by
    simpa [prefixWord, tailWord_780679, baseEnd_780679] using wordTrace_append hprefix tailTrace_780679
  have hstable : (prefixWord ++ tailWord_780679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780679).length < 2 ^ (prefixWord ++ tailWord_780679).sum := by decide
  have hdescent : baseEnd_780679 < baseStart_780679 := by decide
  rcases family_descends (prefixWord ++ tailWord_780679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780682 : List Nat := [3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_780682 : Nat := 118140960795 + 780682 * 2 ^ 59
def prefixEnd_780682 : Nat := 4983230072969 + 3 ^ 40 * 780682 * 2
def baseEnd_780682 : Nat := 118774845722494759047323

theorem tailTrace_780682 : CollatzResearch.WordTrace tailWord_780682 prefixEnd_780682 118774845722494759047323 := by
  unfold tailWord_780682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118452939432479678944075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18982541171819945810517533 7118452939432479678944075)
  ·
    refine ⟨10677679409148719518416113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7118452939432479678944075 10677679409148719518416113)
    ·
      refine ⟨8008259556861539638812085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10677679409148719518416113 8008259556861539638812085)
      ·
        refine ⟨750774333455769341138633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8008259556861539638812085 750774333455769341138633)
        ·
          refine ⟨563080750091827005853975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750774333455769341138633 563080750091827005853975)
          ·
            refine ⟨844621125137740508780963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563080750091827005853975 844621125137740508780963)
            ·
              refine ⟨1266931687706610763171445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844621125137740508780963 1266931687706610763171445)
              ·
                refine ⟨118774845722494759047323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266931687706610763171445 118774845722494759047323)
                ·
                  rfl

theorem cell20_780682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_780682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780682 prefixEnd_780682 := by exact prefixLift 780682
  have htrace : WordTrace (prefixWord ++ tailWord_780682) baseStart_780682 baseEnd_780682 := by
    simpa [prefixWord, tailWord_780682, baseEnd_780682] using wordTrace_append hprefix tailTrace_780682
  have hstable : (prefixWord ++ tailWord_780682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780682).length < 2 ^ (prefixWord ++ tailWord_780682).sum := by decide
  have hdescent : baseEnd_780682 < baseStart_780682 := by decide
  rcases family_descends (prefixWord ++ tailWord_780682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780686 : List Nat := [4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_780686 : Nat := 118140960795 + 780686 * 2 ^ 59
def prefixEnd_780686 : Nat := 4983230072969 + 3 ^ 40 * 780686 * 2
def baseEnd_780686 : Nat := 118775454292159347002873

theorem tailTrace_780686 : CollatzResearch.WordTrace tailWord_780686 prefixEnd_780686 118775454292159347002873 := by
  unfold tailWord_780686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559244706214428424865239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18982638433143618265947941 3559244706214428424865239)
  ·
    refine ⟨5338867059321642637297859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3559244706214428424865239 5338867059321642637297859)
    ·
      refine ⟨8008300588982463955946789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338867059321642637297859 8008300588982463955946789)
      ·
        refine ⟨1501556360434211991740023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8008300588982463955946789 1501556360434211991740023)
        ·
          refine ⟨2252334540651317987610035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501556360434211991740023 2252334540651317987610035)
          ·
            refine ⟨3378501810976976981415053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252334540651317987610035 3378501810976976981415053)
            ·
              refine ⟨1266938179116366368030645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378501810976976981415053 1266938179116366368030645)
              ·
                refine ⟨118775454292159347002873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266938179116366368030645 118775454292159347002873)
                ·
                  rfl

theorem cell20_780686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_780686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780686 prefixEnd_780686 := by exact prefixLift 780686
  have htrace : WordTrace (prefixWord ++ tailWord_780686) baseStart_780686 baseEnd_780686 := by
    simpa [prefixWord, tailWord_780686, baseEnd_780686] using wordTrace_append hprefix tailTrace_780686
  have hstable : (prefixWord ++ tailWord_780686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780686).length < 2 ^ (prefixWord ++ tailWord_780686).sum := by decide
  have hdescent : baseEnd_780686 < baseStart_780686 := by decide
  rcases family_descends (prefixWord ++ tailWord_780686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780789 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 4]
def baseStart_780789 : Nat := 118140960795 + 780789 * 2 ^ 59
def prefixEnd_780789 : Nat := 4983230072969 + 3 ^ 40 * 780789 * 2
def baseEnd_780789 : Nat := 356373374883067460574865

theorem tailTrace_780789 : CollatzResearch.WordTrace tailWord_780789 prefixEnd_780789 356373374883067460574865 := by
  unfold tailWord_780789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28477714368342275989921421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18985142912228183993280947 28477714368342275989921421)
  ·
    refine ⟨10679142888128353496220533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28477714368342275989921421 10679142888128353496220533)
    ·
      refine ⟨1001169645762033140270675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10679142888128353496220533 1001169645762033140270675)
      ·
        refine ⟨1501754468643049710406013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001169645762033140270675 1501754468643049710406013)
        ·
          refine ⟨563157925741143641402255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1501754468643049710406013 563157925741143641402255)
          ·
            refine ⟨844736888611715462103383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563157925741143641402255 844736888611715462103383)
            ·
              refine ⟨1267105332917573193155075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844736888611715462103383 1267105332917573193155075)
              ·
                refine ⟨1900657999376359789732613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267105332917573193155075 1900657999376359789732613)
                ·
                  refine ⟨356373374883067460574865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900657999376359789732613 356373374883067460574865)
                  ·
                    rfl

theorem cell20_780789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_780789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780789 prefixEnd_780789 := by exact prefixLift 780789
  have htrace : WordTrace (prefixWord ++ tailWord_780789) baseStart_780789 baseEnd_780789 := by
    simpa [prefixWord, tailWord_780789, baseEnd_780789] using wordTrace_append hprefix tailTrace_780789
  have hstable : (prefixWord ++ tailWord_780789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780789).length < 2 ^ (prefixWord ++ tailWord_780789).sum := by decide
  have hdescent : baseEnd_780789 < baseStart_780789 := by decide
  rcases family_descends (prefixWord ++ tailWord_780789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780911 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_780911 : Nat := 118140960795 + 780911 * 2 ^ 59
def prefixEnd_780911 : Nat := 4983230072969 + 3 ^ 40 * 780911 * 2
def baseEnd_780911 : Nat := 356429059007377258507699

theorem tailTrace_780911 : CollatzResearch.WordTrace tailWord_780911 prefixEnd_780911 356429059007377258507699 := by
  unfold tailWord_780911
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482164073900290825862587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988109382600193883908391 28482164073900290825862587)
  ·
    refine ⟨42723246110850436238793881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28482164073900290825862587 42723246110850436238793881)
    ·
      refine ⟨32042434583137827179095411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42723246110850436238793881 32042434583137827179095411)
      ·
        refine ⟨48063651874706740768643117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32042434583137827179095411 48063651874706740768643117)
        ·
          refine ⟨18023869453015027788241169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48063651874706740768643117 18023869453015027788241169)
          ·
            refine ⟨13517902089761270841180877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18023869453015027788241169 13517902089761270841180877)
            ·
              refine ⟨5069213283660476565442829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13517902089761270841180877 5069213283660476565442829)
              ·
                refine ⟨1900954981372678712041061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069213283660476565442829 1900954981372678712041061)
                ·
                  refine ⟨356429059007377258507699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900954981372678712041061 356429059007377258507699)
                  ·
                    rfl

theorem cell20_780911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_780911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780911 prefixEnd_780911 := by exact prefixLift 780911
  have htrace : WordTrace (prefixWord ++ tailWord_780911) baseStart_780911 baseEnd_780911 := by
    simpa [prefixWord, tailWord_780911, baseEnd_780911] using wordTrace_append hprefix tailTrace_780911
  have hstable : (prefixWord ++ tailWord_780911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780911).length < 2 ^ (prefixWord ++ tailWord_780911).sum := by decide
  have hdescent : baseEnd_780911 < baseStart_780911 := by decide
  rcases family_descends (prefixWord ++ tailWord_780911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780917 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_780917 : Nat := 118140960795 + 780917 * 2 ^ 59
def prefixEnd_780917 : Nat := 4983230072969 + 3 ^ 40 * 780917 * 2
def baseEnd_780917 : Nat := 356431797570867904307675

theorem tailTrace_780917 : CollatzResearch.WordTrace tailWord_780917 prefixEnd_780917 356431797570867904307675 := by
  unfold tailWord_780917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482382911878553850581005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988255274585702567054003 28482382911878553850581005)
  ·
    refine ⟨10680893591954457693967877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28482382911878553850581005 10680893591954457693967877)
    ·
      refine ⟨2002667548491460817618977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10680893591954457693967877 2002667548491460817618977)
      ·
        refine ⟨1502000661368595613214233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2002667548491460817618977 1502000661368595613214233)
        ·
          refine ⟨1126500496026446709910675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502000661368595613214233 1126500496026446709910675)
          ·
            refine ⟨1689750744039670064866013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126500496026446709910675 1689750744039670064866013)
            ·
              refine ⟨633656529014876274324755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1689750744039670064866013 633656529014876274324755)
              ·
                refine ⟨950484793522314411487133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633656529014876274324755 950484793522314411487133)
                ·
                  refine ⟨356431797570867904307675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950484793522314411487133 356431797570867904307675)
                  ·
                    rfl

theorem cell20_780917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_780917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780917 prefixEnd_780917 := by exact prefixLift 780917
  have htrace : WordTrace (prefixWord ++ tailWord_780917) baseStart_780917 baseEnd_780917 := by
    simpa [prefixWord, tailWord_780917, baseEnd_780917] using wordTrace_append hprefix tailTrace_780917
  have hstable : (prefixWord ++ tailWord_780917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780917).length < 2 ^ (prefixWord ++ tailWord_780917).sum := by decide
  have hdescent : baseEnd_780917 < baseStart_780917 := by decide
  rcases family_descends (prefixWord ++ tailWord_780917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780942 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_780942 : Nat := 118140960795 + 780942 * 2 ^ 59
def prefixEnd_780942 : Nat := 4983230072969 + 3 ^ 40 * 780942 * 2
def baseEnd_780942 : Nat := 356443208252078928474239

theorem tailTrace_780942 : CollatzResearch.WordTrace tailWord_780942 prefixEnd_780942 356443208252078928474239 := by
  unfold tailWord_780942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560411842098497890030135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18988863157858655413494053 3560411842098497890030135)
  ·
    refine ⟨5340617763147746835045203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560411842098497890030135 5340617763147746835045203)
    ·
      refine ⟨8010926644721620252567805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340617763147746835045203 8010926644721620252567805)
      ·
        refine ⟨3004097491770607594712927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8010926644721620252567805 3004097491770607594712927)
        ·
          refine ⟨4506146237655911392069391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004097491770607594712927 4506146237655911392069391)
          ·
            refine ⟨6759219356483867088104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506146237655911392069391 6759219356483867088104087)
            ·
              refine ⟨10138829034725800632156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759219356483867088104087 10138829034725800632156131)
              ·
                refine ⟨15208243552088700948234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138829034725800632156131 15208243552088700948234197)
                ·
                  refine ⟨356443208252078928474239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15208243552088700948234197 356443208252078928474239)
                  ·
                    rfl

theorem cell20_780942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_780942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780942 prefixEnd_780942 := by exact prefixLift 780942
  have htrace : WordTrace (prefixWord ++ tailWord_780942) baseStart_780942 baseEnd_780942 := by
    simpa [prefixWord, tailWord_780942, baseEnd_780942] using wordTrace_append hprefix tailTrace_780942
  have hstable : (prefixWord ++ tailWord_780942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780942).length < 2 ^ (prefixWord ++ tailWord_780942).sum := by decide
  have hdescent : baseEnd_780942 < baseStart_780942 := by decide
  rcases family_descends (prefixWord ++ tailWord_780942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780973 : List Nat := [1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_780973 : Nat := 118140960795 + 780973 * 2 ^ 59
def prefixEnd_780973 : Nat := 4983230072969 + 3 ^ 40 * 780973 * 2
def baseEnd_780973 : Nat := 118819119165593532813593

theorem tailTrace_780973 : CollatzResearch.WordTrace tailWord_780973 prefixEnd_780973 118819119165593532813593 := by
  unfold tailWord_780973
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484425399675675414619573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18989616933117116943079715 28484425399675675414619573)
  ·
    refine ⟨2670414881219594570120585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28484425399675675414619573 2670414881219594570120585)
    ·
      refine ⟨2002811160914695927590439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2670414881219594570120585 2002811160914695927590439)
      ·
        refine ⟨3004216741372043891385659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002811160914695927590439 3004216741372043891385659)
        ·
          refine ⟨4506325112058065837078489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004216741372043891385659 4506325112058065837078489)
          ·
            refine ⟨3379743834043549377808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506325112058065837078489 3379743834043549377808867)
            ·
              refine ⟨5069615751065324066713301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379743834043549377808867 5069615751065324066713301)
              ·
                refine ⟨118819119165593532813593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5069615751065324066713301 118819119165593532813593)
                ·
                  rfl

theorem cell20_780973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_780973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_780973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_780973 prefixEnd_780973 := by exact prefixLift 780973
  have htrace : WordTrace (prefixWord ++ tailWord_780973) baseStart_780973 baseEnd_780973 := by
    simpa [prefixWord, tailWord_780973, baseEnd_780973] using wordTrace_append hprefix tailTrace_780973
  have hstable : (prefixWord ++ tailWord_780973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780973).length < 2 ^ (prefixWord ++ tailWord_780973).sum := by decide
  have hdescent : baseEnd_780973 < baseStart_780973 := by decide
  rcases family_descends (prefixWord ++ tailWord_780973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781042 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_781042 : Nat := 118140960795 + 781042 * 2 ^ 59
def prefixEnd_781042 : Nat := 4983230072969 + 3 ^ 40 * 781042 * 2
def baseEnd_781042 : Nat := 356488850976923025140497

theorem tailTrace_781042 : CollatzResearch.WordTrace tailWord_781042 prefixEnd_781042 356488850976923025140497 := by
  unfold tailWord_781042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121735509106425049720345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18991294690950466799254253 7121735509106425049720345)
  ·
    refine ⟨5341301631829818787290259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7121735509106425049720345 5341301631829818787290259)
    ·
      refine ⟨8011952447744728180935389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341301631829818787290259 8011952447744728180935389)
      ·
        refine ⟨3004482167904273067850771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8011952447744728180935389 3004482167904273067850771)
        ·
          refine ⟨4506723251856409601776157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004482167904273067850771 4506723251856409601776157)
          ·
            refine ⟨1690021219446153600666059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4506723251856409601776157 1690021219446153600666059)
            ·
              refine ⟨2535031829169230400999089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690021219446153600666059 2535031829169230400999089)
              ·
                refine ⟨1901273871876922800749317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535031829169230400999089 1901273871876922800749317)
                ·
                  refine ⟨356488850976923025140497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901273871876922800749317 356488850976923025140497)
                  ·
                    rfl

theorem cell20_781042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_781042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781042 prefixEnd_781042 := by exact prefixLift 781042
  have htrace : WordTrace (prefixWord ++ tailWord_781042) baseStart_781042 baseEnd_781042 := by
    simpa [prefixWord, tailWord_781042, baseEnd_781042] using wordTrace_append hprefix tailTrace_781042
  have hstable : (prefixWord ++ tailWord_781042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781042).length < 2 ^ (prefixWord ++ tailWord_781042).sum := by decide
  have hdescent : baseEnd_781042 < baseStart_781042 := by decide
  rcases family_descends (prefixWord ++ tailWord_781042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781090 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_781090 : Nat := 118140960795 + 781090 * 2 ^ 59
def prefixEnd_781090 : Nat := 4983230072969 + 3 ^ 40 * 781090 * 2
def baseEnd_781090 : Nat := 356510759484848191540301

theorem tailTrace_781090 : CollatzResearch.WordTrace tailWord_781090 prefixEnd_781090 356510759484848191540301 := by
  unfold tailWord_781090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122173185062951099157181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18992461826834536264419149 7122173185062951099157181)
  ·
    refine ⟨2670814944398606662183943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7122173185062951099157181 2670814944398606662183943)
    ·
      refine ⟨4006222416597909993275915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670814944398606662183943 4006222416597909993275915)
      ·
        refine ⟨6009333624896864989913873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006222416597909993275915 6009333624896864989913873)
        ·
          refine ⟨4507000218672648742435405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6009333624896864989913873 4507000218672648742435405)
          ·
            refine ⟨1690125082002243278413277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4507000218672648742435405 1690125082002243278413277)
            ·
              refine ⟨633796905750841229404979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690125082002243278413277 633796905750841229404979)
              ·
                refine ⟨950695358626261844107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633796905750841229404979 950695358626261844107469)
                ·
                  refine ⟨356510759484848191540301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950695358626261844107469 356510759484848191540301)
                  ·
                    rfl

theorem cell20_781090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_781090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781090 prefixEnd_781090 := by exact prefixLift 781090
  have htrace : WordTrace (prefixWord ++ tailWord_781090) baseStart_781090 baseEnd_781090 := by
    simpa [prefixWord, tailWord_781090, baseEnd_781090] using wordTrace_append hprefix tailTrace_781090
  have hstable : (prefixWord ++ tailWord_781090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781090).length < 2 ^ (prefixWord ++ tailWord_781090).sum := by decide
  have hdescent : baseEnd_781090 < baseStart_781090 := by decide
  rcases family_descends (prefixWord ++ tailWord_781090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781110 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_781110 : Nat := 118140960795 + 781110 * 2 ^ 59
def prefixEnd_781110 : Nat := 4983230072969 + 3 ^ 40 * 781110 * 2
def baseEnd_781110 : Nat := 356519888029817010873553

theorem tailTrace_781110 : CollatzResearch.WordTrace tailWord_781110 prefixEnd_781110 356519888029817010873553 := by
  unfold tailWord_781110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780588887511209238272299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18992948133452898541571189 1780588887511209238272299)
  ·
    refine ⟨2670883331266813857408449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1780588887511209238272299 2670883331266813857408449)
    ·
      refine ⟨2003162498450110393056337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2670883331266813857408449 2003162498450110393056337)
      ·
        refine ⟨1502371873837582794792253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2003162498450110393056337 1502371873837582794792253)
        ·
          refine ⟨563389452689093548047095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1502371873837582794792253 563389452689093548047095)
          ·
            refine ⟨845084179033640322070643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563389452689093548047095 845084179033640322070643)
            ·
              refine ⟨1267626268550460483105965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845084179033640322070643 1267626268550460483105965)
              ·
                refine ⟨475359850706422681164737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1267626268550460483105965 475359850706422681164737)
                ·
                  refine ⟨356519888029817010873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475359850706422681164737 356519888029817010873553)
                  ·
                    rfl

theorem cell20_781110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_781110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781110 prefixEnd_781110 := by exact prefixLift 781110
  have htrace : WordTrace (prefixWord ++ tailWord_781110) baseStart_781110 baseEnd_781110 := by
    simpa [prefixWord, tailWord_781110, baseEnd_781110] using wordTrace_append hprefix tailTrace_781110
  have hstable : (prefixWord ++ tailWord_781110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781110).length < 2 ^ (prefixWord ++ tailWord_781110).sum := by decide
  have hdescent : baseEnd_781110 < baseStart_781110 := by decide
  rcases family_descends (prefixWord ++ tailWord_781110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781114 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_781114 : Nat := 118140960795 + 781114 * 2 ^ 59
def prefixEnd_781114 : Nat := 4983230072969 + 3 ^ 40 * 781114 * 2
def baseEnd_781114 : Nat := 356521713738810774740203

theorem tailTrace_781114 : CollatzResearch.WordTrace tailWord_781114 prefixEnd_781114 356521713738810774740203 := by
  unfold tailWord_781114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122392023041214123875599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18993045394776570997001597 7122392023041214123875599)
  ·
    refine ⟨10683588034561821185813399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122392023041214123875599 10683588034561821185813399)
    ·
      refine ⟨16025382051842731778720099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683588034561821185813399 16025382051842731778720099)
      ·
        refine ⟨24038073077764097668080149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16025382051842731778720099 24038073077764097668080149)
        ·
          refine ⟨1126784675520192078191257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24038073077764097668080149 1126784675520192078191257)
          ·
            refine ⟨845088506640144058643443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126784675520192078191257 845088506640144058643443)
            ·
              refine ⟨1267632759960216087965165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845088506640144058643443 1267632759960216087965165)
              ·
                refine ⟨475362284985081032986937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1267632759960216087965165 475362284985081032986937)
                ·
                  refine ⟨356521713738810774740203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475362284985081032986937 356521713738810774740203)
                  ·
                    rfl

theorem cell20_781114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_781114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781114 prefixEnd_781114 := by exact prefixLift 781114
  have htrace : WordTrace (prefixWord ++ tailWord_781114) baseStart_781114 baseEnd_781114 := by
    simpa [prefixWord, tailWord_781114, baseEnd_781114] using wordTrace_append hprefix tailTrace_781114
  have hstable : (prefixWord ++ tailWord_781114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781114).length < 2 ^ (prefixWord ++ tailWord_781114).sum := by decide
  have hdescent : baseEnd_781114 < baseStart_781114 := by decide
  rcases family_descends (prefixWord ++ tailWord_781114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781121 : List Nat := [1, 2, 5, 3, 2, 1, 6]
def baseStart_781121 : Nat := 118140960795 + 781121 * 2 ^ 59
def prefixEnd_781121 : Nat := 4983230072969 + 3 ^ 40 * 781121 * 2
def baseEnd_781121 : Nat := 39613878747727762389649

theorem tailTrace_781121 : CollatzResearch.WordTrace tailWord_781121 prefixEnd_781121 39613878747727762389649 := by
  unfold tailWord_781121
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489823403139496691007217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18993215602092997794004811 28489823403139496691007217)
  ·
    refine ⟨21367367552354622518255413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28489823403139496691007217 21367367552354622518255413)
    ·
      refine ⟨2003190708033245861086445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21367367552354622518255413 2003190708033245861086445)
      ·
        refine ⟨751196515512467197907417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2003190708033245861086445 751196515512467197907417)
        ·
          refine ⟨563397386634350398430563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751196515512467197907417 563397386634350398430563)
          ·
            refine ⟨845096079951525597645845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563397386634350398430563 845096079951525597645845)
            ·
              refine ⟨39613878747727762389649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 845096079951525597645845 39613878747727762389649)
              ·
                rfl

theorem cell20_781121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_781121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781121 prefixEnd_781121 := by exact prefixLift 781121
  have htrace : WordTrace (prefixWord ++ tailWord_781121) baseStart_781121 baseEnd_781121 := by
    simpa [prefixWord, tailWord_781121, baseEnd_781121] using wordTrace_append hprefix tailTrace_781121
  have hstable : (prefixWord ++ tailWord_781121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781121).length < 2 ^ (prefixWord ++ tailWord_781121).sum := by decide
  have hdescent : baseEnd_781121 < baseStart_781121 := by decide
  rcases family_descends (prefixWord ++ tailWord_781121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781132 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_781132 : Nat := 118140960795 + 781132 * 2 ^ 59
def prefixEnd_781132 : Nat := 4983230072969 + 3 ^ 40 * 781132 * 2
def baseEnd_781132 : Nat := 356529929429282712140129

theorem tailTrace_781132 : CollatzResearch.WordTrace tailWord_781132 prefixEnd_781132 356529929429282712140129 := by
  unfold tailWord_781132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245112303049822784828825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18993483070733097046438433 14245112303049822784828825)
  ·
    refine ⟨10683834227287367088621619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14245112303049822784828825 10683834227287367088621619)
    ·
      refine ⟨16025751340931050632932429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683834227287367088621619 16025751340931050632932429)
      ·
        refine ⟨6009656752849143987349661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16025751340931050632932429 6009656752849143987349661)
        ·
          refine ⟨2253621282318428995256123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6009656752849143987349661 2253621282318428995256123)
          ·
            refine ⟨3380431923477643492884185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253621282318428995256123 3380431923477643492884185)
            ·
              refine ⟨2535323942608232619663139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380431923477643492884185 2535323942608232619663139)
              ·
                refine ⟨3802985913912348929494709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535323942608232619663139 3802985913912348929494709)
                ·
                  refine ⟨356529929429282712140129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3802985913912348929494709 356529929429282712140129)
                  ·
                    rfl

theorem cell20_781132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_781132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781132 prefixEnd_781132 := by exact prefixLift 781132
  have htrace : WordTrace (prefixWord ++ tailWord_781132) baseStart_781132 baseEnd_781132 := by
    simpa [prefixWord, tailWord_781132, baseEnd_781132] using wordTrace_append hprefix tailTrace_781132
  have hstable : (prefixWord ++ tailWord_781132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781132).length < 2 ^ (prefixWord ++ tailWord_781132).sum := by decide
  have hdescent : baseEnd_781132 < baseStart_781132 := by decide
  rcases family_descends (prefixWord ++ tailWord_781132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781146 : List Nat := [3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_781146 : Nat := 118140960795 + 781146 * 2 ^ 59
def prefixEnd_781146 : Nat := 4983230072969 + 3 ^ 40 * 781146 * 2
def baseEnd_781146 : Nat := 118845439803586961891135

theorem tailTrace_781146 : CollatzResearch.WordTrace tailWord_781146 prefixEnd_781146 118845439803586961891135 := by
  unfold tailWord_781146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122683807012231490166823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18993823485365950640444861 7122683807012231490166823)
  ·
    refine ⟨10684025710518347235250235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122683807012231490166823 10684025710518347235250235)
    ·
      refine ⟨16026038565777520852875353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10684025710518347235250235 16026038565777520852875353)
      ·
        refine ⟨12019528924333140639656515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16026038565777520852875353 12019528924333140639656515)
        ·
          refine ⟨18029293386499710959484773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019528924333140639656515 18029293386499710959484773)
          ·
            refine ⟨3380492509968695804903395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18029293386499710959484773 3380492509968695804903395)
            ·
              refine ⟨5070738764953043707355093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380492509968695804903395 5070738764953043707355093)
              ·
                refine ⟨118845439803586961891135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5070738764953043707355093 118845439803586961891135)
                ·
                  rfl

theorem cell20_781146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_781146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781146 prefixEnd_781146 := by exact prefixLift 781146
  have htrace : WordTrace (prefixWord ++ tailWord_781146) baseStart_781146 baseEnd_781146 := by
    simpa [prefixWord, tailWord_781146, baseEnd_781146] using wordTrace_append hprefix tailTrace_781146
  have hstable : (prefixWord ++ tailWord_781146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781146).length < 2 ^ (prefixWord ++ tailWord_781146).sum := by decide
  have hdescent : baseEnd_781146 < baseStart_781146 := by decide
  rcases family_descends (prefixWord ++ tailWord_781146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781153 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_781153 : Nat := 118140960795 + 781153 * 2 ^ 59
def prefixEnd_781153 : Nat := 4983230072969 + 3 ^ 40 * 781153 * 2
def baseEnd_781153 : Nat := 356539514401499972440043

theorem tailTrace_781153 : CollatzResearch.WordTrace tailWord_781153 prefixEnd_781153 356539514401499972440043 := by
  unfold tailWord_781153
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490990539023566156172113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18993993692682377437448075 28490990539023566156172113)
  ·
    refine ⟨21368242904267674617129085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28490990539023566156172113 21368242904267674617129085)
    ·
      refine ⟨8013091089100377981423407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21368242904267674617129085 8013091089100377981423407)
      ·
        refine ⟨12019636633650566972135111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8013091089100377981423407 12019636633650566972135111)
        ·
          refine ⟨18029454950475850458202667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019636633650566972135111 18029454950475850458202667)
          ·
            refine ⟨27044182425713775687304001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029454950475850458202667 27044182425713775687304001)
            ·
              refine ⟨20283136819285331765478001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27044182425713775687304001 20283136819285331765478001)
              ·
                refine ⟨15212352614463998824108501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20283136819285331765478001 15212352614463998824108501)
                ·
                  refine ⟨356539514401499972440043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15212352614463998824108501 356539514401499972440043)
                  ·
                    rfl

theorem cell20_781153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_781153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781153 prefixEnd_781153 := by exact prefixLift 781153
  have htrace : WordTrace (prefixWord ++ tailWord_781153) baseStart_781153 baseEnd_781153 := by
    simpa [prefixWord, tailWord_781153, baseEnd_781153] using wordTrace_append hprefix tailTrace_781153
  have hstable : (prefixWord ++ tailWord_781153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781153).length < 2 ^ (prefixWord ++ tailWord_781153).sum := by decide
  have hdescent : baseEnd_781153 < baseStart_781153 := by decide
  rcases family_descends (prefixWord ++ tailWord_781153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781215 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_781215 : Nat := 118140960795 + 781215 * 2 ^ 59
def prefixEnd_781215 : Nat := 4983230072969 + 3 ^ 40 * 781215 * 2
def baseEnd_781215 : Nat := 356567812890903312373123

theorem tailTrace_781215 : CollatzResearch.WordTrace tailWord_781215 prefixEnd_781215 356567812890903312373123 := by
  unfold tailWord_781215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28493251864798950744929099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18995501243199300496619399 28493251864798950744929099)
  ·
    refine ⟨42739877797198426117393649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28493251864798950744929099 42739877797198426117393649)
    ·
      refine ⟨32054908347898819588045237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42739877797198426117393649 32054908347898819588045237)
      ·
        refine ⟨3005147657615514336379241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32054908347898819588045237 3005147657615514336379241)
        ·
          refine ⟨2253860743211635752284431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005147657615514336379241 2253860743211635752284431)
          ·
            refine ⟨3380791114817453628426647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253860743211635752284431 3380791114817453628426647)
            ·
              refine ⟨5071186672226180442639971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380791114817453628426647 5071186672226180442639971)
              ·
                refine ⟨7606780008339270663959957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071186672226180442639971 7606780008339270663959957)
                ·
                  refine ⟨356567812890903312373123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7606780008339270663959957 356567812890903312373123)
                  ·
                    rfl

theorem cell20_781215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_781215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781215 prefixEnd_781215 := by exact prefixLift 781215
  have htrace : WordTrace (prefixWord ++ tailWord_781215) baseStart_781215 baseEnd_781215 := by
    simpa [prefixWord, tailWord_781215, baseEnd_781215] using wordTrace_append hprefix tailTrace_781215
  have hstable : (prefixWord ++ tailWord_781215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781215).length < 2 ^ (prefixWord ++ tailWord_781215).sum := by decide
  have hdescent : baseEnd_781215 < baseStart_781215 := by decide
  rcases family_descends (prefixWord ++ tailWord_781215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781218 : List Nat := [3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_781218 : Nat := 118140960795 + 781218 * 2 ^ 59
def prefixEnd_781218 : Nat := 4983230072969 + 3 ^ 40 * 781218 * 2
def baseEnd_781218 : Nat := 118856394057549545091037

theorem tailTrace_781218 : CollatzResearch.WordTrace tailWord_781218 prefixEnd_781218 118856394057549545091037 := by
  unfold tailWord_781218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123340320947020564322077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18995574189192054838192205 7123340320947020564322077)
  ·
    refine ⟨2671252620355132711620779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7123340320947020564322077 2671252620355132711620779)
    ·
      refine ⟨4006878930532699067431169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671252620355132711620779 4006878930532699067431169)
      ·
        refine ⟨3005159197899524300573377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006878930532699067431169 3005159197899524300573377)
        ·
          refine ⟨2253869398424643225430033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005159197899524300573377 2253869398424643225430033)
          ·
            refine ⟨1690402048818482419072525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253869398424643225430033 1690402048818482419072525)
            ·
              refine ⟨633900768306930907152197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690402048818482419072525 633900768306930907152197)
              ·
                refine ⟨118856394057549545091037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633900768306930907152197 118856394057549545091037)
                ·
                  rfl

theorem cell20_781218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_781218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781218 prefixEnd_781218 := by exact prefixLift 781218
  have htrace : WordTrace (prefixWord ++ tailWord_781218) baseStart_781218 baseEnd_781218 := by
    simpa [prefixWord, tailWord_781218, baseEnd_781218] using wordTrace_append hprefix tailTrace_781218
  have hstable : (prefixWord ++ tailWord_781218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781218).length < 2 ^ (prefixWord ++ tailWord_781218).sum := by decide
  have hdescent : baseEnd_781218 < baseStart_781218 := by decide
  rcases family_descends (prefixWord ++ tailWord_781218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781246 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_781246 : Nat := 118140960795 + 781246 * 2 ^ 59
def prefixEnd_781246 : Nat := 4983230072969 + 3 ^ 40 * 781246 * 2
def baseEnd_781246 : Nat := 356581962135604982339663

theorem tailTrace_781246 : CollatzResearch.WordTrace tailWord_781246 prefixEnd_781246 356581962135604982339663 := by
  unfold tailWord_781246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561797815960830379913449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18996255018457762026205061 3561797815960830379913449)
  ·
    refine ⟨2671348361970622784935087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3561797815960830379913449 2671348361970622784935087)
    ·
      refine ⟨4007022542955934177402631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671348361970622784935087 4007022542955934177402631)
      ·
        refine ⟨6010533814433901266103947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007022542955934177402631 6010533814433901266103947)
        ·
          refine ⟨9015800721650851899155921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010533814433901266103947 9015800721650851899155921)
          ·
            refine ⟨6761850541238138924366941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9015800721650851899155921 6761850541238138924366941)
            ·
              refine ⟨2535693952964302096637603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761850541238138924366941 2535693952964302096637603)
              ·
                refine ⟨3803540929446453144956405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535693952964302096637603 3803540929446453144956405)
                ·
                  refine ⟨356581962135604982339663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803540929446453144956405 356581962135604982339663)
                  ·
                    rfl

theorem cell20_781246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_781246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781246 prefixEnd_781246 := by exact prefixLift 781246
  have htrace : WordTrace (prefixWord ++ tailWord_781246) baseStart_781246 baseEnd_781246 := by
    simpa [prefixWord, tailWord_781246, baseEnd_781246] using wordTrace_append hprefix tailTrace_781246
  have hstable : (prefixWord ++ tailWord_781246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781246).length < 2 ^ (prefixWord ++ tailWord_781246).sum := by decide
  have hdescent : baseEnd_781246 < baseStart_781246 := by decide
  rcases family_descends (prefixWord ++ tailWord_781246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781260 : List Nat := [2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_781260 : Nat := 118140960795 + 781260 * 2 ^ 59
def prefixEnd_781260 : Nat := 4983230072969 + 3 ^ 40 * 781260 * 2
def baseEnd_781260 : Nat := 118862784039027718624313

theorem tailTrace_781260 : CollatzResearch.WordTrace tailWord_781260 prefixEnd_781260 118862784039027718624313 := by
  unfold tailWord_781260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247446574817961715158617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18996595433090615620211489 14247446574817961715158617)
  ·
    refine ⟨10685584931113471286368963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14247446574817961715158617 10685584931113471286368963)
    ·
      refine ⟨16028377396670206929553445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685584931113471286368963 16028377396670206929553445)
      ·
        refine ⟨3005320761875663799291271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16028377396670206929553445 3005320761875663799291271)
        ·
          refine ⟨4507981142813495698936907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005320761875663799291271 4507981142813495698936907)
          ·
            refine ⟨6761971714220243548405361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507981142813495698936907 6761971714220243548405361)
            ·
              refine ⟨5071478785665182661304021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6761971714220243548405361 5071478785665182661304021)
              ·
                refine ⟨118862784039027718624313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5071478785665182661304021 118862784039027718624313)
                ·
                  rfl

theorem cell20_781260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_781260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781260 prefixEnd_781260 := by exact prefixLift 781260
  have htrace : WordTrace (prefixWord ++ tailWord_781260) baseStart_781260 baseEnd_781260 := by
    simpa [prefixWord, tailWord_781260, baseEnd_781260] using wordTrace_append hprefix tailTrace_781260
  have hstable : (prefixWord ++ tailWord_781260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781260).length < 2 ^ (prefixWord ++ tailWord_781260).sum := by decide
  have hdescent : baseEnd_781260 < baseStart_781260 := by decide
  rcases family_descends (prefixWord ++ tailWord_781260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781263 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_781263 : Nat := 118140960795 + 781263 * 2 ^ 59
def prefixEnd_781263 : Nat := 4983230072969 + 3 ^ 40 * 781263 * 2
def baseEnd_781263 : Nat := 356589721398828478772927

theorem tailTrace_781263 : CollatzResearch.WordTrace tailWord_781263 prefixEnd_781263 356589721398828478772927 := by
  unfold tailWord_781263
  simp only [CollatzResearch.WordTrace]
  refine ⟨28495002568625054942676443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18996668379083369961784295 28495002568625054942676443)
  ·
    refine ⟨42742503852937582414014665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28495002568625054942676443 42742503852937582414014665)
    ·
      refine ⟨32056877889703186810510999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42742503852937582414014665 32056877889703186810510999)
      ·
        refine ⟨48085316834554780215766499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32056877889703186810510999 48085316834554780215766499)
        ·
          refine ⟨72127975251832170323649749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48085316834554780215766499 72127975251832170323649749)
          ·
            refine ⟨1690499419964816491960541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72127975251832170323649749 1690499419964816491960541)
            ·
              refine ⟨633937282486806184485203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690499419964816491960541 633937282486806184485203)
              ·
                refine ⟨950905923730209276727805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633937282486806184485203 950905923730209276727805)
                ·
                  refine ⟨356589721398828478772927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950905923730209276727805 356589721398828478772927)
                  ·
                    rfl

theorem cell20_781263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_781263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781263 prefixEnd_781263 := by exact prefixLift 781263
  have htrace : WordTrace (prefixWord ++ tailWord_781263) baseStart_781263 baseEnd_781263 := by
    simpa [prefixWord, tailWord_781263, baseEnd_781263] using wordTrace_append hprefix tailTrace_781263
  have hstable : (prefixWord ++ tailWord_781263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781263).length < 2 ^ (prefixWord ++ tailWord_781263).sum := by decide
  have hdescent : baseEnd_781263 < baseStart_781263 := by decide
  rcases family_descends (prefixWord ++ tailWord_781263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781277 : List Nat := [1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_781277 : Nat := 118140960795 + 781277 * 2 ^ 59
def prefixEnd_781277 : Nat := 4983230072969 + 3 ^ 40 * 781277 * 2
def baseEnd_781277 : Nat := 118865370460102217435401

theorem tailTrace_781277 : CollatzResearch.WordTrace tailWord_781277 prefixEnd_781277 118865370460102217435401 := by
  unfold tailWord_781277
  simp only [CollatzResearch.WordTrace]
  refine ⟨28495513190574335333686085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997008793716223555790723 28495513190574335333686085)
  ·
    refine ⟨5342908723232687875066141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28495513190574335333686085 5342908723232687875066141)
    ·
      refine ⟨2003590771212257953149803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5342908723232687875066141 2003590771212257953149803)
      ·
        refine ⟨3005386156818386929724705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003590771212257953149803 3005386156818386929724705)
        ·
          refine ⟨2254039617613790197293529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005386156818386929724705 2254039617613790197293529)
          ·
            refine ⟨1690529713210342647970147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254039617613790197293529 1690529713210342647970147)
            ·
              refine ⟨2535794569815513971955221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690529713210342647970147 2535794569815513971955221)
              ·
                refine ⟨118865370460102217435401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2535794569815513971955221 118865370460102217435401)
                ·
                  rfl

theorem cell20_781277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_781277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781277 prefixEnd_781277 := by exact prefixLift 781277
  have htrace : WordTrace (prefixWord ++ tailWord_781277) baseStart_781277 baseEnd_781277 := by
    simpa [prefixWord, tailWord_781277, baseEnd_781277] using wordTrace_append hprefix tailTrace_781277
  have hstable : (prefixWord ++ tailWord_781277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781277).length < 2 ^ (prefixWord ++ tailWord_781277).sum := by decide
  have hdescent : baseEnd_781277 < baseStart_781277 := by decide
  rcases family_descends (prefixWord ++ tailWord_781277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781287 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 2]
def baseStart_781287 : Nat := 118140960795 + 781287 * 2 ^ 59
def prefixEnd_781287 : Nat := 4983230072969 + 3 ^ 40 * 781287 * 2
def baseEnd_781287 : Nat := 356600675652791061972829

theorem tailTrace_781287 : CollatzResearch.WordTrace tailWord_781287 prefixEnd_781287 356600675652791061972829 := by
  unfold tailWord_781287
  simp only [CollatzResearch.WordTrace]
  refine ⟨28495877920538107041550115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997251947025404694366743 28495877920538107041550115)
  ·
    refine ⟨42743816880807160562325173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28495877920538107041550115 42743816880807160562325173)
    ·
      refine ⟨4007232832575671302717985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42743816880807160562325173 4007232832575671302717985)
      ·
        refine ⟨3005424624431753477038489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007232832575671302717985 3005424624431753477038489)
        ·
          refine ⟨2254068468323815107778867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005424624431753477038489 2254068468323815107778867)
          ·
            refine ⟨3381102702485722661668301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254068468323815107778867 3381102702485722661668301)
            ·
              refine ⟨1267913513432145998125613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3381102702485722661668301 1267913513432145998125613)
              ·
                refine ⟨475467567537054749297105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1267913513432145998125613 475467567537054749297105)
                ·
                  refine ⟨356600675652791061972829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475467567537054749297105 356600675652791061972829)
                  ·
                    rfl

theorem cell20_781287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2].length) (baseStart_781287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781287 prefixEnd_781287 := by exact prefixLift 781287
  have htrace : WordTrace (prefixWord ++ tailWord_781287) baseStart_781287 baseEnd_781287 := by
    simpa [prefixWord, tailWord_781287, baseEnd_781287] using wordTrace_append hprefix tailTrace_781287
  have hstable : (prefixWord ++ tailWord_781287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781287).length < 2 ^ (prefixWord ++ tailWord_781287).sum := by decide
  have hdescent : baseEnd_781287 < baseStart_781287 := by decide
  rcases family_descends (prefixWord ++ tailWord_781287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781294 : List Nat := [4, 1, 2, 1, 5, 1, 6]
def baseStart_781294 : Nat := 118140960795 + 781294 * 2 ^ 59
def prefixEnd_781294 : Nat := 4983230072969 + 3 ^ 40 * 781294 * 2
def baseEnd_781294 : Nat := 39622652293725572082163

theorem tailTrace_781294 : CollatzResearch.WordTrace tailWord_781294 prefixEnd_781294 39622652293725572082163 := by
  unfold tailWord_781294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562016653939093404631867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18997422154341831491369957 3562016653939093404631867)
  ·
    refine ⟨5343024980908640106947801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562016653939093404631867 5343024980908640106947801)
    ·
      refine ⟨4007268735681480080210851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5343024980908640106947801 4007268735681480080210851)
      ·
        refine ⟨6010903103522220120316277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007268735681480080210851 6010903103522220120316277)
        ·
          refine ⟨563522165955208136279651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6010903103522220120316277 563522165955208136279651)
          ·
            refine ⟨845283248932812204419477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563522165955208136279651 845283248932812204419477)
            ·
              refine ⟨39622652293725572082163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 845283248932812204419477 39622652293725572082163)
              ·
                rfl

theorem cell20_781294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_781294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781294 prefixEnd_781294 := by exact prefixLift 781294
  have htrace : WordTrace (prefixWord ++ tailWord_781294) baseStart_781294 baseEnd_781294 := by
    simpa [prefixWord, tailWord_781294, baseEnd_781294] using wordTrace_append hprefix tailTrace_781294
  have hstable : (prefixWord ++ tailWord_781294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781294).length < 2 ^ (prefixWord ++ tailWord_781294).sum := by decide
  have hdescent : baseEnd_781294 < baseStart_781294 := by decide
  rcases family_descends (prefixWord ++ tailWord_781294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781300 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_781300 : Nat := 118140960795 + 781300 * 2 ^ 59
def prefixEnd_781300 : Nat := 4983230072969 + 3 ^ 40 * 781300 * 2
def baseEnd_781300 : Nat := 356606609207020794539443

theorem tailTrace_781300 : CollatzResearch.WordTrace tailWord_781300 prefixEnd_781300 356606609207020794539443 := by
  unfold tailWord_781300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248176034745505130886677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18997568046327340174515569 14248176034745505130886677)
  ·
    refine ⟨667883251628695553010313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14248176034745505130886677 667883251628695553010313)
    ·
      refine ⟨500912438721521664757735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667883251628695553010313 500912438721521664757735)
      ·
        refine ⟨751368658082282497136603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500912438721521664757735 751368658082282497136603)
        ·
          refine ⟨1127052987123423745704905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751368658082282497136603 1127052987123423745704905)
          ·
            refine ⟨845289740342567809278679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127052987123423745704905 845289740342567809278679)
            ·
              refine ⟨1267934610513851713918019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845289740342567809278679 1267934610513851713918019)
              ·
                refine ⟨1901901915770777570877029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267934610513851713918019 1901901915770777570877029)
                ·
                  refine ⟨356606609207020794539443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901901915770777570877029 356606609207020794539443)
                  ·
                    rfl

theorem cell20_781300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_781300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781300 prefixEnd_781300 := by exact prefixLift 781300
  have htrace : WordTrace (prefixWord ++ tailWord_781300) baseStart_781300 baseEnd_781300 := by
    simpa [prefixWord, tailWord_781300, baseEnd_781300] using wordTrace_append hprefix tailTrace_781300
  have hstable : (prefixWord ++ tailWord_781300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781300).length < 2 ^ (prefixWord ++ tailWord_781300).sum := by decide
  have hdescent : baseEnd_781300 < baseStart_781300 := by decide
  rcases family_descends (prefixWord ++ tailWord_781300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781305 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_781305 : Nat := 118140960795 + 781305 * 2 ^ 59
def prefixEnd_781305 : Nat := 4983230072969 + 3 ^ 40 * 781305 * 2
def baseEnd_781305 : Nat := 356608891343262999372755

theorem tailTrace_781305 : CollatzResearch.WordTrace tailWord_781305 prefixEnd_781305 356608891343262999372755 := by
  unfold tailWord_781305
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496534434472896115705369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997689622981930743803579 28496534434472896115705369)
  ·
    refine ⟨21372400825854672086779027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28496534434472896115705369 21372400825854672086779027)
    ·
      refine ⟨32058601238782008130168541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21372400825854672086779027 32058601238782008130168541)
      ·
        refine ⟨12021975464543253048813203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32058601238782008130168541 12021975464543253048813203)
        ·
          refine ⟨18032963196814879573219805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12021975464543253048813203 18032963196814879573219805)
          ·
            refine ⟨6762361198805579839957427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18032963196814879573219805 6762361198805579839957427)
            ·
              refine ⟨10143541798208369759936141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762361198805579839957427 10143541798208369759936141)
              ·
                refine ⟨3803828174328138659976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10143541798208369759936141 3803828174328138659976053)
                ·
                  refine ⟨356608891343262999372755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803828174328138659976053 356608891343262999372755)
                  ·
                    rfl

theorem cell20_781305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_781305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781305 prefixEnd_781305 := by exact prefixLift 781305
  have htrace : WordTrace (prefixWord ++ tailWord_781305) baseStart_781305 baseEnd_781305 := by
    simpa [prefixWord, tailWord_781305, baseEnd_781305] using wordTrace_append hprefix tailTrace_781305
  have hstable : (prefixWord ++ tailWord_781305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781305).length < 2 ^ (prefixWord ++ tailWord_781305).sum := by decide
  have hdescent : baseEnd_781305 < baseStart_781305 := by decide
  rcases family_descends (prefixWord ++ tailWord_781305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781308 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_781308 : Nat := 118140960795 + 781308 * 2 ^ 59
def prefixEnd_781308 : Nat := 4983230072969 + 3 ^ 40 * 781308 * 2
def baseEnd_781308 : Nat := 356610260625008322272743

theorem tailTrace_781308 : CollatzResearch.WordTrace tailWord_781308 prefixEnd_781308 356610260625008322272743 := by
  unfold tailWord_781308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248321926731013814032289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18997762568974685085376385 14248321926731013814032289)
  ·
    refine ⟨10686241445048260360524217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14248321926731013814032289 10686241445048260360524217)
    ·
      refine ⟨8014681083786195270393163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10686241445048260360524217 8014681083786195270393163)
      ·
        refine ⟨12022021625679292905589745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014681083786195270393163 12022021625679292905589745)
        ·
          refine ⟨9016516219259469679192309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12022021625679292905589745 9016516219259469679192309)
          ·
            refine ⟨845298395555575282424279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9016516219259469679192309 845298395555575282424279)
            ·
              refine ⟨1267947593333362923636419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845298395555575282424279 1267947593333362923636419)
              ·
                refine ⟨1901921390000044385454629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267947593333362923636419 1901921390000044385454629)
                ·
                  refine ⟨356610260625008322272743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901921390000044385454629 356610260625008322272743)
                  ·
                    rfl

theorem cell20_781308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_781308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781308 prefixEnd_781308 := by exact prefixLift 781308
  have htrace : WordTrace (prefixWord ++ tailWord_781308) baseStart_781308 baseEnd_781308 := by
    simpa [prefixWord, tailWord_781308, baseEnd_781308] using wordTrace_append hprefix tailTrace_781308
  have hstable : (prefixWord ++ tailWord_781308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781308).length < 2 ^ (prefixWord ++ tailWord_781308).sum := by decide
  have hdescent : baseEnd_781308 < baseStart_781308 := by decide
  rcases family_descends (prefixWord ++ tailWord_781308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781314 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_781314 : Nat := 118140960795 + 781314 * 2 ^ 59
def prefixEnd_781314 : Nat := 4983230072969 + 3 ^ 40 * 781314 * 2
def baseEnd_781314 : Nat := 356612999188498968072719

theorem tailTrace_781314 : CollatzResearch.WordTrace tailWord_781314 prefixEnd_781314 356612999188498968072719 := by
  unfold tailWord_781314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7124215672860072663195749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18997908460960193768521997 7124215672860072663195749)
  ·
    refine ⟨1335790438661263624349203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7124215672860072663195749 1335790438661263624349203)
    ·
      refine ⟨2003685657991895436523805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335790438661263624349203 2003685657991895436523805)
      ·
        refine ⟨751382121746960788696427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2003685657991895436523805 751382121746960788696427)
        ·
          refine ⟨1127073182620441183044641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751382121746960788696427 1127073182620441183044641)
          ·
            refine ⟨845304886965330887283481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127073182620441183044641 845304886965330887283481)
            ·
              refine ⟨633978665223998165462611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845304886965330887283481 633978665223998165462611)
              ·
                refine ⟨950967997835997248193917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633978665223998165462611 950967997835997248193917)
                ·
                  refine ⟨356612999188498968072719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950967997835997248193917 356612999188498968072719)
                  ·
                    rfl

theorem cell20_781314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_781314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781314 prefixEnd_781314 := by exact prefixLift 781314
  have htrace : WordTrace (prefixWord ++ tailWord_781314) baseStart_781314 baseEnd_781314 := by
    simpa [prefixWord, tailWord_781314, baseEnd_781314] using wordTrace_append hprefix tailTrace_781314
  have hstable : (prefixWord ++ tailWord_781314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781314).length < 2 ^ (prefixWord ++ tailWord_781314).sum := by decide
  have hdescent : baseEnd_781314 < baseStart_781314 := by decide
  rcases family_descends (prefixWord ++ tailWord_781314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781336 : List Nat := [2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_781336 : Nat := 118140960795 + 781336 * 2 ^ 59
def prefixEnd_781336 : Nat := 4983230072969 + 3 ^ 40 * 781336 * 2
def baseEnd_781336 : Nat := 118874346862654889779765

theorem tailTrace_781336 : CollatzResearch.WordTrace tailWord_781336 prefixEnd_781336 118874346862654889779765 := by
  unfold tailWord_781336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248832548680294205041931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18998443398240392273389241 14248832548680294205041931)
  ·
    refine ⟨21373248823020441307562897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14248832548680294205041931 21373248823020441307562897)
    ·
      refine ⟨16029936617265330980672173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21373248823020441307562897 16029936617265330980672173)
      ·
        refine ⟨6011226231474499117752065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16029936617265330980672173 6011226231474499117752065)
        ·
          refine ⟨4508419673605874338314049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011226231474499117752065 4508419673605874338314049)
          ·
            refine ⟨3381314755204405753735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4508419673605874338314049 3381314755204405753735537)
            ·
              refine ⟨2535986066403304315301653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381314755204405753735537 2535986066403304315301653)
              ·
                refine ⟨118874346862654889779765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2535986066403304315301653 118874346862654889779765)
                ·
                  rfl

theorem cell20_781336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_781336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781336 prefixEnd_781336 := by exact prefixLift 781336
  have htrace : WordTrace (prefixWord ++ tailWord_781336) baseStart_781336 baseEnd_781336 := by
    simpa [prefixWord, tailWord_781336, baseEnd_781336] using wordTrace_append hprefix tailTrace_781336
  have hstable : (prefixWord ++ tailWord_781336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781336).length < 2 ^ (prefixWord ++ tailWord_781336).sum := by decide
  have hdescent : baseEnd_781336 < baseStart_781336 := by decide
  rcases family_descends (prefixWord ++ tailWord_781336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781360 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_781360 : Nat := 118140960795 + 781360 * 2 ^ 59
def prefixEnd_781360 : Nat := 4983230072969 + 3 ^ 40 * 781360 * 2
def baseEnd_781360 : Nat := 356633994841927252539197

theorem tailTrace_781360 : CollatzResearch.WordTrace tailWord_781360 prefixEnd_781360 356633994841927252539197 := by
  unfold tailWord_781360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249270224636820254478767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18999026966182427005971689 14249270224636820254478767)
  ·
    refine ⟨21373905336955230381718151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14249270224636820254478767 21373905336955230381718151)
    ·
      refine ⟨32060858005432845572577227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21373905336955230381718151 32060858005432845572577227)
      ·
        refine ⟨48091287008149268358865841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32060858005432845572577227 48091287008149268358865841)
        ·
          refine ⟨36068465256111951269149381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48091287008149268358865841 36068465256111951269149381)
          ·
            refine ⟨6762837235520990862965509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36068465256111951269149381 6762837235520990862965509)
            ·
              refine ⟨1268031981660185786806033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6762837235520990862965509 1268031981660185786806033)
              ·
                refine ⟨951023986245139340104525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268031981660185786806033 951023986245139340104525)
                ·
                  refine ⟨356633994841927252539197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951023986245139340104525 356633994841927252539197)
                  ·
                    rfl

theorem cell20_781360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_781360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781360 prefixEnd_781360 := by exact prefixLift 781360
  have htrace : WordTrace (prefixWord ++ tailWord_781360) baseStart_781360 baseEnd_781360 := by
    simpa [prefixWord, tailWord_781360, baseEnd_781360] using wordTrace_append hprefix tailTrace_781360
  have hstable : (prefixWord ++ tailWord_781360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781360).length < 2 ^ (prefixWord ++ tailWord_781360).sum := by decide
  have hdescent : baseEnd_781360 < baseStart_781360 := by decide
  rcases family_descends (prefixWord ++ tailWord_781360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781415 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_781415 : Nat := 118140960795 + 781415 * 2 ^ 59
def prefixEnd_781415 : Nat := 4983230072969 + 3 ^ 40 * 781415 * 2
def baseEnd_781415 : Nat := 356659098340591505705639

theorem tailTrace_781415 : CollatzResearch.WordTrace tailWord_781415 prefixEnd_781415 356659098340591505705639 := by
  unfold tailWord_781415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500546464074384902209699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19000364309382923268139799 28500546464074384902209699)
  ·
    refine ⟨42750819696111577353314549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28500546464074384902209699 42750819696111577353314549)
    ·
      refine ⟨4007889346510460376873239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42750819696111577353314549 4007889346510460376873239)
      ·
        refine ⟨6011834019765690565309859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007889346510460376873239 6011834019765690565309859)
        ·
          refine ⟨9017751029648535847964789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011834019765690565309859 9017751029648535847964789)
          ·
            refine ⟨845414159029550235746699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9017751029648535847964789 845414159029550235746699)
            ·
              refine ⟨1268121238544325353620049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845414159029550235746699 1268121238544325353620049)
              ·
                refine ⟨951090928908244015215037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268121238544325353620049 951090928908244015215037)
                ·
                  refine ⟨356659098340591505705639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951090928908244015215037 356659098340591505705639)
                  ·
                    rfl

theorem cell20_781415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_781415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781415 prefixEnd_781415 := by exact prefixLift 781415
  have htrace : WordTrace (prefixWord ++ tailWord_781415) baseStart_781415 baseEnd_781415 := by
    simpa [prefixWord, tailWord_781415, baseEnd_781415] using wordTrace_append hprefix tailTrace_781415
  have hstable : (prefixWord ++ tailWord_781415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781415).length < 2 ^ (prefixWord ++ tailWord_781415).sum := by decide
  have hdescent : baseEnd_781415 < baseStart_781415 := by decide
  rcases family_descends (prefixWord ++ tailWord_781415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781422 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_781422 : Nat := 118140960795 + 781422 * 2 ^ 59
def prefixEnd_781422 : Nat := 4983230072969 + 3 ^ 40 * 781422 * 2
def baseEnd_781422 : Nat := 356662293331330592472277

theorem tailTrace_781422 : CollatzResearch.WordTrace tailWord_781422 prefixEnd_781422 356662293331330592472277 := by
  unfold tailWord_781422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562600221881128137214315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19000534516699350065143013 3562600221881128137214315)
  ·
    refine ⟨5343900332821692205821473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562600221881128137214315 5343900332821692205821473)
    ·
      refine ⟨4007925249616269154366105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5343900332821692205821473 4007925249616269154366105)
      ·
        refine ⟨3005943937212201865774579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007925249616269154366105 3005943937212201865774579)
        ·
          refine ⟨4508915905818302798661869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005943937212201865774579 4508915905818302798661869)
          ·
            refine ⟨1690843464681863549498201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4508915905818302798661869 1690843464681863549498201)
            ·
              refine ⟨1268132598511397662123651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690843464681863549498201 1268132598511397662123651)
              ·
                refine ⟨1902198897767096493185477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268132598511397662123651 1902198897767096493185477)
                ·
                  refine ⟨356662293331330592472277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902198897767096493185477 356662293331330592472277)
                  ·
                    rfl

theorem cell20_781422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_781422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781422 prefixEnd_781422 := by exact prefixLift 781422
  have htrace : WordTrace (prefixWord ++ tailWord_781422) baseStart_781422 baseEnd_781422 := by
    simpa [prefixWord, tailWord_781422, baseEnd_781422] using wordTrace_append hprefix tailTrace_781422
  have hstable : (prefixWord ++ tailWord_781422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781422).length < 2 ^ (prefixWord ++ tailWord_781422).sum := by decide
  have hdescent : baseEnd_781422 < baseStart_781422 := by decide
  rcases family_descends (prefixWord ++ tailWord_781422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781450 : List Nat := [3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_781450 : Nat := 118140960795 + 781450 * 2 ^ 59
def prefixEnd_781450 : Nat := 4983230072969 + 3 ^ 40 * 781450 * 2
def baseEnd_781450 : Nat := 118891691098095646512943

theorem tailTrace_781450 : CollatzResearch.WordTrace tailWord_781450 prefixEnd_781450 118891691098095646512943 := by
  unfold tailWord_781450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125455754736896469933451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19001215345965057253155869 7125455754736896469933451)
  ·
    refine ⟨10688183632105344704900177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7125455754736896469933451 10688183632105344704900177)
    ·
      refine ⟨8016137724079008528675133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10688183632105344704900177 8016137724079008528675133)
      ·
        refine ⟨3006051646529628198253175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8016137724079008528675133 3006051646529628198253175)
        ·
          refine ⟨4509077469794442297379763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006051646529628198253175 4509077469794442297379763)
          ·
            refine ⟨6763616204691663446069645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509077469794442297379763 6763616204691663446069645)
            ·
              refine ⟨2536356076759373792276117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6763616204691663446069645 2536356076759373792276117)
              ·
                refine ⟨118891691098095646512943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2536356076759373792276117 118891691098095646512943)
                ·
                  rfl

theorem cell20_781450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_781450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781450 prefixEnd_781450 := by exact prefixLift 781450
  have htrace : WordTrace (prefixWord ++ tailWord_781450) baseStart_781450 baseEnd_781450 := by
    simpa [prefixWord, tailWord_781450, baseEnd_781450] using wordTrace_append hprefix tailTrace_781450
  have hstable : (prefixWord ++ tailWord_781450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781450).length < 2 ^ (prefixWord ++ tailWord_781450).sum := by decide
  have hdescent : baseEnd_781450 < baseStart_781450 := by decide
  rcases family_descends (prefixWord ++ tailWord_781450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781477 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 2]
def baseStart_781477 : Nat := 118140960795 + 781477 * 2 ^ 59
def prefixEnd_781477 : Nat := 4983230072969 + 3 ^ 40 * 781477 * 2
def baseEnd_781477 : Nat := 356687396829994845638719

theorem tailTrace_781477 : CollatzResearch.WordTrace tailWord_781477 prefixEnd_781477 356687396829994845638719 := by
  unfold tailWord_781477
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502807789849769490966685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19001871859899846327311123 28502807789849769490966685)
  ·
    refine ⟨10688552921193663559112507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28502807789849769490966685 10688552921193663559112507)
    ·
      refine ⟨16032829381790495338668761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10688552921193663559112507 16032829381790495338668761)
      ·
        refine ⟨12024622036342871504001571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16032829381790495338668761 12024622036342871504001571)
        ·
          refine ⟨18036933054514307256002357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12024622036342871504001571 18036933054514307256002357)
          ·
            refine ⟨1690962473860716305250221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18036933054514307256002357 1690962473860716305250221)
            ·
              refine ⟨634110927697768614468833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690962473860716305250221 634110927697768614468833)
              ·
                refine ⟨475583195773326460851625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634110927697768614468833 475583195773326460851625)
                ·
                  refine ⟨356687396829994845638719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475583195773326460851625 356687396829994845638719)
                  ·
                    rfl

theorem cell20_781477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_781477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781477 prefixEnd_781477 := by exact prefixLift 781477
  have htrace : WordTrace (prefixWord ++ tailWord_781477) baseStart_781477 baseEnd_781477 := by
    simpa [prefixWord, tailWord_781477, baseEnd_781477] using wordTrace_append hprefix tailTrace_781477
  have hstable : (prefixWord ++ tailWord_781477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781477).length < 2 ^ (prefixWord ++ tailWord_781477).sum := by decide
  have hdescent : baseEnd_781477 < baseStart_781477 := by decide
  rcases family_descends (prefixWord ++ tailWord_781477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781505 : List Nat := [1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_781505 : Nat := 118140960795 + 781505 * 2 ^ 59
def prefixEnd_781505 : Nat := 4983230072969 + 3 ^ 40 * 781505 * 2
def baseEnd_781505 : Nat := 118900058930983730901757

theorem tailTrace_781505 : CollatzResearch.WordTrace tailWord_781505 prefixEnd_781505 118900058930983730901757 := by
  unfold tailWord_781505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28503829033748330272985969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19002552689165553515323979 28503829033748330272985969)
  ·
    refine ⟨21377871775311247704739477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28503829033748330272985969 21377871775311247704739477)
    ·
      refine ⟨1002087739467714736159663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21377871775311247704739477 1002087739467714736159663)
      ·
        refine ⟨1503131609201572104239495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002087739467714736159663 1503131609201572104239495)
        ·
          refine ⟨2254697413802358156359243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503131609201572104239495 2254697413802358156359243)
          ·
            refine ⟨3382046120703537234538865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254697413802358156359243 3382046120703537234538865)
            ·
              refine ⟨2536534590527652925904149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3382046120703537234538865 2536534590527652925904149)
              ·
                refine ⟨118900058930983730901757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2536534590527652925904149 118900058930983730901757)
                ·
                  rfl

theorem cell20_781505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_781505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781505 prefixEnd_781505 := by exact prefixLift 781505
  have htrace : WordTrace (prefixWord ++ tailWord_781505) baseStart_781505 baseEnd_781505 := by
    simpa [prefixWord, tailWord_781505, baseEnd_781505] using wordTrace_append hprefix tailTrace_781505
  have hstable : (prefixWord ++ tailWord_781505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781505).length < 2 ^ (prefixWord ++ tailWord_781505).sum := by decide
  have hdescent : baseEnd_781505 < baseStart_781505 := by decide
  rcases family_descends (prefixWord ++ tailWord_781505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781536 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_781536 : Nat := 118140960795 + 781536 * 2 ^ 59
def prefixEnd_781536 : Nat := 4983230072969 + 3 ^ 40 * 781536 * 2
def baseEnd_781536 : Nat := 356714326037652862671811

theorem tailTrace_781536 : CollatzResearch.WordTrace tailWord_781536 prefixEnd_781536 356714326037652862671811 := by
  unfold tailWord_781536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252479848318011283682231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19003306464424015044909641 14252479848318011283682231)
  ·
    refine ⟨21378719772477016925523347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252479848318011283682231 21378719772477016925523347)
    ·
      refine ⟨32068079658715525388285021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21378719772477016925523347 32068079658715525388285021)
      ·
        refine ⟨12025529872018322020606883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32068079658715525388285021 12025529872018322020606883)
        ·
          refine ⟨18038294808027483030910325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12025529872018322020606883 18038294808027483030910325)
          ·
            refine ⟨1691090138252576534147843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18038294808027483030910325 1691090138252576534147843)
            ·
              refine ⟨2536635207378864801221765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691090138252576534147843 2536635207378864801221765)
              ·
                refine ⟨475619101383537150229081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2536635207378864801221765 475619101383537150229081)
                ·
                  refine ⟨356714326037652862671811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475619101383537150229081 356714326037652862671811)
                  ·
                    rfl

theorem cell20_781536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_781536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781536 prefixEnd_781536 := by exact prefixLift 781536
  have htrace : WordTrace (prefixWord ++ tailWord_781536) baseStart_781536 baseEnd_781536 := by
    simpa [prefixWord, tailWord_781536, baseEnd_781536] using wordTrace_append hprefix tailTrace_781536
  have hstable : (prefixWord ++ tailWord_781536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781536).length < 2 ^ (prefixWord ++ tailWord_781536).sum := by decide
  have hdescent : baseEnd_781536 < baseStart_781536 := by decide
  rcases family_descends (prefixWord ++ tailWord_781536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781550 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_781550 : Nat := 118140960795 + 781550 * 2 ^ 59
def prefixEnd_781550 : Nat := 4983230072969 + 3 ^ 40 * 781550 * 2
def baseEnd_781550 : Nat := 356720716019131036205087

theorem tailTrace_781550 : CollatzResearch.WordTrace tailWord_781550 prefixEnd_781550 356720716019131036205087 := by
  unfold tailWord_781550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563183789823162869796763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19003646879056868638916069 3563183789823162869796763)
  ·
    refine ⟨5344775684734744304695145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563183789823162869796763 5344775684734744304695145)
    ·
      refine ⟨4008581763551058228521359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5344775684734744304695145 4008581763551058228521359)
      ·
        refine ⟨6012872645326587342782039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008581763551058228521359 6012872645326587342782039)
        ·
          refine ⟨9019308967989881014173059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012872645326587342782039 9019308967989881014173059)
          ·
            refine ⟨13528963451984821521259589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019308967989881014173059 13528963451984821521259589)
            ·
              refine ⟨2536680647247154035236173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13528963451984821521259589 2536680647247154035236173)
              ·
                refine ⟨951255242717682763213565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2536680647247154035236173 951255242717682763213565)
                ·
                  refine ⟨356720716019131036205087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951255242717682763213565 356720716019131036205087)
                  ·
                    rfl

theorem cell20_781550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_781550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781550 prefixEnd_781550 := by exact prefixLift 781550
  have htrace : WordTrace (prefixWord ++ tailWord_781550) baseStart_781550 baseEnd_781550 := by
    simpa [prefixWord, tailWord_781550, baseEnd_781550] using wordTrace_append hprefix tailTrace_781550
  have hstable : (prefixWord ++ tailWord_781550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781550).length < 2 ^ (prefixWord ++ tailWord_781550).sum := by decide
  have hdescent : baseEnd_781550 < baseStart_781550 := by decide
  rcases family_descends (prefixWord ++ tailWord_781550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781556 : List Nat := [2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_781556 : Nat := 118140960795 + 781556 * 2 ^ 59
def prefixEnd_781556 : Nat := 4983230072969 + 3 ^ 40 * 781556 * 2
def baseEnd_781556 : Nat := 118907818194207227335021

theorem tailTrace_781556 : CollatzResearch.WordTrace tailWord_781556 prefixEnd_781556 118907818194207227335021 := by
  unfold tailWord_781556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252844578281782991546261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19003792771042377322061681 14252844578281782991546261)
  ·
    refine ⟨668102089606958577728731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14252844578281782991546261 668102089606958577728731)
    ·
      refine ⟨1002153134410437866593097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668102089606958577728731 1002153134410437866593097)
      ·
        refine ⟨751614850807828399944823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1002153134410437866593097 751614850807828399944823)
        ·
          refine ⟨1127422276211742599917235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751614850807828399944823 1127422276211742599917235)
          ·
            refine ⟨1691133414317613899875853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127422276211742599917235 1691133414317613899875853)
            ·
              refine ⟨634175030369105212453445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1691133414317613899875853 634175030369105212453445)
              ·
                refine ⟨118907818194207227335021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634175030369105212453445 118907818194207227335021)
                ·
                  rfl

theorem cell20_781556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_781556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781556 prefixEnd_781556 := by exact prefixLift 781556
  have htrace : WordTrace (prefixWord ++ tailWord_781556) baseStart_781556 baseEnd_781556 := by
    simpa [prefixWord, tailWord_781556, baseEnd_781556] using wordTrace_append hprefix tailTrace_781556
  have hstable : (prefixWord ++ tailWord_781556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781556).length < 2 ^ (prefixWord ++ tailWord_781556).sum := by decide
  have hdescent : baseEnd_781556 < baseStart_781556 := by decide
  rcases family_descends (prefixWord ++ tailWord_781556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781570 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_781570 : Nat := 118140960795 + 781570 * 2 ^ 59
def prefixEnd_781570 : Nat := 4983230072969 + 3 ^ 40 * 781570 * 2
def baseEnd_781570 : Nat := 356729844564099855538339

theorem tailTrace_781570 : CollatzResearch.WordTrace tailWord_781570 prefixEnd_781570 356729844564099855538339 := by
  unfold tailWord_781570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126549944628211593525541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19004133185675230916068109 7126549944628211593525541)
  ·
    refine ⟨1336228114617789673786039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7126549944628211593525541 1336228114617789673786039)
    ·
      refine ⟨2004342171926684510679059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336228114617789673786039 2004342171926684510679059)
      ·
        refine ⟨3006513257890026766018589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004342171926684510679059 3006513257890026766018589)
        ·
          refine ⟨1127442471708760037256971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3006513257890026766018589 1127442471708760037256971)
          ·
            refine ⟨1691163707563140055885457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127442471708760037256971 1691163707563140055885457)
            ·
              refine ⟨1268372780672355041914093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691163707563140055885457 1268372780672355041914093)
              ·
                refine ⟨475639792752133140717785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268372780672355041914093 475639792752133140717785)
                ·
                  refine ⟨356729844564099855538339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475639792752133140717785 356729844564099855538339)
                  ·
                    rfl

theorem cell20_781570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_781570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781570 prefixEnd_781570 := by exact prefixLift 781570
  have htrace : WordTrace (prefixWord ++ tailWord_781570) baseStart_781570 baseEnd_781570 := by
    simpa [prefixWord, tailWord_781570, baseEnd_781570] using wordTrace_append hprefix tailTrace_781570
  have hstable : (prefixWord ++ tailWord_781570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781570).length < 2 ^ (prefixWord ++ tailWord_781570).sum := by decide
  have hdescent : baseEnd_781570 < baseStart_781570 := by decide
  rcases family_descends (prefixWord ++ tailWord_781570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781578 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_781578 : Nat := 118140960795 + 781578 * 2 ^ 59
def prefixEnd_781578 : Nat := 4983230072969 + 3 ^ 40 * 781578 * 2
def baseEnd_781578 : Nat := 356733495982087383271639

theorem tailTrace_781578 : CollatzResearch.WordTrace tailWord_781578 prefixEnd_781578 356733495982087383271639 := by
  unfold tailWord_781578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126622890620965935098347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19004327708322575826928925 7126622890620965935098347)
  ·
    refine ⟨10689934335931448902647521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126622890620965935098347 10689934335931448902647521)
    ·
      refine ⟨8017450751948586676985641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10689934335931448902647521 8017450751948586676985641)
      ·
        refine ⟨6013088063961440007739231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8017450751948586676985641 6013088063961440007739231)
        ·
          refine ⟨9019632095942160011608847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013088063961440007739231 9019632095942160011608847)
          ·
            refine ⟨13529448143913240017413271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019632095942160011608847 13529448143913240017413271)
            ·
              refine ⟨20294172215869860026119907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529448143913240017413271 20294172215869860026119907)
              ·
                refine ⟨30441258323804790039179861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20294172215869860026119907 30441258323804790039179861)
                ·
                  refine ⟨356733495982087383271639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30441258323804790039179861 356733495982087383271639)
                  ·
                    rfl

theorem cell20_781578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_781578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781578 prefixEnd_781578 := by exact prefixLift 781578
  have htrace : WordTrace (prefixWord ++ tailWord_781578) baseStart_781578 baseEnd_781578 := by
    simpa [prefixWord, tailWord_781578, baseEnd_781578] using wordTrace_append hprefix tailTrace_781578
  have hstable : (prefixWord ++ tailWord_781578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781578).length < 2 ^ (prefixWord ++ tailWord_781578).sum := by decide
  have hdescent : baseEnd_781578 < baseStart_781578 := by decide
  rcases family_descends (prefixWord ++ tailWord_781578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781585 : List Nat := [1, 2, 2, 1, 1, 4, 9]
def baseStart_781585 : Nat := 118140960795 + 781585 * 2 ^ 59
def prefixEnd_781585 : Nat := 4983230072969 + 3 ^ 40 * 781585 * 2
def baseEnd_781585 : Nat := 39637410108091830004253

theorem tailTrace_781585 : CollatzResearch.WordTrace tailWord_781585 prefixEnd_781585 39637410108091830004253 := by
  unfold tailWord_781585
  simp only [CollatzResearch.WordTrace]
  refine ⟨28506746873458503935898209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19004497915639002623932139 28506746873458503935898209)
  ·
    refine ⟨21380060155093877951923657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28506746873458503935898209 21380060155093877951923657)
    ·
      refine ⟨16035045116320408463942743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21380060155093877951923657 16035045116320408463942743)
      ·
        refine ⟨24052567674480612695914115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16035045116320408463942743 24052567674480612695914115)
        ·
          refine ⟨36078851511720919043871173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24052567674480612695914115 36078851511720919043871173)
          ·
            refine ⟨6764784658447672320725845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36078851511720919043871173 6764784658447672320725845)
            ·
              refine ⟨39637410108091830004253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6764784658447672320725845 39637410108091830004253)
              ·
                rfl

theorem cell20_781585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_781585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781585 prefixEnd_781585 := by exact prefixLift 781585
  have htrace : WordTrace (prefixWord ++ tailWord_781585) baseStart_781585 baseEnd_781585 := by
    simpa [prefixWord, tailWord_781585, baseEnd_781585] using wordTrace_append hprefix tailTrace_781585
  have hstable : (prefixWord ++ tailWord_781585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781585).length < 2 ^ (prefixWord ++ tailWord_781585).sum := by decide
  have hdescent : baseEnd_781585 < baseStart_781585 := by decide
  rcases family_descends (prefixWord ++ tailWord_781585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781605 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_781605 : Nat := 118140960795 + 781605 * 2 ^ 59
def prefixEnd_781605 : Nat := 4983230072969 + 3 ^ 40 * 781605 * 2
def baseEnd_781605 : Nat := 356745819517795289371529

theorem tailTrace_781605 : CollatzResearch.WordTrace tailWord_781605 prefixEnd_781605 356745819517795289371529 := by
  unfold tailWord_781605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28507476333386047351626269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19004984222257364901084179 28507476333386047351626269)
  ·
    refine ⟨10690303625019767756859851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28507476333386047351626269 10690303625019767756859851)
    ·
      refine ⟨16035455437529651635289777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690303625019767756859851 16035455437529651635289777)
      ·
        refine ⟨12026591578147238726467333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16035455437529651635289777 12026591578147238726467333)
        ·
          refine ⟨2254985920902607261212625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12026591578147238726467333 2254985920902607261212625)
          ·
            refine ⟨1691239440676955445909469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254985920902607261212625 1691239440676955445909469)
            ·
              refine ⟨634214790253858292216051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1691239440676955445909469 634214790253858292216051)
              ·
                refine ⟨951322185380787438324077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634214790253858292216051 951322185380787438324077)
                ·
                  refine ⟨356745819517795289371529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951322185380787438324077 356745819517795289371529)
                  ·
                    rfl

theorem cell20_781605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_781605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781605 prefixEnd_781605 := by exact prefixLift 781605
  have htrace : WordTrace (prefixWord ++ tailWord_781605) baseStart_781605 baseEnd_781605 := by
    simpa [prefixWord, tailWord_781605, baseEnd_781605] using wordTrace_append hprefix tailTrace_781605
  have hstable : (prefixWord ++ tailWord_781605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781605).length < 2 ^ (prefixWord ++ tailWord_781605).sum := by decide
  have hdescent : baseEnd_781605 < baseStart_781605 := by decide
  rcases family_descends (prefixWord ++ tailWord_781605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781616 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_781616 : Nat := 118140960795 + 781616 * 2 ^ 59
def prefixEnd_781616 : Nat := 4983230072969 + 3 ^ 40 * 781616 * 2
def baseEnd_781616 : Nat := 356750840217528140004817

theorem tailTrace_781616 : CollatzResearch.WordTrace tailWord_781616 prefixEnd_781616 356750840217528140004817 := by
  unfold tailWord_781616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14253938768173098115138351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19005251690897464153517801 14253938768173098115138351)
  ·
    refine ⟨21380908152259647172707527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14253938768173098115138351 21380908152259647172707527)
    ·
      refine ⟨32071362228389470759061291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21380908152259647172707527 32071362228389470759061291)
      ·
        refine ⟨48107043342584206138591937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32071362228389470759061291 48107043342584206138591937)
        ·
          refine ⟨36080282506938154603943953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48107043342584206138591937 36080282506938154603943953)
          ·
            refine ⟨27060211880203615952957965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36080282506938154603943953 27060211880203615952957965)
            ·
              refine ⟨10147579455076355982359237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27060211880203615952957965 10147579455076355982359237)
              ·
                refine ⟨1902671147826816746692357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10147579455076355982359237 1902671147826816746692357)
                ·
                  refine ⟨356750840217528140004817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902671147826816746692357 356750840217528140004817)
                  ·
                    rfl

theorem cell20_781616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_781616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781616 prefixEnd_781616 := by exact prefixLift 781616
  have htrace : WordTrace (prefixWord ++ tailWord_781616) baseStart_781616 baseEnd_781616 := by
    simpa [prefixWord, tailWord_781616, baseEnd_781616] using wordTrace_append hprefix tailTrace_781616
  have hstable : (prefixWord ++ tailWord_781616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781616).length < 2 ^ (prefixWord ++ tailWord_781616).sum := by decide
  have hdescent : baseEnd_781616 < baseStart_781616 := by decide
  rcases family_descends (prefixWord ++ tailWord_781616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781619 : List Nat := [1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_781619 : Nat := 118140960795 + 781619 * 2 ^ 59
def prefixEnd_781619 : Nat := 4983230072969 + 3 ^ 40 * 781619 * 2
def baseEnd_781619 : Nat := 118917403166424487634935

theorem tailTrace_781619 : CollatzResearch.WordTrace tailWord_781619 prefixEnd_781619 118917403166424487634935 := by
  unfold tailWord_781619
  simp only [CollatzResearch.WordTrace]
  refine ⟨28507986955335327742635911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19005324636890218495090607 28507986955335327742635911)
  ·
    refine ⟨42761980433002991613953867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28507986955335327742635911 42761980433002991613953867)
    ·
      refine ⟨64142970649504487420930801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42761980433002991613953867 64142970649504487420930801)
      ·
        refine ⟨48107227987128365565698101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64142970649504487420930801 48107227987128365565698101)
        ·
          refine ⟨4510052623793284271784197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48107227987128365565698101 4510052623793284271784197)
          ·
            refine ⟨845634866961240800959537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4510052623793284271784197 845634866961240800959537)
            ·
              refine ⟨634226150220930600719653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845634866961240800959537 634226150220930600719653)
              ·
                refine ⟨118917403166424487634935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634226150220930600719653 118917403166424487634935)
                ·
                  rfl

theorem cell20_781619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_781619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781619 prefixEnd_781619 := by exact prefixLift 781619
  have htrace : WordTrace (prefixWord ++ tailWord_781619) baseStart_781619 baseEnd_781619 := by
    simpa [prefixWord, tailWord_781619, baseEnd_781619] using wordTrace_append hprefix tailTrace_781619
  have hstable : (prefixWord ++ tailWord_781619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781619).length < 2 ^ (prefixWord ++ tailWord_781619).sum := by decide
  have hdescent : baseEnd_781619 < baseStart_781619 := by decide
  rcases family_descends (prefixWord ++ tailWord_781619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781664 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_781664 : Nat := 118140960795 + 781664 * 2 ^ 59
def prefixEnd_781664 : Nat := 4983230072969 + 3 ^ 40 * 781664 * 2
def baseEnd_781664 : Nat := 356772748725453306404621

theorem tailTrace_781664 : CollatzResearch.WordTrace tailWord_781664 prefixEnd_781664 356772748725453306404621 := by
  unfold tailWord_781664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254814120086150214012023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19006418826781533618682697 14254814120086150214012023)
  ·
    refine ⟨21382221180129225321018035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14254814120086150214012023 21382221180129225321018035)
    ·
      refine ⟨32073331770193837981527053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21382221180129225321018035 32073331770193837981527053)
      ·
        refine ⟨12027499413822689243072645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32073331770193837981527053 12027499413822689243072645)
        ·
          refine ⟨2255156140091754233076121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12027499413822689243072645 2255156140091754233076121)
          ·
            refine ⟨1691367105068815674807091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255156140091754233076121 1691367105068815674807091)
            ·
              refine ⟨2537050657603223512210637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691367105068815674807091 2537050657603223512210637)
              ·
                refine ⟨951393996601208817078989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537050657603223512210637 951393996601208817078989)
                ·
                  refine ⟨356772748725453306404621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951393996601208817078989 356772748725453306404621)
                  ·
                    rfl

theorem cell20_781664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_781664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781664 prefixEnd_781664 := by exact prefixLift 781664
  have htrace : WordTrace (prefixWord ++ tailWord_781664) baseStart_781664 baseEnd_781664 := by
    simpa [prefixWord, tailWord_781664, baseEnd_781664] using wordTrace_append hprefix tailTrace_781664
  have hstable : (prefixWord ++ tailWord_781664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781664).length < 2 ^ (prefixWord ++ tailWord_781664).sum := by decide
  have hdescent : baseEnd_781664 < baseStart_781664 := by decide
  rcases family_descends (prefixWord ++ tailWord_781664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781698 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_781698 : Nat := 118140960795 + 781698 * 2 ^ 59
def prefixEnd_781698 : Nat := 4983230072969 + 3 ^ 40 * 781698 * 2
def baseEnd_781698 : Nat := 356788267251900299271149

theorem tailTrace_781698 : CollatzResearch.WordTrace tailWord_781698 prefixEnd_781698 356788267251900299271149 := by
  unfold tailWord_781698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127717080512281058690437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19007245548032749489841165 7127717080512281058690437)
  ·
    refine ⟨1336446952596052698504457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7127717080512281058690437 1336446952596052698504457)
    ·
      refine ⟨1002335214447039523878343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1336446952596052698504457 1002335214447039523878343)
      ·
        refine ⟨1503502821670559285817515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002335214447039523878343 1503502821670559285817515)
        ·
          refine ⟨2255254232505838928726273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503502821670559285817515 2255254232505838928726273)
          ·
            refine ⟨1691440674379379196544705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255254232505838928726273 1691440674379379196544705)
            ·
              refine ⟨1268580505784534397408529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691440674379379196544705 1268580505784534397408529)
              ·
                refine ⟨951435379338400798056397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268580505784534397408529 951435379338400798056397)
                ·
                  refine ⟨356788267251900299271149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951435379338400798056397 356788267251900299271149)
                  ·
                    rfl

theorem cell20_781698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_781698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781698 prefixEnd_781698 := by exact prefixLift 781698
  have htrace : WordTrace (prefixWord ++ tailWord_781698) baseStart_781698 baseEnd_781698 := by
    simpa [prefixWord, tailWord_781698, baseEnd_781698] using wordTrace_append hprefix tailTrace_781698
  have hstable : (prefixWord ++ tailWord_781698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781698).length < 2 ^ (prefixWord ++ tailWord_781698).sum := by decide
  have hdescent : baseEnd_781698 < baseStart_781698 := by decide
  rcases family_descends (prefixWord ++ tailWord_781698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781699 : List Nat := [1, 1, 1, 3, 5, 9]
def baseStart_781699 : Nat := 118140960795 + 781699 * 2 ^ 59
def prefixEnd_781699 : Nat := 4983230072969 + 3 ^ 40 * 781699 * 2
def baseEnd_781699 : Nat := 13214397173301805193993

theorem tailTrace_781699 : CollatzResearch.WordTrace tailWord_781699 prefixEnd_781699 13214397173301805193993 := by
  unfold tailWord_781699
  simp only [CollatzResearch.WordTrace]
  refine ⟨28510904795045501405548151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19007269863363667603698767 28510904795045501405548151)
  ·
    refine ⟨42766357192568252108322227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28510904795045501405548151 42766357192568252108322227)
    ·
      refine ⟨64149535788852378162483341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42766357192568252108322227 64149535788852378162483341)
      ·
        refine ⟨24056075920819641810931253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64149535788852378162483341 24056075920819641810931253)
        ·
          refine ⟨2255257117576841419774805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24056075920819641810931253 2255257117576841419774805)
          ·
            refine ⟨13214397173301805193993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2255257117576841419774805 13214397173301805193993)
            ·
              rfl

theorem cell20_781699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_781699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781699 prefixEnd_781699 := by exact prefixLift 781699
  have htrace : WordTrace (prefixWord ++ tailWord_781699) baseStart_781699 baseEnd_781699 := by
    simpa [prefixWord, tailWord_781699, baseEnd_781699] using wordTrace_append hprefix tailTrace_781699
  have hstable : (prefixWord ++ tailWord_781699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781699).length < 2 ^ (prefixWord ++ tailWord_781699).sum := by decide
  have hdescent : baseEnd_781699 < baseStart_781699 := by decide
  rcases family_descends (prefixWord ++ tailWord_781699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781764 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_781764 : Nat := 118140960795 + 781764 * 2 ^ 59
def prefixEnd_781764 : Nat := 4983230072969 + 3 ^ 40 * 781764 * 2
def baseEnd_781764 : Nat := 356818391450297403070879

theorem tailTrace_781764 : CollatzResearch.WordTrace tailWord_781764 prefixEnd_781764 356818391450297403070879 := by
  unfold tailWord_781764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14256637769905008753332173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19008850359873345004442897 14256637769905008753332173)
  ·
    refine ⟨5346239163714378282499565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14256637769905008753332173 5346239163714378282499565)
    ·
      refine ⟨2004839686392891855937337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5346239163714378282499565 2004839686392891855937337)
      ·
        refine ⟨1503629764794668891953003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004839686392891855937337 1503629764794668891953003)
        ·
          refine ⟨2255444647192003337929505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503629764794668891953003 2255444647192003337929505)
          ·
            refine ⟨1691583485394002503447129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255444647192003337929505 1691583485394002503447129)
            ·
              refine ⟨1268687614045501877585347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691583485394002503447129 1268687614045501877585347)
              ·
                refine ⟨1903031421068252816378021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268687614045501877585347 1903031421068252816378021)
                ·
                  refine ⟨356818391450297403070879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903031421068252816378021 356818391450297403070879)
                  ·
                    rfl

theorem cell20_781764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_781764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781764 prefixEnd_781764 := by exact prefixLift 781764
  have htrace : WordTrace (prefixWord ++ tailWord_781764) baseStart_781764 baseEnd_781764 := by
    simpa [prefixWord, tailWord_781764, baseEnd_781764] using wordTrace_append hprefix tailTrace_781764
  have hstable : (prefixWord ++ tailWord_781764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781764).length < 2 ^ (prefixWord ++ tailWord_781764).sum := by decide
  have hdescent : baseEnd_781764 < baseStart_781764 := by decide
  rcases family_descends (prefixWord ++ tailWord_781764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781799 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_781799 : Nat := 118140960795 + 781799 * 2 ^ 59
def prefixEnd_781799 : Nat := 4983230072969 + 3 ^ 40 * 781799 * 2
def baseEnd_781799 : Nat := 356834366403992836904069

theorem tailTrace_781799 : CollatzResearch.WordTrace tailWord_781799 prefixEnd_781799 356834366403992836904069 := by
  unfold tailWord_781799
  simp only [CollatzResearch.WordTrace]
  refine ⟨28514552094683218484188451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19009701396455478989458967 28514552094683218484188451)
  ·
    refine ⟨42771828142024827726282677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28514552094683218484188451 42771828142024827726282677)
    ·
      refine ⟨4009858888314827599339001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42771828142024827726282677 4009858888314827599339001)
      ·
        refine ⟨3007394166236120699504251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4009858888314827599339001 3007394166236120699504251)
        ·
          refine ⟨4511091249354181049256377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007394166236120699504251 4511091249354181049256377)
          ·
            refine ⟨3383318437015635786942283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4511091249354181049256377 3383318437015635786942283)
            ·
              refine ⟨5074977655523453680413425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383318437015635786942283 5074977655523453680413425)
              ·
                refine ⟨3806233241642590260310069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5074977655523453680413425 3806233241642590260310069)
                ·
                  refine ⟨356834366403992836904069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806233241642590260310069 356834366403992836904069)
                  ·
                    rfl

theorem cell20_781799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_781799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781799 prefixEnd_781799 := by exact prefixLift 781799
  have htrace : WordTrace (prefixWord ++ tailWord_781799) baseStart_781799 baseEnd_781799 := by
    simpa [prefixWord, tailWord_781799, baseEnd_781799] using wordTrace_append hprefix tailTrace_781799
  have hstable : (prefixWord ++ tailWord_781799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781799).length < 2 ^ (prefixWord ++ tailWord_781799).sum := by decide
  have hdescent : baseEnd_781799 < baseStart_781799 := by decide
  rcases family_descends (prefixWord ++ tailWord_781799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781861 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 2]
def baseStart_781861 : Nat := 118140960795 + 781861 * 2 ^ 59
def prefixEnd_781861 : Nat := 4983230072969 + 3 ^ 40 * 781861 * 2
def baseEnd_781861 : Nat := 356862664893396176837149

theorem tailTrace_781861 : CollatzResearch.WordTrace tailWord_781861 prefixEnd_781861 356862664893396176837149 := by
  unfold tailWord_781861
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516813420458603072945437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011208946972402048630291 28516813420458603072945437)
  ·
    refine ⟨10693805032671976152354539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28516813420458603072945437 10693805032671976152354539)
    ·
      refine ⟨16040707549007964228531809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693805032671976152354539 16040707549007964228531809)
      ·
        refine ⟨12030530661755973171398857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16040707549007964228531809 12030530661755973171398857)
        ·
          refine ⟨9022897996316979878549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12030530661755973171398857 9022897996316979878549143)
          ·
            refine ⟨13534346994475469817823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022897996316979878549143 13534346994475469817823715)
            ·
              refine ⟨20301520491713204726735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13534346994475469817823715 20301520491713204726735573)
              ·
                refine ⟨475816886524528235782865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20301520491713204726735573 475816886524528235782865)
                ·
                  refine ⟨356862664893396176837149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475816886524528235782865 356862664893396176837149)
                  ·
                    rfl

theorem cell20_781861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_781861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781861 prefixEnd_781861 := by exact prefixLift 781861
  have htrace : WordTrace (prefixWord ++ tailWord_781861) baseStart_781861 baseEnd_781861 := by
    simpa [prefixWord, tailWord_781861, baseEnd_781861] using wordTrace_append hprefix tailTrace_781861
  have hstable : (prefixWord ++ tailWord_781861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781861).length < 2 ^ (prefixWord ++ tailWord_781861).sum := by decide
  have hdescent : baseEnd_781861 < baseStart_781861 := by decide
  rcases family_descends (prefixWord ++ tailWord_781861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781875 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_781875 : Nat := 118140960795 + 781875 * 2 ^ 59
def prefixEnd_781875 : Nat := 4983230072969 + 3 ^ 40 * 781875 * 2
def baseEnd_781875 : Nat := 356869054874874350370425

theorem tailTrace_781875 : CollatzResearch.WordTrace tailWord_781875 prefixEnd_781875 356869054874874350370425 := by
  unfold tailWord_781875
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517324042407883463955079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011549361605255642636719 28517324042407883463955079)
  ·
    refine ⟨42775986063611825195932619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28517324042407883463955079 42775986063611825195932619)
    ·
      refine ⟨64163979095417737793898929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42775986063611825195932619 64163979095417737793898929)
      ·
        refine ⟨48122984321563303345424197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64163979095417737793898929 48122984321563303345424197)
        ·
          refine ⟨9023059560293119377267037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48122984321563303345424197 9023059560293119377267037)
          ·
            refine ⟨3383647335109919766475139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9023059560293119377267037 3383647335109919766475139)
            ·
              refine ⟨5075471002664879649712709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383647335109919766475139 5075471002664879649712709)
              ·
                refine ⟨951650812999664934321133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5075471002664879649712709 951650812999664934321133)
                ·
                  refine ⟨356869054874874350370425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951650812999664934321133 356869054874874350370425)
                  ·
                    rfl

theorem cell20_781875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_781875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781875 prefixEnd_781875 := by exact prefixLift 781875
  have htrace : WordTrace (prefixWord ++ tailWord_781875) baseStart_781875 baseEnd_781875 := by
    simpa [prefixWord, tailWord_781875, baseEnd_781875] using wordTrace_append hprefix tailTrace_781875
  have hstable : (prefixWord ++ tailWord_781875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781875).length < 2 ^ (prefixWord ++ tailWord_781875).sum := by decide
  have hdescent : baseEnd_781875 < baseStart_781875 := by decide
  rcases family_descends (prefixWord ++ tailWord_781875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781882 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_781882 : Nat := 118140960795 + 781882 * 2 ^ 59
def prefixEnd_781882 : Nat := 4983230072969 + 3 ^ 40 * 781882 * 2
def baseEnd_781882 : Nat := 356872249865613437137063

theorem tailTrace_781882 : CollatzResearch.WordTrace tailWord_781882 prefixEnd_781882 356872249865613437137063 := by
  unfold tailWord_781882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129394838345630914864975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19011719568921682439639933 7129394838345630914864975)
  ·
    refine ⟨10694092257518446372297463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7129394838345630914864975 10694092257518446372297463)
    ·
      refine ⟨16041138386277669558446195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694092257518446372297463 16041138386277669558446195)
      ·
        refine ⟨24061707579416504337669293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16041138386277669558446195 24061707579416504337669293)
        ·
          refine ⟨9023140342281189126625985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24061707579416504337669293 9023140342281189126625985)
          ·
            refine ⟨6767355256710891844969489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9023140342281189126625985 6767355256710891844969489)
            ·
              refine ⟨5075516442533168883727117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6767355256710891844969489 5075516442533168883727117)
              ·
                refine ⟨1903318665949938331397669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5075516442533168883727117 1903318665949938331397669)
                ·
                  refine ⟨356872249865613437137063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903318665949938331397669 356872249865613437137063)
                  ·
                    rfl

theorem cell20_781882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_781882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781882 prefixEnd_781882 := by exact prefixLift 781882
  have htrace : WordTrace (prefixWord ++ tailWord_781882) baseStart_781882 baseEnd_781882 := by
    simpa [prefixWord, tailWord_781882, baseEnd_781882] using wordTrace_append hprefix tailTrace_781882
  have hstable : (prefixWord ++ tailWord_781882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781882).length < 2 ^ (prefixWord ++ tailWord_781882).sum := by decide
  have hdescent : baseEnd_781882 < baseStart_781882 := by decide
  rcases family_descends (prefixWord ++ tailWord_781882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781885 : List Nat := [1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_781885 : Nat := 118140960795 + 781885 * 2 ^ 59
def prefixEnd_781885 : Nat := 4983230072969 + 3 ^ 40 * 781885 * 2
def baseEnd_781885 : Nat := 118957873049119586679017

theorem tailTrace_781885 : CollatzResearch.WordTrace tailWord_781885 prefixEnd_781885 118957873049119586679017 := by
  unfold tailWord_781885
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517688772371655171819109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011792514914436781212739 28517688772371655171819109)
  ·
    refine ⟨5347066644819685344716083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28517688772371655171819109 5347066644819685344716083)
    ·
      refine ⟨8020599967229528017074125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347066644819685344716083 8020599967229528017074125)
      ·
        refine ⟨3007724987711073006402797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8020599967229528017074125 3007724987711073006402797)
        ·
          refine ⟨1127896870391652377401049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3007724987711073006402797 1127896870391652377401049)
          ·
            refine ⟨845922652793739283050787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127896870391652377401049 845922652793739283050787)
            ·
              refine ⟨1268883979190608924576181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845922652793739283050787 1268883979190608924576181)
              ·
                refine ⟨118957873049119586679017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1268883979190608924576181 118957873049119586679017)
                ·
                  rfl

theorem cell20_781885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_781885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781885 prefixEnd_781885 := by exact prefixLift 781885
  have htrace : WordTrace (prefixWord ++ tailWord_781885) baseStart_781885 baseEnd_781885 := by
    simpa [prefixWord, tailWord_781885, baseEnd_781885] using wordTrace_append hprefix tailTrace_781885
  have hstable : (prefixWord ++ tailWord_781885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781885).length < 2 ^ (prefixWord ++ tailWord_781885).sum := by decide
  have hdescent : baseEnd_781885 < baseStart_781885 := by decide
  rcases family_descends (prefixWord ++ tailWord_781885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781896 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_781896 : Nat := 118140960795 + 781896 * 2 ^ 59
def prefixEnd_781896 : Nat := 4983230072969 + 3 ^ 40 * 781896 * 2
def baseEnd_781896 : Nat := 356878639847091610670339

theorem tailTrace_781896 : CollatzResearch.WordTrace tailWord_781896 prefixEnd_781896 356878639847091610670339 := by
  unfold tailWord_781896
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259044987665902025234771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19012059983554536033646361 14259044987665902025234771)
  ·
    refine ⟨21388567481498853037852157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14259044987665902025234771 21388567481498853037852157)
    ·
      refine ⟨8020712805562069889194559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21388567481498853037852157 8020712805562069889194559)
      ·
        refine ⟨12031069208343104833791839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020712805562069889194559 12031069208343104833791839)
        ·
          refine ⟨18046603812514657250687759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031069208343104833791839 18046603812514657250687759)
          ·
            refine ⟨27069905718771985876031639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18046603812514657250687759 27069905718771985876031639)
            ·
              refine ⟨40604858578157978814047459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27069905718771985876031639 40604858578157978814047459)
              ·
                refine ⟨60907287867236968221071189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40604858578157978814047459 60907287867236968221071189)
                ·
                  refine ⟨356878639847091610670339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60907287867236968221071189 356878639847091610670339)
                  ·
                    rfl

theorem cell20_781896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_781896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781896 prefixEnd_781896 := by exact prefixLift 781896
  have htrace : WordTrace (prefixWord ++ tailWord_781896) baseStart_781896 baseEnd_781896 := by
    simpa [prefixWord, tailWord_781896, baseEnd_781896] using wordTrace_append hprefix tailTrace_781896
  have hstable : (prefixWord ++ tailWord_781896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781896).length < 2 ^ (prefixWord ++ tailWord_781896).sum := by decide
  have hdescent : baseEnd_781896 < baseStart_781896 := by decide
  rcases family_descends (prefixWord ++ tailWord_781896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781916 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_781916 : Nat := 118140960795 + 781916 * 2 ^ 59
def prefixEnd_781916 : Nat := 4983230072969 + 3 ^ 40 * 781916 * 2
def baseEnd_781916 : Nat := 356887768392060430003591

theorem tailTrace_781916 : CollatzResearch.WordTrace tailWord_781916 prefixEnd_781916 356887768392060430003591 := by
  unfold tailWord_781916
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259409717629673733098801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19012546290172898310798401 14259409717629673733098801)
  ·
    refine ⟨10694557288222255299824101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14259409717629673733098801 10694557288222255299824101)
    ·
      refine ⟨2005229491541672868717019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10694557288222255299824101 2005229491541672868717019)
      ·
        refine ⟨3007844237312509303075529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005229491541672868717019 3007844237312509303075529)
        ·
          refine ⟨2255883177984381977306647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007844237312509303075529 2255883177984381977306647)
          ·
            refine ⟨3383824766976572965959971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255883177984381977306647 3383824766976572965959971)
            ·
              refine ⟨5075737150464859448939957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383824766976572965959971 5075737150464859448939957)
              ·
                refine ⟨475850357856080573338121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5075737150464859448939957 475850357856080573338121)
                ·
                  refine ⟨356887768392060430003591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475850357856080573338121 356887768392060430003591)
                  ·
                    rfl

theorem cell20_781916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_781916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781916 prefixEnd_781916 := by exact prefixLift 781916
  have htrace : WordTrace (prefixWord ++ tailWord_781916) baseStart_781916 baseEnd_781916 := by
    simpa [prefixWord, tailWord_781916, baseEnd_781916] using wordTrace_append hprefix tailTrace_781916
  have hstable : (prefixWord ++ tailWord_781916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781916).length < 2 ^ (prefixWord ++ tailWord_781916).sum := by decide
  have hdescent : baseEnd_781916 < baseStart_781916 := by decide
  rcases family_descends (prefixWord ++ tailWord_781916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781930 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_781930 : Nat := 118140960795 + 781930 * 2 ^ 59
def prefixEnd_781930 : Nat := 4983230072969 + 3 ^ 40 * 781930 * 2
def baseEnd_781930 : Nat := 356894158373538603536867

theorem tailTrace_781930 : CollatzResearch.WordTrace tailWord_781930 prefixEnd_781930 356894158373538603536867 := by
  unfold tailWord_781930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129832514302156964301811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19012886704805751904804829 7129832514302156964301811)
  ·
    refine ⟨10694748771453235446452717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7129832514302156964301811 10694748771453235446452717)
    ·
      refine ⟨4010530789294963292419769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10694748771453235446452717 4010530789294963292419769)
      ·
        refine ⟨3007898091971222469314827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010530789294963292419769 3007898091971222469314827)
        ·
          refine ⟨4511847137956833703972241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007898091971222469314827 4511847137956833703972241)
          ·
            refine ⟨3383885353467625277979181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4511847137956833703972241 3383885353467625277979181)
            ·
              refine ⟨1268957007550359479242193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3383885353467625277979181 1268957007550359479242193)
              ·
                refine ⟨951717755662769609431645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268957007550359479242193 951717755662769609431645)
                ·
                  refine ⟨356894158373538603536867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951717755662769609431645 356894158373538603536867)
                  ·
                    rfl

theorem cell20_781930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_781930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781930 prefixEnd_781930 := by exact prefixLift 781930
  have htrace : WordTrace (prefixWord ++ tailWord_781930) baseStart_781930 baseEnd_781930 := by
    simpa [prefixWord, tailWord_781930, baseEnd_781930] using wordTrace_append hprefix tailTrace_781930
  have hstable : (prefixWord ++ tailWord_781930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781930).length < 2 ^ (prefixWord ++ tailWord_781930).sum := by decide
  have hdescent : baseEnd_781930 < baseStart_781930 := by decide
  rcases family_descends (prefixWord ++ tailWord_781930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781982 : List Nat := [4, 3, 1, 1, 1, 2, 8]
def baseStart_781982 : Nat := 118140960795 + 781982 * 2 ^ 59
def prefixEnd_781982 : Nat := 4983230072969 + 3 ^ 40 * 781982 * 2
def baseEnd_781982 : Nat := 39657543621161948200369

theorem tailTrace_781982 : CollatzResearch.WordTrace tailWord_781982 prefixEnd_781982 39657543621161948200369 := by
  unfold tailWord_781982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565153331627530092262525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19014151102013493825400133 3565153331627530092262525)
  ·
    refine ⟨1336932499360323784598447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3565153331627530092262525 1336932499360323784598447)
    ·
      refine ⟨2005398749040485676897671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336932499360323784598447 2005398749040485676897671)
      ·
        refine ⟨3008098123560728515346507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005398749040485676897671 3008098123560728515346507)
        ·
          refine ⟨4512147185341092773019761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008098123560728515346507 4512147185341092773019761)
          ·
            refine ⟨3384110389005819579764821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512147185341092773019761 3384110389005819579764821)
            ·
              refine ⟨39657543621161948200369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3384110389005819579764821 39657543621161948200369)
              ·
                rfl

theorem cell20_781982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_781982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_781982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_781982 prefixEnd_781982 := by exact prefixLift 781982
  have htrace : WordTrace (prefixWord ++ tailWord_781982) baseStart_781982 baseEnd_781982 := by
    simpa [prefixWord, tailWord_781982, baseEnd_781982] using wordTrace_append hprefix tailTrace_781982
  have hstable : (prefixWord ++ tailWord_781982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781982).length < 2 ^ (prefixWord ++ tailWord_781982).sum := by decide
  have hdescent : baseEnd_781982 < baseStart_781982 := by decide
  rcases family_descends (prefixWord ++ tailWord_781982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782003 : List Nat := [1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_782003 : Nat := 118140960795 + 782003 * 2 ^ 59
def prefixEnd_782003 : Nat := 4983230072969 + 3 ^ 40 * 782003 * 2
def baseEnd_782003 : Nat := 118975825854224931367745

theorem tailTrace_782003 : CollatzResearch.WordTrace tailWord_782003 prefixEnd_782003 118975825854224931367745 := by
  unfold tailWord_782003
  simp only [CollatzResearch.WordTrace]
  refine ⟨28521992585944161324614663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19014661723962774216409775 28521992585944161324614663)
  ·
    refine ⟨42782988878916241986921995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28521992585944161324614663 42782988878916241986921995)
    ·
      refine ⟨64174483318374362980382993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42782988878916241986921995 64174483318374362980382993)
      ·
        refine ⟨48130862488780772235287245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64174483318374362980382993 48130862488780772235287245)
        ·
          refine ⟨18049073433292789588232717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48130862488780772235287245 18049073433292789588232717)
          ·
            refine ⟨6768402537484796095587269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18049073433292789588232717 6768402537484796095587269)
            ·
              refine ⟨1269075475778399267922613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6768402537484796095587269 1269075475778399267922613)
              ·
                refine ⟨118975825854224931367745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1269075475778399267922613 118975825854224931367745)
                ·
                  rfl

theorem cell20_782003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_782003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782003 prefixEnd_782003 := by exact prefixLift 782003
  have htrace : WordTrace (prefixWord ++ tailWord_782003) baseStart_782003 baseEnd_782003 := by
    simpa [prefixWord, tailWord_782003, baseEnd_782003] using wordTrace_append hprefix tailTrace_782003
  have hstable : (prefixWord ++ tailWord_782003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782003).length < 2 ^ (prefixWord ++ tailWord_782003).sum := by decide
  have hdescent : baseEnd_782003 < baseStart_782003 := by decide
  rcases family_descends (prefixWord ++ tailWord_782003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782048 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_782048 : Nat := 118140960795 + 782048 * 2 ^ 59
def prefixEnd_782048 : Nat := 4983230072969 + 3 ^ 40 * 782048 * 2
def baseEnd_782048 : Nat := 356948016788854637603051

theorem tailTrace_782048 : CollatzResearch.WordTrace tailWord_782048 prefixEnd_782048 356948016788854637603051 := by
  unfold tailWord_782048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261816935390567005001399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19015755913854089340001865 14261816935390567005001399)
  ·
    refine ⟨21392725403085850507502099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14261816935390567005001399 21392725403085850507502099)
    ·
      refine ⟨32089088104628775761253149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21392725403085850507502099 32089088104628775761253149)
      ·
        refine ⟨12033408039235790910469931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32089088104628775761253149 12033408039235790910469931)
        ·
          refine ⟨18050112058853686365704897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12033408039235790910469931 18050112058853686365704897)
          ·
            refine ⟨13537584044140264774278673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18050112058853686365704897 13537584044140264774278673)
            ·
              refine ⟨10153188033105198580709005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13537584044140264774278673 10153188033105198580709005)
              ·
                refine ⟨3807445512414449467765877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10153188033105198580709005 3807445512414449467765877)
                ·
                  refine ⟨356948016788854637603051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807445512414449467765877 356948016788854637603051)
                  ·
                    rfl

theorem cell20_782048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_782048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782048 prefixEnd_782048 := by exact prefixLift 782048
  have htrace : WordTrace (prefixWord ++ tailWord_782048) baseStart_782048 baseEnd_782048 := by
    simpa [prefixWord, tailWord_782048, baseEnd_782048] using wordTrace_append hprefix tailTrace_782048
  have hstable : (prefixWord ++ tailWord_782048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782048).length < 2 ^ (prefixWord ++ tailWord_782048).sum := by decide
  have hdescent : baseEnd_782048 < baseStart_782048 := by decide
  rcases family_descends (prefixWord ++ tailWord_782048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782065 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_782065 : Nat := 118140960795 + 782065 * 2 ^ 59
def prefixEnd_782065 : Nat := 4983230072969 + 3 ^ 40 * 782065 * 2
def baseEnd_782065 : Nat := 356955776052078134036315

theorem tailTrace_782065 : CollatzResearch.WordTrace tailWord_782065 prefixEnd_782065 356955776052078134036315 := by
  unfold tailWord_782065
  simp only [CollatzResearch.WordTrace]
  refine ⟨28524253911719545913371649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19016169274479697275581099 28524253911719545913371649)
  ·
    refine ⟨21393190433789659435028737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28524253911719545913371649 21393190433789659435028737)
    ·
      refine ⟨16044892825342244576271553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21393190433789659435028737 16044892825342244576271553)
      ·
        refine ⟨12033669619006683432203665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16044892825342244576271553 12033669619006683432203665)
        ·
          refine ⟨9025252214255012574152749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033669619006683432203665 9025252214255012574152749)
          ·
            refine ⟨3384469580345629715307281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9025252214255012574152749 3384469580345629715307281)
            ·
              refine ⟨2538352185259222286480461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384469580345629715307281 2538352185259222286480461)
              ·
                refine ⟨951882069472208357430173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538352185259222286480461 951882069472208357430173)
                ·
                  refine ⟨356955776052078134036315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951882069472208357430173 356955776052078134036315)
                  ·
                    rfl

theorem cell20_782065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_782065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782065 prefixEnd_782065 := by exact prefixLift 782065
  have htrace : WordTrace (prefixWord ++ tailWord_782065) baseStart_782065 baseEnd_782065 := by
    simpa [prefixWord, tailWord_782065, baseEnd_782065] using wordTrace_append hprefix tailTrace_782065
  have hstable : (prefixWord ++ tailWord_782065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782065).length < 2 ^ (prefixWord ++ tailWord_782065).sum := by decide
  have hdescent : baseEnd_782065 < baseStart_782065 := by decide
  rcases family_descends (prefixWord ++ tailWord_782065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782068 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_782068 : Nat := 118140960795 + 782068 * 2 ^ 59
def prefixEnd_782068 : Nat := 4983230072969 + 3 ^ 40 * 782068 * 2
def baseEnd_782068 : Nat := 356957145333823456936303

theorem tailTrace_782068 : CollatzResearch.WordTrace tailWord_782068 prefixEnd_782068 356957145333823456936303 := by
  unfold tailWord_782068
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262181665354338712865429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19016242220472451617153905 14262181665354338712865429)
  ·
    refine ⟨668539765563484627165567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14262181665354338712865429 668539765563484627165567)
    ·
      refine ⟨1002809648345226940748351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668539765563484627165567 1002809648345226940748351)
      ·
        refine ⟨1504214472517840411122527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002809648345226940748351 1504214472517840411122527)
        ·
          refine ⟨2256321708776760616683791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504214472517840411122527 2256321708776760616683791)
          ·
            refine ⟨3384482563165140925025687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256321708776760616683791 3384482563165140925025687)
            ·
              refine ⟨5076723844747711387538531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384482563165140925025687 5076723844747711387538531)
              ·
                refine ⟨7615085767121567081307797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076723844747711387538531 7615085767121567081307797)
                ·
                  refine ⟨356957145333823456936303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7615085767121567081307797 356957145333823456936303)
                  ·
                    rfl

theorem cell20_782068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_782068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782068 prefixEnd_782068 := by exact prefixLift 782068
  have htrace : WordTrace (prefixWord ++ tailWord_782068) baseStart_782068 baseEnd_782068 := by
    simpa [prefixWord, tailWord_782068, baseEnd_782068] using wordTrace_append hprefix tailTrace_782068
  have hstable : (prefixWord ++ tailWord_782068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782068).length < 2 ^ (prefixWord ++ tailWord_782068).sum := by decide
  have hdescent : baseEnd_782068 < baseStart_782068 := by decide
  rcases family_descends (prefixWord ++ tailWord_782068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782103 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_782103 : Nat := 118140960795 + 782103 * 2 ^ 59
def prefixEnd_782103 : Nat := 4983230072969 + 3 ^ 40 * 782103 * 2
def baseEnd_782103 : Nat := 356973120287518890769493

theorem tailTrace_782103 : CollatzResearch.WordTrace tailWord_782103 prefixEnd_782103 356973120287518890769493 := by
  unfold tailWord_782103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525639885581878403254963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19017093257054585602169975 28525639885581878403254963)
  ·
    refine ⟨42788459828372817604882445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28525639885581878403254963 42788459828372817604882445)
    ·
      refine ⟨16045672435639806601830917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42788459828372817604882445 16045672435639806601830917)
      ·
        refine ⟨3008563581682463737843297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16045672435639806601830917 3008563581682463737843297)
        ·
          refine ⟨2256422686261847803382473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008563581682463737843297 2256422686261847803382473)
          ·
            refine ⟨1692317014696385852536855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256422686261847803382473 1692317014696385852536855)
            ·
              refine ⟨2538475522044578778805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692317014696385852536855 2538475522044578778805283)
              ·
                refine ⟨3807713283066868168207925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538475522044578778805283 3807713283066868168207925)
                ·
                  refine ⟨356973120287518890769493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807713283066868168207925 356973120287518890769493)
                  ·
                    rfl

theorem cell20_782103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_782103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782103 prefixEnd_782103 := by exact prefixLift 782103
  have htrace : WordTrace (prefixWord ++ tailWord_782103) baseStart_782103 baseEnd_782103 := by
    simpa [prefixWord, tailWord_782103, baseEnd_782103] using wordTrace_append hprefix tailTrace_782103
  have hstable : (prefixWord ++ tailWord_782103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782103).length < 2 ^ (prefixWord ++ tailWord_782103).sum := by decide
  have hdescent : baseEnd_782103 < baseStart_782103 := by decide
  rcases family_descends (prefixWord ++ tailWord_782103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782141 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_782141 : Nat := 118140960795 + 782141 * 2 ^ 59
def prefixEnd_782141 : Nat := 4983230072969 + 3 ^ 40 * 782141 * 2
def baseEnd_782141 : Nat := 356990464522959647502671

theorem tailTrace_782141 : CollatzResearch.WordTrace tailWord_782141 prefixEnd_782141 356990464522959647502671 := by
  unfold tailWord_782141
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527025859444210893138277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19018017239629473928758851 28527025859444210893138277)
  ·
    refine ⟨5348817348645789542463427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28527025859444210893138277 5348817348645789542463427)
    ·
      refine ⟨8023226022968684313695141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348817348645789542463427 8023226022968684313695141)
      ·
        refine ⟨1504354879306628308817839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8023226022968684313695141 1504354879306628308817839)
        ·
          refine ⟨2256532318959942463226759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504354879306628308817839 2256532318959942463226759)
          ·
            refine ⟨3384798478439913694840139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256532318959942463226759 3384798478439913694840139)
            ·
              refine ⟨5077197717659870542260209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384798478439913694840139 5077197717659870542260209)
              ·
                refine ⟨3807898288244902906695157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077197717659870542260209 3807898288244902906695157)
                ·
                  refine ⟨356990464522959647502671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807898288244902906695157 356990464522959647502671)
                  ·
                    rfl

theorem cell20_782141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_782141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782141 prefixEnd_782141 := by exact prefixLift 782141
  have htrace : WordTrace (prefixWord ++ tailWord_782141) baseStart_782141 baseEnd_782141 := by
    simpa [prefixWord, tailWord_782141, baseEnd_782141] using wordTrace_append hprefix tailTrace_782141
  have hstable : (prefixWord ++ tailWord_782141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782141).length < 2 ^ (prefixWord ++ tailWord_782141).sum := by decide
  have hdescent : baseEnd_782141 < baseStart_782141 := by decide
  rcases family_descends (prefixWord ++ tailWord_782141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782165 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_782165 : Nat := 118140960795 + 782165 * 2 ^ 59
def prefixEnd_782165 : Nat := 4983230072969 + 3 ^ 40 * 782165 * 2
def baseEnd_782165 : Nat := 357001418776922230702573

theorem tailTrace_782165 : CollatzResearch.WordTrace tailWord_782165 prefixEnd_782165 357001418776922230702573 := by
  unfold tailWord_782165
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527901211357262992011949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19018600807571508661341299 28527901211357262992011949)
  ·
    refine ⟨10697962954258973622004481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28527901211357262992011949 10697962954258973622004481)
    ·
      refine ⟨8023472215694230216503361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697962954258973622004481 8023472215694230216503361)
      ·
        refine ⟨6017604161770672662377521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023472215694230216503361 6017604161770672662377521)
        ·
          refine ⟨4513203121328004496783141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017604161770672662377521 4513203121328004496783141)
          ·
            refine ⟨846225585249000843146839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4513203121328004496783141 846225585249000843146839)
            ·
              refine ⟨1269338377873501264720259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846225585249000843146839 1269338377873501264720259)
              ·
                refine ⟨1904007566810251897080389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269338377873501264720259 1904007566810251897080389)
                ·
                  refine ⟨357001418776922230702573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904007566810251897080389 357001418776922230702573)
                  ·
                    rfl

theorem cell20_782165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_782165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782165 prefixEnd_782165 := by exact prefixLift 782165
  have htrace : WordTrace (prefixWord ++ tailWord_782165) baseStart_782165 baseEnd_782165 := by
    simpa [prefixWord, tailWord_782165, baseEnd_782165] using wordTrace_append hprefix tailTrace_782165
  have hstable : (prefixWord ++ tailWord_782165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782165).length < 2 ^ (prefixWord ++ tailWord_782165).sum := by decide
  have hdescent : baseEnd_782165 < baseStart_782165 := by decide
  rcases family_descends (prefixWord ++ tailWord_782165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782216 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_782216 : Nat := 118140960795 + 782216 * 2 ^ 59
def prefixEnd_782216 : Nat := 4983230072969 + 3 ^ 40 * 782216 * 2
def baseEnd_782216 : Nat := 357024696566592720002365

theorem tailTrace_782216 : CollatzResearch.WordTrace tailWord_782216 prefixEnd_782216 357024696566592720002365 := by
  unfold tailWord_782216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264880667086249351059251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19019840889448332468079001 14264880667086249351059251)
  ·
    refine ⟨21397321000629374026588877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14264880667086249351059251 21397321000629374026588877)
    ·
      refine ⟨8023995375236015259970829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21397321000629374026588877 8023995375236015259970829)
      ·
        refine ⟨3008998265713505722489061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8023995375236015259970829 3008998265713505722489061)
        ·
          refine ⟨564187174821282322966699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3008998265713505722489061 564187174821282322966699)
          ·
            refine ⟨846280762231923484450049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564187174821282322966699 846280762231923484450049)
            ·
              refine ⟨634710571673942613337537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846280762231923484450049 634710571673942613337537)
              ·
                refine ⟨476032928755456960003153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634710571673942613337537 476032928755456960003153)
                ·
                  refine ⟨357024696566592720002365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476032928755456960003153 357024696566592720002365)
                  ·
                    rfl

theorem cell20_782216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_782216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782216 prefixEnd_782216 := by exact prefixLift 782216
  have htrace : WordTrace (prefixWord ++ tailWord_782216) baseStart_782216 baseEnd_782216 := by
    simpa [prefixWord, tailWord_782216, baseEnd_782216] using wordTrace_append hprefix tailTrace_782216
  have hstable : (prefixWord ++ tailWord_782216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782216).length < 2 ^ (prefixWord ++ tailWord_782216).sum := by decide
  have hdescent : baseEnd_782216 < baseStart_782216 := by decide
  rcases family_descends (prefixWord ++ tailWord_782216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782217 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_782217 : Nat := 118140960795 + 782217 * 2 ^ 59
def prefixEnd_782217 : Nat := 4983230072969 + 3 ^ 40 * 782217 * 2
def baseEnd_782217 : Nat := 357025152993841160969027

theorem tailTrace_782217 : CollatzResearch.WordTrace tailWord_782217 prefixEnd_782217 357025152993841160969027 := by
  unfold tailWord_782217
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529797807168875872904905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19019865204779250581936603 28529797807168875872904905)
  ·
    refine ⟨21397348355376656904678679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28529797807168875872904905 21397348355376656904678679)
    ·
      refine ⟨32096022533064985357018019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397348355376656904678679 32096022533064985357018019)
      ·
        refine ⟨48144033799597478035527029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32096022533064985357018019 48144033799597478035527029)
        ·
          refine ⟨4513503168712263565830659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48144033799597478035527029 4513503168712263565830659)
          ·
            refine ⟨6770254753068395348745989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513503168712263565830659 6770254753068395348745989)
            ·
              refine ⟨1269422766200324127889873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6770254753068395348745989 1269422766200324127889873)
              ·
                refine ⟨952067074650243095917405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269422766200324127889873 952067074650243095917405)
                ·
                  refine ⟨357025152993841160969027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952067074650243095917405 357025152993841160969027)
                  ·
                    rfl

theorem cell20_782217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_782217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782217 prefixEnd_782217 := by exact prefixLift 782217
  have htrace : WordTrace (prefixWord ++ tailWord_782217) baseStart_782217 baseEnd_782217 := by
    simpa [prefixWord, tailWord_782217, baseEnd_782217] using wordTrace_append hprefix tailTrace_782217
  have hstable : (prefixWord ++ tailWord_782217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782217).length < 2 ^ (prefixWord ++ tailWord_782217).sum := by decide
  have hdescent : baseEnd_782217 < baseStart_782217 := by decide
  rcases family_descends (prefixWord ++ tailWord_782217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782231 : List Nat := [1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_782231 : Nat := 118140960795 + 782231 * 2 ^ 59
def prefixEnd_782231 : Nat := 4983230072969 + 3 ^ 40 * 782231 * 2
def baseEnd_782231 : Nat := 119010514325106444834101

theorem tailTrace_782231 : CollatzResearch.WordTrace tailWord_782231 prefixEnd_782231 119010514325106444834101 := by
  unfold tailWord_782231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28530308429118156263914547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19020205619412104175943031 28530308429118156263914547)
  ·
    refine ⟨42795462643677234395871821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28530308429118156263914547 42795462643677234395871821)
    ·
      refine ⟨16048298491378962898451933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42795462643677234395871821 16048298491378962898451933)
      ·
        refine ⟨6018111934267111086919475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16048298491378962898451933 6018111934267111086919475)
        ·
          refine ⟨9027167901400666630379213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018111934267111086919475 9027167901400666630379213)
          ·
            refine ⟨3385187963025249986392205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9027167901400666630379213 3385187963025249986392205)
            ·
              refine ⟨1269445486134468744897077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385187963025249986392205 1269445486134468744897077)
              ·
                refine ⟨119010514325106444834101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1269445486134468744897077 119010514325106444834101)
                ·
                  rfl

theorem cell20_782231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_782231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782231 prefixEnd_782231 := by exact prefixLift 782231
  have htrace : WordTrace (prefixWord ++ tailWord_782231) baseStart_782231 baseEnd_782231 := by
    simpa [prefixWord, tailWord_782231, baseEnd_782231] using wordTrace_append hprefix tailTrace_782231
  have hstable : (prefixWord ++ tailWord_782231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782231).length < 2 ^ (prefixWord ++ tailWord_782231).sum := by decide
  have hdescent : baseEnd_782231 < baseStart_782231 := by decide
  rcases family_descends (prefixWord ++ tailWord_782231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782241 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_782241 : Nat := 118140960795 + 782241 * 2 ^ 59
def prefixEnd_782241 : Nat := 4983230072969 + 3 ^ 40 * 782241 * 2
def baseEnd_782241 : Nat := 357036107247803744168929

theorem tailTrace_782241 : CollatzResearch.WordTrace tailWord_782241 prefixEnd_782241 357036107247803744168929 := by
  unfold tailWord_782241
  simp only [CollatzResearch.WordTrace]
  refine ⟨28530673159081927971778577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19020448772721285314519051 28530673159081927971778577)
  ·
    refine ⟨21398004869311445978833933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28530673159081927971778577 21398004869311445978833933)
    ·
      refine ⟨8024251825991792242062725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21398004869311445978833933 8024251825991792242062725)
      ·
        refine ⟨1504547217373461045386761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8024251825991792242062725 1504547217373461045386761)
        ·
          refine ⟨1128410413030095784040071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504547217373461045386761 1128410413030095784040071)
          ·
            refine ⟨1692615619545143676060107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128410413030095784040071 1692615619545143676060107)
            ·
              refine ⟨2538923429317715514090161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692615619545143676060107 2538923429317715514090161)
              ·
                refine ⟨1904192571988286635567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538923429317715514090161 1904192571988286635567621)
                ·
                  refine ⟨357036107247803744168929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904192571988286635567621 357036107247803744168929)
                  ·
                    rfl

theorem cell20_782241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_782241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782241 prefixEnd_782241 := by exact prefixLift 782241
  have htrace : WordTrace (prefixWord ++ tailWord_782241) baseStart_782241 baseEnd_782241 := by
    simpa [prefixWord, tailWord_782241, baseEnd_782241] using wordTrace_append hprefix tailTrace_782241
  have hstable : (prefixWord ++ tailWord_782241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782241).length < 2 ^ (prefixWord ++ tailWord_782241).sum := by decide
  have hdescent : baseEnd_782241 < baseStart_782241 := by decide
  rcases family_descends (prefixWord ++ tailWord_782241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782268 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_782268 : Nat := 118140960795 + 782268 * 2 ^ 59
def prefixEnd_782268 : Nat := 4983230072969 + 3 ^ 40 * 782268 * 2
def baseEnd_782268 : Nat := 357048430783511650268819

theorem tailTrace_782268 : CollatzResearch.WordTrace tailWord_782268 prefixEnd_782268 357048430783511650268819 := by
  unfold tailWord_782268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265828964992055791505729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19021105286656074388674305 14265828964992055791505729)
  ·
    refine ⟨10699371723744041843629297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14265828964992055791505729 10699371723744041843629297)
    ·
      refine ⟨8024528792808031382721973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10699371723744041843629297 8024528792808031382721973)
      ·
        refine ⟨752299574325752942130185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8024528792808031382721973 752299574325752942130185)
        ·
          refine ⟨564224680744314706597639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752299574325752942130185 564224680744314706597639)
          ·
            refine ⟨846337021116472059896459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564224680744314706597639 846337021116472059896459)
            ·
              refine ⟨1269505531674708089844689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846337021116472059896459 1269505531674708089844689)
              ·
                refine ⟨952129148756031067383517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269505531674708089844689 952129148756031067383517)
                ·
                  refine ⟨357048430783511650268819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952129148756031067383517 357048430783511650268819)
                  ·
                    rfl

theorem cell20_782268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_782268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782268 prefixEnd_782268 := by exact prefixLift 782268
  have htrace : WordTrace (prefixWord ++ tailWord_782268) baseStart_782268 baseEnd_782268 := by
    simpa [prefixWord, tailWord_782268, baseEnd_782268] using wordTrace_append hprefix tailTrace_782268
  have hstable : (prefixWord ++ tailWord_782268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782268).length < 2 ^ (prefixWord ++ tailWord_782268).sum := by decide
  have hdescent : baseEnd_782268 < baseStart_782268 := by decide
  rcases family_descends (prefixWord ++ tailWord_782268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782269 : List Nat := [1, 4, 1, 2, 3, 2, 7]
def baseStart_782269 : Nat := 118140960795 + 782269 * 2 ^ 59
def prefixEnd_782269 : Nat := 4983230072969 + 3 ^ 40 * 782269 * 2
def baseEnd_782269 : Nat := 39672098578973343470609

theorem tailTrace_782269 : CollatzResearch.WordTrace tailWord_782269 prefixEnd_782269 39672098578973343470609 := by
  unfold tailWord_782269
  simp only [CollatzResearch.WordTrace]
  refine ⟨28531694402980488753797861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19021129601986992502531907 28531694402980488753797861)
  ·
    refine ⟨5349692700558841641337099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28531694402980488753797861 5349692700558841641337099)
    ·
      refine ⟨8024539050838262462005649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349692700558841641337099 8024539050838262462005649)
      ·
        refine ⟨6018404288128696846504237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024539050838262462005649 6018404288128696846504237)
        ·
          refine ⟨2256901608048261317439089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6018404288128696846504237 2256901608048261317439089)
          ·
            refine ⟨1692676206036195988079317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256901608048261317439089 1692676206036195988079317)
            ·
              refine ⟨39672098578973343470609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1692676206036195988079317 39672098578973343470609)
              ·
                rfl

theorem cell20_782269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_782269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782269 prefixEnd_782269 := by exact prefixLift 782269
  have htrace : WordTrace (prefixWord ++ tailWord_782269) baseStart_782269 baseEnd_782269 := by
    simpa [prefixWord, tailWord_782269, baseEnd_782269] using wordTrace_append hprefix tailTrace_782269
  have hstable : (prefixWord ++ tailWord_782269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782269).length < 2 ^ (prefixWord ++ tailWord_782269).sum := by decide
  have hdescent : baseEnd_782269 < baseStart_782269 := by decide
  rcases family_descends (prefixWord ++ tailWord_782269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782307 : List Nat := [1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_782307 : Nat := 118140960795 + 782307 * 2 ^ 59
def prefixEnd_782307 : Nat := 4983230072969 + 3 ^ 40 * 782307 * 2
def baseEnd_782307 : Nat := 119022077148733615989553

theorem tailTrace_782307 : CollatzResearch.WordTrace tailWord_782307 prefixEnd_782307 119022077148733615989553 := by
  unfold tailWord_782307
  simp only [CollatzResearch.WordTrace]
  refine ⟨28533080376842821243681175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19022053584561880829120783 28533080376842821243681175)
  ·
    refine ⟨42799620565264231865521763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28533080376842821243681175 42799620565264231865521763)
    ·
      refine ⟨64199430847896347798282645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799620565264231865521763 64199430847896347798282645)
      ·
        refine ⟨3009348320995141303044499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64199430847896347798282645 3009348320995141303044499)
        ·
          refine ⟨4514022481492711954566749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009348320995141303044499 4514022481492711954566749)
          ·
            refine ⟨1692758430559766982962531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4514022481492711954566749 1692758430559766982962531)
            ·
              refine ⟨2539137645839650474443797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692758430559766982962531 2539137645839650474443797)
              ·
                refine ⟨119022077148733615989553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2539137645839650474443797 119022077148733615989553)
                ·
                  rfl

theorem cell20_782307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_782307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782307 prefixEnd_782307 := by exact prefixLift 782307
  have htrace : WordTrace (prefixWord ++ tailWord_782307) baseStart_782307 baseEnd_782307 := by
    simpa [prefixWord, tailWord_782307, baseEnd_782307] using wordTrace_append hprefix tailTrace_782307
  have hstable : (prefixWord ++ tailWord_782307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782307).length < 2 ^ (prefixWord ++ tailWord_782307).sum := by decide
  have hdescent : baseEnd_782307 < baseStart_782307 := by decide
  rcases family_descends (prefixWord ++ tailWord_782307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782314 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_782314 : Nat := 118140960795 + 782314 * 2 ^ 59
def prefixEnd_782314 : Nat := 4983230072969 + 3 ^ 40 * 782314 * 2
def baseEnd_782314 : Nat := 357069426436939934735297

theorem tailTrace_782314 : CollatzResearch.WordTrace tailWord_782314 prefixEnd_782314 357069426436939934735297 := by
  unfold tailWord_782314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133333921954365359796499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19022223791878307626123997 7133333921954365359796499)
  ·
    refine ⟨10700000882931548039694749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7133333921954365359796499 10700000882931548039694749)
    ·
      refine ⟨4012500331099330514885531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10700000882931548039694749 4012500331099330514885531)
      ·
        refine ⟨6018750496648995772328297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012500331099330514885531 6018750496648995772328297)
        ·
          refine ⟨4514062872486746829246223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018750496648995772328297 4514062872486746829246223)
          ·
            refine ⟨6771094308730120243869335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514062872486746829246223 6771094308730120243869335)
            ·
              refine ⟨10156641463095180365804003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771094308730120243869335 10156641463095180365804003)
              ·
                refine ⟨15234962194642770548706005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156641463095180365804003 15234962194642770548706005)
                ·
                  refine ⟨357069426436939934735297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15234962194642770548706005 357069426436939934735297)
                  ·
                    rfl

theorem cell20_782314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_782314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782314 prefixEnd_782314 := by exact prefixLift 782314
  have htrace : WordTrace (prefixWord ++ tailWord_782314) baseStart_782314 baseEnd_782314 := by
    simpa [prefixWord, tailWord_782314, baseEnd_782314] using wordTrace_append hprefix tailTrace_782314
  have hstable : (prefixWord ++ tailWord_782314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782314).length < 2 ^ (prefixWord ++ tailWord_782314).sum := by decide
  have hdescent : baseEnd_782314 < baseStart_782314 := by decide
  rcases family_descends (prefixWord ++ tailWord_782314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782328 : List Nat := [2, 1, 2, 1, 1, 3, 10]
def baseStart_782328 : Nat := 118140960795 + 782328 * 2 ^ 59
def prefixEnd_782328 : Nat := 4983230072969 + 3 ^ 40 * 782328 * 2
def baseEnd_782328 : Nat := 39675090713157567585397

theorem tailTrace_782328 : CollatzResearch.WordTrace tailWord_782328 prefixEnd_782328 39675090713157567585397 := by
  unfold tailWord_782328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266923154883370915097819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19022564206511161220130425 14266923154883370915097819)
  ·
    refine ⟨21400384732325056372646729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14266923154883370915097819 21400384732325056372646729)
    ·
      refine ⟨16050288549243792279485047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21400384732325056372646729 16050288549243792279485047)
      ·
        refine ⟨24075432823865688419227571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16050288549243792279485047 24075432823865688419227571)
        ·
          refine ⟨36113149235798532628841357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24075432823865688419227571 36113149235798532628841357)
          ·
            refine ⟨13542430963424449735815509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36113149235798532628841357 13542430963424449735815509)
            ·
              refine ⟨39675090713157567585397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13542430963424449735815509 39675090713157567585397)
              ·
                rfl

theorem cell20_782328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_782328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782328 prefixEnd_782328 := by exact prefixLift 782328
  have htrace : WordTrace (prefixWord ++ tailWord_782328) baseStart_782328 baseEnd_782328 := by
    simpa [prefixWord, tailWord_782328, baseEnd_782328] using wordTrace_append hprefix tailTrace_782328
  have hstable : (prefixWord ++ tailWord_782328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782328).length < 2 ^ (prefixWord ++ tailWord_782328).sum := by decide
  have hdescent : baseEnd_782328 < baseStart_782328 := by decide
  rcases family_descends (prefixWord ++ tailWord_782328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782334 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_782334 : Nat := 118140960795 + 782334 * 2 ^ 59
def prefixEnd_782334 : Nat := 4983230072969 + 3 ^ 40 * 782334 * 2
def baseEnd_782334 : Nat := 357078554981908754068549

theorem tailTrace_782334 : CollatzResearch.WordTrace tailWord_782334 prefixEnd_782334 357078554981908754068549 := by
  unfold tailWord_782334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566758143468125606864257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19022710098496669903276037 3566758143468125606864257)
  ·
    refine ⟨2675068607601094205148193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3566758143468125606864257 2675068607601094205148193)
    ·
      refine ⟨2006301455700820653861145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675068607601094205148193 2006301455700820653861145)
      ·
        refine ⟨1504726091775615490395859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2006301455700820653861145 1504726091775615490395859)
        ·
          refine ⟨2257089137663423235593789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504726091775615490395859 2257089137663423235593789)
          ·
            refine ⟨846408426623783713347671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257089137663423235593789 846408426623783713347671)
            ·
              refine ⟨1269612639935675570021507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846408426623783713347671 1269612639935675570021507)
              ·
                refine ⟨1904418959903513355032261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269612639935675570021507 1904418959903513355032261)
                ·
                  refine ⟨357078554981908754068549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904418959903513355032261 357078554981908754068549)
                  ·
                    rfl

theorem cell20_782334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_782334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782334 prefixEnd_782334 := by exact prefixLift 782334
  have htrace : WordTrace (prefixWord ++ tailWord_782334) baseStart_782334 baseEnd_782334 := by
    simpa [prefixWord, tailWord_782334, baseEnd_782334] using wordTrace_append hprefix tailTrace_782334
  have hstable : (prefixWord ++ tailWord_782334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782334).length < 2 ^ (prefixWord ++ tailWord_782334).sum := by decide
  have hdescent : baseEnd_782334 < baseStart_782334 := by decide
  rcases family_descends (prefixWord ++ tailWord_782334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782352 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_782352 : Nat := 118140960795 + 782352 * 2 ^ 59
def prefixEnd_782352 : Nat := 4983230072969 + 3 ^ 40 * 782352 * 2
def baseEnd_782352 : Nat := 357086770672380691468475

theorem tailTrace_782352 : CollatzResearch.WordTrace tailWord_782352 prefixEnd_782352 357086770672380691468475 := by
  unfold tailWord_782352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267360830839896964534655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19023147774453195952712873 14267360830839896964534655)
  ·
    refine ⟨21401041246259845446801983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14267360830839896964534655 21401041246259845446801983)
    ·
      refine ⟨32101561869389768170202975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21401041246259845446801983 32101561869389768170202975)
      ·
        refine ⟨48152342804084652255304463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32101561869389768170202975 48152342804084652255304463)
        ·
          refine ⟨72228514206126978382956695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48152342804084652255304463 72228514206126978382956695)
          ·
            refine ⟨108342771309190467574435043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72228514206126978382956695 108342771309190467574435043)
            ·
              refine ⟨162514156963785701361652565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108342771309190467574435043 162514156963785701361652565)
              ·
                refine ⟨952231388459681843915933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 162514156963785701361652565 952231388459681843915933)
                ·
                  refine ⟨357086770672380691468475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952231388459681843915933 357086770672380691468475)
                  ·
                    rfl

theorem cell20_782352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_782352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782352 prefixEnd_782352 := by exact prefixLift 782352
  have htrace : WordTrace (prefixWord ++ tailWord_782352) baseStart_782352 baseEnd_782352 := by
    simpa [prefixWord, tailWord_782352, baseEnd_782352] using wordTrace_append hprefix tailTrace_782352
  have hstable : (prefixWord ++ tailWord_782352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782352).length < 2 ^ (prefixWord ++ tailWord_782352).sum := by decide
  have hdescent : baseEnd_782352 < baseStart_782352 := by decide
  rcases family_descends (prefixWord ++ tailWord_782352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782414 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_782414 : Nat := 118140960795 + 782414 * 2 ^ 59
def prefixEnd_782414 : Nat := 4983230072969 + 3 ^ 40 * 782414 * 2
def baseEnd_782414 : Nat := 357115069161784031401555

theorem tailTrace_782414 : CollatzResearch.WordTrace tailWord_782414 prefixEnd_782414 357115069161784031401555 := by
  unfold tailWord_782414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567122873431897314728287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19024655324970119011884197 3567122873431897314728287)
  ·
    refine ⟨5350684310147845972092431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3567122873431897314728287 5350684310147845972092431)
    ·
      refine ⟨8026026465221768958138647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350684310147845972092431 8026026465221768958138647)
      ·
        refine ⟨12039039697832653437207971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026026465221768958138647 12039039697832653437207971)
        ·
          refine ⟨18058559546748980155811957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039039697832653437207971 18058559546748980155811957)
          ·
            refine ⟨1692989957507716889607371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18058559546748980155811957 1692989957507716889607371)
            ·
              refine ⟨2539484936261575334411057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692989957507716889607371 2539484936261575334411057)
              ·
                refine ⟨1904613702196181500808293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539484936261575334411057 1904613702196181500808293)
                ·
                  refine ⟨357115069161784031401555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904613702196181500808293 357115069161784031401555)
                  ·
                    rfl

theorem cell20_782414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_782414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782414 prefixEnd_782414 := by exact prefixLift 782414
  have htrace : WordTrace (prefixWord ++ tailWord_782414) baseStart_782414 baseEnd_782414 := by
    simpa [prefixWord, tailWord_782414, baseEnd_782414] using wordTrace_append hprefix tailTrace_782414
  have hstable : (prefixWord ++ tailWord_782414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782414).length < 2 ^ (prefixWord ++ tailWord_782414).sum := by decide
  have hdescent : baseEnd_782414 < baseStart_782414 := by decide
  rcases family_descends (prefixWord ++ tailWord_782414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782473 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_782473 : Nat := 118140960795 + 782473 * 2 ^ 59
def prefixEnd_782473 : Nat := 4983230072969 + 3 ^ 40 * 782473 * 2
def baseEnd_782473 : Nat := 357141998369442048434647

theorem tailTrace_782473 : CollatzResearch.WordTrace tailWord_782473 prefixEnd_782473 357141998369442048434647 := by
  unfold tailWord_782473
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539134894241431594224073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19026089929494287729482715 28539134894241431594224073)
  ·
    refine ⟨21404351170681073695668055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28539134894241431594224073 21404351170681073695668055)
    ·
      refine ⟨32106526756021610543502083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404351170681073695668055 32106526756021610543502083)
      ·
        refine ⟨48159790134032415815253125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32106526756021610543502083 48159790134032415815253125)
        ·
          refine ⟨9029960650131077965359961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48159790134032415815253125 9029960650131077965359961)
          ·
            refine ⟨6772470487598308474019971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9029960650131077965359961 6772470487598308474019971)
            ·
              refine ⟨10158705731397462711029957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772470487598308474019971 10158705731397462711029957)
              ·
                refine ⟨1904757324637024258318117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10158705731397462711029957 1904757324637024258318117)
                ·
                  refine ⟨357141998369442048434647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904757324637024258318117 357141998369442048434647)
                  ·
                    rfl

theorem cell20_782473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_782473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782473 prefixEnd_782473 := by exact prefixLift 782473
  have htrace : WordTrace (prefixWord ++ tailWord_782473) baseStart_782473 baseEnd_782473 := by
    simpa [prefixWord, tailWord_782473, baseEnd_782473] using wordTrace_append hprefix tailTrace_782473
  have hstable : (prefixWord ++ tailWord_782473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782473).length < 2 ^ (prefixWord ++ tailWord_782473).sum := by decide
  have hdescent : baseEnd_782473 < baseStart_782473 := by decide
  rcases family_descends (prefixWord ++ tailWord_782473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782480 : List Nat := [2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_782480 : Nat := 118140960795 + 782480 * 2 ^ 59
def prefixEnd_782480 : Nat := 4983230072969 + 3 ^ 40 * 782480 * 2
def baseEnd_782480 : Nat := 119048397786727045067095

theorem tailTrace_782480 : CollatzResearch.WordTrace tailWord_782480 prefixEnd_782480 119048397786727045067095 := by
  unfold tailWord_782480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269695102608035894864447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19026260136810714526485929 14269695102608035894864447)
  ·
    refine ⟨21404542653912053842296671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269695102608035894864447 21404542653912053842296671)
    ·
      refine ⟨32106813980868080763445007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404542653912053842296671 32106813980868080763445007)
      ·
        refine ⟨48160220971302121145167511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32106813980868080763445007 48160220971302121145167511)
        ·
          refine ⟨72240331456953181717751267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48160220971302121145167511 72240331456953181717751267)
          ·
            refine ⟨108360497185429772576626901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72240331456953181717751267 108360497185429772576626901)
            ·
              refine ⟨2539699152783510294764693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108360497185429772576626901 2539699152783510294764693)
              ·
                refine ⟨119048397786727045067095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2539699152783510294764693 119048397786727045067095)
                ·
                  rfl

theorem cell20_782480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_782480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782480 prefixEnd_782480 := by exact prefixLift 782480
  have htrace : WordTrace (prefixWord ++ tailWord_782480) baseStart_782480 baseEnd_782480 := by
    simpa [prefixWord, tailWord_782480, baseEnd_782480] using wordTrace_append hprefix tailTrace_782480
  have hstable : (prefixWord ++ tailWord_782480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782480).length < 2 ^ (prefixWord ++ tailWord_782480).sum := by decide
  have hdescent : baseEnd_782480 < baseStart_782480 := by decide
  rcases family_descends (prefixWord ++ tailWord_782480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782497 : List Nat := [1, 2, 3, 3, 1, 4, 6]
def baseStart_782497 : Nat := 118140960795 + 782497 * 2 ^ 59
def prefixEnd_782497 : Nat := 4983230072969 + 3 ^ 40 * 782497 * 2
def baseEnd_782497 : Nat := 39683661402600514626061

theorem tailTrace_782497 : CollatzResearch.WordTrace tailWord_782497 prefixEnd_782497 39683661402600514626061 := by
  unfold tailWord_782497
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540010246154483693097745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19026673497436322462065163 28540010246154483693097745)
  ·
    refine ⟨21405007684615862769823309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28540010246154483693097745 21405007684615862769823309)
    ·
      refine ⟨8026877881730948538683741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21405007684615862769823309 8026877881730948538683741)
      ·
        refine ⟨3010079205649105702006403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8026877881730948538683741 3010079205649105702006403)
        ·
          refine ⟨4515118808473658553009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010079205649105702006403 4515118808473658553009605)
          ·
            refine ⟨846584776588810978689301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4515118808473658553009605 846584776588810978689301)
            ·
              refine ⟨39683661402600514626061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 846584776588810978689301 39683661402600514626061)
              ·
                rfl

theorem cell20_782497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_782497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782497 prefixEnd_782497 := by exact prefixLift 782497
  have htrace : WordTrace (prefixWord ++ tailWord_782497) baseStart_782497 baseEnd_782497 := by
    simpa [prefixWord, tailWord_782497, baseEnd_782497] using wordTrace_append hprefix tailTrace_782497
  have hstable : (prefixWord ++ tailWord_782497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782497).length < 2 ^ (prefixWord ++ tailWord_782497).sum := by decide
  have hdescent : baseEnd_782497 < baseStart_782497 := by decide
  rcases family_descends (prefixWord ++ tailWord_782497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782503 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 2]
def baseStart_782503 : Nat := 118140960795 + 782503 * 2 ^ 59
def prefixEnd_782503 : Nat := 4983230072969 + 3 ^ 40 * 782503 * 2
def baseEnd_782503 : Nat := 357155691186895277434525

theorem tailTrace_782503 : CollatzResearch.WordTrace tailWord_782503 prefixEnd_782503 357155691186895277434525 := by
  unfold tailWord_782503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540229084132746717816163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19026819389421831145210775 28540229084132746717816163)
  ·
    refine ⟨42810343626199120076724245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28540229084132746717816163 42810343626199120076724245)
    ·
      refine ⟨2006734857478083753596449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42810343626199120076724245 2006734857478083753596449)
      ·
        refine ⟨1505051143108562815197337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2006734857478083753596449 1505051143108562815197337)
        ·
          refine ⟨1128788357331422111398003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505051143108562815197337 1128788357331422111398003)
          ·
            refine ⟨1693182535997133167097005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128788357331422111398003 1693182535997133167097005)
            ·
              refine ⟨634943450998924937661377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693182535997133167097005 634943450998924937661377)
              ·
                refine ⟨476207588249193703246033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634943450998924937661377 476207588249193703246033)
                ·
                  refine ⟨357155691186895277434525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476207588249193703246033 357155691186895277434525)
                  ·
                    rfl

theorem cell20_782503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2].length) (baseStart_782503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782503 prefixEnd_782503 := by exact prefixLift 782503
  have htrace : WordTrace (prefixWord ++ tailWord_782503) baseStart_782503 baseEnd_782503 := by
    simpa [prefixWord, tailWord_782503, baseEnd_782503] using wordTrace_append hprefix tailTrace_782503
  have hstable : (prefixWord ++ tailWord_782503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782503).length < 2 ^ (prefixWord ++ tailWord_782503).sum := by decide
  have hdescent : baseEnd_782503 < baseStart_782503 := by decide
  rcases family_descends (prefixWord ++ tailWord_782503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782590 : List Nat := [4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_782590 : Nat := 118140960795 + 782590 * 2 ^ 59
def prefixEnd_782590 : Nat := 4983230072969 + 3 ^ 40 * 782590 * 2
def baseEnd_782590 : Nat := 119065133452503213844723

theorem tailTrace_782590 : CollatzResearch.WordTrace tailWord_782590 prefixEnd_782590 119065133452503213844723 := by
  unfold tailWord_782590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567925279352195072029153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19028934823211707050822149 3567925279352195072029153)
  ·
    refine ⟨2675943959514146304021865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567925279352195072029153 2675943959514146304021865)
    ·
      refine ⟨2006957969635609728016399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675943959514146304021865 2006957969635609728016399)
      ·
        refine ⟨3010436954453414592024599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006957969635609728016399 3010436954453414592024599)
        ·
          refine ⟨4515655431680121888036899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010436954453414592024599 4515655431680121888036899)
          ·
            refine ⟨6773483147520182832055349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515655431680121888036899 6773483147520182832055349)
            ·
              refine ⟨635014045080017140505189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6773483147520182832055349 635014045080017140505189)
              ·
                refine ⟨119065133452503213844723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635014045080017140505189 119065133452503213844723)
                ·
                  rfl

theorem cell20_782590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_782590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782590 prefixEnd_782590 := by exact prefixLift 782590
  have htrace : WordTrace (prefixWord ++ tailWord_782590) baseStart_782590 baseEnd_782590 := by
    simpa [prefixWord, tailWord_782590, baseEnd_782590] using wordTrace_append hprefix tailTrace_782590
  have hstable : (prefixWord ++ tailWord_782590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782590).length < 2 ^ (prefixWord ++ tailWord_782590).sum := by decide
  have hdescent : baseEnd_782590 < baseStart_782590 := by decide
  rcases family_descends (prefixWord ++ tailWord_782590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782621 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_782621 : Nat := 118140960795 + 782621 * 2 ^ 59
def prefixEnd_782621 : Nat := 4983230072969 + 3 ^ 40 * 782621 * 2
def baseEnd_782621 : Nat := 357209549602211311500709

theorem tailTrace_782621 : CollatzResearch.WordTrace tailWord_782621 prefixEnd_782621 357209549602211311500709 := by
  unfold tailWord_782621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544532897705252870611717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19029688598470168580407811 28544532897705252870611717)
  ·
    refine ⟨5352099918319734913239697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28544532897705252870611717 5352099918319734913239697)
    ·
      refine ⟨4014074938739801184929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352099918319734913239697 4014074938739801184929773)
      ·
        refine ⟨1505278102027425444348665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4014074938739801184929773 1505278102027425444348665)
        ·
          refine ⟨1128958576520569083261499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505278102027425444348665 1128958576520569083261499)
          ·
            refine ⟨1693437864780853624892249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128958576520569083261499 1693437864780853624892249)
            ·
              refine ⟨1270078398585640218669187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693437864780853624892249 1270078398585640218669187)
              ·
                refine ⟨1905117597878460328003781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270078398585640218669187 1905117597878460328003781)
                ·
                  refine ⟨357209549602211311500709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905117597878460328003781 357209549602211311500709)
                  ·
                    rfl

theorem cell20_782621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_782621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782621 prefixEnd_782621 := by exact prefixLift 782621
  have htrace : WordTrace (prefixWord ++ tailWord_782621) baseStart_782621 baseEnd_782621 := by
    simpa [prefixWord, tailWord_782621, baseEnd_782621] using wordTrace_append hprefix tailTrace_782621
  have hstable : (prefixWord ++ tailWord_782621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782621).length < 2 ^ (prefixWord ++ tailWord_782621).sum := by decide
  have hdescent : baseEnd_782621 < baseStart_782621 := by decide
  rcases family_descends (prefixWord ++ tailWord_782621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782625 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_782625 : Nat := 118140960795 + 782625 * 2 ^ 59
def prefixEnd_782625 : Nat := 4983230072969 + 3 ^ 40 * 782625 * 2
def baseEnd_782625 : Nat := 357211375311205075367359

theorem tailTrace_782625 : CollatzResearch.WordTrace tailWord_782625 prefixEnd_782625 357211375311205075367359 := by
  unfold tailWord_782625
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544678789690761553757329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19029785859793841035838219 28544678789690761553757329)
  ·
    refine ⟨21408509092268071165317997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28544678789690761553757329 21408509092268071165317997)
    ·
      refine ⟨8028190909600526686994249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21408509092268071165317997 8028190909600526686994249)
      ·
        refine ⟨6021143182200395015245687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8028190909600526686994249 6021143182200395015245687)
        ·
          refine ⟨9031714773300592522868531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021143182200395015245687 9031714773300592522868531)
          ·
            refine ⟨13547572159950888784302797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031714773300592522868531 13547572159950888784302797)
            ·
              refine ⟨5080339559981583294113549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13547572159950888784302797 5080339559981583294113549)
              ·
                refine ⟨1905127334993093735292581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5080339559981583294113549 1905127334993093735292581)
                ·
                  refine ⟨357211375311205075367359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905127334993093735292581 357211375311205075367359)
                  ·
                    rfl

theorem cell20_782625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_782625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782625 prefixEnd_782625 := by exact prefixLift 782625
  have htrace : WordTrace (prefixWord ++ tailWord_782625) baseStart_782625 baseEnd_782625 := by
    simpa [prefixWord, tailWord_782625, baseEnd_782625] using wordTrace_append hprefix tailTrace_782625
  have hstable : (prefixWord ++ tailWord_782625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782625).length < 2 ^ (prefixWord ++ tailWord_782625).sum := by decide
  have hdescent : baseEnd_782625 < baseStart_782625 := by decide
  rcases family_descends (prefixWord ++ tailWord_782625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782649 : List Nat := [1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_782649 : Nat := 118140960795 + 782649 * 2 ^ 59
def prefixEnd_782649 : Nat := 4983230072969 + 3 ^ 40 * 782649 * 2
def baseEnd_782649 : Nat := 119074109855055886189087

theorem tailTrace_782649 : CollatzResearch.WordTrace tailWord_782649 prefixEnd_782649 119074109855055886189087 := by
  unfold tailWord_782649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545554141603813652631001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19030369427735875768420667 28545554141603813652631001)
  ·
    refine ⟨21409165606202860239473251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28545554141603813652631001 21409165606202860239473251)
    ·
      refine ⟨32113748409304290359209877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21409165606202860239473251 32113748409304290359209877)
      ·
        refine ⟨1505331956686138610587963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32113748409304290359209877 1505331956686138610587963)
        ·
          refine ⟨2257997935029207915881945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505331956686138610587963 2257997935029207915881945)
          ·
            refine ⟨1693498451271905936911459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257997935029207915881945 1693498451271905936911459)
            ·
              refine ⟨2540247676907858905367189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693498451271905936911459 2540247676907858905367189)
              ·
                refine ⟨119074109855055886189087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2540247676907858905367189 119074109855055886189087)
                ·
                  rfl

theorem cell20_782649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_782649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782649 prefixEnd_782649 := by exact prefixLift 782649
  have htrace : WordTrace (prefixWord ++ tailWord_782649) baseStart_782649 baseEnd_782649 := by
    simpa [prefixWord, tailWord_782649, baseEnd_782649] using wordTrace_append hprefix tailTrace_782649
  have hstable : (prefixWord ++ tailWord_782649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782649).length < 2 ^ (prefixWord ++ tailWord_782649).sum := by decide
  have hdescent : baseEnd_782649 < baseStart_782649 := by decide
  rcases family_descends (prefixWord ++ tailWord_782649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782676 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_782676 : Nat := 118140960795 + 782676 * 2 ^ 59
def prefixEnd_782676 : Nat := 4983230072969 + 3 ^ 40 * 782676 * 2
def baseEnd_782676 : Nat := 357234653100875564667151

theorem tailTrace_782676 : CollatzResearch.WordTrace tailWord_782676 prefixEnd_782676 357234653100875564667151 := by
  unfold tailWord_782676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273269456252998631931941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19031025941670664842575921 14273269456252998631931941)
  ·
    refine ⟨2676238023047437243487239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14273269456252998631931941 2676238023047437243487239)
    ·
      refine ⟨4014357034571155865230859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676238023047437243487239 4014357034571155865230859)
      ·
        refine ⟨6021535551856733797846289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014357034571155865230859 6021535551856733797846289)
        ·
          refine ⟨4516151663892550348384717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021535551856733797846289 4516151663892550348384717)
          ·
            refine ⟨1693556873959706380644269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4516151663892550348384717 1693556873959706380644269)
            ·
              refine ⟨635083827734889892741601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693556873959706380644269 635083827734889892741601)
              ·
                refine ⟨476312870801167419556201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635083827734889892741601 476312870801167419556201)
                ·
                  refine ⟨357234653100875564667151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476312870801167419556201 357234653100875564667151)
                  ·
                    rfl

theorem cell20_782676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_782676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782676 prefixEnd_782676 := by exact prefixLift 782676
  have htrace : WordTrace (prefixWord ++ tailWord_782676) baseStart_782676 baseEnd_782676 := by
    simpa [prefixWord, tailWord_782676, baseEnd_782676] using wordTrace_append hprefix tailTrace_782676
  have hstable : (prefixWord ++ tailWord_782676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782676).length < 2 ^ (prefixWord ++ tailWord_782676).sum := by decide
  have hdescent : baseEnd_782676 < baseStart_782676 := by decide
  rcases family_descends (prefixWord ++ tailWord_782676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782690 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_782690 : Nat := 118140960795 + 782690 * 2 ^ 59
def prefixEnd_782690 : Nat := 4983230072969 + 3 ^ 40 * 782690 * 2
def baseEnd_782690 : Nat := 357241043082353738200427

theorem tailTrace_782690 : CollatzResearch.WordTrace tailWord_782690 prefixEnd_782690 357241043082353738200427 := by
  unfold tailWord_782690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136762383613819413718381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19031366356303518436582349 7136762383613819413718381)
  ·
    refine ⟨2676285893855182280144393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7136762383613819413718381 2676285893855182280144393)
    ·
      refine ⟨2007214420391386710108295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2676285893855182280144393 2007214420391386710108295)
      ·
        refine ⟨3010821630587080065162443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007214420391386710108295 3010821630587080065162443)
        ·
          refine ⟨4516232445880620097743665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010821630587080065162443 4516232445880620097743665)
          ·
            refine ⟨3387174334410465073307749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4516232445880620097743665 3387174334410465073307749)
            ·
              refine ⟨635095187701962201245203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3387174334410465073307749 635095187701962201245203)
              ·
                refine ⟨952642781552943301867805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635095187701962201245203 952642781552943301867805)
                ·
                  refine ⟨357241043082353738200427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952642781552943301867805 357241043082353738200427)
                  ·
                    rfl

theorem cell20_782690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_782690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782690 prefixEnd_782690 := by exact prefixLift 782690
  have htrace : WordTrace (prefixWord ++ tailWord_782690) baseStart_782690 baseEnd_782690 := by
    simpa [prefixWord, tailWord_782690, baseEnd_782690] using wordTrace_append hprefix tailTrace_782690
  have hstable : (prefixWord ++ tailWord_782690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782690).length < 2 ^ (prefixWord ++ tailWord_782690).sum := by decide
  have hdescent : baseEnd_782690 < baseStart_782690 := by decide
  rcases family_descends (prefixWord ++ tailWord_782690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782701 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_782701 : Nat := 118140960795 + 782701 * 2 ^ 59
def prefixEnd_782701 : Nat := 4983230072969 + 3 ^ 40 * 782701 * 2
def baseEnd_782701 : Nat := 357246063782086588833715

theorem tailTrace_782701 : CollatzResearch.WordTrace tailWord_782701 prefixEnd_782701 357246063782086588833715 := by
  unfold tailWord_782701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28547450737415426533523957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19031633824943617689015971 28547450737415426533523957)
  ·
    refine ⟨2676323506632696237517871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28547450737415426533523957 2676323506632696237517871)
    ·
      refine ⟨4014485259949044356276807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676323506632696237517871 4014485259949044356276807)
      ·
        refine ⟨6021727889923566534415211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014485259949044356276807 6021727889923566534415211)
        ·
          refine ⟨9032591834885349801622817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021727889923566534415211 9032591834885349801622817)
          ·
            refine ⟨6774443876164012351217113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9032591834885349801622817 6774443876164012351217113)
            ·
              refine ⟨5080832907123009263412835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6774443876164012351217113 5080832907123009263412835)
              ·
                refine ⟨7621249360684513895119253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080832907123009263412835 7621249360684513895119253)
                ·
                  refine ⟨357246063782086588833715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7621249360684513895119253 357246063782086588833715)
                  ·
                    rfl

theorem cell20_782701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_782701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782701 prefixEnd_782701 := by exact prefixLift 782701
  have htrace : WordTrace (prefixWord ++ tailWord_782701) baseStart_782701 baseEnd_782701 := by
    simpa [prefixWord, tailWord_782701, baseEnd_782701] using wordTrace_append hprefix tailTrace_782701
  have hstable : (prefixWord ++ tailWord_782701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782701).length < 2 ^ (prefixWord ++ tailWord_782701).sum := by decide
  have hdescent : baseEnd_782701 < baseStart_782701 := by decide
  rcases family_descends (prefixWord ++ tailWord_782701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782732 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_782732 : Nat := 118140960795 + 782732 * 2 ^ 59
def prefixEnd_782732 : Nat := 4983230072969 + 3 ^ 40 * 782732 * 2
def baseEnd_782732 : Nat := 357260213026788258800255

theorem tailTrace_782732 : CollatzResearch.WordTrace tailWord_782732 prefixEnd_782732 357260213026788258800255 := by
  unfold tailWord_782732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274290700151559413951225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19032387600202079218601633 14274290700151559413951225)
  ·
    refine ⟨10705718025113669560463419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14274290700151559413951225 10705718025113669560463419)
    ·
      refine ⟨16058577037670504340695129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705718025113669560463419 16058577037670504340695129)
      ·
        refine ⟨12043932778252878255521347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16058577037670504340695129 12043932778252878255521347)
        ·
          refine ⟨18065899167379317383282021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043932778252878255521347 18065899167379317383282021)
          ·
            refine ⟨3387356093883622009365379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18065899167379317383282021 3387356093883622009365379)
            ·
              refine ⟨5081034140825433014048069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387356093883622009365379 5081034140825433014048069)
              ·
                refine ⟨952693901404768690134013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5081034140825433014048069 952693901404768690134013)
                ·
                  refine ⟨357260213026788258800255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952693901404768690134013 357260213026788258800255)
                  ·
                    rfl

theorem cell20_782732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_782732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782732 prefixEnd_782732 := by exact prefixLift 782732
  have htrace : WordTrace (prefixWord ++ tailWord_782732) baseStart_782732 baseEnd_782732 := by
    simpa [prefixWord, tailWord_782732, baseEnd_782732] using wordTrace_append hprefix tailTrace_782732
  have hstable : (prefixWord ++ tailWord_782732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782732).length < 2 ^ (prefixWord ++ tailWord_782732).sum := by decide
  have hdescent : baseEnd_782732 < baseStart_782732 := by decide
  rcases family_descends (prefixWord ++ tailWord_782732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782794 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_782794 : Nat := 118140960795 + 782794 * 2 ^ 59
def prefixEnd_782794 : Nat := 4983230072969 + 3 ^ 40 * 782794 * 2
def baseEnd_782794 : Nat := 357288511516191598733335

theorem tailTrace_782794 : CollatzResearch.WordTrace tailWord_782794 prefixEnd_782794 357288511516191598733335 := by
  unfold tailWord_782794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137710681519625854164859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19033895150719002277772957 7137710681519625854164859)
  ·
    refine ⟨10706566022279438781247289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137710681519625854164859 10706566022279438781247289)
    ·
      refine ⟨8029924516709579085935467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10706566022279438781247289 8029924516709579085935467)
      ·
        refine ⟨12044886775064368628903201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8029924516709579085935467 12044886775064368628903201)
        ·
          refine ⟨9033665081298276471677401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12044886775064368628903201 9033665081298276471677401)
          ·
            refine ⟨6775248810973707353758051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033665081298276471677401 6775248810973707353758051)
            ·
              refine ⟨10162873216460561030637077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775248810973707353758051 10162873216460561030637077)
              ·
                refine ⟨476384682021588798311113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10162873216460561030637077 476384682021588798311113)
                ·
                  refine ⟨357288511516191598733335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476384682021588798311113 357288511516191598733335)
                  ·
                    rfl

theorem cell20_782794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_782794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782794 prefixEnd_782794 := by exact prefixLift 782794
  have htrace : WordTrace (prefixWord ++ tailWord_782794) baseStart_782794 baseEnd_782794 := by
    simpa [prefixWord, tailWord_782794, baseEnd_782794] using wordTrace_append hprefix tailTrace_782794
  have hstable : (prefixWord ++ tailWord_782794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782794).length < 2 ^ (prefixWord ++ tailWord_782794).sum := by decide
  have hdescent : baseEnd_782794 < baseStart_782794 := by decide
  rcases family_descends (prefixWord ++ tailWord_782794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782804 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_782804 : Nat := 118140960795 + 782804 * 2 ^ 59
def prefixEnd_782804 : Nat := 4983230072969 + 3 ^ 40 * 782804 * 2
def baseEnd_782804 : Nat := 357293075788676008399961

theorem tailTrace_782804 : CollatzResearch.WordTrace tailWord_782804 prefixEnd_782804 357293075788676008399961 := by
  unfold tailWord_782804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275603728021137562261733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19034138304028183416348977 14275603728021137562261733)
  ·
    refine ⟨2676675699003963292924075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14275603728021137562261733 2676675699003963292924075)
    ·
      refine ⟨4015013548505944939386113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676675699003963292924075 4015013548505944939386113)
      ·
        refine ⟨3011260161379458704539585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015013548505944939386113 3011260161379458704539585)
        ·
          refine ⟨2258445121034594028404689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3011260161379458704539585 2258445121034594028404689)
          ·
            refine ⟨1693833840775945521303517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258445121034594028404689 1693833840775945521303517)
            ·
              refine ⟨635187690290979570488819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693833840775945521303517 635187690290979570488819)
              ·
                refine ⟨952781535436469355733229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635187690290979570488819 952781535436469355733229)
                ·
                  refine ⟨357293075788676008399961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952781535436469355733229 357293075788676008399961)
                  ·
                    rfl

theorem cell20_782804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_782804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782804 prefixEnd_782804 := by exact prefixLift 782804
  have htrace : WordTrace (prefixWord ++ tailWord_782804) baseStart_782804 baseEnd_782804 := by
    simpa [prefixWord, tailWord_782804, baseEnd_782804] using wordTrace_append hprefix tailTrace_782804
  have hstable : (prefixWord ++ tailWord_782804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782804).length < 2 ^ (prefixWord ++ tailWord_782804).sum := by decide
  have hdescent : baseEnd_782804 < baseStart_782804 := by decide
  rcases family_descends (prefixWord ++ tailWord_782804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782815 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_782815 : Nat := 118140960795 + 782815 * 2 ^ 59
def prefixEnd_782815 : Nat := 4983230072969 + 3 ^ 40 * 782815 * 2
def baseEnd_782815 : Nat := 357298096488408859033249

theorem tailTrace_782815 : CollatzResearch.WordTrace tailWord_782815 prefixEnd_782815 357298096488408859033249 := by
  unfold tailWord_782815
  simp only [CollatzResearch.WordTrace]
  refine ⟨28551608659002424003173899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19034405772668282668782599 28551608659002424003173899)
  ·
    refine ⟨42827412988503636004760849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28551608659002424003173899 42827412988503636004760849)
    ·
      refine ⟨32120559741377727003570637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42827412988503636004760849 32120559741377727003570637)
      ·
        refine ⟨12045209903016647626338989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32120559741377727003570637 12045209903016647626338989)
        ·
          refine ⟨4516953713631242859877121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12045209903016647626338989 4516953713631242859877121)
          ·
            refine ⟨3387715285223432144907841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4516953713631242859877121 3387715285223432144907841)
            ·
              refine ⟨2540786463917574108680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387715285223432144907841 2540786463917574108680881)
              ·
                refine ⟨1905589847938180581510661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540786463917574108680881 1905589847938180581510661)
                ·
                  refine ⟨357298096488408859033249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905589847938180581510661 357298096488408859033249)
                  ·
                    rfl

theorem cell20_782815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_782815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782815 prefixEnd_782815 := by exact prefixLift 782815
  have htrace : WordTrace (prefixWord ++ tailWord_782815) baseStart_782815 baseEnd_782815 := by
    simpa [prefixWord, tailWord_782815, baseEnd_782815] using wordTrace_append hprefix tailTrace_782815
  have hstable : (prefixWord ++ tailWord_782815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782815).length < 2 ^ (prefixWord ++ tailWord_782815).sum := by decide
  have hdescent : baseEnd_782815 < baseStart_782815 := by decide
  rcases family_descends (prefixWord ++ tailWord_782815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782853 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_782853 : Nat := 118140960795 + 782853 * 2 ^ 59
def prefixEnd_782853 : Nat := 4983230072969 + 3 ^ 40 * 782853 * 2
def baseEnd_782853 : Nat := 357315440723849615766427

theorem tailTrace_782853 : CollatzResearch.WordTrace tailWord_782853 prefixEnd_782853 357315440723849615766427 := by
  unfold tailWord_782853
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552994632864756493057213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19035329755243170995371475 28552994632864756493057213)
  ·
    refine ⟨10707372987324283684896455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28552994632864756493057213 10707372987324283684896455)
    ·
      refine ⟨16061059480986425527344683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707372987324283684896455 16061059480986425527344683)
      ·
        refine ⟨24091589221479638291017025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061059480986425527344683 24091589221479638291017025)
        ·
          refine ⟨18068691916109728718262769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24091589221479638291017025 18068691916109728718262769)
          ·
            refine ⟨13551518937082296538697077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18068691916109728718262769 13551518937082296538697077)
            ·
              refine ⟨1270454900351465300502851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13551518937082296538697077 1270454900351465300502851)
              ·
                refine ⟨1905682350527197950754277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270454900351465300502851 1905682350527197950754277)
                ·
                  refine ⟨357315440723849615766427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905682350527197950754277 357315440723849615766427)
                  ·
                    rfl

theorem cell20_782853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_782853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782853 prefixEnd_782853 := by exact prefixLift 782853
  have htrace : WordTrace (prefixWord ++ tailWord_782853) baseStart_782853 baseEnd_782853 := by
    simpa [prefixWord, tailWord_782853, baseEnd_782853] using wordTrace_append hprefix tailTrace_782853
  have hstable : (prefixWord ++ tailWord_782853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782853).length < 2 ^ (prefixWord ++ tailWord_782853).sum := by decide
  have hdescent : baseEnd_782853 < baseStart_782853 := by decide
  rcases family_descends (prefixWord ++ tailWord_782853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782860 : List Nat := [2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_782860 : Nat := 118140960795 + 782860 * 2 ^ 59
def prefixEnd_782860 : Nat := 4983230072969 + 3 ^ 40 * 782860 * 2
def baseEnd_782860 : Nat := 119106211904862900844355

theorem tailTrace_782860 : CollatzResearch.WordTrace tailWord_782860 prefixEnd_782860 119106211904862900844355 := by
  unfold tailWord_782860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276624971919698344281017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19035499962559597792374689 14276624971919698344281017)
  ·
    refine ⟨10707468728939773758210763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14276624971919698344281017 10707468728939773758210763)
    ·
      refine ⟨16061203093409660637316145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707468728939773758210763 16061203093409660637316145)
      ·
        refine ⟨12045902320057245477987109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16061203093409660637316145 12045902320057245477987109)
        ·
          refine ⟨2258606685010733527122583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12045902320057245477987109 2258606685010733527122583)
          ·
            refine ⟨3387910027516100290683875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258606685010733527122583 3387910027516100290683875)
            ·
              refine ⟨5081865041274150436025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387910027516100290683875 5081865041274150436025813)
              ·
                refine ⟨119106211904862900844355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5081865041274150436025813 119106211904862900844355)
                ·
                  rfl

theorem cell20_782860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_782860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782860 prefixEnd_782860 := by exact prefixLift 782860
  have htrace : WordTrace (prefixWord ++ tailWord_782860) baseStart_782860 baseEnd_782860 := by
    simpa [prefixWord, tailWord_782860, baseEnd_782860] using wordTrace_append hprefix tailTrace_782860
  have hstable : (prefixWord ++ tailWord_782860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782860).length < 2 ^ (prefixWord ++ tailWord_782860).sum := by decide
  have hdescent : baseEnd_782860 < baseStart_782860 := by decide
  rcases family_descends (prefixWord ++ tailWord_782860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782900 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_782900 : Nat := 118140960795 + 782900 * 2 ^ 59
def prefixEnd_782900 : Nat := 4983230072969 + 3 ^ 40 * 782900 * 2
def baseEnd_782900 : Nat := 357336892804526341199569

theorem tailTrace_782900 : CollatzResearch.WordTrace tailWord_782900 prefixEnd_782900 357336892804526341199569 := by
  unfold tailWord_782900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277354431847241760009077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19036472575796322346678769 14277354431847241760009077)
  ·
    refine ⟨1338501977985678915000851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14277354431847241760009077 1338501977985678915000851)
    ·
      refine ⟨2007752966978518372501277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338501977985678915000851 2007752966978518372501277)
      ·
        refine ⟨752907362616944389687979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2007752966978518372501277 752907362616944389687979)
        ·
          refine ⟨1129361043925416584531969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752907362616944389687979 1129361043925416584531969)
          ·
            refine ⟨847020782944062438398977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129361043925416584531969 847020782944062438398977)
            ·
              refine ⟨635265587208046828799233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847020782944062438398977 635265587208046828799233)
              ·
                refine ⟨476449190406035121599425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635265587208046828799233 476449190406035121599425)
                ·
                  refine ⟨357336892804526341199569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476449190406035121599425 357336892804526341199569)
                  ·
                    rfl

theorem cell20_782900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_782900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782900 prefixEnd_782900 := by exact prefixLift 782900
  have htrace : WordTrace (prefixWord ++ tailWord_782900) baseStart_782900 baseEnd_782900 := by
    simpa [prefixWord, tailWord_782900, baseEnd_782900] using wordTrace_append hprefix tailTrace_782900
  have hstable : (prefixWord ++ tailWord_782900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782900).length < 2 ^ (prefixWord ++ tailWord_782900).sum := by decide
  have hdescent : baseEnd_782900 < baseStart_782900 := by decide
  rcases family_descends (prefixWord ++ tailWord_782900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782918 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_782918 : Nat := 118140960795 + 782918 * 2 ^ 59
def prefixEnd_782918 : Nat := 4983230072969 + 3 ^ 40 * 782918 * 2
def baseEnd_782918 : Nat := 357345108494998278599495

theorem tailTrace_782918 : CollatzResearch.WordTrace tailWord_782918 prefixEnd_782918 357345108494998278599495 := by
  unfold tailWord_782918
  simp only [CollatzResearch.WordTrace]
  refine ⟨892355168050914768567919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19036910251752848396115605 892355168050914768567919)
  ·
    refine ⟨1338532752076372152851879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892355168050914768567919 1338532752076372152851879)
    ·
      refine ⟨2007799128114558229277819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338532752076372152851879 2007799128114558229277819)
      ·
        refine ⟨3011698692171837343916729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007799128114558229277819 3011698692171837343916729)
        ·
          refine ⟨2258774019128878007937547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3011698692171837343916729 2258774019128878007937547)
          ·
            refine ⟨3388161028693317011906321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258774019128878007937547 3388161028693317011906321)
            ·
              refine ⟨2541120771519987758929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388161028693317011906321 2541120771519987758929741)
              ·
                refine ⟨952920289319995409598653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541120771519987758929741 952920289319995409598653)
                ·
                  refine ⟨357345108494998278599495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952920289319995409598653 357345108494998278599495)
                  ·
                    rfl

theorem cell20_782918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_782918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782918 prefixEnd_782918 := by exact prefixLift 782918
  have htrace : WordTrace (prefixWord ++ tailWord_782918) baseStart_782918 baseEnd_782918 := by
    simpa [prefixWord, tailWord_782918, baseEnd_782918] using wordTrace_append hprefix tailTrace_782918
  have hstable : (prefixWord ++ tailWord_782918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782918).length < 2 ^ (prefixWord ++ tailWord_782918).sum := by decide
  have hdescent : baseEnd_782918 < baseStart_782918 := by decide
  rcases family_descends (prefixWord ++ tailWord_782918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782922 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_782922 : Nat := 118140960795 + 782922 * 2 ^ 59
def prefixEnd_782922 : Nat := 4983230072969 + 3 ^ 40 * 782922 * 2
def baseEnd_782922 : Nat := 357346934203992042466145

theorem tailTrace_782922 : CollatzResearch.WordTrace tailWord_782922 prefixEnd_782922 357346934203992042466145 := by
  unfold tailWord_782922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138877817403695319329755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19037007513076520851546013 7138877817403695319329755)
  ·
    refine ⟨10708316726105542978994633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7138877817403695319329755 10708316726105542978994633)
    ·
      refine ⟨8031237544579157234245975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10708316726105542978994633 8031237544579157234245975)
      ·
        refine ⟨12046856316868735851368963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8031237544579157234245975 12046856316868735851368963)
        ·
          refine ⟨18070284475303103777053445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12046856316868735851368963 18070284475303103777053445)
          ·
            refine ⟨3388178339119331958197521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18070284475303103777053445 3388178339119331958197521)
            ·
              refine ⟨2541133754339498968648141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388178339119331958197521 2541133754339498968648141)
              ·
                refine ⟨952925157877312113243053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541133754339498968648141 952925157877312113243053)
                ·
                  refine ⟨357346934203992042466145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952925157877312113243053 357346934203992042466145)
                  ·
                    rfl

theorem cell20_782922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_782922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782922 prefixEnd_782922 := by exact prefixLift 782922
  have htrace : WordTrace (prefixWord ++ tailWord_782922) baseStart_782922 baseEnd_782922 := by
    simpa [prefixWord, tailWord_782922, baseEnd_782922] using wordTrace_append hprefix tailTrace_782922
  have hstable : (prefixWord ++ tailWord_782922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782922).length < 2 ^ (prefixWord ++ tailWord_782922).sum := by decide
  have hdescent : baseEnd_782922 < baseStart_782922 := by decide
  rcases family_descends (prefixWord ++ tailWord_782922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782929 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_782929 : Nat := 118140960795 + 782929 * 2 ^ 59
def prefixEnd_782929 : Nat := 4983230072969 + 3 ^ 40 * 782929 * 2
def baseEnd_782929 : Nat := 357350129194731129232783

theorem tailTrace_782929 : CollatzResearch.WordTrace tailWord_782929 prefixEnd_782929 357350129194731129232783 := by
  unfold tailWord_782929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555766580589421472823841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19037177720392947648549227 28555766580589421472823841)
  ·
    refine ⟨21416824935442066104617881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28555766580589421472823841 21416824935442066104617881)
    ·
      refine ⟨16062618701581549578463411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21416824935442066104617881 16062618701581549578463411)
      ·
        refine ⟨24093928052372324367695117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062618701581549578463411 24093928052372324367695117)
        ·
          refine ⟨9035223019639621637885669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24093928052372324367695117 9035223019639621637885669)
          ·
            refine ⟨1694104316182429057103563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9035223019639621637885669 1694104316182429057103563)
            ·
              refine ⟨2541156474273643585655345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694104316182429057103563 2541156474273643585655345)
              ·
                refine ⟨1905867355705232689241509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541156474273643585655345 1905867355705232689241509)
                ·
                  refine ⟨357350129194731129232783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905867355705232689241509 357350129194731129232783)
                  ·
                    rfl

theorem cell20_782929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_782929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782929 prefixEnd_782929 := by exact prefixLift 782929
  have htrace : WordTrace (prefixWord ++ tailWord_782929) baseStart_782929 baseEnd_782929 := by
    simpa [prefixWord, tailWord_782929, baseEnd_782929] using wordTrace_append hprefix tailTrace_782929
  have hstable : (prefixWord ++ tailWord_782929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782929).length < 2 ^ (prefixWord ++ tailWord_782929).sum := by decide
  have hdescent : baseEnd_782929 < baseStart_782929 := by decide
  rcases family_descends (prefixWord ++ tailWord_782929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782960 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_782960 : Nat := 118140960795 + 782960 * 2 ^ 59
def prefixEnd_782960 : Nat := 4983230072969 + 3 ^ 40 * 782960 * 2
def baseEnd_782960 : Nat := 357364278439432799199323

theorem tailTrace_782960 : CollatzResearch.WordTrace tailWord_782960 prefixEnd_782960 357364278439432799199323 := by
  unfold tailWord_782960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278448621738556883601167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19037931495651409178134889 14278448621738556883601167)
  ·
    refine ⟨21417672932607835325401751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278448621738556883601167 21417672932607835325401751)
    ·
      refine ⟨32126509398911752988102627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21417672932607835325401751 32126509398911752988102627)
      ·
        refine ⟨48189764098367629482153941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32126509398911752988102627 48189764098367629482153941)
        ·
          refine ⟨1129447596055491315987983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48189764098367629482153941 1129447596055491315987983)
          ·
            refine ⟨1694171394083236973981975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129447596055491315987983 1694171394083236973981975)
            ·
              refine ⟨2541257091124855460972963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694171394083236973981975 2541257091124855460972963)
              ·
                refine ⟨3811885636687283191459445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541257091124855460972963 3811885636687283191459445)
                ·
                  refine ⟨357364278439432799199323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811885636687283191459445 357364278439432799199323)
                  ·
                    rfl

theorem cell20_782960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_782960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782960 prefixEnd_782960 := by exact prefixLift 782960
  have htrace : WordTrace (prefixWord ++ tailWord_782960) baseStart_782960 baseEnd_782960 := by
    simpa [prefixWord, tailWord_782960, baseEnd_782960] using wordTrace_append hprefix tailTrace_782960
  have hstable : (prefixWord ++ tailWord_782960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782960).length < 2 ^ (prefixWord ++ tailWord_782960).sum := by decide
  have hdescent : baseEnd_782960 < baseStart_782960 := by decide
  rcases family_descends (prefixWord ++ tailWord_782960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782977 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_782977 : Nat := 118140960795 + 782977 * 2 ^ 59
def prefixEnd_782977 : Nat := 4983230072969 + 3 ^ 40 * 782977 * 2
def baseEnd_782977 : Nat := 357372037702656295632587

theorem tailTrace_782977 : CollatzResearch.WordTrace tailWord_782977 prefixEnd_782977 357372037702656295632587 := by
  unfold tailWord_782977
  simp only [CollatzResearch.WordTrace]
  refine ⟨28557517284415525670571185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19038344856277017113714123 28557517284415525670571185)
  ·
    refine ⟨21418137963311644252928389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28557517284415525670571185 21418137963311644252928389)
    ·
      refine ⟨4015900868120933297424073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21418137963311644252928389 4015900868120933297424073)
      ·
        refine ⟨3011925651090699973068055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015900868120933297424073 3011925651090699973068055)
        ·
          refine ⟨4517888476636049959602083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011925651090699973068055 4517888476636049959602083)
          ·
            refine ⟨6776832714954074939403125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517888476636049959602083 6776832714954074939403125)
            ·
              refine ⟨635328067026944525569043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6776832714954074939403125 635328067026944525569043)
              ·
                refine ⟨952992100540416788353565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635328067026944525569043 952992100540416788353565)
                ·
                  refine ⟨357372037702656295632587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952992100540416788353565 357372037702656295632587)
                  ·
                    rfl

theorem cell20_782977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_782977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782977 prefixEnd_782977 := by exact prefixLift 782977
  have htrace : WordTrace (prefixWord ++ tailWord_782977) baseStart_782977 baseEnd_782977 := by
    simpa [prefixWord, tailWord_782977, baseEnd_782977] using wordTrace_append hprefix tailTrace_782977
  have hstable : (prefixWord ++ tailWord_782977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782977).length < 2 ^ (prefixWord ++ tailWord_782977).sum := by decide
  have hdescent : baseEnd_782977 < baseStart_782977 := by decide
  rcases family_descends (prefixWord ++ tailWord_782977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782988 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_782988 : Nat := 118140960795 + 782988 * 2 ^ 59
def prefixEnd_782988 : Nat := 4983230072969 + 3 ^ 40 * 782988 * 2
def baseEnd_782988 : Nat := 357377058402389146265875

theorem tailTrace_782988 : CollatzResearch.WordTrace tailWord_782988 prefixEnd_782988 357377058402389146265875 := by
  unfold tailWord_782988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278959243687837274610809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19038612324917116366147745 14278959243687837274610809)
  ·
    refine ⟨10709219432765877955958107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14278959243687837274610809 10709219432765877955958107)
    ·
      refine ⟨16063829149148816933937161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10709219432765877955958107 16063829149148816933937161)
      ·
        refine ⟨12047871861861612700452871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16063829149148816933937161 12047871861861612700452871)
        ·
          refine ⟨18071807792792419050679307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12047871861861612700452871 18071807792792419050679307)
          ·
            refine ⟨27107711689188628576018961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18071807792792419050679307 27107711689188628576018961)
            ·
              refine ⟨20330783766891471432014221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27107711689188628576018961 20330783766891471432014221)
              ·
                refine ⟨7624043912584301787005333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20330783766891471432014221 7624043912584301787005333)
                ·
                  refine ⟨357377058402389146265875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7624043912584301787005333 357377058402389146265875)
                  ·
                    rfl

theorem cell20_782988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_782988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782988 prefixEnd_782988 := by exact prefixLift 782988
  have htrace : WordTrace (prefixWord ++ tailWord_782988) baseStart_782988 baseEnd_782988 := by
    simpa [prefixWord, tailWord_782988, baseEnd_782988] using wordTrace_append hprefix tailTrace_782988
  have hstable : (prefixWord ++ tailWord_782988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782988).length < 2 ^ (prefixWord ++ tailWord_782988).sum := by decide
  have hdescent : baseEnd_782988 < baseStart_782988 := by decide
  rcases family_descends (prefixWord ++ tailWord_782988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782995 : List Nat := [1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_782995 : Nat := 118140960795 + 782995 * 2 ^ 59
def prefixEnd_782995 : Nat := 4983230072969 + 3 ^ 40 * 782995 * 2
def baseEnd_782995 : Nat := 119126751131042744344171

theorem tailTrace_782995 : CollatzResearch.WordTrace tailWord_782995 prefixEnd_782995 119126751131042744344171 := by
  unfold tailWord_782995
  simp only [CollatzResearch.WordTrace]
  refine ⟨28558173798350314744726439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19038782532233543163150959 28558173798350314744726439)
  ·
    refine ⟨42837260697525472117089659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28558173798350314744726439 42837260697525472117089659)
    ·
      refine ⟨64255891046288208175634489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42837260697525472117089659 64255891046288208175634489)
      ·
        refine ⟨48191918284716156131725867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64255891046288208175634489 48191918284716156131725867)
        ·
          refine ⟨72287877427074234197588801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48191918284716156131725867 72287877427074234197588801)
          ·
            refine ⟨54215908070305675648191601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72287877427074234197588801 54215908070305675648191601)
            ·
              refine ⟨40661931052729256736143701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54215908070305675648191601 40661931052729256736143701)
              ·
                refine ⟨119126751131042744344171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40661931052729256736143701 119126751131042744344171)
                ·
                  rfl

theorem cell20_782995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_782995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_782995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_782995 prefixEnd_782995 := by exact prefixLift 782995
  have htrace : WordTrace (prefixWord ++ tailWord_782995) baseStart_782995 baseEnd_782995 := by
    simpa [prefixWord, tailWord_782995, baseEnd_782995] using wordTrace_append hprefix tailTrace_782995
  have hstable : (prefixWord ++ tailWord_782995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782995).length < 2 ^ (prefixWord ++ tailWord_782995).sum := by decide
  have hdescent : baseEnd_782995 < baseStart_782995 := by decide
  rcases family_descends (prefixWord ++ tailWord_782995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783018 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_783018 : Nat := 118140960795 + 783018 * 2 ^ 59
def prefixEnd_783018 : Nat := 4983230072969 + 3 ^ 40 * 783018 * 2
def baseEnd_783018 : Nat := 357390751219842375265753

theorem tailTrace_783018 : CollatzResearch.WordTrace tailWord_783018 prefixEnd_783018 357390751219842375265753 := by
  unfold tailWord_783018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139753169316747418203427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19039341784844659781875805 7139753169316747418203427)
  ·
    refine ⟨10709629753975121127305141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7139753169316747418203427 10709629753975121127305141)
    ·
      refine ⟨1004027789435167605684857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10709629753975121127305141 1004027789435167605684857)
      ·
        refine ⟨753020842076375704263643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004027789435167605684857 753020842076375704263643)
        ·
          refine ⟨1129531263114563556395465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753020842076375704263643 1129531263114563556395465)
          ·
            refine ⟨847148447335922667296599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129531263114563556395465 847148447335922667296599)
            ·
              refine ⟨1270722671003884000944899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847148447335922667296599 1270722671003884000944899)
              ·
                refine ⟨1906084006505826001417349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270722671003884000944899 1906084006505826001417349)
                ·
                  refine ⟨357390751219842375265753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906084006505826001417349 357390751219842375265753)
                  ·
                    rfl

theorem cell20_783018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_783018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783018 prefixEnd_783018 := by exact prefixLift 783018
  have htrace : WordTrace (prefixWord ++ tailWord_783018) baseStart_783018 baseEnd_783018 := by
    simpa [prefixWord, tailWord_783018, baseEnd_783018] using wordTrace_append hprefix tailTrace_783018
  have hstable : (prefixWord ++ tailWord_783018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783018).length < 2 ^ (prefixWord ++ tailWord_783018).sum := by decide
  have hdescent : baseEnd_783018 < baseStart_783018 := by decide
  rcases family_descends (prefixWord ++ tailWord_783018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783029 : List Nat := [1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_783029 : Nat := 118140960795 + 783029 * 2 ^ 59
def prefixEnd_783029 : Nat := 4983230072969 + 3 ^ 40 * 783029 * 2
def baseEnd_783029 : Nat := 119131923973191741966347

theorem tailTrace_783029 : CollatzResearch.WordTrace tailWord_783029 prefixEnd_783029 119131923973191741966347 := by
  unfold tailWord_783029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559413880227138551464141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19039609253484759034309427 28559413880227138551464141)
  ·
    refine ⟨10709780205085176956799053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28559413880227138551464141 10709780205085176956799053)
    ·
      refine ⟨4016167576906941358799645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10709780205085176956799053 4016167576906941358799645)
      ·
        refine ⟨1506062841340103009549867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4016167576906941358799645 1506062841340103009549867)
        ·
          refine ⟨2259094262010154514324801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506062841340103009549867 2259094262010154514324801)
          ·
            refine ⟨1694320696507615885743601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259094262010154514324801 1694320696507615885743601)
            ·
              refine ⟨1270740522380711914307701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694320696507615885743601 1270740522380711914307701)
              ·
                refine ⟨119131923973191741966347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1270740522380711914307701 119131923973191741966347)
                ·
                  rfl

theorem cell20_783029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_783029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783029 prefixEnd_783029 := by exact prefixLift 783029
  have htrace : WordTrace (prefixWord ++ tailWord_783029) baseStart_783029 baseEnd_783029 := by
    simpa [prefixWord, tailWord_783029, baseEnd_783029] using wordTrace_append hprefix tailTrace_783029
  have hstable : (prefixWord ++ tailWord_783029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783029).length < 2 ^ (prefixWord ++ tailWord_783029).sum := by decide
  have hdescent : baseEnd_783029 < baseStart_783029 := by decide
  rcases family_descends (prefixWord ++ tailWord_783029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783036 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_783036 : Nat := 118140960795 + 783036 * 2 ^ 59
def prefixEnd_783036 : Nat := 4983230072969 + 3 ^ 40 * 783036 * 2
def baseEnd_783036 : Nat := 357398966910314312665679

theorem tailTrace_783036 : CollatzResearch.WordTrace tailWord_783036 prefixEnd_783036 357398966910314312665679 := by
  unfold tailWord_783036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14279834595600889373484481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19039779460801185831312641 14279834595600889373484481)
  ·
    refine ⟨10709875946700667030113361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14279834595600889373484481 10709875946700667030113361)
    ·
      refine ⟨8032406960025500272585021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10709875946700667030113361 8032406960025500272585021)
      ·
        refine ⟨3012152610009562602219383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8032406960025500272585021 3012152610009562602219383)
        ·
          refine ⟨4518228915014343903329075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012152610009562602219383 4518228915014343903329075)
          ·
            refine ⟨6777343372521515854993613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518228915014343903329075 6777343372521515854993613)
            ·
              refine ⟨2541503764695568445622605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6777343372521515854993613 2541503764695568445622605)
              ·
                refine ⟨953063911760838167108477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541503764695568445622605 953063911760838167108477)
                ·
                  refine ⟨357398966910314312665679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953063911760838167108477 357398966910314312665679)
                  ·
                    rfl

theorem cell20_783036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_783036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783036 prefixEnd_783036 := by exact prefixLift 783036
  have htrace : WordTrace (prefixWord ++ tailWord_783036) baseStart_783036 baseEnd_783036 := by
    simpa [prefixWord, tailWord_783036, baseEnd_783036] using wordTrace_append hprefix tailTrace_783036
  have hstable : (prefixWord ++ tailWord_783036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783036).length < 2 ^ (prefixWord ++ tailWord_783036).sum := by decide
  have hdescent : baseEnd_783036 < baseStart_783036 := by decide
  rcases family_descends (prefixWord ++ tailWord_783036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783050 : List Nat := [3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_783050 : Nat := 118140960795 + 783050 * 2 ^ 59
def prefixEnd_783050 : Nat := 4983230072969 + 3 ^ 40 * 783050 * 2
def baseEnd_783050 : Nat := 119135118963930828732985

theorem tailTrace_783050 : CollatzResearch.WordTrace tailWord_783050 prefixEnd_783050 119135118963930828732985 := by
  unfold tailWord_783050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140044953287764784494651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19040119875434039425319069 7140044953287764784494651)
  ·
    refine ⟨10710067429931647176741977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140044953287764784494651 10710067429931647176741977)
    ·
      refine ⟨8032550572448735382556483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10710067429931647176741977 8032550572448735382556483)
      ·
        refine ⟨12048825858673103073834725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8032550572448735382556483 12048825858673103073834725)
        ·
          refine ⟨2259154848501206826344011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12048825858673103073834725 2259154848501206826344011)
          ·
            refine ⟨3388732272751810239516017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259154848501206826344011 3388732272751810239516017)
            ·
              refine ⟨2541549204563857679637013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388732272751810239516017 2541549204563857679637013)
              ·
                refine ⟨119135118963930828732985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2541549204563857679637013 119135118963930828732985)
                ·
                  rfl

theorem cell20_783050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_783050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783050 prefixEnd_783050 := by exact prefixLift 783050
  have htrace : WordTrace (prefixWord ++ tailWord_783050) baseStart_783050 baseEnd_783050 := by
    simpa [prefixWord, tailWord_783050, baseEnd_783050] using wordTrace_append hprefix tailTrace_783050
  have hstable : (prefixWord ++ tailWord_783050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783050).length < 2 ^ (prefixWord ++ tailWord_783050).sum := by decide
  have hdescent : baseEnd_783050 < baseStart_783050 := by decide
  rcases family_descends (prefixWord ++ tailWord_783050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783071 : List Nat := [1, 1, 2, 3, 2, 11]
def baseStart_783071 : Nat := 118140960795 + 783071 * 2 ^ 59
def prefixEnd_783071 : Nat := 4983230072969 + 3 ^ 40 * 783071 * 2
def baseEnd_783071 : Nat := 13237590439407768388847

theorem tailTrace_783071 : CollatzResearch.WordTrace tailWord_783071 prefixEnd_783071 13237590439407768388847 := by
  unfold tailWord_783071
  simp only [CollatzResearch.WordTrace]
  refine ⟨28560945746074979724493067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040630497383319816328711 28560945746074979724493067)
  ·
    refine ⟨42841418619112469586739601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28560945746074979724493067 42841418619112469586739601)
    ·
      refine ⟨32131063964334352190054701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42841418619112469586739601 32131063964334352190054701)
      ·
        refine ⟨12049148986625382071270513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32131063964334352190054701 12049148986625382071270513)
        ·
          refine ⟨9036861739969036553452885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12049148986625382071270513 9036861739969036553452885)
          ·
            refine ⟨13237590439407768388847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9036861739969036553452885 13237590439407768388847)
            ·
              rfl

theorem cell20_783071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_783071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783071 prefixEnd_783071 := by exact prefixLift 783071
  have htrace : WordTrace (prefixWord ++ tailWord_783071) baseStart_783071 baseEnd_783071 := by
    simpa [prefixWord, tailWord_783071, baseEnd_783071] using wordTrace_append hprefix tailTrace_783071
  have hstable : (prefixWord ++ tailWord_783071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783071).length < 2 ^ (prefixWord ++ tailWord_783071).sum := by decide
  have hdescent : baseEnd_783071 < baseStart_783071 := by decide
  rcases family_descends (prefixWord ++ tailWord_783071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783077 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 2]
def baseStart_783077 : Nat := 118140960795 + 783077 * 2 ^ 59
def prefixEnd_783077 : Nat := 4983230072969 + 3 ^ 40 * 783077 * 2
def baseEnd_783077 : Nat := 357417680427500392298845

theorem tailTrace_783077 : CollatzResearch.WordTrace tailWord_783077 prefixEnd_783077 357417680427500392298845 := by
  unfold tailWord_783077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561164584053242749211485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040776389368828499474323 28561164584053242749211485)
  ·
    refine ⟨10710436719019966030954307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28561164584053242749211485 10710436719019966030954307)
    ·
      refine ⟨16065655078529949046431461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10710436719019966030954307 16065655078529949046431461)
      ·
        refine ⟨3012310327224365446205899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16065655078529949046431461 3012310327224365446205899)
        ·
          refine ⟨4518465490836548169308849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012310327224365446205899 4518465490836548169308849)
          ·
            refine ⟨3388849118127411126981637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4518465490836548169308849 3388849118127411126981637)
            ·
              refine ⟨635409209648889586309057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3388849118127411126981637 635409209648889586309057)
              ·
                refine ⟨476556907236667189731793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635409209648889586309057 476556907236667189731793)
                ·
                  refine ⟨357417680427500392298845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476556907236667189731793 357417680427500392298845)
                  ·
                    rfl

theorem cell20_783077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_783077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783077 prefixEnd_783077 := by exact prefixLift 783077
  have htrace : WordTrace (prefixWord ++ tailWord_783077) baseStart_783077 baseEnd_783077 := by
    simpa [prefixWord, tailWord_783077, baseEnd_783077] using wordTrace_append hprefix tailTrace_783077
  have hstable : (prefixWord ++ tailWord_783077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783077).length < 2 ^ (prefixWord ++ tailWord_783077).sum := by decide
  have hdescent : baseEnd_783077 < baseStart_783077 := by decide
  rcases family_descends (prefixWord ++ tailWord_783077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783109 : List Nat := [1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_783109 : Nat := 118140960795 + 783109 * 2 ^ 59
def prefixEnd_783109 : Nat := 4983230072969 + 3 ^ 40 * 783109 * 2
def baseEnd_783109 : Nat := 119144095366483501077349

theorem tailTrace_783109 : CollatzResearch.WordTrace tailWord_783109 prefixEnd_783109 119144095366483501077349 := by
  unfold tailWord_783109
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562331719937312214376381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19041554479958208142917587 28562331719937312214376381)
  ·
    refine ⟨10710874394976492080391143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28562331719937312214376381 10710874394976492080391143)
    ·
      refine ⟨16066311592464738120586715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10710874394976492080391143 16066311592464738120586715)
      ·
        refine ⟨24099467388697107180880073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16066311592464738120586715 24099467388697107180880073)
        ·
          refine ⟨18074600541522830385660055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24099467388697107180880073 18074600541522830385660055)
          ·
            refine ⟨27111900812284245578490083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18074600541522830385660055 27111900812284245578490083)
            ·
              refine ⟨40667851218426368367735125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27111900812284245578490083 40667851218426368367735125)
              ·
                refine ⟨119144095366483501077349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40667851218426368367735125 119144095366483501077349)
                ·
                  rfl

theorem cell20_783109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_783109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783109 prefixEnd_783109 := by exact prefixLift 783109
  have htrace : WordTrace (prefixWord ++ tailWord_783109) baseStart_783109 baseEnd_783109 := by
    simpa [prefixWord, tailWord_783109, baseEnd_783109] using wordTrace_append hprefix tailTrace_783109
  have hstable : (prefixWord ++ tailWord_783109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783109).length < 2 ^ (prefixWord ++ tailWord_783109).sum := by decide
  have hdescent : baseEnd_783109 < baseStart_783109 := by decide
  rcases family_descends (prefixWord ++ tailWord_783109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783136 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_783136 : Nat := 118140960795 + 783136 * 2 ^ 59
def prefixEnd_783136 : Nat := 4983230072969 + 3 ^ 40 * 783136 * 2
def baseEnd_783136 : Nat := 357444609635158409331937

theorem tailTrace_783136 : CollatzResearch.WordTrace tailWord_783136 prefixEnd_783136 357444609635158409331937 := by
  unfold tailWord_783136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281658245419747912804631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19042210993892997217072841 14281658245419747912804631)
  ·
    refine ⟨21422487368129621869206947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14281658245419747912804631 21422487368129621869206947)
    ·
      refine ⟨32133731052194432803810421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21422487368129621869206947 32133731052194432803810421)
      ·
        refine ⟨3012537286143228075357227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32133731052194432803810421 3012537286143228075357227)
        ·
          refine ⟨4518805929214842113035841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012537286143228075357227 4518805929214842113035841)
          ·
            refine ⟨3389104446911131584776881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4518805929214842113035841 3389104446911131584776881)
            ·
              refine ⟨2541828335183348688582661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389104446911131584776881 2541828335183348688582661)
              ·
                refine ⟨476592812846877879109249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2541828335183348688582661 476592812846877879109249)
                ·
                  refine ⟨357444609635158409331937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476592812846877879109249 357444609635158409331937)
                  ·
                    rfl

theorem cell20_783136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_783136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783136 prefixEnd_783136 := by exact prefixLift 783136
  have htrace : WordTrace (prefixWord ++ tailWord_783136) baseStart_783136 baseEnd_783136 := by
    simpa [prefixWord, tailWord_783136, baseEnd_783136] using wordTrace_append hprefix tailTrace_783136
  have hstable : (prefixWord ++ tailWord_783136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783136).length < 2 ^ (prefixWord ++ tailWord_783136).sum := by decide
  have hdescent : baseEnd_783136 < baseStart_783136 := by decide
  rcases family_descends (prefixWord ++ tailWord_783136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783157 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_783157 : Nat := 118140960795 + 783157 * 2 ^ 59
def prefixEnd_783157 : Nat := 4983230072969 + 3 ^ 40 * 783157 * 2
def baseEnd_783157 : Nat := 357454194607375669631851

theorem tailTrace_783157 : CollatzResearch.WordTrace tailWord_783157 prefixEnd_783157 357454194607375669631851 := by
  unfold tailWord_783157
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564082423763416412123725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19042721615842277608082483 28564082423763416412123725)
  ·
    refine ⟨10711530908911281154546397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28564082423763416412123725 10711530908911281154546397)
    ·
      refine ⟨4016824090841730432954899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10711530908911281154546397 4016824090841730432954899)
      ·
        refine ⟨6025236136262595649432349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016824090841730432954899 6025236136262595649432349)
        ·
          refine ⟨2259463551098473368537131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6025236136262595649432349 2259463551098473368537131)
          ·
            refine ⟨3389195326647710052805697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259463551098473368537131 3389195326647710052805697)
            ·
              refine ⟨2541896494985782539604273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389195326647710052805697 2541896494985782539604273)
              ·
                refine ⟨1906422371239336904703205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541896494985782539604273 1906422371239336904703205)
                ·
                  refine ⟨357454194607375669631851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906422371239336904703205 357454194607375669631851)
                  ·
                    rfl

theorem cell20_783157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_783157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783157 prefixEnd_783157 := by exact prefixLift 783157
  have htrace : WordTrace (prefixWord ++ tailWord_783157) baseStart_783157 baseEnd_783157 := by
    simpa [prefixWord, tailWord_783157, baseEnd_783157] using wordTrace_append hprefix tailTrace_783157
  have hstable : (prefixWord ++ tailWord_783157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783157).length < 2 ^ (prefixWord ++ tailWord_783157).sum := by decide
  have hdescent : baseEnd_783157 < baseStart_783157 := by decide
  rcases family_descends (prefixWord ++ tailWord_783157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783191 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 2]
def baseStart_783191 : Nat := 118140960795 + 783191 * 2 ^ 59
def prefixEnd_783191 : Nat := 4983230072969 + 3 ^ 40 * 783191 * 2
def baseEnd_783191 : Nat := 357469713133822662498379

theorem tailTrace_783191 : CollatzResearch.WordTrace tailWord_783191 prefixEnd_783191 357469713133822662498379 := by
  unfold tailWord_783191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565322505640240218861427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19043548337093493479240951 28565322505640240218861427)
  ·
    refine ⟨42847983758460360328292141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565322505640240218861427 42847983758460360328292141)
    ·
      refine ⟨16067993909422635123109553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42847983758460360328292141 16067993909422635123109553)
      ·
        refine ⟨12050995432066976342332165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16067993909422635123109553 12050995432066976342332165)
        ·
          refine ⟨2259561643512558064187281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12050995432066976342332165 2259561643512558064187281)
          ·
            refine ⟨1694671232634418548140461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259561643512558064187281 1694671232634418548140461)
            ·
              refine ⟨635501712237906955552673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1694671232634418548140461 635501712237906955552673)
              ·
                refine ⟨476626284178430216664505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635501712237906955552673 476626284178430216664505)
                ·
                  refine ⟨357469713133822662498379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476626284178430216664505 357469713133822662498379)
                  ·
                    rfl

theorem cell20_783191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2].length) (baseStart_783191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783191 prefixEnd_783191 := by exact prefixLift 783191
  have htrace : WordTrace (prefixWord ++ tailWord_783191) baseStart_783191 baseEnd_783191 := by
    simpa [prefixWord, tailWord_783191, baseEnd_783191] using wordTrace_append hprefix tailTrace_783191
  have hstable : (prefixWord ++ tailWord_783191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783191).length < 2 ^ (prefixWord ++ tailWord_783191).sum := by decide
  have hdescent : baseEnd_783191 < baseStart_783191 := by decide
  rcases family_descends (prefixWord ++ tailWord_783191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783216 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_783216 : Nat := 118140960795 + 783216 * 2 ^ 59
def prefixEnd_783216 : Nat := 4983230072969 + 3 ^ 40 * 783216 * 2
def baseEnd_783216 : Nat := 357481123815033686664943

theorem tailTrace_783216 : CollatzResearch.WordTrace tailWord_783216 prefixEnd_783216 357481123815033686664943 := by
  unfold tailWord_783216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283117165274834744260751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19044156220366446325681001 14283117165274834744260751)
  ·
    refine ⟨21424675747912252116391127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283117165274834744260751 21424675747912252116391127)
    ·
      refine ⟨32137013621868378174586691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21424675747912252116391127 32137013621868378174586691)
      ·
        refine ⟨48205520432802567261880037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137013621868378174586691 48205520432802567261880037)
        ·
          refine ⟨9038535081150481361602507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48205520432802567261880037 9038535081150481361602507)
          ·
            refine ⟨13557802621725722042403761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038535081150481361602507 13557802621725722042403761)
            ·
              refine ⟨10168351966294291531802821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557802621725722042403761 10168351966294291531802821)
              ·
                refine ⟨1906565993680179662213029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10168351966294291531802821 1906565993680179662213029)
                ·
                  refine ⟨357481123815033686664943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906565993680179662213029 357481123815033686664943)
                  ·
                    rfl

theorem cell20_783216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_783216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783216 prefixEnd_783216 := by exact prefixLift 783216
  have htrace : WordTrace (prefixWord ++ tailWord_783216) baseStart_783216 baseEnd_783216 := by
    simpa [prefixWord, tailWord_783216, baseEnd_783216] using wordTrace_append hprefix tailTrace_783216
  have hstable : (prefixWord ++ tailWord_783216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783216).length < 2 ^ (prefixWord ++ tailWord_783216).sum := by decide
  have hdescent : baseEnd_783216 < baseStart_783216 := by decide
  rcases family_descends (prefixWord ++ tailWord_783216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783284 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_783284 : Nat := 118140960795 + 783284 * 2 ^ 59
def prefixEnd_783284 : Nat := 4983230072969 + 3 ^ 40 * 783284 * 2
def baseEnd_783284 : Nat := 357512160867927672397999

theorem tailTrace_783284 : CollatzResearch.WordTrace tailWord_783284 prefixEnd_783284 357512160867927672397999 := by
  unfold tailWord_783284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284357247151658550998453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19045809662868878067997937 14284357247151658550998453)
  ·
    refine ⟨1339158491920467989156105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14284357247151658550998453 1339158491920467989156105)
    ·
      refine ⟨1004368868940350991867079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339158491920467989156105 1004368868940350991867079)
      ·
        refine ⟨1506553303410526487800619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004368868940350991867079 1506553303410526487800619)
        ·
          refine ⟨2259829955115789731700929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506553303410526487800619 2259829955115789731700929)
          ·
            refine ⟨1694872466336842298775697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259829955115789731700929 1694872466336842298775697)
            ·
              refine ⟨1271154349752631724081773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694872466336842298775697 1271154349752631724081773)
              ·
                refine ⟨476682881157236896530665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271154349752631724081773 476682881157236896530665)
                ·
                  refine ⟨357512160867927672397999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476682881157236896530665 357512160867927672397999)
                  ·
                    rfl

theorem cell20_783284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_783284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783284 prefixEnd_783284 := by exact prefixLift 783284
  have htrace : WordTrace (prefixWord ++ tailWord_783284) baseStart_783284 baseEnd_783284 := by
    simpa [prefixWord, tailWord_783284, baseEnd_783284] using wordTrace_append hprefix tailTrace_783284
  have hstable : (prefixWord ++ tailWord_783284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783284).length < 2 ^ (prefixWord ++ tailWord_783284).sum := by decide
  have hdescent : baseEnd_783284 < baseStart_783284 := by decide
  rcases family_descends (prefixWord ++ tailWord_783284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783285 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_783285 : Nat := 118140960795 + 783285 * 2 ^ 59
def prefixEnd_783285 : Nat := 4983230072969 + 3 ^ 40 * 783285 * 2
def baseEnd_783285 : Nat := 357512617295176113364661

theorem tailTrace_783285 : CollatzResearch.WordTrace tailWord_783285 prefixEnd_783285 357512617295176113364661 := by
  unfold tailWord_783285
  simp only [CollatzResearch.WordTrace]
  refine ⟨28568750967299694272783309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19045833978199796181855539 28568750967299694272783309)
  ·
    refine ⟨10713281612737385352293741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28568750967299694272783309 10713281612737385352293741)
    ·
      refine ⟨4017480604776519507110153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10713281612737385352293741 4017480604776519507110153)
      ·
        refine ⟨3013110453582389630332615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017480604776519507110153 3013110453582389630332615)
        ·
          refine ⟨4519665680373584445498923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013110453582389630332615 4519665680373584445498923)
          ·
            refine ⟨6779498520560376668248385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519665680373584445498923 6779498520560376668248385)
            ·
              refine ⟨5084623890420282501186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6779498520560376668248385 5084623890420282501186289)
              ·
                refine ⟨3813467917815211875889717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5084623890420282501186289 3813467917815211875889717)
                ·
                  refine ⟨357512617295176113364661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813467917815211875889717 357512617295176113364661)
                  ·
                    rfl

theorem cell20_783285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_783285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783285 prefixEnd_783285 := by exact prefixLift 783285
  have htrace : WordTrace (prefixWord ++ tailWord_783285) baseStart_783285 baseEnd_783285 := by
    simpa [prefixWord, tailWord_783285, baseEnd_783285] using wordTrace_append hprefix tailTrace_783285
  have hstable : (prefixWord ++ tailWord_783285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783285).length < 2 ^ (prefixWord ++ tailWord_783285).sum := by decide
  have hdescent : baseEnd_783285 < baseStart_783285 := by decide
  rcases family_descends (prefixWord ++ tailWord_783285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783288 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_783288 : Nat := 118140960795 + 783288 * 2 ^ 59
def prefixEnd_783288 : Nat := 4983230072969 + 3 ^ 40 * 783288 * 2
def baseEnd_783288 : Nat := 357513986576921436264649

theorem tailTrace_783288 : CollatzResearch.WordTrace tailWord_783288 prefixEnd_783288 357513986576921436264649 := by
  unfold tailWord_783288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284430193144412892571259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19045906924192550523428345 14284430193144412892571259)
  ·
    refine ⟨21426645289716619338856889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14284430193144412892571259 21426645289716619338856889)
    ·
      refine ⟨16069983967287464504142667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21426645289716619338856889 16069983967287464504142667)
      ·
        refine ⟨24104975950931196756214001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16069983967287464504142667 24104975950931196756214001)
        ·
          refine ⟨18078731963198397567160501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24104975950931196756214001 18078731963198397567160501)
          ·
            refine ⟨1694881121549849771921297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18078731963198397567160501 1694881121549849771921297)
            ·
              refine ⟨1271160841162387328940973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694881121549849771921297 1271160841162387328940973)
              ·
                refine ⟨476685315435895248352865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271160841162387328940973 476685315435895248352865)
                ·
                  refine ⟨357513986576921436264649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476685315435895248352865 357513986576921436264649)
                  ·
                    rfl

theorem cell20_783288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_783288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783288 prefixEnd_783288 := by exact prefixLift 783288
  have htrace : WordTrace (prefixWord ++ tailWord_783288) baseStart_783288 baseEnd_783288 := by
    simpa [prefixWord, tailWord_783288, baseEnd_783288] using wordTrace_append hprefix tailTrace_783288
  have hstable : (prefixWord ++ tailWord_783288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783288).length < 2 ^ (prefixWord ++ tailWord_783288).sum := by decide
  have hdescent : baseEnd_783288 < baseStart_783288 := by decide
  rcases family_descends (prefixWord ++ tailWord_783288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783333 : List Nat := [1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_783333 : Nat := 118140960795 + 783333 * 2 ^ 59
def prefixEnd_783333 : Nat := 4983230072969 + 3 ^ 40 * 783333 * 2
def baseEnd_783333 : Nat := 119178175267700426588155

theorem tailTrace_783333 : CollatzResearch.WordTrace tailWord_783333 prefixEnd_783333 119178175267700426588155 := by
  unfold tailWord_783333
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570501671125798470530653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19047001114083865647020435 28570501671125798470530653)
  ·
    refine ⟨10713938126672174426448995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28570501671125798470530653 10713938126672174426448995)
    ·
      refine ⟨16070907190008261639673493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10713938126672174426448995 16070907190008261639673493)
      ·
        refine ⟨753323774531637264359695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16070907190008261639673493 753323774531637264359695)
        ·
          refine ⟨1129985661797455896539543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753323774531637264359695 1129985661797455896539543)
          ·
            refine ⟨1694978492696183844809315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129985661797455896539543 1694978492696183844809315)
            ·
              refine ⟨2542467739044275767213973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694978492696183844809315 2542467739044275767213973)
              ·
                refine ⟨119178175267700426588155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2542467739044275767213973 119178175267700426588155)
                ·
                  rfl

theorem cell20_783333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_783333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783333 prefixEnd_783333 := by exact prefixLift 783333
  have htrace : WordTrace (prefixWord ++ tailWord_783333) baseStart_783333 baseEnd_783333 := by
    simpa [prefixWord, tailWord_783333, baseEnd_783333] using wordTrace_append hprefix tailTrace_783333
  have hstable : (prefixWord ++ tailWord_783333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783333).length < 2 ^ (prefixWord ++ tailWord_783333).sum := by decide
  have hdescent : baseEnd_783333 < baseStart_783333 := by decide
  rcases family_descends (prefixWord ++ tailWord_783333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783361 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_783361 : Nat := 118140960795 + 783361 * 2 ^ 59
def prefixEnd_783361 : Nat := 4983230072969 + 3 ^ 40 * 783361 * 2
def baseEnd_783361 : Nat := 357547305766057626831017

theorem tailTrace_783361 : CollatzResearch.WordTrace tailWord_783361 prefixEnd_783361 357547305766057626831017 := by
  unfold tailWord_783361
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571522915024359252549937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19047681943349572835033291 28571522915024359252549937)
  ·
    refine ⟨21428642186268269439412453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28571522915024359252549937 21428642186268269439412453)
    ·
      refine ⟨4017870409925300519889835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21428642186268269439412453 4017870409925300519889835)
      ·
        refine ⟨6026805614887950779834753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017870409925300519889835 6026805614887950779834753)
        ·
          refine ⟨4520104211165963084876065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6026805614887950779834753 4520104211165963084876065)
          ·
            refine ⟨3390078158374472313657049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520104211165963084876065 3390078158374472313657049)
            ·
              refine ⟨2542558618780854235242787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390078158374472313657049 2542558618780854235242787)
              ·
                refine ⟨3813837928171281352864181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542558618780854235242787 3813837928171281352864181)
                ·
                  refine ⟨357547305766057626831017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813837928171281352864181 357547305766057626831017)
                  ·
                    rfl

theorem cell20_783361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_783361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783361 prefixEnd_783361 := by exact prefixLift 783361
  have htrace : WordTrace (prefixWord ++ tailWord_783361) baseStart_783361 baseEnd_783361 := by
    simpa [prefixWord, tailWord_783361, baseEnd_783361] using wordTrace_append hprefix tailTrace_783361
  have hstable : (prefixWord ++ tailWord_783361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783361).length < 2 ^ (prefixWord ++ tailWord_783361).sum := by decide
  have hdescent : baseEnd_783361 < baseStart_783361 := by decide
  rcases family_descends (prefixWord ++ tailWord_783361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783416 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_783416 : Nat := 118140960795 + 783416 * 2 ^ 59
def prefixEnd_783416 : Nat := 4983230072969 + 3 ^ 40 * 783416 * 2
def baseEnd_783416 : Nat := 357572409264721879997459

theorem tailTrace_783416 : CollatzResearch.WordTrace tailWord_783416 prefixEnd_783416 357572409264721879997459 := by
  unfold tailWord_783416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286764464912551822901051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19049019286550069097201401 14286764464912551822901051)
  ·
    refine ⟨21430146697368827734351577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14286764464912551822901051 21430146697368827734351577)
    ·
      refine ⟨16072610023026620800763683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21430146697368827734351577 16072610023026620800763683)
      ·
        refine ⟨24108915034539931201145525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16072610023026620800763683 24108915034539931201145525)
        ·
          refine ⟨2260210784488118550107393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24108915034539931201145525 2260210784488118550107393)
          ·
            refine ⟨1695158088366088912580545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260210784488118550107393 1695158088366088912580545)
            ·
              refine ⟨1271368566274566684435409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695158088366088912580545 1271368566274566684435409)
              ·
                refine ⟨953526424705925013326557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271368566274566684435409 953526424705925013326557)
                ·
                  refine ⟨357572409264721879997459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953526424705925013326557 357572409264721879997459)
                  ·
                    rfl

theorem cell20_783416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_783416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783416 prefixEnd_783416 := by exact prefixLift 783416
  have htrace : WordTrace (prefixWord ++ tailWord_783416) baseStart_783416 baseEnd_783416 := by
    simpa [prefixWord, tailWord_783416, baseEnd_783416] using wordTrace_append hprefix tailTrace_783416
  have hstable : (prefixWord ++ tailWord_783416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783416).length < 2 ^ (prefixWord ++ tailWord_783416).sum := by decide
  have hdescent : baseEnd_783416 < baseStart_783416 := by decide
  rcases family_descends (prefixWord ++ tailWord_783416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783444 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_783444 : Nat := 118140960795 + 783444 * 2 ^ 59
def prefixEnd_783444 : Nat := 4983230072969 + 3 ^ 40 * 783444 * 2
def baseEnd_783444 : Nat := 357585189227678227064011

theorem tailTrace_783444 : CollatzResearch.WordTrace tailWord_783444 prefixEnd_783444 357585189227678227064011 := by
  unfold tailWord_783444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287275086861832213910693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19049700115815776285214257 14287275086861832213910693)
  ·
    refine ⟨2678864078786593540108255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14287275086861832213910693 2678864078786593540108255)
    ·
      refine ⟨4018296118179890310162383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678864078786593540108255 4018296118179890310162383)
      ·
        refine ⟨6027444177269835465243575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018296118179890310162383 6027444177269835465243575)
        ·
          refine ⟨9041166265904753197865363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027444177269835465243575 9041166265904753197865363)
          ·
            refine ⟨13561749398857129796798045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041166265904753197865363 13561749398857129796798045)
            ·
              refine ⟨5085656024571423673799267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13561749398857129796798045 5085656024571423673799267)
              ·
                refine ⟨7628484036857135510698901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085656024571423673799267 7628484036857135510698901)
                ·
                  refine ⟨357585189227678227064011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7628484036857135510698901 357585189227678227064011)
                  ·
                    rfl

theorem cell20_783444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_783444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783444 prefixEnd_783444 := by exact prefixLift 783444
  have htrace : WordTrace (prefixWord ++ tailWord_783444) baseStart_783444 baseEnd_783444 := by
    simpa [prefixWord, tailWord_783444, baseEnd_783444] using wordTrace_append hprefix tailTrace_783444
  have hstable : (prefixWord ++ tailWord_783444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783444).length < 2 ^ (prefixWord ++ tailWord_783444).sum := by decide
  have hdescent : baseEnd_783444 < baseStart_783444 := by decide
  rcases family_descends (prefixWord ++ tailWord_783444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783478 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_783478 : Nat := 118140960795 + 783478 * 2 ^ 59
def prefixEnd_783478 : Nat := 4983230072969 + 3 ^ 40 * 783478 * 2
def baseEnd_783478 : Nat := 357600707754125219930539

theorem tailTrace_783478 : CollatzResearch.WordTrace tailWord_783478 prefixEnd_783478 357600707754125219930539 := by
  unfold tailWord_783478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785986890975030514659943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19050526837066992156372725 1785986890975030514659943)
  ·
    refine ⟨2678980336462545771989915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1785986890975030514659943 2678980336462545771989915)
    ·
      refine ⟨4018470504693818657984873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678980336462545771989915 4018470504693818657984873)
      ·
        refine ⟨3013852878520363993488655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4018470504693818657984873 3013852878520363993488655)
        ·
          refine ⟨4520779317780545990232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013852878520363993488655 4520779317780545990232983)
          ·
            refine ⟨6781168976670818985349475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520779317780545990232983 6781168976670818985349475)
            ·
              refine ⟨10171753465006228478024213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781168976670818985349475 10171753465006228478024213)
              ·
                refine ⟨476800943672166959907385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10171753465006228478024213 476800943672166959907385)
                ·
                  refine ⟨357600707754125219930539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476800943672166959907385 357600707754125219930539)
                  ·
                    rfl

theorem cell20_783478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_783478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783478 prefixEnd_783478 := by exact prefixLift 783478
  have htrace : WordTrace (prefixWord ++ tailWord_783478) baseStart_783478 baseEnd_783478 := by
    simpa [prefixWord, tailWord_783478, baseEnd_783478] using wordTrace_append hprefix tailTrace_783478
  have hstable : (prefixWord ++ tailWord_783478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783478).length < 2 ^ (prefixWord ++ tailWord_783478).sum := by decide
  have hdescent : baseEnd_783478 < baseStart_783478 := by decide
  rcases family_descends (prefixWord ++ tailWord_783478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783503 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_783503 : Nat := 118140960795 + 783503 * 2 ^ 59
def prefixEnd_783503 : Nat := 4983230072969 + 3 ^ 40 * 783503 * 2
def baseEnd_783503 : Nat := 357612118435336244097103

theorem tailTrace_783503 : CollatzResearch.WordTrace tailWord_783503 prefixEnd_783503 357612118435336244097103 := by
  unfold tailWord_783503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28576702080509917504219163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19051134720339945002812775 28576702080509917504219163)
  ·
    refine ⟨42865053120764876256328745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28576702080509917504219163 42865053120764876256328745)
    ·
      refine ⟨32148789840573657192246559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42865053120764876256328745 32148789840573657192246559)
      ·
        refine ⟨48223184760860485788369839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32148789840573657192246559 48223184760860485788369839)
        ·
          refine ⟨72334777141290728682554759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48223184760860485788369839 72334777141290728682554759)
          ·
            refine ⟨108502165711936093023832139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72334777141290728682554759 108502165711936093023832139)
            ·
              refine ⟨162753248567904139535748209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108502165711936093023832139 162753248567904139535748209)
              ·
                refine ⟨122064936425928104651811157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162753248567904139535748209 122064936425928104651811157)
                ·
                  refine ⟨357612118435336244097103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122064936425928104651811157 357612118435336244097103)
                  ·
                    rfl

theorem cell20_783503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_783503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783503 prefixEnd_783503 := by exact prefixLift 783503
  have htrace : WordTrace (prefixWord ++ tailWord_783503) baseStart_783503 baseEnd_783503 := by
    simpa [prefixWord, tailWord_783503, baseEnd_783503] using wordTrace_append hprefix tailTrace_783503
  have hstable : (prefixWord ++ tailWord_783503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783503).length < 2 ^ (prefixWord ++ tailWord_783503).sum := by decide
  have hdescent : baseEnd_783503 < baseStart_783503 := by decide
  rcases family_descends (prefixWord ++ tailWord_783503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783506 : List Nat := [3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_783506 : Nat := 118140960795 + 783506 * 2 ^ 59
def prefixEnd_783506 : Nat := 4983230072969 + 3 ^ 40 * 783506 * 2
def baseEnd_783506 : Nat := 119204495905693855665697

theorem tailTrace_783506 : CollatzResearch.WordTrace tailWord_783506 prefixEnd_783506 119204495905693855665697 := by
  unfold tailWord_783506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144202874874762254144593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19051207666332699344385581 7144202874874762254144593)
  ·
    refine ⟨5358152156156071690608445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7144202874874762254144593 5358152156156071690608445)
    ·
      refine ⟨2009307058558526883978167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5358152156156071690608445 2009307058558526883978167)
      ·
        refine ⟨3013960587837790325967251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009307058558526883978167 3013960587837790325967251)
        ·
          refine ⟨4520940881756685488950877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013960587837790325967251 4520940881756685488950877)
          ·
            refine ⟨1695352830658757058356579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4520940881756685488950877 1695352830658757058356579)
            ·
              refine ⟨2543029245988135587534869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695352830658757058356579 2543029245988135587534869)
              ·
                refine ⟨119204495905693855665697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2543029245988135587534869 119204495905693855665697)
                ·
                  rfl

theorem cell20_783506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_783506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783506 prefixEnd_783506 := by exact prefixLift 783506
  have htrace : WordTrace (prefixWord ++ tailWord_783506) baseStart_783506 baseEnd_783506 := by
    simpa [prefixWord, tailWord_783506, baseEnd_783506] using wordTrace_append hprefix tailTrace_783506
  have hstable : (prefixWord ++ tailWord_783506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783506).length < 2 ^ (prefixWord ++ tailWord_783506).sum := by decide
  have hdescent : baseEnd_783506 < baseStart_783506 := by decide
  rcases family_descends (prefixWord ++ tailWord_783506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783516 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_783516 : Nat := 118140960795 + 783516 * 2 ^ 59
def prefixEnd_783516 : Nat := 4983230072969 + 3 ^ 40 * 783516 * 2
def baseEnd_783516 : Nat := 357618051989565976663717

theorem tailTrace_783516 : CollatzResearch.WordTrace tailWord_783516 prefixEnd_783516 357618051989565976663717 := by
  unfold tailWord_783516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288588114731410362221201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19051450819641880482961601 14288588114731410362221201)
  ·
    refine ⟨10716441086048557771665901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14288588114731410362221201 10716441086048557771665901)
    ·
      refine ⟨4018665407268209164374713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10716441086048557771665901 4018665407268209164374713)
      ·
        refine ⟨3013999055451156873281035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4018665407268209164374713 3013999055451156873281035)
        ·
          refine ⟨4520998583176735309921553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013999055451156873281035 4520998583176735309921553)
          ·
            refine ⟨3390748937382551482441165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520998583176735309921553 3390748937382551482441165)
            ·
              refine ⟨1271530851518456805915437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3390748937382551482441165 1271530851518456805915437)
              ·
                refine ⟨476824069319421302218289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271530851518456805915437 476824069319421302218289)
                ·
                  refine ⟨357618051989565976663717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476824069319421302218289 357618051989565976663717)
                  ·
                    rfl

theorem cell20_783516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_783516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783516 prefixEnd_783516 := by exact prefixLift 783516
  have htrace : WordTrace (prefixWord ++ tailWord_783516) baseStart_783516 baseEnd_783516 := by
    simpa [prefixWord, tailWord_783516, baseEnd_783516] using wordTrace_append hprefix tailTrace_783516
  have hstable : (prefixWord ++ tailWord_783516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783516).length < 2 ^ (prefixWord ++ tailWord_783516).sum := by decide
  have hdescent : baseEnd_783516 < baseStart_783516 := by decide
  rcases family_descends (prefixWord ++ tailWord_783516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783530 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_783530 : Nat := 118140960795 + 783530 * 2 ^ 59
def prefixEnd_783530 : Nat := 4983230072969 + 3 ^ 40 * 783530 * 2
def baseEnd_783530 : Nat := 357624441971044150196993

theorem tailTrace_783530 : CollatzResearch.WordTrace tailWord_783530 prefixEnd_783530 357624441971044150196993 := by
  unfold tailWord_783530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144421712853025278863011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19051791234274734076968029 7144421712853025278863011)
  ·
    refine ⟨10716632569279537918294517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7144421712853025278863011 10716632569279537918294517)
    ·
      refine ⟨1004684303369956679840111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10716632569279537918294517 1004684303369956679840111)
      ·
        refine ⟨1507026455054935019760167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004684303369956679840111 1507026455054935019760167)
        ·
          refine ⟨2260539682582402529640251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507026455054935019760167 2260539682582402529640251)
          ·
            refine ⟨3390809523873603794460377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260539682582402529640251 3390809523873603794460377)
            ·
              refine ⟨2543107142905202845845283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390809523873603794460377 2543107142905202845845283)
              ·
                refine ⟨3814660714357804268767925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543107142905202845845283 3814660714357804268767925)
                ·
                  refine ⟨357624441971044150196993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814660714357804268767925 357624441971044150196993)
                  ·
                    rfl

theorem cell20_783530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_783530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783530 prefixEnd_783530 := by exact prefixLift 783530
  have htrace : WordTrace (prefixWord ++ tailWord_783530) baseStart_783530 baseEnd_783530 := by
    simpa [prefixWord, tailWord_783530, baseEnd_783530] using wordTrace_append hprefix tailTrace_783530
  have hstable : (prefixWord ++ tailWord_783530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783530).length < 2 ^ (prefixWord ++ tailWord_783530).sum := by decide
  have hdescent : baseEnd_783530 < baseStart_783530 := by decide
  rcases family_descends (prefixWord ++ tailWord_783530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783533 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 4]
def baseStart_783533 : Nat := 118140960795 + 783533 * 2 ^ 59
def prefixEnd_783533 : Nat := 4983230072969 + 3 ^ 40 * 783533 * 2
def baseEnd_783533 : Nat := 357625811252789473096981

theorem tailTrace_783533 : CollatzResearch.WordTrace tailWord_783533 prefixEnd_783533 357625811252789473096981 := by
  unfold tailWord_783533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28577796270401232627811253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19051864180267488418540835 28577796270401232627811253)
  ·
    refine ⟨2679168400350115558857305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28577796270401232627811253 2679168400350115558857305)
    ·
      refine ⟨2009376300262586669142979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679168400350115558857305 2009376300262586669142979)
      ·
        refine ⟨3014064450393880003714469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009376300262586669142979 3014064450393880003714469)
        ·
          refine ⟨565137084448852500696463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3014064450393880003714469 565137084448852500696463)
          ·
            refine ⟨847705626673278751044695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565137084448852500696463 847705626673278751044695)
            ·
              refine ⟨1271558440009918126567043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847705626673278751044695 1271558440009918126567043)
              ·
                refine ⟨1907337660014877189850565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271558440009918126567043 1907337660014877189850565)
                ·
                  refine ⟨357625811252789473096981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907337660014877189850565 357625811252789473096981)
                  ·
                    rfl

theorem cell20_783533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_783533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783533 prefixEnd_783533 := by exact prefixLift 783533
  have htrace : WordTrace (prefixWord ++ tailWord_783533) baseStart_783533 baseEnd_783533 := by
    simpa [prefixWord, tailWord_783533, baseEnd_783533] using wordTrace_append hprefix tailTrace_783533
  have hstable : (prefixWord ++ tailWord_783533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783533).length < 2 ^ (prefixWord ++ tailWord_783533).sum := by decide
  have hdescent : baseEnd_783533 < baseStart_783533 := by decide
  rcases family_descends (prefixWord ++ tailWord_783533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783537 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_783537 : Nat := 118140960795 + 783537 * 2 ^ 59
def prefixEnd_783537 : Nat := 4983230072969 + 3 ^ 40 * 783537 * 2
def baseEnd_783537 : Nat := 357627636961783236963631

theorem tailTrace_783537 : CollatzResearch.WordTrace tailWord_783537 prefixEnd_783537 357627636961783236963631 := by
  unfold tailWord_783537
  simp only [CollatzResearch.WordTrace]
  refine ⟨28577942162386741310956865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19051961441591160873971243 28577942162386741310956865)
  ·
    refine ⟨21433456621790055983217649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28577942162386741310956865 21433456621790055983217649)
    ·
      refine ⟨16075092466342541987413237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21433456621790055983217649 16075092466342541987413237)
      ·
        refine ⟨1507039918719613311319991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16075092466342541987413237 1507039918719613311319991)
        ·
          refine ⟨2260559878079419966979987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507039918719613311319991 2260559878079419966979987)
          ·
            refine ⟨3390839817119129950469981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260559878079419966979987 3390839817119129950469981)
            ·
              refine ⟨1271564931419673731426243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3390839817119129950469981 1271564931419673731426243)
              ·
                refine ⟨1907347397129510597139365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271564931419673731426243 1907347397129510597139365)
                ·
                  refine ⟨357627636961783236963631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907347397129510597139365 357627636961783236963631)
                  ·
                    rfl

theorem cell20_783537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_783537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783537 prefixEnd_783537 := by exact prefixLift 783537
  have htrace : WordTrace (prefixWord ++ tailWord_783537) baseStart_783537 baseEnd_783537 := by
    simpa [prefixWord, tailWord_783537, baseEnd_783537] using wordTrace_append hprefix tailTrace_783537
  have hstable : (prefixWord ++ tailWord_783537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783537).length < 2 ^ (prefixWord ++ tailWord_783537).sum := by decide
  have hdescent : baseEnd_783537 < baseStart_783537 := by decide
  rcases family_descends (prefixWord ++ tailWord_783537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783599 : List Nat := [1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_783599 : Nat := 118140960795 + 783599 * 2 ^ 59
def prefixEnd_783599 : Nat := 4983230072969 + 3 ^ 40 * 783599 * 2
def baseEnd_783599 : Nat := 119218645150395525632237

theorem tailTrace_783599 : CollatzResearch.WordTrace tailWord_783599 prefixEnd_783599 119218645150395525632237 := by
  unfold tailWord_783599
  simp only [CollatzResearch.WordTrace]
  refine ⟨28580203488162125899713851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19053468992108083933142567 28580203488162125899713851)
  ·
    refine ⟨42870305232243188849570777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28580203488162125899713851 42870305232243188849570777)
    ·
      refine ⟨32152728924182391637178083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42870305232243188849570777 32152728924182391637178083)
      ·
        refine ⟨48229093386273587455767125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32152728924182391637178083 48229093386273587455767125)
        ·
          refine ⟨565184688120393602997271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 48229093386273587455767125 565184688120393602997271)
          ·
            refine ⟨847777032180590404495907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565184688120393602997271 847777032180590404495907)
            ·
              refine ⟨1271665548270885606743861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847777032180590404495907 1271665548270885606743861)
              ·
                refine ⟨119218645150395525632237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271665548270885606743861 119218645150395525632237)
                ·
                  rfl

theorem cell20_783599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_783599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783599 prefixEnd_783599 := by exact prefixLift 783599
  have htrace : WordTrace (prefixWord ++ tailWord_783599) baseStart_783599 baseEnd_783599 := by
    simpa [prefixWord, tailWord_783599, baseEnd_783599] using wordTrace_append hprefix tailTrace_783599
  have hstable : (prefixWord ++ tailWord_783599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783599).length < 2 ^ (prefixWord ++ tailWord_783599).sum := by decide
  have hdescent : baseEnd_783599 < baseStart_783599 := by decide
  rcases family_descends (prefixWord ++ tailWord_783599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783603 : List Nat := [1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_783603 : Nat := 118140960795 + 783603 * 2 ^ 59
def prefixEnd_783603 : Nat := 4983230072969 + 3 ^ 40 * 783603 * 2
def baseEnd_783603 : Nat := 119219253720060113587787

theorem tailTrace_783603 : CollatzResearch.WordTrace tailWord_783603 prefixEnd_783603 119219253720060113587787 := by
  unfold tailWord_783603
  simp only [CollatzResearch.WordTrace]
  refine ⟨28580349380147634582859463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19053566253431756388572975 28580349380147634582859463)
  ·
    refine ⟨42870524070221451874289195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28580349380147634582859463 42870524070221451874289195)
    ·
      refine ⟨64305786105332177811433793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42870524070221451874289195 64305786105332177811433793)
      ·
        refine ⟨48229339578999133358575345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64305786105332177811433793 48229339578999133358575345)
        ·
          refine ⟨36172004684249350018931509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48229339578999133358575345 36172004684249350018931509)
          ·
            refine ⟨3391125439148376564274829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36172004684249350018931509 3391125439148376564274829)
            ·
              refine ⟨1271672039680641211603061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3391125439148376564274829 1271672039680641211603061)
              ·
                refine ⟨119219253720060113587787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271672039680641211603061 119219253720060113587787)
                ·
                  rfl

theorem cell20_783603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_783603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783603 prefixEnd_783603 := by exact prefixLift 783603
  have htrace : WordTrace (prefixWord ++ tailWord_783603) baseStart_783603 baseEnd_783603 := by
    simpa [prefixWord, tailWord_783603, baseEnd_783603] using wordTrace_append hprefix tailTrace_783603
  have hstable : (prefixWord ++ tailWord_783603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783603).length < 2 ^ (prefixWord ++ tailWord_783603).sum := by decide
  have hdescent : baseEnd_783603 < baseStart_783603 := by decide
  rcases family_descends (prefixWord ++ tailWord_783603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783630 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_783630 : Nat := 118140960795 + 783630 * 2 ^ 59
def prefixEnd_783630 : Nat := 4983230072969 + 3 ^ 40 * 783630 * 2
def baseEnd_783630 : Nat := 357670084695888246863251

theorem tailTrace_783630 : CollatzResearch.WordTrace tailWord_783630 prefixEnd_783630 357670084695888246863251 := by
  unfold tailWord_783630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572666768881227274261543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19054222767366545462728229 3572666768881227274261543)
  ·
    refine ⟨5359000153321840911392315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572666768881227274261543 5359000153321840911392315)
    ·
      refine ⟨8038500229982761367088473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359000153321840911392315 8038500229982761367088473)
      ·
        refine ⟨6028875172487071025316355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038500229982761367088473 6028875172487071025316355)
        ·
          refine ⟨9043312758730606537974533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028875172487071025316355 9043312758730606537974533)
          ·
            refine ⟨1695621142261988725870225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9043312758730606537974533 1695621142261988725870225)
            ·
              refine ⟨1271715856696491544402669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695621142261988725870225 1271715856696491544402669)
              ·
                refine ⟨476893446261184329151001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271715856696491544402669 476893446261184329151001)
                ·
                  refine ⟨357670084695888246863251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476893446261184329151001 357670084695888246863251)
                  ·
                    rfl

theorem cell20_783630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_783630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783630 prefixEnd_783630 := by exact prefixLift 783630
  have htrace : WordTrace (prefixWord ++ tailWord_783630) baseStart_783630 baseEnd_783630 := by
    simpa [prefixWord, tailWord_783630, baseEnd_783630] using wordTrace_append hprefix tailTrace_783630
  have hstable : (prefixWord ++ tailWord_783630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783630).length < 2 ^ (prefixWord ++ tailWord_783630).sum := by decide
  have hdescent : baseEnd_783630 < baseStart_783630 := by decide
  rcases family_descends (prefixWord ++ tailWord_783630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783651 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 2]
def baseStart_783651 : Nat := 118140960795 + 783651 * 2 ^ 59
def prefixEnd_783651 : Nat := 4983230072969 + 3 ^ 40 * 783651 * 2
def baseEnd_783651 : Nat := 357679669668105507163165

theorem tailTrace_783651 : CollatzResearch.WordTrace tailWord_783651 prefixEnd_783651 357679669668105507163165 := by
  unfold tailWord_783651
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582100083973738780606807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19054733389315825853737871 28582100083973738780606807)
  ·
    refine ⟨42873150125960608170910211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28582100083973738780606807 42873150125960608170910211)
    ·
      refine ⟨64309725188940912256365317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42873150125960608170910211 64309725188940912256365317)
      ·
        refine ⟨12058073472926421048068497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64309725188940912256365317 12058073472926421048068497)
        ·
          refine ⟨9043555104694815786051373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12058073472926421048068497 9043555104694815786051373)
          ·
            refine ⟨3391333164260555919769265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9043555104694815786051373 3391333164260555919769265)
            ·
              refine ⟨2543499873195416939826949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391333164260555919769265 2543499873195416939826949)
              ·
                refine ⟨476906226224140676217553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2543499873195416939826949 476906226224140676217553)
                ·
                  refine ⟨357679669668105507163165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476906226224140676217553 357679669668105507163165)
                  ·
                    rfl

theorem cell20_783651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2].length) (baseStart_783651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783651 prefixEnd_783651 := by exact prefixLift 783651
  have htrace : WordTrace (prefixWord ++ tailWord_783651) baseStart_783651 baseEnd_783651 := by
    simpa [prefixWord, tailWord_783651, baseEnd_783651] using wordTrace_append hprefix tailTrace_783651
  have hstable : (prefixWord ++ tailWord_783651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783651).length < 2 ^ (prefixWord ++ tailWord_783651).sum := by decide
  have hdescent : baseEnd_783651 < baseStart_783651 := by decide
  rcases family_descends (prefixWord ++ tailWord_783651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783679 : List Nat := [1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_783679 : Nat := 118140960795 + 783679 * 2 ^ 59
def prefixEnd_783679 : Nat := 4983230072969 + 3 ^ 40 * 783679 * 2
def baseEnd_783679 : Nat := 119230816543687284743239

theorem tailTrace_783679 : CollatzResearch.WordTrace tailWord_783679 prefixEnd_783679 119230816543687284743239 := by
  unfold tailWord_783679
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583121327872299562626091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19055414218581533041750727 28583121327872299562626091)
  ·
    refine ⟨42874681991808449343939137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28583121327872299562626091 42874681991808449343939137)
    ·
      refine ⟨32156011493856337007954353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42874681991808449343939137 32156011493856337007954353)
      ·
        refine ⟨24117008620392252755965765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32156011493856337007954353 24117008620392252755965765)
        ·
          refine ⟨4521939116323547391743581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24117008620392252755965765 4521939116323547391743581)
          ·
            refine ⟨1695727168621330271903843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4521939116323547391743581 1695727168621330271903843)
            ·
              refine ⟨2543590752931995407855765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695727168621330271903843 2543590752931995407855765)
              ·
                refine ⟨119230816543687284743239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2543590752931995407855765 119230816543687284743239)
                ·
                  rfl

theorem cell20_783679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_783679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783679 prefixEnd_783679 := by exact prefixLift 783679
  have htrace : WordTrace (prefixWord ++ tailWord_783679) baseStart_783679 baseEnd_783679 := by
    simpa [prefixWord, tailWord_783679, baseEnd_783679] using wordTrace_append hprefix tailTrace_783679
  have hstable : (prefixWord ++ tailWord_783679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783679).length < 2 ^ (prefixWord ++ tailWord_783679).sum := by decide
  have hdescent : baseEnd_783679 < baseStart_783679 := by decide
  rcases family_descends (prefixWord ++ tailWord_783679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783689 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 2]
def baseStart_783689 : Nat := 118140960795 + 783689 * 2 ^ 59
def prefixEnd_783689 : Nat := 4983230072969 + 3 ^ 40 * 783689 * 2
def baseEnd_783689 : Nat := 357697013903546263896343

theorem tailTrace_783689 : CollatzResearch.WordTrace tailWord_783689 prefixEnd_783689 357697013903546263896343 := by
  unfold tailWord_783689
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583486057836071270490121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19055657371890714180326747 28583486057836071270490121)
  ·
    refine ⟨21437614543377053452867591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28583486057836071270490121 21437614543377053452867591)
    ·
      refine ⟨32156421815065580179301387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21437614543377053452867591 32156421815065580179301387)
      ·
        refine ⟨48234632722598370268952081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32156421815065580179301387 48234632722598370268952081)
        ·
          refine ⟨36175974541948777701714061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48234632722598370268952081 36175974541948777701714061)
          ·
            refine ⟨13565990453230791638142773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36175974541948777701714061 13565990453230791638142773)
            ·
              refine ⟨1271811604990386716075885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13565990453230791638142773 1271811604990386716075885)
              ·
                refine ⟨476929351871395018528457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271811604990386716075885 476929351871395018528457)
                ·
                  refine ⟨357697013903546263896343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476929351871395018528457 357697013903546263896343)
                  ·
                    rfl

theorem cell20_783689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_783689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783689 prefixEnd_783689 := by exact prefixLift 783689
  have htrace : WordTrace (prefixWord ++ tailWord_783689) baseStart_783689 baseEnd_783689 := by
    simpa [prefixWord, tailWord_783689, baseEnd_783689] using wordTrace_append hprefix tailTrace_783689
  have hstable : (prefixWord ++ tailWord_783689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783689).length < 2 ^ (prefixWord ++ tailWord_783689).sum := by decide
  have hdescent : baseEnd_783689 < baseStart_783689 := by decide
  rcases family_descends (prefixWord ++ tailWord_783689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783717 : List Nat := [1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_783717 : Nat := 118140960795 + 783717 * 2 ^ 59
def prefixEnd_783717 : Nat := 4983230072969 + 3 ^ 40 * 783717 * 2
def baseEnd_783717 : Nat := 119236597955500870320965

theorem tailTrace_783717 : CollatzResearch.WordTrace tailWord_783717 prefixEnd_783717 119236597955500870320965 := by
  unfold tailWord_783717
  simp only [CollatzResearch.WordTrace]
  refine ⟨28584507301734632052509405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19056338201156421368339603 28584507301734632052509405)
  ·
    refine ⟨10719190238150487019691027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28584507301734632052509405 10719190238150487019691027)
    ·
      refine ⟨16078785357225730529536541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719190238150487019691027 16078785357225730529536541)
      ·
        refine ⟨6029544508959648948576203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16078785357225730529536541 6029544508959648948576203)
        ·
          refine ⟨9044316763439473422864305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029544508959648948576203 9044316763439473422864305)
          ·
            refine ⟨6783237572579605067148229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044316763439473422864305 6783237572579605067148229)
            ·
              refine ⟨1271857044858675950090293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6783237572579605067148229 1271857044858675950090293)
              ·
                refine ⟨119236597955500870320965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271857044858675950090293 119236597955500870320965)
                ·
                  rfl

theorem cell20_783717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_783717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783717 prefixEnd_783717 := by exact prefixLift 783717
  have htrace : WordTrace (prefixWord ++ tailWord_783717) baseStart_783717 baseEnd_783717 := by
    simpa [prefixWord, tailWord_783717, baseEnd_783717] using wordTrace_append hprefix tailTrace_783717
  have hstable : (prefixWord ++ tailWord_783717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783717).length < 2 ^ (prefixWord ++ tailWord_783717).sum := by decide
  have hdescent : baseEnd_783717 < baseStart_783717 := by decide
  rcases family_descends (prefixWord ++ tailWord_783717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783720 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_783720 : Nat := 118140960795 + 783720 * 2 ^ 59
def prefixEnd_783720 : Nat := 4983230072969 + 3 ^ 40 * 783720 * 2
def baseEnd_783720 : Nat := 357711163148247933862883

theorem tailTrace_783720 : CollatzResearch.WordTrace tailWord_783720 prefixEnd_783720 357711163148247933862883 := by
  unfold tailWord_783720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292308360361881782434307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19056411147149175709912409 14292308360361881782434307)
  ·
    refine ⟨21438462540542822673651461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14292308360361881782434307 21438462540542822673651461)
    ·
      refine ⟨4019711726351779251309649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21438462540542822673651461 4019711726351779251309649)
      ·
        refine ⟨3014783794763834438482237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4019711726351779251309649 3014783794763834438482237)
        ·
          refine ⟨1130543923036437914430839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3014783794763834438482237 1130543923036437914430839)
          ·
            refine ⟨1695815884554656871646259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130543923036437914430839 1695815884554656871646259)
            ·
              refine ⟨2543723826831985307469389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695815884554656871646259 2543723826831985307469389)
              ·
                refine ⟨953896435061994490301021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2543723826831985307469389 953896435061994490301021)
                ·
                  refine ⟨357711163148247933862883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953896435061994490301021 357711163148247933862883)
                  ·
                    rfl

theorem cell20_783720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_783720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783720 prefixEnd_783720 := by exact prefixLift 783720
  have htrace : WordTrace (prefixWord ++ tailWord_783720) baseStart_783720 baseEnd_783720 := by
    simpa [prefixWord, tailWord_783720, baseEnd_783720] using wordTrace_append hprefix tailTrace_783720
  have hstable : (prefixWord ++ tailWord_783720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783720).length < 2 ^ (prefixWord ++ tailWord_783720).sum := by decide
  have hdescent : baseEnd_783720 < baseStart_783720 := by decide
  rcases family_descends (prefixWord ++ tailWord_783720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783789 : List Nat := [1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_783789 : Nat := 118140960795 + 783789 * 2 ^ 59
def prefixEnd_783789 : Nat := 4983230072969 + 3 ^ 40 * 783789 * 2
def baseEnd_783789 : Nat := 119247552209463453520867

theorem tailTrace_783789 : CollatzResearch.WordTrace tailWord_783789 prefixEnd_783789 119247552209463453520867 := by
  unfold tailWord_783789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587133357473788349130421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19058088904982525566086947 28587133357473788349130421)
  ·
    refine ⟨2680043752263167657730977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28587133357473788349130421 2680043752263167657730977)
    ·
      refine ⟨2010032814197375743298233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680043752263167657730977 2010032814197375743298233)
      ·
        refine ⟨1507524610648031807473675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010032814197375743298233 1507524610648031807473675)
        ·
          refine ⟨2261286915972047711210513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507524610648031807473675 2261286915972047711210513)
          ·
            refine ⟨1695965186979035783407885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261286915972047711210513 1695965186979035783407885)
            ·
              refine ⟨635986945117138418777957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1695965186979035783407885 635986945117138418777957)
              ·
                refine ⟨119247552209463453520867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635986945117138418777957 119247552209463453520867)
                ·
                  rfl

theorem cell20_783789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_783789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783789 prefixEnd_783789 := by exact prefixLift 783789
  have htrace : WordTrace (prefixWord ++ tailWord_783789) baseStart_783789 baseEnd_783789 := by
    simpa [prefixWord, tailWord_783789, baseEnd_783789] using wordTrace_append hprefix tailTrace_783789
  have hstable : (prefixWord ++ tailWord_783789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783789).length < 2 ^ (prefixWord ++ tailWord_783789).sum := by decide
  have hdescent : baseEnd_783789 < baseStart_783789 := by decide
  rcases family_descends (prefixWord ++ tailWord_783789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783834 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_783834 : Nat := 118140960795 + 783834 * 2 ^ 59
def prefixEnd_783834 : Nat := 4983230072969 + 3 ^ 40 * 783834 * 2
def baseEnd_783834 : Nat := 357763195854570204062417

theorem tailTrace_783834 : CollatzResearch.WordTrace tailWord_783834 prefixEnd_783834 357763195854570204062417 := by
  unfold tailWord_783834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7147193660577690258629639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19059183094873840689679037 7147193660577690258629639)
  ·
    refine ⟨10720790490866535387944459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7147193660577690258629639 10720790490866535387944459)
    ·
      refine ⟨16081185736299803081916689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10720790490866535387944459 16081185736299803081916689)
      ·
        refine ⟨12060889302224852311437517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16081185736299803081916689 12060889302224852311437517)
        ·
          refine ⟨4522833488334319616789069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12060889302224852311437517 4522833488334319616789069)
          ·
            refine ⟨1696062558125369856295901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4522833488334319616789069 1696062558125369856295901)
            ·
              refine ⟨636023459297013696110963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1696062558125369856295901 636023459297013696110963)
              ·
                refine ⟨954035188945520544166445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636023459297013696110963 954035188945520544166445)
                ·
                  refine ⟨357763195854570204062417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954035188945520544166445 357763195854570204062417)
                  ·
                    rfl

theorem cell20_783834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_783834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783834 prefixEnd_783834 := by exact prefixLift 783834
  have htrace : WordTrace (prefixWord ++ tailWord_783834) baseStart_783834 baseEnd_783834 := by
    simpa [prefixWord, tailWord_783834, baseEnd_783834] using wordTrace_append hprefix tailTrace_783834
  have hstable : (prefixWord ++ tailWord_783834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783834).length < 2 ^ (prefixWord ++ tailWord_783834).sum := by decide
  have hdescent : baseEnd_783834 < baseStart_783834 := by decide
  rcases family_descends (prefixWord ++ tailWord_783834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783858 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_783858 : Nat := 118140960795 + 783858 * 2 ^ 59
def prefixEnd_783858 : Nat := 4983230072969 + 3 ^ 40 * 783858 * 2
def baseEnd_783858 : Nat := 357774150108532787262319

theorem tailTrace_783858 : CollatzResearch.WordTrace tailWord_783858 prefixEnd_783858 357774150108532787262319 := by
  unfold tailWord_783858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7147412498555953283348057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19059766662815875422261485 7147412498555953283348057)
  ·
    refine ⟨5360559373916964962511043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7147412498555953283348057 5360559373916964962511043)
    ·
      refine ⟨8040839060875447443766565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360559373916964962511043 8040839060875447443766565)
      ·
        refine ⟨1507657323914146395706231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8040839060875447443766565 1507657323914146395706231)
        ·
          refine ⟨2261485985871219593559347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507657323914146395706231 2261485985871219593559347)
          ·
            refine ⟨3392228978806829390339021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261485985871219593559347 3392228978806829390339021)
            ·
              refine ⟨1272085867052561021377133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3392228978806829390339021 1272085867052561021377133)
              ·
                refine ⟨477032200144710383016425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272085867052561021377133 477032200144710383016425)
                ·
                  refine ⟨357774150108532787262319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477032200144710383016425 357774150108532787262319)
                  ·
                    rfl

theorem cell20_783858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_783858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783858 prefixEnd_783858 := by exact prefixLift 783858
  have htrace : WordTrace (prefixWord ++ tailWord_783858) baseStart_783858 baseEnd_783858 := by
    simpa [prefixWord, tailWord_783858, baseEnd_783858] using wordTrace_append hprefix tailTrace_783858
  have hstable : (prefixWord ++ tailWord_783858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783858).length < 2 ^ (prefixWord ++ tailWord_783858).sum := by decide
  have hdescent : baseEnd_783858 < baseStart_783858 := by decide
  rcases family_descends (prefixWord ++ tailWord_783858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783869 : List Nat := [1, 4, 1, 1, 1, 6, 6]
def baseStart_783869 : Nat := 118140960795 + 783869 * 2 ^ 59
def prefixEnd_783869 : Nat := 4983230072969 + 3 ^ 40 * 783869 * 2
def baseEnd_783869 : Nat := 39753241200918404210623

theorem tailTrace_783869 : CollatzResearch.WordTrace tailWord_783869 prefixEnd_783869 39753241200918404210623 := by
  unfold tailWord_783869
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590051197183962012042661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060034131455974674695107 28590051197183962012042661)
  ·
    refine ⟨5360634599471992877257999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28590051197183962012042661 5360634599471992877257999)
    ·
      refine ⟨8040951899207989315886999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360634599471992877257999 8040951899207989315886999)
      ·
        refine ⟨12061427848811983973830499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040951899207989315886999 12061427848811983973830499)
        ·
          refine ⟨18092141773217975960745749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061427848811983973830499 18092141773217975960745749)
          ·
            refine ⟨848069145619592623159957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18092141773217975960745749 848069145619592623159957)
            ·
              refine ⟨39753241200918404210623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 848069145619592623159957 39753241200918404210623)
              ·
                rfl

theorem cell20_783869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_783869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783869 prefixEnd_783869 := by exact prefixLift 783869
  have htrace : WordTrace (prefixWord ++ tailWord_783869) baseStart_783869 baseEnd_783869 := by
    simpa [prefixWord, tailWord_783869, baseEnd_783869] using wordTrace_append hprefix tailTrace_783869
  have hstable : (prefixWord ++ tailWord_783869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783869).length < 2 ^ (prefixWord ++ tailWord_783869).sum := by decide
  have hdescent : baseEnd_783869 < baseStart_783869 := by decide
  rcases family_descends (prefixWord ++ tailWord_783869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783879 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_783879 : Nat := 118140960795 + 783879 * 2 ^ 59
def prefixEnd_783879 : Nat := 4983230072969 + 3 ^ 40 * 783879 * 2
def baseEnd_783879 : Nat := 357783735080750047562233

theorem tailTrace_783879 : CollatzResearch.WordTrace tailWord_783879 prefixEnd_783879 357783735080750047562233 := by
  unfold tailWord_783879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590415927147733719906691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060277284765155813271127 28590415927147733719906691)
  ·
    refine ⟨42885623890721600579860037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28590415927147733719906691 42885623890721600579860037)
    ·
      refine ⟨8041054479510300108723757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42885623890721600579860037 8041054479510300108723757)
      ·
        refine ⟨3015395429816362540771409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8041054479510300108723757 3015395429816362540771409)
        ·
          refine ⟨2261546572362271905578557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015395429816362540771409 2261546572362271905578557)
          ·
            refine ⟨848079964635851964591959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2261546572362271905578557 848079964635851964591959)
            ·
              refine ⟨1272119946953777946887939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848079964635851964591959 1272119946953777946887939)
              ·
                refine ⟨1908179920430666920331909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272119946953777946887939 1908179920430666920331909)
                ·
                  refine ⟨357783735080750047562233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908179920430666920331909 357783735080750047562233)
                  ·
                    rfl

theorem cell20_783879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_783879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783879 prefixEnd_783879 := by exact prefixLift 783879
  have htrace : WordTrace (prefixWord ++ tailWord_783879) baseStart_783879 baseEnd_783879 := by
    simpa [prefixWord, tailWord_783879, baseEnd_783879] using wordTrace_append hprefix tailTrace_783879
  have hstable : (prefixWord ++ tailWord_783879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783879).length < 2 ^ (prefixWord ++ tailWord_783879).sum := by decide
  have hdescent : baseEnd_783879 < baseStart_783879 := by decide
  rcases family_descends (prefixWord ++ tailWord_783879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783885 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_783885 : Nat := 118140960795 + 783885 * 2 ^ 59
def prefixEnd_783885 : Nat := 4983230072969 + 3 ^ 40 * 783885 * 2
def baseEnd_783885 : Nat := 357786473644240693362209

theorem tailTrace_783885 : CollatzResearch.WordTrace tailWord_783885 prefixEnd_783885 357786473644240693362209 := by
  unfold tailWord_783885
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590634765125996744625109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060423176750664496416739 28590634765125996744625109)
  ·
    refine ⟨670093002307640548702151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28590634765125996744625109 670093002307640548702151)
    ·
      refine ⟨1005139503461460823053227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670093002307640548702151 1005139503461460823053227)
      ·
        refine ⟨1507709255192191234579841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005139503461460823053227 1507709255192191234579841)
        ·
          refine ⟨1130781941394143425934881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507709255192191234579841 1130781941394143425934881)
          ·
            refine ⟨848086456045607569451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130781941394143425934881 848086456045607569451161)
            ·
              refine ⟨636064842034205677088371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848086456045607569451161 636064842034205677088371)
              ·
                refine ⟨954097263051308515632557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636064842034205677088371 954097263051308515632557)
                ·
                  refine ⟨357786473644240693362209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954097263051308515632557 357786473644240693362209)
                  ·
                    rfl

theorem cell20_783885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_783885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783885 prefixEnd_783885 := by exact prefixLift 783885
  have htrace : WordTrace (prefixWord ++ tailWord_783885) baseStart_783885 baseEnd_783885 := by
    simpa [prefixWord, tailWord_783885, baseEnd_783885] using wordTrace_append hprefix tailTrace_783885
  have hstable : (prefixWord ++ tailWord_783885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783885).length < 2 ^ (prefixWord ++ tailWord_783885).sum := by decide
  have hdescent : baseEnd_783885 < baseStart_783885 := by decide
  rcases family_descends (prefixWord ++ tailWord_783885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783886 : List Nat := [4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_783886 : Nat := 118140960795 + 783886 * 2 ^ 59
def prefixEnd_783886 : Nat := 4983230072969 + 3 ^ 40 * 783886 * 2
def baseEnd_783886 : Nat := 119262310023829711442957

theorem tailTrace_783886 : CollatzResearch.WordTrace tailWord_783886 prefixEnd_783886 119262310023829711442957 := by
  unfold tailWord_783886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573833904765296739426439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19060447492081582610274341 3573833904765296739426439)
  ·
    refine ⟨5360750857147945109139659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573833904765296739426439 5360750857147945109139659)
    ·
      refine ⟨8041126285721917663709489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360750857147945109139659 8041126285721917663709489)
      ·
        refine ⟨6030844714291438247782117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041126285721917663709489 6030844714291438247782117)
        ·
          refine ⟨1130783383929644671459147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6030844714291438247782117 1130783383929644671459147)
          ·
            refine ⟨1696175075894467007188721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130783383929644671459147 1696175075894467007188721)
            ·
              refine ⟨1272131306920850255391541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696175075894467007188721 1272131306920850255391541)
              ·
                refine ⟨119262310023829711442957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272131306920850255391541 119262310023829711442957)
                ·
                  rfl

theorem cell20_783886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_783886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783886 prefixEnd_783886 := by exact prefixLift 783886
  have htrace : WordTrace (prefixWord ++ tailWord_783886) baseStart_783886 baseEnd_783886 := by
    simpa [prefixWord, tailWord_783886, baseEnd_783886] using wordTrace_append hprefix tailTrace_783886
  have hstable : (prefixWord ++ tailWord_783886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783886).length < 2 ^ (prefixWord ++ tailWord_783886).sum := by decide
  have hdescent : baseEnd_783886 < baseStart_783886 := by decide
  rcases family_descends (prefixWord ++ tailWord_783886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783893 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_783893 : Nat := 118140960795 + 783893 * 2 ^ 59
def prefixEnd_783893 : Nat := 4983230072969 + 3 ^ 40 * 783893 * 2
def baseEnd_783893 : Nat := 357790125062228221095509

theorem tailTrace_783893 : CollatzResearch.WordTrace tailWord_783893 prefixEnd_783893 357790125062228221095509 := by
  unfold tailWord_783893
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590926549097014110916333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060617699398009407277555 28590926549097014110916333)
  ·
    refine ⟨10721597455911380291593625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28590926549097014110916333 10721597455911380291593625)
    ·
      refine ⟨8041198091933535218695219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10721597455911380291593625 8041198091933535218695219)
      ·
        refine ⟨12061797137900302828042829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041198091933535218695219 12061797137900302828042829)
        ·
          refine ⟨4523173926712613560516061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12061797137900302828042829 4523173926712613560516061)
          ·
            refine ⟨1696190222517230085193523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4523173926712613560516061 1696190222517230085193523)
            ·
              refine ⟨2544285333775845127790285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696190222517230085193523 2544285333775845127790285)
              ·
                refine ⟨954107000165941922921357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544285333775845127790285 954107000165941922921357)
                ·
                  refine ⟨357790125062228221095509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954107000165941922921357 357790125062228221095509)
                  ·
                    rfl

theorem cell20_783893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_783893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783893 prefixEnd_783893 := by exact prefixLift 783893
  have htrace : WordTrace (prefixWord ++ tailWord_783893) baseStart_783893 baseEnd_783893 := by
    simpa [prefixWord, tailWord_783893, baseEnd_783893] using wordTrace_append hprefix tailTrace_783893
  have hstable : (prefixWord ++ tailWord_783893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783893).length < 2 ^ (prefixWord ++ tailWord_783893).sum := by decide
  have hdescent : baseEnd_783893 < baseStart_783893 := by decide
  rcases family_descends (prefixWord ++ tailWord_783893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783928 : List Nat := [2, 1, 2, 1, 4, 10]
def baseStart_783928 : Nat := 118140960795 + 783928 * 2 ^ 59
def prefixEnd_783928 : Nat := 4983230072969 + 3 ^ 40 * 783928 * 2
def baseEnd_783928 : Nat := 13252077778367542775137

theorem tailTrace_783928 : CollatzResearch.WordTrace tailWord_783928 prefixEnd_783928 13252077778367542775137 := by
  unfold tailWord_783928
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296101551985107544220219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19061468735980143392293625 14296101551985107544220219)
  ·
    refine ⟨21444152327977661316330329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14296101551985107544220219 21444152327977661316330329)
    ·
      refine ⟨16083114245983245987247747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21444152327977661316330329 16083114245983245987247747)
      ·
        refine ⟨24124671368974868980871621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083114245983245987247747 24124671368974868980871621)
        ·
          refine ⟨4523375881682787933913429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24124671368974868980871621 4523375881682787933913429)
          ·
            refine ⟨13252077778367542775137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4523375881682787933913429 13252077778367542775137)
            ·
              rfl

theorem cell20_783928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 10].length) (baseStart_783928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783928 prefixEnd_783928 := by exact prefixLift 783928
  have htrace : WordTrace (prefixWord ++ tailWord_783928) baseStart_783928 baseEnd_783928 := by
    simpa [prefixWord, tailWord_783928, baseEnd_783928] using wordTrace_append hprefix tailTrace_783928
  have hstable : (prefixWord ++ tailWord_783928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783928).length < 2 ^ (prefixWord ++ tailWord_783928).sum := by decide
  have hdescent : baseEnd_783928 < baseStart_783928 := by decide
  rcases family_descends (prefixWord ++ tailWord_783928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783952 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_783952 : Nat := 118140960795 + 783952 * 2 ^ 59
def prefixEnd_783952 : Nat := 4983230072969 + 3 ^ 40 * 783952 * 2
def baseEnd_783952 : Nat := 357817054269886238128601

theorem tailTrace_783952 : CollatzResearch.WordTrace tailWord_783952 prefixEnd_783952 357817054269886238128601 := by
  unfold tailWord_783952
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296539227941633593657055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19062052303922178124876073 14296539227941633593657055)
  ·
    refine ⟨21444808841912450390485583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14296539227941633593657055 21444808841912450390485583)
    ·
      refine ⟨32167213262868675585728375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21444808841912450390485583 32167213262868675585728375)
      ·
        refine ⟨48250819894303013378592563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32167213262868675585728375 48250819894303013378592563)
        ·
          refine ⟨72376229841454520067888845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48250819894303013378592563 72376229841454520067888845)
          ·
            refine ⟨27141086190545445025458317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72376229841454520067888845 27141086190545445025458317)
            ·
              refine ⟨10177907321454541884546869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27141086190545445025458317 10177907321454541884546869)
              ·
                refine ⟨954178811386363301676269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10177907321454541884546869 954178811386363301676269)
                ·
                  refine ⟨357817054269886238128601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954178811386363301676269 357817054269886238128601)
                  ·
                    rfl

theorem cell20_783952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_783952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783952 prefixEnd_783952 := by exact prefixLift 783952
  have htrace : WordTrace (prefixWord ++ tailWord_783952) baseStart_783952 baseEnd_783952 := by
    simpa [prefixWord, tailWord_783952, baseEnd_783952] using wordTrace_append hprefix tailTrace_783952
  have hstable : (prefixWord ++ tailWord_783952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783952).length < 2 ^ (prefixWord ++ tailWord_783952).sum := by decide
  have hdescent : baseEnd_783952 < baseStart_783952 := by decide
  rcases family_descends (prefixWord ++ tailWord_783952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783959 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_783959 : Nat := 118140960795 + 783959 * 2 ^ 59
def prefixEnd_783959 : Nat := 4983230072969 + 3 ^ 40 * 783959 * 2
def baseEnd_783959 : Nat := 357820249260625324895239

theorem tailTrace_783959 : CollatzResearch.WordTrace tailWord_783959 prefixEnd_783959 357820249260625324895239 := by
  unfold tailWord_783959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593333766857907382818931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19062222511238604921879287 28593333766857907382818931)
  ·
    refine ⟨42890000650286861074228397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28593333766857907382818931 42890000650286861074228397)
    ·
      refine ⟨16083750243857572902835649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42890000650286861074228397 16083750243857572902835649)
      ·
        refine ⟨12062812682893179677126737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16083750243857572902835649 12062812682893179677126737)
        ·
          refine ⟨9047109512169884757845053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12062812682893179677126737 9047109512169884757845053)
          ·
            refine ⟨3392666067063706784191895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9047109512169884757845053 3392666067063706784191895)
            ·
              refine ⟨5088999100595560176287843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392666067063706784191895 5088999100595560176287843)
              ·
                refine ⟨7633498650893340264431765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088999100595560176287843 7633498650893340264431765)
                ·
                  refine ⟨357820249260625324895239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7633498650893340264431765 357820249260625324895239)
                  ·
                    rfl

theorem cell20_783959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_783959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783959 prefixEnd_783959 := by exact prefixLift 783959
  have htrace : WordTrace (prefixWord ++ tailWord_783959) baseStart_783959 baseEnd_783959 := by
    simpa [prefixWord, tailWord_783959, baseEnd_783959] using wordTrace_append hprefix tailTrace_783959
  have hstable : (prefixWord ++ tailWord_783959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783959).length < 2 ^ (prefixWord ++ tailWord_783959).sum := by decide
  have hdescent : baseEnd_783959 < baseStart_783959 := by decide
  rcases family_descends (prefixWord ++ tailWord_783959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783986 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_783986 : Nat := 118140960795 + 783986 * 2 ^ 59
def prefixEnd_783986 : Nat := 4983230072969 + 3 ^ 40 * 783986 * 2
def baseEnd_783986 : Nat := 357832572796333230995129

theorem tailTrace_783986 : CollatzResearch.WordTrace tailWord_783986 prefixEnd_783986 357832572796333230995129 := by
  unfold tailWord_783986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148579634440022748512953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19062879025173393996034541 7148579634440022748512953)
  ·
    refine ⟨5361434725830017061384715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7148579634440022748512953 5361434725830017061384715)
    ·
      refine ⟨8042152088745025592077073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361434725830017061384715 8042152088745025592077073)
      ·
        refine ⟨6031614066558769194057805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8042152088745025592077073 6031614066558769194057805)
        ·
          refine ⟨2261855274959538447771677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6031614066558769194057805 2261855274959538447771677)
          ·
            refine ⟨848195728109826917914379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2261855274959538447771677 848195728109826917914379)
            ·
              refine ⟨1272293592164740376871569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848195728109826917914379 1272293592164740376871569)
              ·
                refine ⟨954220194123555282653677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272293592164740376871569 954220194123555282653677)
                ·
                  refine ⟨357832572796333230995129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954220194123555282653677 357832572796333230995129)
                  ·
                    rfl

theorem cell20_783986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_783986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_783986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_783986 prefixEnd_783986 := by exact prefixLift 783986
  have htrace : WordTrace (prefixWord ++ tailWord_783986) baseStart_783986 baseEnd_783986 := by
    simpa [prefixWord, tailWord_783986, baseEnd_783986] using wordTrace_append hprefix tailTrace_783986
  have hstable : (prefixWord ++ tailWord_783986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783986).length < 2 ^ (prefixWord ++ tailWord_783986).sum := by decide
  have hdescent : baseEnd_783986 < baseStart_783986 := by decide
  rcases family_descends (prefixWord ++ tailWord_783986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784014 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_784014 : Nat := 118140960795 + 784014 * 2 ^ 59
def prefixEnd_784014 : Nat := 4983230072969 + 3 ^ 40 * 784014 * 2
def baseEnd_784014 : Nat := 357845352759289578061681

theorem tailTrace_784014 : CollatzResearch.WordTrace tailWord_784014 prefixEnd_784014 357845352759289578061681 := by
  unfold tailWord_784014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574417472707331472008887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19063559854439101184047397 3574417472707331472008887)
  ·
    refine ⟨5361626209060997208013331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574417472707331472008887 5361626209060997208013331)
    ·
      refine ⟨8042439313591495812019997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361626209060997208013331 8042439313591495812019997)
      ·
        refine ⟨3015914742596810929507499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8042439313591495812019997 3015914742596810929507499)
        ·
          refine ⟨4523872113895216394261249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015914742596810929507499 4523872113895216394261249)
          ·
            refine ⟨3392904085421412295695937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523872113895216394261249 3392904085421412295695937)
            ·
              refine ⟨2544678064066059221771953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392904085421412295695937 2544678064066059221771953)
              ·
                refine ⟨1908508548049544416328965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544678064066059221771953 1908508548049544416328965)
                ·
                  refine ⟨357845352759289578061681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908508548049544416328965 357845352759289578061681)
                  ·
                    rfl

theorem cell20_784014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_784014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784014 prefixEnd_784014 := by exact prefixLift 784014
  have htrace : WordTrace (prefixWord ++ tailWord_784014) baseStart_784014 baseEnd_784014 := by
    simpa [prefixWord, tailWord_784014, baseEnd_784014] using wordTrace_append hprefix tailTrace_784014
  have hstable : (prefixWord ++ tailWord_784014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784014).length < 2 ^ (prefixWord ++ tailWord_784014).sum := by decide
  have hdescent : baseEnd_784014 < baseStart_784014 := by decide
  rcases family_descends (prefixWord ++ tailWord_784014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784045 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_784045 : Nat := 118140960795 + 784045 * 2 ^ 59
def prefixEnd_784045 : Nat := 4983230072969 + 3 ^ 40 * 784045 * 2
def baseEnd_784045 : Nat := 357859502003991248028221

theorem tailTrace_784045 : CollatzResearch.WordTrace tailWord_784045 prefixEnd_784045 357859502003991248028221 := by
  unfold tailWord_784045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28596470444546344070449589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19064313629697562713633059 28596470444546344070449589)
  ·
    refine ⟨2680919104176219756604649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28596470444546344070449589 2680919104176219756604649)
    ·
      refine ⟨2010689328132164817453487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680919104176219756604649 2010689328132164817453487)
      ·
        refine ⟨3016033992198247226180231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010689328132164817453487 3016033992198247226180231)
        ·
          refine ⟨4524050988297370839270347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016033992198247226180231 4524050988297370839270347)
          ·
            refine ⟨6786076482446056258905521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524050988297370839270347 6786076482446056258905521)
            ·
              refine ⟨5089557361834542194179141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786076482446056258905521 5089557361834542194179141)
              ·
                refine ⟨954292005343976661408589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5089557361834542194179141 954292005343976661408589)
                ·
                  refine ⟨357859502003991248028221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954292005343976661408589 357859502003991248028221)
                  ·
                    rfl

theorem cell20_784045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_784045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784045 prefixEnd_784045 := by exact prefixLift 784045
  have htrace : WordTrace (prefixWord ++ tailWord_784045) baseStart_784045 baseEnd_784045 := by
    simpa [prefixWord, tailWord_784045, baseEnd_784045] using wordTrace_append hprefix tailTrace_784045
  have hstable : (prefixWord ++ tailWord_784045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784045).length < 2 ^ (prefixWord ++ tailWord_784045).sum := by decide
  have hdescent : baseEnd_784045 < baseStart_784045 := by decide
  rcases family_descends (prefixWord ++ tailWord_784045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784062 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_784062 : Nat := 118140960795 + 784062 * 2 ^ 59
def prefixEnd_784062 : Nat := 4983230072969 + 3 ^ 40 * 784062 * 2
def baseEnd_784062 : Nat := 357867261267214744461485

theorem tailTrace_784062 : CollatzResearch.WordTrace tailWord_784062 prefixEnd_784062 357867261267214744461485 := by
  unfold tailWord_784062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574636310685594496727305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19064726990323170649212293 3574636310685594496727305)
  ·
    refine ⟨2680977233014195872545479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3574636310685594496727305 2680977233014195872545479)
    ·
      refine ⟨4021465849521293808818219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680977233014195872545479 4021465849521293808818219)
      ·
        refine ⟨6032198774281940713227329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021465849521293808818219 6032198774281940713227329)
        ·
          refine ⟨4524149080711455534920497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6032198774281940713227329 4524149080711455534920497)
          ·
            refine ⟨3393111810533591651190373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524149080711455534920497 3393111810533591651190373)
            ·
              refine ⟨636208464475048434598195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3393111810533591651190373 636208464475048434598195)
              ·
                refine ⟨954312696712572651897293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636208464475048434598195 954312696712572651897293)
                ·
                  refine ⟨357867261267214744461485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954312696712572651897293 357867261267214744461485)
                  ·
                    rfl

theorem cell20_784062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_784062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784062 prefixEnd_784062 := by exact prefixLift 784062
  have htrace : WordTrace (prefixWord ++ tailWord_784062) baseStart_784062 baseEnd_784062 := by
    simpa [prefixWord, tailWord_784062, baseEnd_784062] using wordTrace_append hprefix tailTrace_784062
  have hstable : (prefixWord ++ tailWord_784062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784062).length < 2 ^ (prefixWord ++ tailWord_784062).sum := by decide
  have hdescent : baseEnd_784062 < baseStart_784062 := by decide
  rcases family_descends (prefixWord ++ tailWord_784062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784097 : List Nat := [1, 2, 3, 1, 6, 7]
def baseStart_784097 : Nat := 118140960795 + 784097 * 2 ^ 59
def prefixEnd_784097 : Nat := 4983230072969 + 3 ^ 40 * 784097 * 2
def baseEnd_784097 : Nat := 13254934674848525122025

theorem tailTrace_784097 : CollatzResearch.WordTrace tailWord_784097 prefixEnd_784097 13254934674848525122025 := by
  unfold tailWord_784097
  simp only [CollatzResearch.WordTrace]
  refine ⟨28598367040357956951342545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19065578026905304634228363 28598367040357956951342545)
  ·
    refine ⟨21448775280268467713506909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28598367040357956951342545 21448775280268467713506909)
    ·
      refine ⟨8043290730100675392565091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21448775280268467713506909 8043290730100675392565091)
      ·
        refine ⟨12064936095151013088847637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043290730100675392565091 12064936095151013088847637)
        ·
          refine ⟨565543879460203738539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12064936095151013088847637 565543879460203738539733)
          ·
            refine ⟨13254934674848525122025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 565543879460203738539733 13254934674848525122025)
            ·
              rfl

theorem cell20_784097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 7].length) (baseStart_784097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784097 prefixEnd_784097 := by exact prefixLift 784097
  have htrace : WordTrace (prefixWord ++ tailWord_784097) baseStart_784097 baseEnd_784097 := by
    simpa [prefixWord, tailWord_784097, baseEnd_784097] using wordTrace_append hprefix tailTrace_784097
  have hstable : (prefixWord ++ tailWord_784097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784097).length < 2 ^ (prefixWord ++ tailWord_784097).sum := by decide
  have hdescent : baseEnd_784097 < baseStart_784097 := by decide
  rcases family_descends (prefixWord ++ tailWord_784097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784107 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 2]
def baseStart_784107 : Nat := 118140960795 + 784107 * 2 ^ 59
def prefixEnd_784107 : Nat := 4983230072969 + 3 ^ 40 * 784107 * 2
def baseEnd_784107 : Nat := 357887800493394587961301

theorem tailTrace_784107 : CollatzResearch.WordTrace tailWord_784107 prefixEnd_784107 357887800493394587961301 := by
  unfold tailWord_784107
  simp only [CollatzResearch.WordTrace]
  refine ⟨28598731770321728659206575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19065821180214485772804383 28598731770321728659206575)
  ·
    refine ⟨42898097655482592988809863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28598731770321728659206575 42898097655482592988809863)
    ·
      refine ⟨64347146483223889483214795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42898097655482592988809863 64347146483223889483214795)
      ·
        refine ⟨96520719724835834224822193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64347146483223889483214795 96520719724835834224822193)
        ·
          refine ⟨72390539793626875668616645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96520719724835834224822193 72390539793626875668616645)
          ·
            refine ⟨13573226211305039187865621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72390539793626875668616645 13573226211305039187865621)
            ·
              refine ⟨636244978654923711931201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13573226211305039187865621 636244978654923711931201)
              ·
                refine ⟨477183733991192783948401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636244978654923711931201 477183733991192783948401)
                ·
                  refine ⟨357887800493394587961301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477183733991192783948401 357887800493394587961301)
                  ·
                    rfl

theorem cell20_784107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2].length) (baseStart_784107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784107 prefixEnd_784107 := by exact prefixLift 784107
  have htrace : WordTrace (prefixWord ++ tailWord_784107) baseStart_784107 baseEnd_784107 := by
    simpa [prefixWord, tailWord_784107, baseEnd_784107] using wordTrace_append hprefix tailTrace_784107
  have hstable : (prefixWord ++ tailWord_784107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784107).length < 2 ^ (prefixWord ++ tailWord_784107).sum := by decide
  have hdescent : baseEnd_784107 < baseStart_784107 := by decide
  rcases family_descends (prefixWord ++ tailWord_784107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784111 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_784111 : Nat := 118140960795 + 784111 * 2 ^ 59
def prefixEnd_784111 : Nat := 4983230072969 + 3 ^ 40 * 784111 * 2
def baseEnd_784111 : Nat := 357889626202388351827951

theorem tailTrace_784111 : CollatzResearch.WordTrace tailWord_784111 prefixEnd_784111 357889626202388351827951 := by
  unfold tailWord_784111
  simp only [CollatzResearch.WordTrace]
  refine ⟨28598877662307237342352187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19065918441538158228234791 28598877662307237342352187)
  ·
    refine ⟨42898316493460856013528281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28598877662307237342352187 42898316493460856013528281)
    ·
      refine ⟨32173737370095642010146211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42898316493460856013528281 32173737370095642010146211)
      ·
        refine ⟨48260606055143463015219317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32173737370095642010146211 48260606055143463015219317)
        ·
          refine ⟨4524431817669699657676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48260606055143463015219317 4524431817669699657676811)
          ·
            refine ⟨6786647726504549486515217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524431817669699657676811 6786647726504549486515217)
            ·
              refine ⟨5089985794878412114886413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786647726504549486515217 5089985794878412114886413)
              ·
                refine ⟨1908744673079404543082405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5089985794878412114886413 1908744673079404543082405)
                ·
                  refine ⟨357889626202388351827951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908744673079404543082405 357889626202388351827951)
                  ·
                    rfl

theorem cell20_784111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_784111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784111 prefixEnd_784111 := by exact prefixLift 784111
  have htrace : WordTrace (prefixWord ++ tailWord_784111) baseStart_784111 baseEnd_784111 := by
    simpa [prefixWord, tailWord_784111, baseEnd_784111] using wordTrace_append hprefix tailTrace_784111
  have hstable : (prefixWord ++ tailWord_784111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784111).length < 2 ^ (prefixWord ++ tailWord_784111).sum := by decide
  have hdescent : baseEnd_784111 < baseStart_784111 := by decide
  rcases family_descends (prefixWord ++ tailWord_784111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784156 : List Nat := [2, 2, 3, 1, 1, 2, 9]
def baseStart_784156 : Nat := 118140960795 + 784156 * 2 ^ 59
def prefixEnd_784156 : Nat := 4983230072969 + 3 ^ 40 * 784156 * 2
def baseEnd_784156 : Nat := 39767796158729799480863

theorem tailTrace_784156 : CollatzResearch.WordTrace tailWord_784156 prefixEnd_784156 39767796158729799480863 := by
  unfold tailWord_784156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300259473572105013870161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19067012631429473351826881 14300259473572105013870161)
  ·
    refine ⟨10725194605179078760402621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14300259473572105013870161 10725194605179078760402621)
    ·
      refine ⟨4021947976942154535150983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10725194605179078760402621 4021947976942154535150983)
      ·
        refine ⟨6032921965413231802726475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021947976942154535150983 6032921965413231802726475)
        ·
          refine ⟨9049382948119847704089713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032921965413231802726475 9049382948119847704089713)
          ·
            refine ⟨6787037211089885778067285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9049382948119847704089713 6787037211089885778067285)
            ·
              refine ⟨39767796158729799480863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6787037211089885778067285 39767796158729799480863)
              ·
                rfl

theorem cell20_784156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_784156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784156 prefixEnd_784156 := by exact prefixLift 784156
  have htrace : WordTrace (prefixWord ++ tailWord_784156) baseStart_784156 baseEnd_784156 := by
    simpa [prefixWord, tailWord_784156, baseEnd_784156] using wordTrace_append hprefix tailTrace_784156
  have hstable : (prefixWord ++ tailWord_784156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784156).length < 2 ^ (prefixWord ++ tailWord_784156).sum := by decide
  have hdescent : baseEnd_784156 < baseStart_784156 := by decide
  rcases family_descends (prefixWord ++ tailWord_784156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784190 : List Nat := [4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_784190 : Nat := 118140960795 + 784190 * 2 ^ 59
def prefixEnd_784190 : Nat := 4983230072969 + 3 ^ 40 * 784190 * 2
def baseEnd_784190 : Nat := 119308561318338396064765

theorem tailTrace_784190 : CollatzResearch.WordTrace tailWord_784190 prefixEnd_784190 119308561318338396064765 := by
  unfold tailWord_784190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575219878627629229309753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19067839352680689222985349 3575219878627629229309753)
  ·
    refine ⟨2681414908970721921982315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3575219878627629229309753 2681414908970721921982315)
    ·
      refine ⟨4022122363456082882973473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681414908970721921982315 4022122363456082882973473)
      ·
        refine ⟨3016591772592062162230105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4022122363456082882973473 3016591772592062162230105)
        ·
          refine ⟨2262443829444046621672579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016591772592062162230105 2262443829444046621672579)
          ·
            refine ⟨3393665744166069932508869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262443829444046621672579 3393665744166069932508869)
            ·
              refine ⟨636312327031138112345413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3393665744166069932508869 636312327031138112345413)
              ·
                refine ⟨119308561318338396064765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636312327031138112345413 119308561318338396064765)
                ·
                  rfl

theorem cell20_784190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_784190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784190 prefixEnd_784190 := by exact prefixLift 784190
  have htrace : WordTrace (prefixWord ++ tailWord_784190) baseStart_784190 baseEnd_784190 := by
    simpa [prefixWord, tailWord_784190, baseEnd_784190] using wordTrace_append hprefix tailTrace_784190
  have hstable : (prefixWord ++ tailWord_784190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784190).length < 2 ^ (prefixWord ++ tailWord_784190).sum := by decide
  have hdescent : baseEnd_784190 < baseStart_784190 := by decide
  rcases family_descends (prefixWord ++ tailWord_784190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784201 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_784201 : Nat := 118140960795 + 784201 * 2 ^ 59
def prefixEnd_784201 : Nat := 4983230072969 + 3 ^ 40 * 784201 * 2
def baseEnd_784201 : Nat := 357930704654748038827583

theorem tailTrace_784201 : CollatzResearch.WordTrace tailWord_784201 prefixEnd_784201 357930704654748038827583 := by
  unfold tailWord_784201
  simp only [CollatzResearch.WordTrace]
  refine ⟨28602160231981182713128457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19068106821320788475418971 28602160231981182713128457)
  ·
    refine ⟨21451620173985887034846343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28602160231981182713128457 21451620173985887034846343)
    ·
      refine ⟨32177430260978830552269515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21451620173985887034846343 32177430260978830552269515)
      ·
        refine ⟨48266145391468245828404273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32177430260978830552269515 48266145391468245828404273)
        ·
          refine ⟨36199609043601184371303205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48266145391468245828404273 36199609043601184371303205)
          ·
            refine ⟨6787426695675222069619351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36199609043601184371303205 6787426695675222069619351)
            ·
              refine ⟨10181140043512833104429027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787426695675222069619351 10181140043512833104429027)
              ·
                refine ⟨15271710065269249656643541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10181140043512833104429027 15271710065269249656643541)
                ·
                  refine ⟨357930704654748038827583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15271710065269249656643541 357930704654748038827583)
                  ·
                    rfl

theorem cell20_784201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_784201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784201 prefixEnd_784201 := by exact prefixLift 784201
  have htrace : WordTrace (prefixWord ++ tailWord_784201) baseStart_784201 baseEnd_784201 := by
    simpa [prefixWord, tailWord_784201, baseEnd_784201] using wordTrace_append hprefix tailTrace_784201
  have hstable : (prefixWord ++ tailWord_784201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784201).length < 2 ^ (prefixWord ++ tailWord_784201).sum := by decide
  have hdescent : baseEnd_784201 < baseStart_784201 := by decide
  rcases family_descends (prefixWord ++ tailWord_784201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784218 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_784218 : Nat := 118140960795 + 784218 * 2 ^ 59
def prefixEnd_784218 : Nat := 4983230072969 + 3 ^ 40 * 784218 * 2
def baseEnd_784218 : Nat := 357938463917971535260847

theorem tailTrace_784218 : CollatzResearch.WordTrace tailWord_784218 prefixEnd_784218 357938463917971535260847 := by
  unfold tailWord_784218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7150695068229898654124327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19068520181946396410998205 7150695068229898654124327)
  ·
    refine ⟨10726042602344847981186491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7150695068229898654124327 10726042602344847981186491)
    ·
      refine ⟨16089063903517271971779737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726042602344847981186491 16089063903517271971779737)
      ·
        refine ⟨12066797927637953978834803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16089063903517271971779737 12066797927637953978834803)
        ·
          refine ⟨18100196891456930968252205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12066797927637953978834803 18100196891456930968252205)
          ·
            refine ⟨6787573834296349113094577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18100196891456930968252205 6787573834296349113094577)
            ·
              refine ⟨5090680375722261834820933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6787573834296349113094577 5090680375722261834820933)
              ·
                refine ⟨954502570447924094028925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5090680375722261834820933 954502570447924094028925)
                ·
                  refine ⟨357938463917971535260847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954502570447924094028925 357938463917971535260847)
                  ·
                    rfl

theorem cell20_784218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_784218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784218 prefixEnd_784218 := by exact prefixLift 784218
  have htrace : WordTrace (prefixWord ++ tailWord_784218) baseStart_784218 baseEnd_784218 := by
    simpa [prefixWord, tailWord_784218, baseEnd_784218] using wordTrace_append hprefix tailTrace_784218
  have hstable : (prefixWord ++ tailWord_784218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784218).length < 2 ^ (prefixWord ++ tailWord_784218).sum := by decide
  have hdescent : baseEnd_784218 < baseStart_784218 := by decide
  rcases family_descends (prefixWord ++ tailWord_784218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784276 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_784276 : Nat := 118140960795 + 784276 * 2 ^ 59
def prefixEnd_784276 : Nat := 4983230072969 + 3 ^ 40 * 784276 * 2
def baseEnd_784276 : Nat := 357964936698381111327277

theorem tailTrace_784276 : CollatzResearch.WordTrace tailWord_784276 prefixEnd_784276 357964936698381111327277 := by
  unfold tailWord_784276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302447853354735261054341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19069930471139647014739121 14302447853354735261054341)
  ·
    refine ⟨2681708972504012861447689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14302447853354735261054341 2681708972504012861447689)
    ·
      refine ⟨2011281729378009646085767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2681708972504012861447689 2011281729378009646085767)
      ·
        refine ⟨3016922594067014469128651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011281729378009646085767 3016922594067014469128651)
        ·
          refine ⟨4525383891100521703692977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016922594067014469128651 4525383891100521703692977)
          ·
            refine ⟨3394037918325391277769733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525383891100521703692977 3394037918325391277769733)
            ·
              refine ⟨636382109686010864581825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3394037918325391277769733 636382109686010864581825)
              ·
                refine ⟨477286582264508148436369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636382109686010864581825 477286582264508148436369)
                ·
                  refine ⟨357964936698381111327277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477286582264508148436369 357964936698381111327277)
                  ·
                    rfl

theorem cell20_784276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_784276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784276 prefixEnd_784276 := by exact prefixLift 784276
  have htrace : WordTrace (prefixWord ++ tailWord_784276) baseStart_784276 baseEnd_784276 := by
    simpa [prefixWord, tailWord_784276, baseEnd_784276] using wordTrace_append hprefix tailTrace_784276
  have hstable : (prefixWord ++ tailWord_784276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784276).length < 2 ^ (prefixWord ++ tailWord_784276).sum := by decide
  have hdescent : baseEnd_784276 < baseStart_784276 := by decide
  rcases family_descends (prefixWord ++ tailWord_784276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784332 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_784332 : Nat := 118140960795 + 784332 * 2 ^ 59
def prefixEnd_784332 : Nat := 4983230072969 + 3 ^ 40 * 784332 * 2
def baseEnd_784332 : Nat := 357990496624293805460381

theorem tailTrace_784332 : CollatzResearch.WordTrace tailWord_784332 prefixEnd_784332 357990496624293805460381 := by
  unfold tailWord_784332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303469097253296043073625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19071292129671061390764833 14303469097253296043073625)
  ·
    refine ⟨10727601822939972032305219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14303469097253296043073625 10727601822939972032305219)
    ·
      refine ⟨16091402734409958048457829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10727601822939972032305219 16091402734409958048457829)
      ·
        refine ⟨3017138012701867134085843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16091402734409958048457829 3017138012701867134085843)
        ·
          refine ⟨4525707019052800701128765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017138012701867134085843 4525707019052800701128765)
          ·
            refine ⟨1697140132144800262923287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4525707019052800701128765 1697140132144800262923287)
            ·
              refine ⟨2545710198217200394384931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697140132144800262923287 2545710198217200394384931)
              ·
                refine ⟨3818565297325800591577397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545710198217200394384931 3818565297325800591577397)
                ·
                  refine ⟨357990496624293805460381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818565297325800591577397 357990496624293805460381)
                  ·
                    rfl

theorem cell20_784332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_784332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784332 prefixEnd_784332 := by exact prefixLift 784332
  have htrace : WordTrace (prefixWord ++ tailWord_784332) baseStart_784332 baseEnd_784332 := by
    simpa [prefixWord, tailWord_784332, baseEnd_784332] using wordTrace_append hprefix tailTrace_784332
  have hstable : (prefixWord ++ tailWord_784332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784332).length < 2 ^ (prefixWord ++ tailWord_784332).sum := by decide
  have hdescent : baseEnd_784332 < baseStart_784332 := by decide
  rcases family_descends (prefixWord ++ tailWord_784332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784359 : List Nat := [1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_784359 : Nat := 118140960795 + 784359 * 2 ^ 59
def prefixEnd_784359 : Nat := 4983230072969 + 3 ^ 40 * 784359 * 2
def baseEnd_784359 : Nat := 119334273386667237186757

theorem tailTrace_784359 : CollatzResearch.WordTrace tailWord_784359 prefixEnd_784359 119334273386667237186757 := by
  unfold tailWord_784359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28607922965408775697380131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19071948643605850464920087 28607922965408775697380131)
  ·
    refine ⟨42911884448113163546070197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28607922965408775697380131 42911884448113163546070197)
    ·
      refine ⟨4022989167010609082444081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42911884448113163546070197 4022989167010609082444081)
      ·
        refine ⟨3017241875257956811833061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4022989167010609082444081 3017241875257956811833061)
        ·
          refine ⟨565732851610866902218699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3017241875257956811833061 565732851610866902218699)
          ·
            refine ⟨848599277416300353328049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565732851610866902218699 848599277416300353328049)
            ·
              refine ⟨636449458062225264996037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848599277416300353328049 636449458062225264996037)
              ·
                refine ⟨119334273386667237186757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636449458062225264996037 119334273386667237186757)
                ·
                  rfl

theorem cell20_784359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_784359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784359 prefixEnd_784359 := by exact prefixLift 784359
  have htrace : WordTrace (prefixWord ++ tailWord_784359) baseStart_784359 baseEnd_784359 := by
    simpa [prefixWord, tailWord_784359, baseEnd_784359] using wordTrace_append hprefix tailTrace_784359
  have hstable : (prefixWord ++ tailWord_784359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784359).length < 2 ^ (prefixWord ++ tailWord_784359).sum := by decide
  have hdescent : baseEnd_784359 < baseStart_784359 := by decide
  rcases family_descends (prefixWord ++ tailWord_784359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784408 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_784408 : Nat := 118140960795 + 784408 * 2 ^ 59
def prefixEnd_784408 : Nat := 4983230072969 + 3 ^ 40 * 784408 * 2
def baseEnd_784408 : Nat := 358025185095175318926737

theorem tailTrace_784408 : CollatzResearch.WordTrace tailWord_784408 prefixEnd_784408 358025185095175318926737 := by
  unfold tailWord_784408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304855071115628532956939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19073140094820838043942585 14304855071115628532956939)
  ·
    refine ⟨21457282606673442799435409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304855071115628532956939 21457282606673442799435409)
    ·
      refine ⟨16092961955005082099576557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21457282606673442799435409 16092961955005082099576557)
      ·
        refine ⟨6034860733126905787341209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16092961955005082099576557 6034860733126905787341209)
        ·
          refine ⟨4526145549845179340505907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6034860733126905787341209 4526145549845179340505907)
          ·
            refine ⟨6789218324767769010758861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526145549845179340505907 6789218324767769010758861)
            ·
              refine ⟨2545956871787913379034573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6789218324767769010758861 2545956871787913379034573)
              ·
                refine ⟨954733826920467517137965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2545956871787913379034573 954733826920467517137965)
                ·
                  refine ⟨358025185095175318926737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954733826920467517137965 358025185095175318926737)
                  ·
                    rfl

theorem cell20_784408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_784408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784408 prefixEnd_784408 := by exact prefixLift 784408
  have htrace : WordTrace (prefixWord ++ tailWord_784408) baseStart_784408 baseEnd_784408 := by
    simpa [prefixWord, tailWord_784408, baseEnd_784408] using wordTrace_append hprefix tailTrace_784408
  have hstable : (prefixWord ++ tailWord_784408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784408).length < 2 ^ (prefixWord ++ tailWord_784408).sum := by decide
  have hdescent : baseEnd_784408 < baseStart_784408 := by decide
  rcases family_descends (prefixWord ++ tailWord_784408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784449 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 2]
def baseStart_784449 : Nat := 118140960795 + 784449 * 2 ^ 59
def prefixEnd_784449 : Nat := 4983230072969 + 3 ^ 40 * 784449 * 2
def baseEnd_784449 : Nat := 358043898612361398559903

theorem tailTrace_784449 : CollatzResearch.WordTrace tailWord_784449 prefixEnd_784449 358043898612361398559903 := by
  unfold tailWord_784449
  simp only [CollatzResearch.WordTrace]
  refine ⟨28611205535082721068156401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19074137023388480712104267 28611205535082721068156401)
  ·
    refine ⟨21458404151312040801117301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28611205535082721068156401 21458404151312040801117301)
    ·
      refine ⟨2011725389185503825104747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21458404151312040801117301 2011725389185503825104747)
      ·
        refine ⟨3017588083778255737657121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011725389185503825104747 3017588083778255737657121)
        ·
          refine ⟨2263191062833691803242841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3017588083778255737657121 2263191062833691803242841)
          ·
            refine ⟨1697393297125268852432131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263191062833691803242841 1697393297125268852432131)
            ·
              refine ⟨2546089945687903278648197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697393297125268852432131 2546089945687903278648197)
              ·
                refine ⟨477391864816481864746537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2546089945687903278648197 477391864816481864746537)
                ·
                  refine ⟨358043898612361398559903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477391864816481864746537 358043898612361398559903)
                  ·
                    rfl

theorem cell20_784449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_784449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784449 prefixEnd_784449 := by exact prefixLift 784449
  have htrace : WordTrace (prefixWord ++ tailWord_784449) baseStart_784449 baseEnd_784449 := by
    simpa [prefixWord, tailWord_784449, baseEnd_784449] using wordTrace_append hprefix tailTrace_784449
  have hstable : (prefixWord ++ tailWord_784449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784449).length < 2 ^ (prefixWord ++ tailWord_784449).sum := by decide
  have hdescent : baseEnd_784449 < baseStart_784449 := by decide
  rcases family_descends (prefixWord ++ tailWord_784449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784460 : List Nat := [2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_784460 : Nat := 118140960795 + 784460 * 2 ^ 59
def prefixEnd_784460 : Nat := 4983230072969 + 3 ^ 40 * 784460 * 2
def baseEnd_784460 : Nat := 119349639770698083064397

theorem tailTrace_784460 : CollatzResearch.WordTrace tailWord_784460 prefixEnd_784460 119349639770698083064397 := by
  unfold tailWord_784460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305803369021434973403417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19074404492028579964537889 14305803369021434973403417)
  ·
    refine ⟨10729352526766076230052563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14305803369021434973403417 10729352526766076230052563)
    ·
      refine ⟨16094028790149114345078845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10729352526766076230052563 16094028790149114345078845)
      ·
        refine ⟨6035260796305917879404567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16094028790149114345078845 6035260796305917879404567)
        ·
          refine ⟨9052891194458876819106851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035260796305917879404567 9052891194458876819106851)
          ·
            refine ⟨13579336791688315228660277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052891194458876819106851 13579336791688315228660277)
            ·
              refine ⟨1273062824220779552686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13579336791688315228660277 1273062824220779552686901)
              ·
                refine ⟨119349639770698083064397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273062824220779552686901 119349639770698083064397)
                ·
                  rfl

theorem cell20_784460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_784460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784460 prefixEnd_784460 := by exact prefixLift 784460
  have htrace : WordTrace (prefixWord ++ tailWord_784460) baseStart_784460 baseEnd_784460 := by
    simpa [prefixWord, tailWord_784460, baseEnd_784460] using wordTrace_append hprefix tailTrace_784460
  have hstable : (prefixWord ++ tailWord_784460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784460).length < 2 ^ (prefixWord ++ tailWord_784460).sum := by decide
  have hdescent : baseEnd_784460 < baseStart_784460 := by decide
  rcases family_descends (prefixWord ++ tailWord_784460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784498 : List Nat := [3, 2, 1, 2, 2, 3, 7]
def baseStart_784498 : Nat := 118140960795 + 784498 * 2 ^ 59
def prefixEnd_784498 : Nat := 4983230072969 + 3 ^ 40 * 784498 * 2
def baseEnd_784498 : Nat := 39785140394170556214041

theorem tailTrace_784498 : CollatzResearch.WordTrace tailWord_784498 prefixEnd_784498 39785140394170556214041 := by
  unfold tailWord_784498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153248177976300609172537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19075328474603468291126765 7153248177976300609172537)
  ·
    refine ⟨5364936133482225456879403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7153248177976300609172537 5364936133482225456879403)
    ·
      refine ⟨8047404200223338185319105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364936133482225456879403 8047404200223338185319105)
      ·
        refine ⟨6035553150167503638989329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8047404200223338185319105 6035553150167503638989329)
        ·
          refine ⟨4526664862625627729241997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6035553150167503638989329 4526664862625627729241997)
          ·
            refine ⟨1697499323484610398465749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4526664862625627729241997 1697499323484610398465749)
            ·
              refine ⟨39785140394170556214041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1697499323484610398465749 39785140394170556214041)
              ·
                rfl

theorem cell20_784498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_784498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784498 prefixEnd_784498 := by exact prefixLift 784498
  have htrace : WordTrace (prefixWord ++ tailWord_784498) baseStart_784498 baseEnd_784498 := by
    simpa [prefixWord, tailWord_784498, baseEnd_784498] using wordTrace_append hprefix tailTrace_784498
  have hstable : (prefixWord ++ tailWord_784498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784498).length < 2 ^ (prefixWord ++ tailWord_784498).sum := by decide
  have hdescent : baseEnd_784498 < baseStart_784498 := by decide
  rcases family_descends (prefixWord ++ tailWord_784498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784508 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_784508 : Nat := 118140960795 + 784508 * 2 ^ 59
def prefixEnd_784508 : Nat := 4983230072969 + 3 ^ 40 * 784508 * 2
def baseEnd_784508 : Nat := 358070827820019415592995

theorem tailTrace_784508 : CollatzResearch.WordTrace tailWord_784508 prefixEnd_784508 358070827820019415592995 := by
  unfold tailWord_784508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306678720934487072277089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19075571627912649429702785 14306678720934487072277089)
  ·
    refine ⟨10730009040700865304207817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14306678720934487072277089 10730009040700865304207817)
    ·
      refine ⟨8047506780525648978155863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10730009040700865304207817 8047506780525648978155863)
      ·
        refine ⟨12071260170788473467233795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047506780525648978155863 12071260170788473467233795)
        ·
          refine ⟨18106890256182710200850693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071260170788473467233795 18106890256182710200850693)
          ·
            refine ⟨3395041923034258162659505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18106890256182710200850693 3395041923034258162659505)
            ·
              refine ⟨2546281442275693621994629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395041923034258162659505 2546281442275693621994629)
              ·
                refine ⟨477427770426692554123993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2546281442275693621994629 477427770426692554123993)
                ·
                  refine ⟨358070827820019415592995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477427770426692554123993 358070827820019415592995)
                  ·
                    rfl

theorem cell20_784508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_784508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784508 prefixEnd_784508 := by exact prefixLift 784508
  have htrace : WordTrace (prefixWord ++ tailWord_784508) baseStart_784508 baseEnd_784508 := by
    simpa [prefixWord, tailWord_784508, baseEnd_784508] using wordTrace_append hprefix tailTrace_784508
  have hstable : (prefixWord ++ tailWord_784508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784508).length < 2 ^ (prefixWord ++ tailWord_784508).sum := by decide
  have hdescent : baseEnd_784508 < baseStart_784508 := by decide
  rcases family_descends (prefixWord ++ tailWord_784508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784532 : List Nat := [2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_784532 : Nat := 118140960795 + 784532 * 2 ^ 59
def prefixEnd_784532 : Nat := 4983230072969 + 3 ^ 40 * 784532 * 2
def baseEnd_784532 : Nat := 119360594024660666264299

theorem tailTrace_784532 : CollatzResearch.WordTrace tailWord_784532 prefixEnd_784532 119360594024660666264299 := by
  unfold tailWord_784532
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307116396891013121713925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19076155195854684162285233 14307116396891013121713925)
  ·
    refine ⟨2682584324417064960321361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14307116396891013121713925 2682584324417064960321361)
    ·
      refine ⟨2011938243312798720241021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2682584324417064960321361 2011938243312798720241021)
      ·
        refine ⟨754476841242299520090383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2011938243312798720241021 754476841242299520090383)
        ·
          refine ⟨1131715261863449280135575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754476841242299520090383 1131715261863449280135575)
          ·
            refine ⟨1697572892795173920203363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131715261863449280135575 1697572892795173920203363)
            ·
              refine ⟨2546359339192760880305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697572892795173920203363 2546359339192760880305045)
              ·
                refine ⟨119360594024660666264299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2546359339192760880305045 119360594024660666264299)
                ·
                  rfl

theorem cell20_784532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_784532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784532 prefixEnd_784532 := by exact prefixLift 784532
  have htrace : WordTrace (prefixWord ++ tailWord_784532) baseStart_784532 baseEnd_784532 := by
    simpa [prefixWord, tailWord_784532, baseEnd_784532] using wordTrace_append hprefix tailTrace_784532
  have hstable : (prefixWord ++ tailWord_784532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784532).length < 2 ^ (prefixWord ++ tailWord_784532).sum := by decide
  have hdescent : baseEnd_784532 < baseStart_784532 := by decide
  rcases family_descends (prefixWord ++ tailWord_784532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784534 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_784534 : Nat := 118140960795 + 784534 * 2 ^ 59
def prefixEnd_784534 : Nat := 4983230072969 + 3 ^ 40 * 784534 * 2
def baseEnd_784534 : Nat := 358082694928478880726223

theorem tailTrace_784534 : CollatzResearch.WordTrace tailWord_784534 prefixEnd_784534 358082694928478880726223 := by
  unfold tailWord_784534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788394108735923786562541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19076203826516520390000437 1788394108735923786562541)
  ·
    refine ⟨670647790775971419960953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1788394108735923786562541 670647790775971419960953)
    ·
      refine ⟨502985843081978564970715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 670647790775971419960953 502985843081978564970715)
      ·
        refine ⟨754478764622967847456073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502985843081978564970715 754478764622967847456073)
        ·
          refine ⟨565859073467225885592055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754478764622967847456073 565859073467225885592055)
          ·
            refine ⟨848788610200838828388083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565859073467225885592055 848788610200838828388083)
            ·
              refine ⟨1273182915301258242582125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848788610200838828388083 1273182915301258242582125)
              ·
                refine ⟨477443593237971840968297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273182915301258242582125 477443593237971840968297)
                ·
                  refine ⟨358082694928478880726223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477443593237971840968297 358082694928478880726223)
                  ·
                    rfl

theorem cell20_784534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_784534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784534 prefixEnd_784534 := by exact prefixLift 784534
  have htrace : WordTrace (prefixWord ++ tailWord_784534) baseStart_784534 baseEnd_784534 := by
    simpa [prefixWord, tailWord_784534, baseEnd_784534] using wordTrace_append hprefix tailTrace_784534
  have hstable : (prefixWord ++ tailWord_784534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784534).length < 2 ^ (prefixWord ++ tailWord_784534).sum := by decide
  have hdescent : baseEnd_784534 < baseStart_784534 := by decide
  rcases family_descends (prefixWord ++ tailWord_784534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784567 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_784567 : Nat := 118140960795 + 784567 * 2 ^ 59
def prefixEnd_784567 : Nat := 4983230072969 + 3 ^ 40 * 784567 * 2
def baseEnd_784567 : Nat := 358097757027677432626087

theorem tailTrace_784567 : CollatzResearch.WordTrace tailWord_784567 prefixEnd_784567 358097757027677432626087 := by
  unfold tailWord_784567
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615509348655227220951955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19077006232436818147301303 28615509348655227220951955)
  ·
    refine ⟨42923264022982840831427933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28615509348655227220951955 42923264022982840831427933)
    ·
      refine ⟨16096224008618565311785475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42923264022982840831427933 16096224008618565311785475)
      ·
        refine ⟨24144336012927847967678213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16096224008618565311785475 24144336012927847967678213)
        ·
          refine ⟨4527063002423971493939665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24144336012927847967678213 4527063002423971493939665)
          ·
            refine ⟨3395297251817978620454749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527063002423971493939665 3395297251817978620454749)
            ·
              refine ⟨1273236469431741982670531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395297251817978620454749 1273236469431741982670531)
              ·
                refine ⟨1909854704147612974005797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273236469431741982670531 1909854704147612974005797)
                ·
                  refine ⟨358097757027677432626087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909854704147612974005797 358097757027677432626087)
                  ·
                    rfl

theorem cell20_784567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_784567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784567 prefixEnd_784567 := by exact prefixLift 784567
  have htrace : WordTrace (prefixWord ++ tailWord_784567) baseStart_784567 baseEnd_784567 := by
    simpa [prefixWord, tailWord_784567, baseEnd_784567] using wordTrace_append hprefix tailTrace_784567
  have hstable : (prefixWord ++ tailWord_784567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784567).length < 2 ^ (prefixWord ++ tailWord_784567).sum := by decide
  have hdescent : baseEnd_784567 < baseStart_784567 := by decide
  rcases family_descends (prefixWord ++ tailWord_784567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784615 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_784615 : Nat := 118140960795 + 784615 * 2 ^ 59
def prefixEnd_784615 : Nat := 4983230072969 + 3 ^ 40 * 784615 * 2
def baseEnd_784615 : Nat := 358119665535602599025891

theorem tailTrace_784615 : CollatzResearch.WordTrace tailWord_784615 prefixEnd_784615 358119665535602599025891 := by
  unfold tailWord_784615
  simp only [CollatzResearch.WordTrace]
  refine ⟨28617260052481331418699299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19078173368320887612466199 28617260052481331418699299)
  ·
    refine ⟨42925890078721997128048949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28617260052481331418699299 42925890078721997128048949)
    ·
      refine ⟨4024302194880187230754589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42925890078721997128048949 4024302194880187230754589)
      ·
        refine ⟨1509113323080070211532971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4024302194880187230754589 1509113323080070211532971)
        ·
          refine ⟨2263669984620105317299457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509113323080070211532971 2263669984620105317299457)
          ·
            refine ⟨1697752488465078987974593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263669984620105317299457 1697752488465078987974593)
            ·
              refine ⟨1273314366348809240980945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697752488465078987974593 1273314366348809240980945)
              ·
                refine ⟨954985774761606930735709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273314366348809240980945 954985774761606930735709)
                ·
                  refine ⟨358119665535602599025891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954985774761606930735709 358119665535602599025891)
                  ·
                    rfl

theorem cell20_784615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_784615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784615 prefixEnd_784615 := by exact prefixLift 784615
  have htrace : WordTrace (prefixWord ++ tailWord_784615) baseStart_784615 baseEnd_784615 := by
    simpa [prefixWord, tailWord_784615, baseEnd_784615] using wordTrace_append hprefix tailTrace_784615
  have hstable : (prefixWord ++ tailWord_784615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784615).length < 2 ^ (prefixWord ++ tailWord_784615).sum := by decide
  have hdescent : baseEnd_784615 < baseStart_784615 := by decide
  rcases family_descends (prefixWord ++ tailWord_784615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784633 : List Nat := [1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_784633 : Nat := 118140960795 + 784633 * 2 ^ 59
def prefixEnd_784633 : Nat := 4983230072969 + 3 ^ 40 * 784633 * 2
def baseEnd_784633 : Nat := 119375960408691512141939

theorem tailTrace_784633 : CollatzResearch.WordTrace tailWord_784633 prefixEnd_784633 119375960408691512141939 := by
  unfold tailWord_784633
  simp only [CollatzResearch.WordTrace]
  refine ⟨28617916566416120492854553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19078611044277413661903035 28617916566416120492854553)
  ·
    refine ⟨21463437424812090369640915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28617916566416120492854553 21463437424812090369640915)
    ·
      refine ⟨32195156137218135554461373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21463437424812090369640915 32195156137218135554461373)
      ·
        refine ⟨12073183551456800832923015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32195156137218135554461373 12073183551456800832923015)
        ·
          refine ⟨18109775327185201249384523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12073183551456800832923015 18109775327185201249384523)
          ·
            refine ⟨27164662990777801874076785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109775327185201249384523 27164662990777801874076785)
            ·
              refine ⟨20373497243083351405557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27164662990777801874076785 20373497243083351405557589)
              ·
                refine ⟨119375960408691512141939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20373497243083351405557589 119375960408691512141939)
                ·
                  rfl

theorem cell20_784633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_784633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784633 prefixEnd_784633 := by exact prefixLift 784633
  have htrace : WordTrace (prefixWord ++ tailWord_784633) baseStart_784633 baseEnd_784633 := by
    simpa [prefixWord, tailWord_784633, baseEnd_784633] using wordTrace_append hprefix tailTrace_784633
  have hstable : (prefixWord ++ tailWord_784633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784633).length < 2 ^ (prefixWord ++ tailWord_784633).sum := by decide
  have hdescent : baseEnd_784633 < baseStart_784633 := by decide
  rcases family_descends (prefixWord ++ tailWord_784633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784636 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_784636 : Nat := 118140960795 + 784636 * 2 ^ 59
def prefixEnd_784636 : Nat := 4983230072969 + 3 ^ 40 * 784636 * 2
def baseEnd_784636 : Nat := 358129250507819859325805

theorem tailTrace_784636 : CollatzResearch.WordTrace tailWord_784636 prefixEnd_784636 358129250507819859325805 := by
  unfold tailWord_784636
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309012992702626002606881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19078683990270168003475841 14309012992702626002606881)
  ·
    refine ⟨10731759744526969501955161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14309012992702626002606881 10731759744526969501955161)
    ·
      refine ⟨8048819808395227126466371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10731759744526969501955161 8048819808395227126466371)
      ·
        refine ⟨12073229712592840689699557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8048819808395227126466371 12073229712592840689699557)
        ·
          refine ⟨2263730571111157629318667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12073229712592840689699557 2263730571111157629318667)
          ·
            refine ⟨3395595856666736443978001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263730571111157629318667 3395595856666736443978001)
            ·
              refine ⟨2546696892500052332983501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395595856666736443978001 2546696892500052332983501)
              ·
                refine ⟨955011334687519624868813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2546696892500052332983501 955011334687519624868813)
                ·
                  refine ⟨358129250507819859325805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955011334687519624868813 358129250507819859325805)
                  ·
                    rfl

theorem cell20_784636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_784636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784636 prefixEnd_784636 := by exact prefixLift 784636
  have htrace : WordTrace (prefixWord ++ tailWord_784636) baseStart_784636 baseEnd_784636 := by
    simpa [prefixWord, tailWord_784636, baseEnd_784636] using wordTrace_append hprefix tailTrace_784636
  have hstable : (prefixWord ++ tailWord_784636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784636).length < 2 ^ (prefixWord ++ tailWord_784636).sum := by decide
  have hdescent : baseEnd_784636 < baseStart_784636 := by decide
  rcases family_descends (prefixWord ++ tailWord_784636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784664 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_784664 : Nat := 118140960795 + 784664 * 2 ^ 59
def prefixEnd_784664 : Nat := 4983230072969 + 3 ^ 40 * 784664 * 2
def baseEnd_784664 : Nat := 358142030470776206392357

theorem tailTrace_784664 : CollatzResearch.WordTrace tailWord_784664 prefixEnd_784664 358142030470776206392357 := by
  unfold tailWord_784664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309523614651906393616523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19079364819535875191488697 14309523614651906393616523)
  ·
    refine ⟨21464285421977859590424785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14309523614651906393616523 21464285421977859590424785)
    ·
      refine ⟨16098214066483394692818589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21464285421977859590424785 16098214066483394692818589)
      ·
        refine ⟨6036830274931273009806971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16098214066483394692818589 6036830274931273009806971)
        ·
          refine ⟨9055245412396909514710457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036830274931273009806971 9055245412396909514710457)
          ·
            refine ⟨6791434059297682136032843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9055245412396909514710457 6791434059297682136032843)
            ·
              refine ⟨10187151088946523204049265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791434059297682136032843 10187151088946523204049265)
              ·
                refine ⟨7640363316709892403036949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10187151088946523204049265 7640363316709892403036949)
                ·
                  refine ⟨358142030470776206392357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7640363316709892403036949 358142030470776206392357)
                  ·
                    rfl

theorem cell20_784664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_784664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784664 prefixEnd_784664 := by exact prefixLift 784664
  have htrace : WordTrace (prefixWord ++ tailWord_784664) baseStart_784664 baseEnd_784664 := by
    simpa [prefixWord, tailWord_784664, baseEnd_784664] using wordTrace_append hprefix tailTrace_784664
  have hstable : (prefixWord ++ tailWord_784664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784664).length < 2 ^ (prefixWord ++ tailWord_784664).sum := by decide
  have hdescent : baseEnd_784664 < baseStart_784664 := by decide
  rcases family_descends (prefixWord ++ tailWord_784664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784670 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_784670 : Nat := 118140960795 + 784670 * 2 ^ 59
def prefixEnd_784670 : Nat := 4983230072969 + 3 ^ 40 * 784670 * 2
def baseEnd_784670 : Nat := 358144769034266852192333

theorem tailTrace_784670 : CollatzResearch.WordTrace tailWord_784670 prefixEnd_784670 358144769034266852192333 := by
  unfold tailWord_784670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577408258410259476493933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19079510711521383874634309 3577408258410259476493933)
  ·
    refine ⟨1341528096903847303685225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3577408258410259476493933 1341528096903847303685225)
    ·
      refine ⟨1006146072677885477763919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341528096903847303685225 1006146072677885477763919)
      ·
        refine ⟨1509219109016828216645879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006146072677885477763919 1509219109016828216645879)
        ·
          refine ⟨2263828663525242324968819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509219109016828216645879 2263828663525242324968819)
          ·
            refine ⟨3395742995287863487453229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263828663525242324968819 3395742995287863487453229)
            ·
              refine ⟨1273403623232948807794961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395742995287863487453229 1273403623232948807794961)
              ·
                refine ⟨955052717424711605846221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273403623232948807794961 955052717424711605846221)
                ·
                  refine ⟨358144769034266852192333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955052717424711605846221 358144769034266852192333)
                  ·
                    rfl

theorem cell20_784670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_784670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784670 prefixEnd_784670 := by exact prefixLift 784670
  have htrace : WordTrace (prefixWord ++ tailWord_784670) baseStart_784670 baseEnd_784670 := by
    simpa [prefixWord, tailWord_784670, baseEnd_784670] using wordTrace_append hprefix tailTrace_784670
  have hstable : (prefixWord ++ tailWord_784670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784670).length < 2 ^ (prefixWord ++ tailWord_784670).sum := by decide
  have hdescent : baseEnd_784670 < baseStart_784670 := by decide
  rcases family_descends (prefixWord ++ tailWord_784670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784674 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_784674 : Nat := 118140960795 + 784674 * 2 ^ 59
def prefixEnd_784674 : Nat := 4983230072969 + 3 ^ 40 * 784674 * 2
def baseEnd_784674 : Nat := 358146594743260616058983

theorem tailTrace_784674 : CollatzResearch.WordTrace tailWord_784674 prefixEnd_784674 358146594743260616058983 := by
  unfold tailWord_784674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154852989816896123774269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19079607972845056330064717 7154852989816896123774269)
  ·
    refine ⟨2683069871181336046415351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7154852989816896123774269 2683069871181336046415351)
    ·
      refine ⟨4024604806772004069623027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683069871181336046415351 4024604806772004069623027)
      ·
        refine ⟨6036907210158006104434541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024604806772004069623027 6036907210158006104434541)
        ·
          refine ⟨2263840203809252289162953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6036907210158006104434541 2263840203809252289162953)
          ·
            refine ⟨1697880152856939216872215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263840203809252289162953 1697880152856939216872215)
            ·
              refine ⟨2546820229285408825308323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697880152856939216872215 2546820229285408825308323)
              ·
                refine ⟨3820230343928113237962485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546820229285408825308323 3820230343928113237962485)
                ·
                  refine ⟨358146594743260616058983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820230343928113237962485 358146594743260616058983)
                  ·
                    rfl

theorem cell20_784674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_784674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784674 prefixEnd_784674 := by exact prefixLift 784674
  have htrace : WordTrace (prefixWord ++ tailWord_784674) baseStart_784674 baseEnd_784674 := by
    simpa [prefixWord, tailWord_784674, baseEnd_784674] using wordTrace_append hprefix tailTrace_784674
  have hstable : (prefixWord ++ tailWord_784674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784674).length < 2 ^ (prefixWord ++ tailWord_784674).sum := by decide
  have hdescent : baseEnd_784674 < baseStart_784674 := by decide
  rcases family_descends (prefixWord ++ tailWord_784674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784695 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_784695 : Nat := 118140960795 + 784695 * 2 ^ 59
def prefixEnd_784695 : Nat := 4983230072969 + 3 ^ 40 * 784695 * 2
def baseEnd_784695 : Nat := 358156179715477876358897

theorem tailTrace_784695 : CollatzResearch.WordTrace tailWord_784695 prefixEnd_784695 358156179715477876358897 := by
  unfold tailWord_784695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28620177892191505081611539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19080118594794336721074359 28620177892191505081611539)
  ·
    refine ⟨42930266838287257622417309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28620177892191505081611539 42930266838287257622417309)
    ·
      refine ⟨16098850064357721608406491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42930266838287257622417309 16098850064357721608406491)
      ·
        refine ⟨24148275096536582412609737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16098850064357721608406491 24148275096536582412609737)
        ·
          refine ⟨18111206322402436809457303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24148275096536582412609737 18111206322402436809457303)
          ·
            refine ⟨27166809483603655214185955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111206322402436809457303 27166809483603655214185955)
            ·
              refine ⟨40750214225405482821278933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27166809483603655214185955 40750214225405482821278933)
              ·
                refine ⟨955083145907941003623725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40750214225405482821278933 955083145907941003623725)
                ·
                  refine ⟨358156179715477876358897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955083145907941003623725 358156179715477876358897)
                  ·
                    rfl

theorem cell20_784695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_784695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784695 prefixEnd_784695 := by exact prefixLift 784695
  have htrace : WordTrace (prefixWord ++ tailWord_784695) baseStart_784695 baseEnd_784695 := by
    simpa [prefixWord, tailWord_784695, baseEnd_784695] using wordTrace_append hprefix tailTrace_784695
  have hstable : (prefixWord ++ tailWord_784695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784695).length < 2 ^ (prefixWord ++ tailWord_784695).sum := by decide
  have hdescent : baseEnd_784695 < baseStart_784695 := by decide
  rcases family_descends (prefixWord ++ tailWord_784695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784705 : List Nat := [1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_784705 : Nat := 118140960795 + 784705 * 2 ^ 59
def prefixEnd_784705 : Nat := 4983230072969 + 3 ^ 40 * 784705 * 2
def baseEnd_784705 : Nat := 119386914662654095341841

theorem tailTrace_784705 : CollatzResearch.WordTrace tailWord_784705 prefixEnd_784705 119386914662654095341841 := by
  unfold tailWord_784705
  simp only [CollatzResearch.WordTrace]
  refine ⟨28620542622155276789475569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19080361748103517859650379 28620542622155276789475569)
  ·
    refine ⟨21465406966616457592106677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28620542622155276789475569 21465406966616457592106677)
    ·
      refine ⟨2012381903120292899260001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21465406966616457592106677 2012381903120292899260001)
      ·
        refine ⟨1509286427340219674445001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012381903120292899260001 1509286427340219674445001)
        ·
          refine ⟨1131964820505164755833751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1509286427340219674445001 1131964820505164755833751)
          ·
            refine ⟨1697947230757747133750627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131964820505164755833751 1697947230757747133750627)
            ·
              refine ⟨2546920846136620700625941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697947230757747133750627 2546920846136620700625941)
              ·
                refine ⟨119386914662654095341841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2546920846136620700625941 119386914662654095341841)
                ·
                  rfl

theorem cell20_784705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_784705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784705 prefixEnd_784705 := by exact prefixLift 784705
  have htrace : WordTrace (prefixWord ++ tailWord_784705) baseStart_784705 baseEnd_784705 := by
    simpa [prefixWord, tailWord_784705, baseEnd_784705] using wordTrace_append hprefix tailTrace_784705
  have hstable : (prefixWord ++ tailWord_784705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784705).length < 2 ^ (prefixWord ++ tailWord_784705).sum := by decide
  have hdescent : baseEnd_784705 < baseStart_784705 := by decide
  rcases family_descends (prefixWord ++ tailWord_784705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
